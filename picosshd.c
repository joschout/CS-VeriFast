/**
 * picosshd : very minimalistic SSH server (do not use in production!)
 *
 * " This is not an SSH server, it is something the SSH client can
 *   connect to "
 * In other words: DO. NOT. USE.
 * EVER.
 *
 * You have been warned.
 *
 * Relevant RFCs are:
 * - RFC4251: The Secure Shell (SSH) Protocol Architecture
 * - RFC4250: The Secure Shell (SSH) Protocol Assigned Numbers
 * - RFC4253: The Secure Shell (SSH) Transport Layer Protocol
 * - RFC5656: Elliptic Curve Algorithm Integration in the Secure Shell Transport Layer
 * - RFC4254: The Secure Shell (SSH) Connection Protocol
 *
 * Linux (Debian 8, Ubuntu 15.04 (Vivid) or later, or compatible)
 * =====
 *
 *   Type these commands on the command line to build and run picosshd:
 *
 *     sudo apt-get install gcc pkg-config libsodium-dev make
 *     cd REPLACE/WITH/DIRECTORY/OF/PICOSSHD
 *     make
 *     sudo ufw enable # Enable Ubuntu's Uncomplicated Firewall (optional)
 *     ./picosshd
 *
 * Windows
 * =======
 *   Install cygwin from https://cygwin.com/install.html (32bit, 64bit is untested)
 *   In the cygwin installer, make sure gcc-core, pkg-config and ca-certificates are
 *   marked for installation.
 *   (you might need some more packages than installed by default, this is untested).
 *
 *   After the cygwin installation has finished, open the cygwin terminal and 
 *   type the following commands:
 *     wget https://download.libsodium.org/libsodium/releases/libsodium-1.0.6.tar.gz
 *     tar xzf libsodium-1.0.6.tar.gz
 *     cd libsodium-1.0.6
 *     ./configure
 *     make
 *     make install
 *     cd /cygdrive/c/directory/of/picosshd
 *     export PKG_CONFIG_PATH=/usr/local/lib/pkgconfig
 *     make
 *     ./picosshd
 *   
 * Other
 * =====
 * 
 *   Unknown. You can run the latest Ubuntu in a virtual machine
 *   (such as Oracle VirtualBox).
 *
 * Connecting to the server
 * ========================
 *  Execute:
 * 
 *    ssh USERNAME@localhost -p 2222 menu
 * 
 *  The initial USERNAME is "admin" with password "123".
 *
 *  This also works under cygwin (install ssh first).
 *  The Putty SSH client does not work because putty does not support the
 *  key exchange algorithm.
 */

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h> // abort()
#include <string.h>
#include "picosshd.h"
#include "skipthis.h"

//@ import_module zout;

/*@ predicate ssh_server(struct ssh_server *server) =
      server == 0 ?
        true
      : 
        malloc_block_ssh_server(server) &*&
        server->ss |-> ?server_socket &*&
        server_socket(server_socket) &*&
        chars(server->host_pub_key, zout_sign_PUBLICKEYBYTES, _) &*&
        chars(server->host_secret_key, zout_sign_SECRETKEYBYTES, _) &*&
        server->host_key_string_without_length |-> ?hkwl &*&
        string_buffer(hkwl, _) &*&
        server->users_mutex |-> ?mutex &*&
        mutex(mutex, ssh_server_userlist(server));
 @*/
/*@ predicate ssh_session(struct ssh_session *session, struct ssh_server *server, struct ssh_kex_data *kex_data, bool isNull) =
      session == 0 ?
        true
      :
        malloc_block_ssh_session(session) &*&
        session->server |-> server &*&
        server != 0 &*&
        session->socket |-> ?socket &*&
        socket(socket) &*&
        session->kex_data |-> kex_data &*&
        (kex_data == 0 ? true : ssh_kex_data(kex_data, isNull) )&*&
        session->keys |-> ?keys &*&
        ssh_keys(keys) &*&
        (keys != 0 ) &*&
        session->cipher_block_size |-> ?cipher_block_size &*&
        (cipher_block_size >= 8) &*&
        session->packets_read |-> ?packets_read &*&
        (packets_read >= 0) &*&
        session->packets_written |-> ?packets_written &*&
        (packets_written >= 0) &*&
        session->channel_id |-> _ &*&
        session->receive_buffer |-> ?rbuffer &*&
        string_buffer(rbuffer, _) &*&
        session->logged_in_as |-> ?logged_in_as &*&
        string_buffer(logged_in_as, _);
 @*/

/*@ predicate ssh_keys(struct ssh_keys *keys) =
      keys == 0 ?
        true
      :
        malloc_block_ssh_keys(keys) &*&
        chars(keys->iv_c2s, zout_hash_sha256_BYTES, _) &*&
        chars(keys->iv_s2c, zout_hash_sha256_BYTES, _) &*&
        chars(keys->key_enc_c2s, zout_hash_sha256_BYTES, _) &*&
        chars(keys->key_enc_s2c, zout_hash_sha256_BYTES, _) &*&
        chars(keys->key_integrity_c2s, zout_hash_sha256_BYTES, _) &*&
        chars(keys->key_integrity_s2c, zout_hash_sha256_BYTES, _);

 @*/


/*@ predicate ssh_kex_data(struct ssh_kex_data *data, bool isNull) =
      data == 0 ?
        true
      :
        malloc_block_ssh_kex_data(data) &*&
        ssh_kex_data_string_buffers(data)(isNull) &*&
        chars(data->dh_server_publickey, zout_box_PUBLICKEYBYTES, _) &*&
        chars(data->dh_server_secretkey, zout_box_SECRETKEYBYTES, _) &*&
        chars(data->dh_shared_secret, zout_scalarmult_BYTES, _) &*&
        chars(data->session_id, zout_hash_sha256_BYTES, _) &*&
        chars(data->dh_hash, zout_hash_sha256_BYTES, _);


 @*/

/**@ predicate ssh_kex_data_string_buffers(struct ssh_kex_data *data) =
      	data->client_version |-> ?client_version &*&
      	( client_version == 0 ?
          data->server_version |-> 0 &*&
          data->server_kex_init |-> 0 &*&
          data->client_kex_init |-> 0 &*&
          data->dh_client_pubkey |-> 0
        :
          string_buffer(client_version, _) &*&
          data->server_version |-> ?server_version &*& server_version != 0 &*&
          string_buffer(server_version, _) &*&
          data->server_kex_init |-> ?server_kex_init  &*& server_kex_init != 0 &*&
          string_buffer(server_kex_init, _) &*&
          data->client_kex_init |-> ?client_kex_init &*& client_kex_init != 0 &*&
          string_buffer(client_kex_init, _) &*&
          data->dh_client_pubkey |-> ?dh_client_pubkey &*& dh_client_pubkey !=0 &*&
          string_buffer(dh_client_pubkey, _)
        );
@*/

/*@ predicate_ctor ssh_kex_data_string_buffers(struct ssh_kex_data *data)(bool isNull) =
      	isNull == true ?
      	(
      	  data->client_version |-> 0 &*&
          data->server_version |-> 0 &*&
          data->server_kex_init |-> 0 &*&
          data->client_kex_init |-> 0 &*&
          data->dh_client_pubkey |-> 0)
        :
         ( data->client_version |-> ?client_version &*&
          string_buffer(client_version, _) &*&
          data->server_version |-> ?server_version &*& server_version != 0 &*&
          string_buffer(server_version, _) &*&
          data->server_kex_init |-> ?server_kex_init  &*& server_kex_init != 0 &*&
          string_buffer(server_kex_init, _) &*&
          data->client_kex_init |-> ?client_kex_init &*& client_kex_init != 0 &*&
          string_buffer(client_kex_init, _) &*&
          data->dh_client_pubkey |-> ?dh_client_pubkey &*& dh_client_pubkey !=0 &*&
          string_buffer(dh_client_pubkey, _)
        );
@*/

/**@ predicate_ctor ssh_server_userlist(struct ssh_server *server)() =
      server->users |-> ?user &*&
      ssh_users(user, ?userlist);
@*/
/*@ predicate_ctor ssh_server_userlist(struct ssh_server *server)() =
      server->users |-> ?user &*&
      users_cfr_nodes(user, ?count);
@*/

// ==============================__

/*@
  predicate ssh_users(struct ssh_user *user, list<void *>values) =
    user == 0?
      values == nil<void *>
    :
      malloc_block_ssh_user(user) &*&
      user->username |-> ?name &*& string_buffer(name, _) &*&
      user->password |-> ?password &*& string_buffer(password, _) &*&
      user->mail |-> ?mail  &*& string_buffer(mail, _) &*&
      user->next |-> ?next &*&
      ssh_users(next, ?values0) &*&
      values == cons<void *>(user, values0);
@*/

/*@
  predicate ssh_users_alt(struct ssh_user *user, int count) =
    user == 0?
      count == 0 &*& single_user(0,0)
    :
      0 < count &*&
      single_user(user, ?next) &*&
      ssh_users_alt(next, count - 1);
@*/

/*@
  predicate ssh_users_alt2(struct ssh_user *user, list<void *>userList) =
    user == 0?
      userList == nil<void *> &*& single_user(0,0)
    :
      0 < length(userList) &*&
      single_user(user, ?next) &*&
      ssh_users_alt2(next, tail(userList));
@*/


/*@
  predicate single_user(struct ssh_user *user, struct ssh_user *nextUser) =
    user == 0?
      true
    :
      malloc_block_ssh_user(user) &*&
      user->username |-> ?name &*& string_buffer(name, _) &*&
      user->password |-> ?password &*& string_buffer(password, _) &*&
      user->mail |-> ?mail  &*& string_buffer(mail, _) &*&
      user->next |-> nextUser;

@*/


/*@
  predicate ssh_users_lseg(struct ssh_user *first, struct ssh_user *last, int count) =
    first == last ?
      count == 0 &*& single_user(0,0)
    :
      0 < count &*&
      first != 0 &*&
      single_user(first, ?next) &*&
      ssh_users_lseg(next, last, count - 1);
@*/

/*@
  predicate ssh_users_lseg2(struct ssh_user *first, struct ssh_user *last, list<void *>userList) =
    first == last ?
      userList == nil<void *> &*& single_user(0,0)
    :
      0 < length(userList) &*&
      first != 0 &*&
      single_user(first, ?next) &*&
      ssh_users_lseg2(next, last, tail(userList));
@*/


/**@
  lemma void lseg2_add_lemma(struct ssh_user *old_user)
    requires ssh_users_lseg2(old_user, ?user, ?userList) &*& user != 0 &*& single_user(user, ?next) &*& ssh_users_lseg2(next, 0, ?userList2);
    ensures ssh_users_lseg2(old_user, next, append(userList, cons(next, nil))) &*& ssh_users_lseg2(next, 0, userList2);
  {
    open ssh_users_lseg2(old_user, user, userList);
    if( old_user == user){
      close ssh_users_lseg2(next, next, nil);
    }
    else{
      lseg2_add_lemma(old_user);
    }
    open ssh_users_lseg2(next, 0, userList2);
    close ssh_users_lseg2(next, 0, userList2);

    close ssh_users_lseg2(old_user, next, append(userList, cons(next, nil)));
  }

@*/

/**@
  lemma void lseg_add_lemma(struct ssh_user *first)
    requires
      ssh_users_lseg(first, ?last, ?count) &*&
      last != 0 &*&
      single_user(last, ?next) &*&
      ssh_users_lseg(next, 0, ?count0);
    ensures
      ssh_users_lseg(first, next, count + 1) &*&
      ssh_users_lseg(next, 0, count0);
  {
    open ssh_users_lseg(first, last, count);
    if( first == last){
      close ssh_users_lseg(next, next, 0);
    }
    else{
      lseg_add_lemma(next);
    }
    open ssh_users_lseg(next, 0, count0);
    open single_user(next,?next0);
    close single_user(next, next0);
    close ssh_users_lseg(next, 0, count0);

    close ssh_users_lseg(first, next, count + 1);
  }

@*/



/*@
  lemma void users_to_lseg_lemma(struct ssh_user *first)
    requires ssh_users_alt(first, ?count);
    ensures ssh_users_lseg(first, 0, count);
  {
    open ssh_users_alt(first, count);
    open single_user(first, ?next);
    if (first !=0 ){
        users_to_lseg_lemma(next);
    }
    close single_user(first, next);
    close ssh_users_lseg(first, 0, count);
  }
 @*/

/*@
  lemma void users_to_lseg_lemma2(struct ssh_user *first)
    requires ssh_users_alt2(first, ?userList);
    ensures ssh_users_lseg2(first, 0, userList);
  {
    open ssh_users_alt2(first, userList);
    open single_user(first, ?next);
    if (first !=0 ){
        users_to_lseg_lemma2(next);
    }
    close single_user(first, next);
    close ssh_users_lseg2(first, 0, userList);
  }
 @*/


/*=====================================================================
 * ====================================================================
 * ================= CFR NODES ========================================
 * ====================================================================
 * ====================================================================*/

/*@
    predicate users_cfr_nodes(struct ssh_user *user, int count) =
        user == 0 ?
            count == 0
        :
            0 < count &*&
            malloc_block_ssh_user(user) &*&
            user->username |-> ?name &*& string_buffer(name, _) &*&
            user->password |-> ?password &*& string_buffer(password, _) &*&
            user->mail |-> ?mail  &*& string_buffer(mail, _) &*&
            user->next |-> ?next &*&
            users_cfr_nodes(next, count - 1);

@*/
/*@
predicate users_cfrnodes_lseg(struct ssh_user  *first, struct ssh_user  *last, int count) =
  first == last ?
    count == 0
  :
    0 < count &*&
    first != 0 &*&
    malloc_block_ssh_user(first) &*&
    first->username |-> ?name &*& string_buffer(name, _) &*&
    first->password |-> ?password &*& string_buffer(password, _) &*&
    first->mail |-> ?mail  &*& string_buffer(mail, _) &*&
    first->next |-> ?next &*&
    users_cfrnodes_lseg(next, last, count - 1);
@*/

//PROOF: nodes(first, count) == lseg(first, 0, count): they bundle the same heap chuncks and conditions
/*@
lemma void users_cfrnodes_to_lseg_lemma(struct ssh_user *first)
  requires users_cfr_nodes(first, ?count);
  ensures users_cfrnodes_lseg(first, 0, count);
{
  open users_cfr_nodes(first, count);
  if(first != 0){
    users_cfrnodes_to_lseg_lemma(first->next);
  }
  close users_cfrnodes_lseg(first, 0, count);
}
@*/
/*@
lemma void lseg_to_users_cfrnodes_lemma(struct ssh_user *first)
  requires users_cfrnodes_lseg(first, 0, ?count);
  ensures users_cfr_nodes(first, count);
{
  open users_cfrnodes_lseg(first, 0, count);
  if(first != 0){
    lseg_to_users_cfrnodes_lemma(first->next);
  }
  close users_cfr_nodes(first, count);
}
@*/

/*@
lemma void users_cfrnodes_lseg_add_lemma(struct ssh_user *first)
requires
  users_cfrnodes_lseg(first, ?last, ?count) &*&
  last != 0 &*&
   malloc_block_ssh_user(last) &*&
    last->username |-> ?name &*& string_buffer(name, _) &*&
    last->password |-> ?password &*& string_buffer(password, _) &*&
    last->mail |-> ?mail  &*& string_buffer(mail, _) &*&
    last->next |-> ?next &*&
  users_cfrnodes_lseg(next, 0, ?count0);
ensures
  users_cfrnodes_lseg(first, next, count + 1) &*&
  users_cfrnodes_lseg(next, 0, count0);
{
  open users_cfrnodes_lseg(first, last, count);
  if(first == last){
  close users_cfrnodes_lseg(next, next, 0);
  } else {
    users_cfrnodes_lseg_add_lemma(first->next);
  }
  open users_cfrnodes_lseg(next, 0, count0);
  close users_cfrnodes_lseg(next, 0, count0);
  close users_cfrnodes_lseg(first, next, count + 1);
}
@*/




/**
 * Adds a new user to the server
 *  INPUT:
 *    * pointer to ssh_server
 *    * pointer to string_buffer containing username
 *    * pointer to string_buffer containing password
 *
 * Allocates memory for new user struct to the heap.
 * Initializes this memory
 * Acquires the user_mutex from the ssh_server
 *    Adds the new user in front of the list of users
 * Releases the user_mutex
 */
void ssh_adduser(struct ssh_server *server, struct string_buffer *username, struct string_buffer *password)
/*@ requires
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(username, ?us) &*&
      string_buffer(password, ?pss);
 @*/
/*@ ensures
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(username, us) &*&
      string_buffer(password, pss);

 @*/
{
  struct ssh_user *user = malloc(sizeof(struct ssh_user));
  if (user == NULL) abort();
  ////@ requires [?f]string_buffer(username, ?cs);
  ////@ ensures [f]string_buffer(username, cs) &*& string_buffer(result, cs);
  user->username = string_buffer_copy(username);
 // //@ open string_buffer(username, _);
  user->password = string_buffer_copy(password);
  user->mail = create_string_buffer();
  mutex_acquire(server->users_mutex);
  //@ open ssh_server_userlist(server)();
  ////@ assert users_cfr_nodes(_, ?count);
  //@ open users_cfr_nodes(?oldUser, ?count);
  //@ close users_cfr_nodes(oldUser, count);
  user->next = server->users;
  server->users = user;
  ////@ close single_user(user, user->next);
  //@ close  users_cfr_nodes(user, count + 1);
  ////@close ssh_users(user, cons(user->next, _));
  //@ close ssh_server_userlist(server)();
  mutex_release(server->users_mutex);
}

/**
 * Checks whether there exists a user on the ssh_server for the given username and password.
 * If there exists such a user:
 *    sets the logged_in_as field of the session to the username of that user
 *    returns true
 * Else returns false
 *
 *
 * Acquires the user_mutex from the ssh_server belonging to the given session
 *    Takes the pointer to the list of users
 *    As long as there are still users in the list
 *    DO:
 *      IF
 *        the username for the currently selected user == given username
 *        AND password for the currently selected user == given password
 *      THEN
 *        Empty the logged_in_as field of the session
 *        Set the logged_in_ass field of the session to the given username
 *        Set the result to true
 *     ELSE
 *       set the next user as current user
 * Release the user_mutex
 */
bool ssh_auth_user(struct ssh_session *session, struct string_buffer *username, struct string_buffer *password)
/*@ requires
      session->logged_in_as |-> ?logged_in_as &*&
      string_buffer(logged_in_as, _) &*&
      session->server |-> ?server &*&
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(username, ?us) &*&
      string_buffer(password, ?pss);
@*/
/*@ ensures
      session->logged_in_as |-> ?logged_in_as2 &*&
      string_buffer(logged_in_as2, _) &*&
      session->server |-> server &*&
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(username, us) &*&
      string_buffer(password, pss); @*/
{
  bool result = false;
  // Totally not secure against timing attacks.
  mutex_acquire(session->server->users_mutex);
  ////@ close ssh_users(0, nil);
  //@ open ssh_server_userlist(server)();
  struct ssh_user *user = session->server->users;
  // Hint: You will need list segments (see tutorial) or Tuerk-loops (see tutorial).
  ////@ open ssh_users_lseg2(user, 0, ?userlist);
  ////@ close ssh_users_lseg2(user, 0, userlist);
  ////@ close single_user(0,0);
  ////@ close ssh_users_lseg2(0, 0, nil);
  //@ users_cfrnodes_to_lseg_lemma(user);

  //@ open users_cfrnodes_lseg(?first_user, 0, ?totalCount);
  //@ close users_cfrnodes_lseg(first_user, 0, totalCount);

  //@ close users_cfrnodes_lseg(user, user, 0);
  while (user != NULL)
/*@ invariant
          session->logged_in_as |-> ?log &*&
          string_buffer(log, _) &*&
          string_buffer(username, us) &*&
          string_buffer(password, pss) &*&
          users_cfrnodes_lseg(first_user, user, ?count1) &*&
          users_cfrnodes_lseg(user, 0, ?count2) &*&
          totalCount == count1 + count2; @*/
  /**@ invariant
          session->logged_in_as |-> _ &*&
          string_buffer(username, us) &*&
          string_buffer(password, pss) &*&
          ssh_users_lseg2(?old_user, user,?userlist1) &*& 
          ssh_users_lseg2(user, 0, ?userlist2) &*&
          userlist == append(userlist1, userlist2); @*/
  {
   //@ assert user != 0;
    //@ open users_cfrnodes_lseg(user, 0, count2);
    ////@ close ssh_users_lseg2(user, last, userlist1);
    ////@ open ssh_users_lseg2(user, last, userlist1);
    if (string_buffer_equals(user->username, username)){
      if(string_buffer_equals(user->password, password)){

        ////@ requires buffer == 0 ? emp : string_buffer(buffer, _);
        ////@ ensures emp;
        string_buffer_dispose(session->logged_in_as);
        session->logged_in_as = string_buffer_copy(username);
        result = true;
        // normally you would "break", but without it's easier to verify.
      }
    }


    //// lemma het vanacher aanvoegen van user aan userlist2 geeft ssh_users(user2, append(userlist2, cons(user, nil)))
    ////@ close ssh_users(user, cons(head(userlist), nil));
    user = user->next;

    //@ users_cfrnodes_lseg_add_lemma(first_user);
    ////@ append(
    ////@ append_assoc(userlist2, cons(user, nil), userlist);
  }
  //@ open users_cfrnodes_lseg(0,0, _);
  //@ lseg_to_users_cfrnodes_lemma(first_user);

  ///@ open ssh_users_lseg2(0, 0, nil);
  ///@ open single_user(0,0);
  
  
  //@ close ssh_server_userlist(server)();
  mutex_release(session->server->users_mutex);
  return result;
}





/**
 * Creates an ssh_server on the given port
 */
struct ssh_server *create_ssh_server(int port)
//@ requires module(zout, true);
//@ ensures ssh_server(result);
{

  if (sodium_init() == -1) {
    //@close ssh_server(0);
    return NULL;
  }

  struct ssh_server *server = malloc(sizeof(struct ssh_server));
  if (server == NULL) {
  //@close ssh_server(0);
    return NULL;
  }

  // == HANDLING OF HOST KEYS === //

  bool failed = false;

  FILE *fp = fopen("host_keys.k", "rb"); // try to read the host keys form file
  if(fp){ // file opening succeeded
    int read_ret = fread(server->host_secret_key, zout_sign_SECRETKEYBYTES, 1, fp);
    if(read_ret < 1) {
      failed = true;
    }
    read_ret = fread(server->host_pub_key, zout_sign_PUBLICKEYBYTES, 1, fp);
    if(read_ret < 1) {
      failed = true;
    }
    fclose(fp);
  }
  else{//file opening failed
    // Generate the server's host public and private keypair (could have
    // been an RSA keypair but we're using elliptic cryptography instead).
    zout_sign_keypair(server->host_pub_key, server->host_secret_key);

    fp = fopen("host_keys.k", "wb");
    if(fp){
      int write_ret = fwrite(server->host_secret_key, zout_sign_SECRETKEYBYTES, 1, fp);
      if(write_ret < 1) {
	failed = true;
      }
      write_ret = fwrite(server->host_pub_key, zout_sign_PUBLICKEYBYTES, 1, fp);
      if(write_ret < 1) {
        failed = true;
      }
      fclose(fp);
    }
    else{
      puts("unable to store keys!");
      failed = true;
    }
  }



  if(failed){
    free(server);
    //@close ssh_server(0);
    return NULL;
  }

  // == END HOST KEY HANDLING == //
  struct server_socket *ss = create_server_socket(port);
  if (ss == NULL) {
    puts("Error: Cannot listen on tcp socket. *Maybe* the port is in use?");
    free(server);
    //@close ssh_server(0);
    return NULL;
  }
  server->host_key_string_without_length = ssh_create_host_key_string_without_length(server);
  server->ss = ss;
  server->users = NULL;
  //@ close ssh_users(0, nil);
  //@ close ssh_server_userlist(server)();
  //@ close create_mutex_ghost_arg(ssh_server_userlist(server));
  server->users_mutex = create_mutex();
 // //@ close ssh_server(server);

  struct string_buffer *username = create_string_buffer_from_string("admin");
  struct string_buffer *password = create_string_buffer_from_string("123");
  ////@ open ssh_server(server);
  ssh_adduser(server, username, password);
  //@ close ssh_server(server);
  string_buffer_dispose(username);
  string_buffer_dispose(password);

  return server;
}

/**
 * Assignes memory for a session on the heap
 * Assignes memory for ssh_keys on the heap
 *
 */
struct ssh_session *ssh_create_session(struct ssh_server *ssh)
//@ requires ssh_server(ssh) &*& ssh != 0;
//@ ensures ssh_server(ssh) &*& ssh_session(result, ssh, 0, true);
{
  struct ssh_session *session = malloc(sizeof(struct ssh_session));
  if (session == NULL) {
  //@close ssh_session(0, ssh, 0, true);
    return NULL;
  }
  struct ssh_keys *keys = malloc(sizeof(struct ssh_keys));
  if (keys == NULL) {
    free(session);
    //@close ssh_session(0, ssh, 0, true);
    return NULL;
  }

  //@ open ssh_server(ssh);
  struct socket* socket = server_socket_accept(ssh->ss);
  //@ close ssh_server(ssh);
  if (socket != NULL){
    session->server = ssh;
    session->packets_read = 0;
    session->packets_written = 0;
    session->cipher_block_size = 8; // initial cipher is "none" and has this block size such that we can read the packet length and padding in the first block.
    session->kex_data = NULL;
    session->keys = keys;
    session->receive_buffer = create_string_buffer();
    session->logged_in_as = NULL;
    session->socket = socket;
    //@ close ssh_keys(keys);
    ////@ close ssh_kex_data(session->kex_data, true);
    //@ close ssh_session(session, ssh, session->kex_data, true);
    return session;
  }else{
    free(session);
    free(keys);
    return NULL;
    //@close ssh_session(0, ssh, 0, true);
  }
}



/**
 * TCP is a stream, so when sending packets in this stream, one has to
 * mark the packets (e.g. by putting markers between messages or prepending
 * messages with the size of it). Gets one such packet from the stream.
 * Returned buffer does not include length, padding length, padding and mac.
 */
struct string_buffer *ssh_read_packet(struct ssh_session *session, success_t *success)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_session(session, ?server, ?kex_data, ?isNull) &*& session != 0
      &*& integer(success, _); @*/
//@ ensures string_buffer(result, _) &*& ssh_session(session, server, kex_data, isNull) &*& integer(success, _);
{
  /* Packet layout is like this:
   *
   *   4 bytes        1 byte                  y bytes
   * +--------------+-------------+---------+---------+-----+
   * | x = packet   | y = padding | payload | padding | mac |
   * |     length   |     length  |         |         |     |
   * +--------------+-------------+---------+---------+-----+
   *
   *                |_________________________________|
   *                              x bytes
   *
   */
  struct string_buffer *first_block = create_string_buffer();
  struct string_buffer *later_blocks = create_string_buffer();
  struct string_buffer *all_blocks = create_string_buffer();
  struct string_buffer *mac_from_network = create_string_buffer();
  struct string_buffer *first_block_without_lengths = create_string_buffer();
  struct string_buffer *payload = create_string_buffer();


  // ============= Read first block. ==========================
  //@ open ssh_session(session, server, kex_data, isNull);
  socket_read_chars(session->socket, session->cipher_block_size, first_block);
  int32_t first_block_length = string_buffer_get_length(first_block);
  if (first_block_length != session->cipher_block_size){
    puts("Error while reading first block of ssh packet.");
    *success = FAILURE;
    goto cleanup;
  }

  // ============== Decrypt first block.=============================
  char *first_block_chars = string_buffer_get_chars(first_block);
  ////@ string_buffer_merge_chars(first_block);
  if (session->kex_data){
    //@ open ssh_keys(session->keys);
    zout_stream_aes128ctr_xor(
      first_block_chars,
      first_block_chars,
      first_block_length,
      session->keys->iv_c2s,
      session->keys->key_enc_c2s);
    zout_update_iv(session->keys->iv_c2s, 1);
    //@ close ssh_keys(session->keys);
  }
  //@ string_buffer_merge_chars(first_block);


  // ================== Obtain lengths =========================
  string_buffer_append_string_buffer(first_block_without_lengths, first_block);
  int32_t packet_length = ssh_buf_pop_uint32(first_block_without_lengths, success);
  uint8_t padding_length = ssh_buf_pop_uint8(first_block_without_lengths, success);

  // Check and calc lengths
  if (packet_length > 1048576){
    puts("Packet length too high");
    *success = FAILURE;
    goto cleanup;
  }
  int32_t payload_length = packet_length - 1 - padding_length;
  if (payload_length < 0){
    *success = FAILURE;
    goto cleanup;
  }
  if ((4 + 1 + padding_length + payload_length) % session->cipher_block_size != 0){
    puts("Evil client neglecting block cipher size!");
    *success = FAILURE;
    goto cleanup;
  }
  int32_t bytes_to_read = (packet_length + 4) - session->cipher_block_size;
  int32_t blocks_to_read = bytes_to_read / session->cipher_block_size;
  if (bytes_to_read < 0 || blocks_to_read < 0){
    // Note: a bit of redundancy here because reasoning about modulo and division in VeriFast is hard.
    puts("Client neglecting block cipher size!");
    *success = FAILURE;
    goto cleanup;
  }

  // ============= Read the next blocks. =======================

  // Hint: call the lemma div_rem((payload_length), session->cipher_block_size)
  socket_read_chars(session->socket, bytes_to_read, later_blocks);
  if (string_buffer_get_length(later_blocks) != bytes_to_read){
    puts("Sudden disconnect?");
    *success = FAILURE;
    goto cleanup;
  }

  // =================== Decrypt these next blocks=================
  if (session->kex_data){
    //@ open ssh_keys(session->keys);
    int later_blocks_length = string_buffer_get_length(later_blocks);
    char *later_blocks_chars = string_buffer_get_chars(later_blocks);
    zout_stream_aes128ctr_xor(
          later_blocks_chars,
          later_blocks_chars,
          later_blocks_length,
          session->keys->iv_c2s,
          session->keys->key_enc_c2s);
    zout_update_iv(session->keys->iv_c2s, blocks_to_read);
    //@ close ssh_keys(session->keys);
    //@ string_buffer_merge_chars(later_blocks);
  }

  string_buffer_append_string_buffer(all_blocks, first_block);
  string_buffer_append_string_buffer(all_blocks, later_blocks);

  //==================== Read and check MAC ============================
  char computed_mac[zout_auth_hmacsha256_BYTES]; // outside if-block to avoid triggering VeriFast bug #1949
  if (session->kex_data){
    // read MAC from network
    socket_read_chars(session->socket, zout_auth_hmacsha256_BYTES, mac_from_network);
    if(string_buffer_get_length(mac_from_network) != zout_auth_hmacsha256_BYTES){
      puts("Network failure! Cannot read mac!");
      *success = FAILURE;
      goto cleanup;
    }

    // Construct data we are going to MAC.
    struct string_buffer *input_for_mac_computation = create_string_buffer();
    ssh_buf_append_uint32(input_for_mac_computation, session->packets_read);
    string_buffer_append_string_buffer(input_for_mac_computation, all_blocks);

    // Perform MAC calculation.
    int for_mac_computation_length = string_buffer_get_length(input_for_mac_computation);
    char *for_mac_computation_chars = string_buffer_get_chars(input_for_mac_computation);
    //@ open ssh_keys(session->keys);
    zout_auth_hmacsha256(computed_mac, for_mac_computation_chars, for_mac_computation_length, session->keys->key_integrity_c2s);
    //@ close ssh_keys(session->keys);
    //@ string_buffer_merge_chars(input_for_mac_computation);
    string_buffer_dispose(input_for_mac_computation);
    // Is MAC correct?
    if (memcmp(string_buffer_get_chars(mac_from_network), computed_mac, zout_auth_hmacsha256_BYTES) != 0){
      //@ string_buffer_merge_chars(mac_from_network);
      puts("Message authentication failed!");
      *success = FAILURE;

      goto cleanup;
    }
    //@ string_buffer_merge_chars(mac_from_network);
  }


  // =========== we have read a packet and should increase the read packets counter ==========
  if (session->packets_read == INT_MAX){
    *success = FAILURE;
    goto cleanup;
  }
  session->packets_read = session->packets_read + 1;

  // ============= Calculate the payload we want to return. ===============
  int all_blocks_length = string_buffer_get_length(all_blocks);
  char *all_blocks_chars = string_buffer_get_chars(all_blocks);

  string_buffer_append_chars(payload,
      all_blocks_chars,
      all_blocks_length - padding_length);
      //@ string_buffer_merge_chars(all_blocks);
  ssh_buf_pop_uint32(payload, success); // drop payload length field
  ssh_buf_pop_uint8(payload, success); // drop padding length field

cleanup:
  string_buffer_dispose(mac_from_network);
  string_buffer_dispose(all_blocks);
  string_buffer_dispose(later_blocks);
  string_buffer_dispose(first_block);
  string_buffer_dispose(first_block_without_lengths);
  return payload;
  //@ close ssh_session(session, server, kex_data, isNull);
}

/*void ssh_send_packet(struct ssh_session *session, struct string_buffer *payload, success_t *success)
**@ requires

      session->cipher_block_size |-> ?cipher_block_size &*& cipher_block_size>=8 &*&
      session->kex_data |-> ?kex_data &*&
      session->packets_written |-> ?packets_written &*& packets_written >= 0 &*&
      session->keys |-> ?keys &*& keys != 0 &*& ssh_keys(keys) &*&
      string_buffer(payload, _) &*&
      integer(success, _) &*&
      [_]sodium_is_initialized(); @*//*
//*@ ensures
      session->cipher_block_size |-> cipher_block_size &*&
      session->kex_data |-> kex_data &*&
      session->packets_written |-> ?packets_written0 &*& packets_written0 >= packets_written &*&
      session->keys |-> keys &*& ssh_keys(keys) &*&
      string_buffer(payload, _) &*&
      integer(success, _); @*//*
{
  struct string_buffer *to_send = create_string_buffer();

  // Calculate lengths
  int32_t payload_length = string_buffer_get_length(payload);
  ////@ open ssh_session(session, _);

  //@ div_rem((payload_length), session->cipher_block_size);
  // Hint: session->cipher_block_size is 8 or 16
  // Hint: call the lemma "div_rem((payload_length), session->cipher_block_size);"
  int32_t padding_length = session->cipher_block_size - (4 + 1 + (payload_length % session->cipher_block_size));
  if (padding_length < 4){
    padding_length = padding_length + session->cipher_block_size;
  }
  if (payload_length > 1048576){
    *success = FAILURE;
    string_buffer_dispose(to_send);
    ////@close ssh_session(session, _);
    return;
  }
  int32_t packet_length = padding_length + 1 + payload_length;
  //@ division_remains_positive(packet_length + 4, session->cipher_block_size);
  int32_t blocks = (packet_length + 4) / session->cipher_block_size;
  // Hint: call the lemma "division_remains_positive(packet_length + 4, session->cipher_block_size);"

  // Construct what we will send
  ssh_buf_append_uint32(to_send, packet_length);
  ssh_buf_append_byte(to_send, (uint8_t)padding_length);
  string_buffer_append_string_buffer(to_send, payload);
  char *padding = malloc(padding_length);
  if(!padding){
    abort();
  }
  zout_randombytes_buf(padding, padding_length);
  string_buffer_append_chars(to_send, padding, padding_length);
  free(padding);

  if (session->kex_data){
    // Build input for MAC
    struct string_buffer *for_mac_computation = create_string_buffer();
    ssh_buf_append_uint32(for_mac_computation, session->packets_written);
    string_buffer_append_string_buffer(for_mac_computation, to_send);

    // Compute MAC
    char computed_mac[zout_auth_hmacsha256_BYTES];
    int for_mac_computation_length = string_buffer_get_length(for_mac_computation);
    char *for_mac_computation_chars = string_buffer_get_chars(for_mac_computation);
    //@open ssh_keys(session->keys);
    ////@ assert session->keys |-> ?keys &*& chars(keys->key_integrity_s2c, _, _);
    zout_auth_hmacsha256(computed_mac, for_mac_computation_chars, for_mac_computation_length, session->keys->key_integrity_s2c);

    // Encrypt
    int to_send_length = string_buffer_get_length(to_send);
    char *to_send_chars = string_buffer_get_chars(to_send);
    zout_stream_aes128ctr_xor(
            to_send_chars,
            to_send_chars,
            to_send_length,
            session->keys->iv_s2c,
            session->keys->key_enc_s2c);

    // Updating initialization vector after encrypting
    zout_update_iv(session->keys->iv_s2c, blocks);

    //@ string_buffer_merge_chars(to_send);
    // Add MAC
    string_buffer_append_chars(to_send, computed_mac, zout_auth_hmacsha256_BYTES);

    //@ string_buffer_merge_chars(for_mac_computation);
    string_buffer_dispose(for_mac_computation);
    //@close ssh_keys(session->keys);
  }

  if (session->packets_written == INT_MAX){
    *success = FAILURE;
  }else{
    session->packets_written = session->packets_written + 1;
    socket_write_string_buffer(session->socket, to_send);
  }
  string_buffer_dispose(to_send);
  ////@close ssh_session(session, _);
}*/



void ssh_send_packet(struct ssh_session *session, struct string_buffer *payload, success_t *success)
/*@ requires
      ssh_session(session, ?server, ?kex_data, ?isNull) &*& session != 0
      &*& string_buffer(payload, _)
      &*& integer(success, _) &*&
      [_]sodium_is_initialized(); @*/

//@ ensures ssh_session(session, server, kex_data, isNull) &*& string_buffer(payload, _) &*& integer(success, _);
{
  struct string_buffer *to_send = create_string_buffer();

  // Calculate lengths
  int32_t payload_length = string_buffer_get_length(payload);
  //@ open ssh_session(session, server, kex_data, isNull);

  //@ div_rem((payload_length), session->cipher_block_size);
  // Hint: session->cipher_block_size is 8 or 16
  // Hint: call the lemma "div_rem((payload_length), session->cipher_block_size);"
  int32_t padding_length = session->cipher_block_size - (4 + 1 + (payload_length % session->cipher_block_size));
  if (padding_length < 4){
    padding_length = padding_length + session->cipher_block_size;
  }
  if (payload_length > 1048576){
    *success = FAILURE;
    string_buffer_dispose(to_send);
    //@close ssh_session(session, server, kex_data, isNull);
    return;
  }
  int32_t packet_length = padding_length + 1 + payload_length;
  //@ division_remains_positive(packet_length + 4, session->cipher_block_size);
  int32_t blocks = (packet_length + 4) / session->cipher_block_size;
  // Hint: call the lemma "division_remains_positive(packet_length + 4, session->cipher_block_size);"

  // Construct what we will send
  ssh_buf_append_uint32(to_send, packet_length);
  ssh_buf_append_byte(to_send, (uint8_t)padding_length);
  string_buffer_append_string_buffer(to_send, payload);
  char *padding = malloc(padding_length);
  if(!padding){
    abort();
  }
  zout_randombytes_buf(padding, padding_length);
  string_buffer_append_chars(to_send, padding, padding_length);
  free(padding);

  if (session->kex_data){
    // Build input for MAC
    struct string_buffer *for_mac_computation = create_string_buffer();
    ssh_buf_append_uint32(for_mac_computation, session->packets_written);
    string_buffer_append_string_buffer(for_mac_computation, to_send);

    // Compute MAC
    char computed_mac[zout_auth_hmacsha256_BYTES];
    int for_mac_computation_length = string_buffer_get_length(for_mac_computation);
    char *for_mac_computation_chars = string_buffer_get_chars(for_mac_computation);
    //@open ssh_keys(session->keys);
    ////@ assert session->keys |-> ?keys &*& chars(keys->key_integrity_s2c, _, _);
    zout_auth_hmacsha256(computed_mac, for_mac_computation_chars, for_mac_computation_length, session->keys->key_integrity_s2c);

    // Encrypt
    int to_send_length = string_buffer_get_length(to_send);
    char *to_send_chars = string_buffer_get_chars(to_send);
    zout_stream_aes128ctr_xor(
        to_send_chars,
        to_send_chars,
        to_send_length,
        session->keys->iv_s2c,
        session->keys->key_enc_s2c);

    // Updating initialization vector after encrypting
    zout_update_iv(session->keys->iv_s2c, blocks);

    //@ string_buffer_merge_chars(to_send);
    // Add MAC
    string_buffer_append_chars(to_send, computed_mac, zout_auth_hmacsha256_BYTES);

    //@ string_buffer_merge_chars(for_mac_computation);
    string_buffer_dispose(for_mac_computation);
    //@close ssh_keys(session->keys);
  }

  if (session->packets_written == INT_MAX){
    *success = FAILURE;
  }else{
    session->packets_written = session->packets_written + 1;
    socket_write_string_buffer(session->socket, to_send);
  }
  string_buffer_dispose(to_send);
  //@close ssh_session(session, server, kex_data, isNull);
}




/*struct string_buffer *ssh_send_kex_init(struct ssh_session *session, success_t *success)
@ requires
      [_]sodium_is_initialized() &*&
       integer(success, _); @
//@ ensures string_buffer(result, _) &*& integer(success, _);
{
  struct string_buffer *kex_init = create_string_buffer();

  // message code:
  ssh_buf_append_byte(kex_init, SSH_MSG_KEXINIT);

  // cookie:
  char random[16];
  zout_randombytes_buf(random, 16);
  string_buffer_append_chars(kex_init, random, 16);

  // kex algorithms:
  ssh_buf_append_string_c_string(kex_init, "curve25519-sha256@libssh.org");

  // server host key algorithms:
  ssh_buf_append_string_c_string(kex_init, "ssh-ed25519");

  // encryption algorithms client to server (c2s) and server to client (s2c):
  ssh_buf_append_string_c_string(kex_init, "aes128-ctr");
  ssh_buf_append_string_c_string(kex_init, "aes128-ctr");

  // c2s and s2c mac algorithms:
  ssh_buf_append_string_c_string(kex_init, "hmac-sha2-256");
  ssh_buf_append_string_c_string(kex_init, "hmac-sha2-256");

  // c2s and s2c compression algorithms:
  ssh_buf_append_string_c_string(kex_init, "none");
  ssh_buf_append_string_c_string(kex_init, "none");

  // c2s and s2c languages:
  ssh_buf_append_string_c_string(kex_init, "");
  ssh_buf_append_string_c_string(kex_init, "");

  // kex first packet follows is set to 0.
  ssh_buf_append_byte(kex_init, 0);

  // Reserved
  ssh_buf_append_byte(kex_init, '\0');
  ssh_buf_append_byte(kex_init, '\0');
  ssh_buf_append_byte(kex_init, '\0');
  ssh_buf_append_byte(kex_init, '\0');

  ssh_send_packet(session, kex_init, success);
  return kex_init;
}*/
struct string_buffer *ssh_send_kex_init(struct ssh_session *session, success_t *success)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_session(session, ?server, ?kex_data, ?isNull) &*& session != 0
      &*& integer(success, _); @*/
/*@ ensures string_buffer(result, _) &*& ssh_session(session, server, kex_data, isNull) &*& integer(success, _); @*/
{
  struct string_buffer *kex_init = create_string_buffer();

  // message code:
  ssh_buf_append_byte(kex_init, SSH_MSG_KEXINIT);

  // cookie:
  char random[16];
  zout_randombytes_buf(random, 16);
  string_buffer_append_chars(kex_init, random, 16);

  // kex algorithms:
  ssh_buf_append_string_c_string(kex_init, "curve25519-sha256@libssh.org");

  // server host key algorithms:
  ssh_buf_append_string_c_string(kex_init, "ssh-ed25519");

  // encryption algorithms client to server (c2s) and server to client (s2c):
  ssh_buf_append_string_c_string(kex_init, "aes128-ctr");
  ssh_buf_append_string_c_string(kex_init, "aes128-ctr");

  // c2s and s2c mac algorithms:
  ssh_buf_append_string_c_string(kex_init, "hmac-sha2-256");
  ssh_buf_append_string_c_string(kex_init, "hmac-sha2-256");

  // c2s and s2c compression algorithms:
  ssh_buf_append_string_c_string(kex_init, "none");
  ssh_buf_append_string_c_string(kex_init, "none");

  // c2s and s2c languages:
  ssh_buf_append_string_c_string(kex_init, "");
  ssh_buf_append_string_c_string(kex_init, "");

  // kex first packet follows is set to 0.
  ssh_buf_append_byte(kex_init, 0);

  // Reserved
  ssh_buf_append_byte(kex_init, '\0');
  ssh_buf_append_byte(kex_init, '\0');
  ssh_buf_append_byte(kex_init, '\0');
  ssh_buf_append_byte(kex_init, '\0');

  ssh_send_packet(session, kex_init, success);
  return kex_init;
}

struct string_buffer *ssh_recv_kex_init(struct ssh_session *session, success_t *success)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_session(session, ?server, ?kex_data, ?isNull) &*& session != 0
      &*& integer(success, _); @*/
//@ ensures string_buffer(result, _) &*& ssh_session(session, server, kex_data, isNull) &*& integer(success, _);
{
  return ssh_read_packet(session, success);
}

struct ssh_kex_data *ssh_kex_data_create()
//@ requires true;
//@ ensures ssh_kex_data(result, true) &*& result != 0;
{
  struct ssh_kex_data *kex_data = malloc(sizeof(struct ssh_kex_data));
  if (kex_data == NULL) abort ();
  //@ assert kex_data != 0;
  kex_data->client_version = NULL;
  kex_data->server_version = NULL;
  kex_data->server_kex_init = NULL;
  kex_data->client_kex_init = NULL;
  kex_data->dh_client_pubkey = NULL;
  //@ close ssh_kex_data_string_buffers(kex_data)(true);
  //@close ssh_kex_data(kex_data, true);
  return kex_data;
}

void ssh_kex_data_dispose(struct ssh_kex_data *kex)
//@ requires ssh_kex_data(kex, ?isNull) &*& kex != 0;
//@ ensures true;
{
  //@ open ssh_kex_data(kex, isNull);
  //@ open ssh_kex_data_string_buffers(kex)(isNull);
  string_buffer_dispose(kex->client_version);
  string_buffer_dispose(kex->server_version);
  string_buffer_dispose(kex->server_kex_init);
  string_buffer_dispose(kex->client_kex_init);
  string_buffer_dispose(kex->dh_client_pubkey);
  free(kex);
}



struct string_buffer *ssh_kex_sign(struct ssh_server *server, struct ssh_kex_data *kex_data)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_server(server) &*& server != 0 &*&
      ssh_kex_data(kex_data, false) &*& kex_data != 0; @*/
/*@ ensures
      string_buffer(result, _) &*&
      ssh_server(server) &*& server != 0 &*&
      ssh_kex_data(kex_data, false) &*& kex_data != 0; @*/
{ 
  int32_t dh_signature_length; // VeriFast: "A local variable whose address is taken must be declared at the start of a block."

  struct string_buffer *to_hash = create_string_buffer();

  //@ open ssh_kex_data(kex_data, false);
  //@ open ssh_kex_data_string_buffers(kex_data)(false);
  ssh_buf_append_string_buf(to_hash, kex_data->client_version);
  ssh_buf_append_string_buf(to_hash, kex_data->server_version);
  ssh_buf_append_string_buf(to_hash, kex_data->client_kex_init);
  ssh_buf_append_string_buf(to_hash, kex_data->server_kex_init);
  //@ open ssh_server(server);
  ssh_buf_append_string_buf(to_hash, server->host_key_string_without_length);
  ssh_buf_append_string_buf(to_hash, kex_data->dh_client_pubkey);
  ssh_buf_append_string_chars(to_hash, kex_data->dh_server_publickey, zout_box_PUBLICKEYBYTES);
  ssh_buf_append_mpint(to_hash, kex_data->dh_shared_secret, zout_scalarmult_BYTES);


  // Now we know what we want to hash, so hash it:
  int to_hash_length = string_buffer_get_length(to_hash);
  char *to_hash_chars = string_buffer_get_chars(to_hash);
  zout_hash_sha256(kex_data->dh_hash, to_hash_chars, to_hash_length);
  //@ close ssh_kex_data_string_buffers(kex_data)(false);

  //@ string_buffer_merge_chars(to_hash);
  string_buffer_dispose(to_hash);

  // Sign the hash
  char dh_signature[zout_sign_BYTES];
  zout_sign_detached(dh_signature, &dh_signature_length, kex_data->dh_hash, zout_hash_sha256_BYTES, server->host_secret_key);
  //@close ssh_kex_data(kex_data, false);
  //@close ssh_server(server);

  struct string_buffer *signature_buf = create_string_buffer();
  ssh_buf_append_string_c_string(signature_buf, "ssh-ed25519");
  ssh_buf_append_string_chars(signature_buf, dh_signature, dh_signature_length);
  return signature_buf;


}

void ssh_kex_calc_key(struct ssh_kex_data *kex_data, int32_t number, char *destination)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_kex_data(kex_data, false) &*& kex_data !=0 &*&
      chars(destination, zout_hash_sha256_BYTES, _); @*/
//@ ensures  ssh_kex_data(kex_data, false) &*& chars(destination, zout_hash_sha256_BYTES, _);
{
  /* RFC says:
    o  Initial IV client to server: HASH(K || H || "A" || session_id)
       (Here K is encoded as mpint and "A" as byte and session_id as raw
       data.  "A" means the single character A, ASCII 65).
    o  Initial IV server to client: HASH(K || H || "B" || session_id)
    o  Encryption key client to server: HASH(K || H || "C" || session_id)
    o  Encryption key server to client: HASH(K || H || "D" || session_id)
    o  Integrity key client to server: HASH(K || H || "E" || session_id)
    o  Integrity key server to client: HASH(K || H || "F" || session_id)
    */
  //@ open ssh_kex_data(kex_data, false);
  struct string_buffer *to_hash = create_string_buffer();
  ssh_buf_append_mpint(to_hash, kex_data->dh_shared_secret, zout_scalarmult_BYTES);
  string_buffer_append_chars(to_hash, kex_data->dh_hash, zout_hash_sha256_BYTES);
  ssh_buf_append_byte(to_hash, (unsigned char)('A' + number));
  string_buffer_append_chars(to_hash, kex_data->session_id, zout_hash_sha256_BYTES);
  //@ close ssh_kex_data(kex_data, false);

  int to_hash_length = string_buffer_get_length(to_hash);
  char *to_hash_chars = string_buffer_get_chars(to_hash);
  zout_hash_sha256(destination, to_hash_chars, to_hash_length);
  //@ string_buffer_merge_chars(to_hash);
  string_buffer_dispose(to_hash);
}

void ssh_kex_calc_keys(struct ssh_kex_data *kex_data, struct ssh_keys *keys)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_kex_data(kex_data, false) &*& kex_data !=0 &*&
      ssh_keys(keys) &*& keys != 0; @*/
/*@ ensures
      ssh_kex_data(kex_data, false) &*& kex_data !=0 &*&
      ssh_keys(keys) &*& keys != 0; @*/
{
  //@ open ssh_keys(keys);
  ssh_kex_calc_key(kex_data, 0, keys->iv_c2s);
  ssh_kex_calc_key(kex_data, 1, keys->iv_s2c);
  ssh_kex_calc_key(kex_data, 2, keys->key_enc_c2s);
  ssh_kex_calc_key(kex_data, 3, keys->key_enc_s2c);
  ssh_kex_calc_key(kex_data, 4, keys->key_integrity_c2s);
  ssh_kex_calc_key(kex_data, 5, keys->key_integrity_s2c);
  //@ close ssh_keys(keys);
}

/**
 * Coordinate key exchange network packets and cryptographic calculations.
 */
void ssh_kex(struct ssh_session *session, success_t *success)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_server(?server) &*&
      ssh_session(session, server, ?kex_data_s, ?isNull) &*& 
      
       integer(success, _) &*& session != 0; @*/
/*@ ensures 
	ssh_server(server) &*& 
	ssh_session(session, server, ?kex_data_new, _)  &*&
	
	integer(success, _); @*/
{

  // =========== initialize key exchange data ==================
  struct ssh_kex_data *kex_data = ssh_kex_data_create();
  //@ assert kex_data != 0;
  
  //@ open ssh_session(session, server, kex_data_s, isNull);
  //@ open ssh_kex_data(kex_data, true);
  //@ open ssh_kex_data_string_buffers(kex_data)(true);
  kex_data->client_version = ssh_recv_version(session);
  kex_data->server_version = ssh_send_version(session);
  ////@ close ssh_kex_data(kex_data);
  //@ close ssh_session(session, server, kex_data_s, isNull);
  kex_data->server_kex_init = ssh_send_kex_init(session, success);
  kex_data->client_kex_init = ssh_recv_kex_init(session, success);
 //@ open ssh_session(session, server, kex_data_s, isNull);
  kex_data->dh_client_pubkey = ssh_read_dh_client_pubkey(session, success);
  ////@ close ssh_kex_data_string_buffers(kex_data)(false);

  // == check whether the received public key of the client has the required length ===
  if (string_buffer_get_length(kex_data->dh_client_pubkey) != zout_box_PUBLICKEYBYTES){
    *success = FAILURE;
  }
  if (*success == FAILURE){ // nor the correct length
    // return instead of passing unallocated memory buffers to zout.
    // cleanup by hand (instead of function call) to make verification easier
    string_buffer_dispose(kex_data->client_version);
    string_buffer_dispose(kex_data->server_version);
    string_buffer_dispose(kex_data->server_kex_init);
    string_buffer_dispose(kex_data->client_kex_init);
    string_buffer_dispose(kex_data->dh_client_pubkey);
    free(kex_data);
    return;
    ////@ close ssh_kex_data_string_buffers(kex_data);
    //@ close ssh_session(session, server, kex_data_s, isNull);
  }


  //============= Create our diffie-hellman (dh) keypair:=======
  zout_box_keypair(kex_data->dh_server_publickey, kex_data->dh_server_secretkey);

  // ======  Calculate shared secret (client will also calculate this) ========
  ////@  ssh_kex_data_string_buffers(kex_data)(false)
  char *client_dh_pubkey_chars = string_buffer_get_chars(kex_data->dh_client_pubkey);
  zout_scalarmult(kex_data->dh_shared_secret, kex_data->dh_server_secretkey, client_dh_pubkey_chars);
  //@ string_buffer_merge_chars(kex_data->dh_client_pubkey);
  //@ close ssh_kex_data_string_buffers(kex_data)(false);
  //@ close ssh_kex_data(kex_data, false);


  struct string_buffer *signature = ssh_kex_sign(session->server, kex_data);
  //@ open ssh_kex_data(kex_data, false);
  memcpy(kex_data->session_id, kex_data->dh_hash, zout_hash_sha256_BYTES);
  ssh_send_kex_reply(session, kex_data, signature);
  string_buffer_dispose(signature);


  //@ close ssh_kex_data(kex_data, false);
  ssh_kex_calc_keys(kex_data, session->keys);
  // send this with the old cipher (in our case "none"):
  ssh_send_receive_newkeys(session, success); // Sends the message that new keys are calculated.

  // switch to new cipher and keys
  // we don't support re-key-exchange, but it's easier to verify like this:
  if (session->kex_data != NULL) ssh_kex_data_dispose(session->kex_data);
  ////@ open ssh_kex_data(session->kex_data, _);
  session->kex_data = kex_data;
  //@ assert session->kex_data == kex_data;
  session->cipher_block_size = zout_stream_aes128ctr_CIPHERBLOCKBYTES;
  ////@ close ssh_kex_data(session->kex_data, false);
  //@ close ssh_session(session, server, kex_data, false);
}


void ssh_userauth_request(struct ssh_session *session, struct string_buffer *packet, success_t *success)
/*@ requires
      ssh_session(session, ?server, ?kex_data, false) &*& session != 0 &*&
      string_buffer(packet, _) &*&

      integer(success, _); @*/
/*@ ensures
      ssh_session(session, server, kex_data, false) &*&
      string_buffer(packet, _) &*&

      integer(success, _); @*/
{
  struct string_buffer *username = ssh_buf_pop_string(packet, success);
  struct string_buffer *service_after_auth = ssh_buf_pop_string(packet, success);
  struct string_buffer *auth_method = ssh_buf_pop_string(packet, success);

  bool authenticated = false;
  
  if(string_buffer_equals_string(auth_method, "password")){
    ssh_buf_pop_uint8(packet, success);//we don't support pasword change and so we ignore such requests
    struct string_buffer *password = ssh_buf_pop_string(packet, success);
    if (ssh_auth_user(session, username, password)){
      struct string_buffer *userauth_succeed = create_string_buffer();
      
      ssh_buf_append_byte(userauth_succeed, SSH_MSG_USERAUTH_SUCCESS);
      ssh_send_packet(session, userauth_succeed, success);
      string_buffer_dispose(userauth_succeed);
      authenticated = true;
    }
    string_buffer_dispose(password);
  }
  if(!authenticated){//if the authentication method is not password or the password provided is wrong.
    struct string_buffer *userauth_fail_allow_pass = create_string_buffer();
  
    ssh_buf_append_byte(userauth_fail_allow_pass, SSH_MSG_USERAUTH_FAILURE);
    ssh_buf_append_string_c_string(userauth_fail_allow_pass, "password");
    ssh_buf_append_byte(userauth_fail_allow_pass, 0/*false*/);
    ssh_send_packet(session, userauth_fail_allow_pass, success);
    string_buffer_dispose(userauth_fail_allow_pass);
  }
  string_buffer_dispose(username);
  string_buffer_dispose(service_after_auth);
  string_buffer_dispose(auth_method);
}


void ssh_menu_adduser(struct ssh_session *session, struct string_buffer *arguments, success_t *success)
/*@ requires
      ssh_session(session, ?server, ?kex_data, false) &*& session != 0 &*&
      string_buffer(arguments, _) &*&
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
/*@ ensures
      ssh_session(session, server, kex_data, false) &*&
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(arguments, _) &*&
      integer(success, _); @*/
{
  struct string_buffer *username = create_string_buffer();
  struct string_buffer *password = create_string_buffer();
  bool can_split_user_pass = string_buffer_split(arguments, " ", username, password);
  //@ open ssh_session(session, server, kex_data, false);
  if (can_split_user_pass){
    
    ssh_adduser(session->server, username, password);
    ssh_send_channel_msg(session, "OK: added the user ``", NULL, success);
    ssh_send_channel_msg(session, "", username, success);
    ssh_send_channel_msg(session, "''.\n", NULL, success);
  }else{
    ssh_send_channel_msg(session, "Syntax error. Usage: adduser USERNAME PASSWORD\n", NULL, success);
  }
  string_buffer_dispose(username);
  string_buffer_dispose(password);
  //@ close ssh_session(session, server, kex_data, false);
}

void ssh_menu_command(struct ssh_session *session, struct string_buffer *full_commandline, success_t *success)
/*@ requires
      ssh_session(session, ?server, ?kex_data, false) &*& session != 0 &*&
      string_buffer(full_commandline, _) &*&
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
/*@ ensures
      ssh_session(session, server, kex_data, false) &*&
      string_buffer(full_commandline, _) &*&
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
{
  struct string_buffer *cmd = create_string_buffer();
  struct string_buffer *all_args = create_string_buffer();
  bool can_split = string_buffer_split(full_commandline, " ", cmd, all_args);

  if (! can_split){
    string_buffer_dispose(cmd);
    cmd = string_buffer_copy(full_commandline);
  }

  if (string_buffer_equals_string(cmd, "adduser")){
    ssh_menu_adduser(session, all_args, success);
  } else if (string_buffer_equals_string(cmd, "sendmail")){
    ssh_menu_sendmail(session, all_args, success);
  } else if (string_buffer_equals_string(cmd, "readmail")){
    ssh_menu_readmail(session, all_args, success);
  } else if (string_buffer_equals_string(full_commandline, "")){
    // No 'unknown command' error on empty command
  } else if (string_buffer_equals_string(cmd, "help")){
    //@ open ssh_session(session, server, kex_data, false);
    ssh_send_channel_msg(session, "Supported commands are: adduser sendmail readmail help.\n", NULL, success);
    //@ close ssh_session(session, server, kex_data, false);
  }else{
    //@ open ssh_session(session, server, kex_data, false);
    ssh_send_channel_msg(session, "Unsupported command: ``", NULL, success);
    ssh_send_channel_msg(session, "", cmd, success);
    ssh_send_channel_msg(session, "''. Type ``help'' (without quotes, followed by enter) for help.\n", NULL, success);
    //@ close ssh_session(session, server, kex_data, false);
  }
  //@ open ssh_session(session, server, kex_data, false);
  ssh_send_channel_msg(session, "picosshd> ", NULL, success);
  //@ close ssh_session(session, server, kex_data, false);
  string_buffer_dispose(cmd);
  string_buffer_dispose(all_args);
}

void ssh_channel_data(struct ssh_session *session, struct string_buffer *packet, success_t *success)
/*@ requires
      ssh_session(session, ?server, ?kex_data, false) &*& session != 0 &*&
      string_buffer(packet, _) &*&
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
/*@ ensures
      ssh_session(session, server, kex_data, false) &*&
      string_buffer(packet, _) &*&
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
{
  //@ open ssh_session(session, server, kex_data, false);
  if (session->logged_in_as == NULL){
    // Evil ssh client tries to execute commands before being logged in
    *success = FAILURE;
    return;
    //@ close ssh_session(session, server, kex_data, false);
  }
  struct string_buffer *data = ssh_buf_pop_string(packet, success);
  string_buffer_append_string_buffer(session->receive_buffer, data);
  string_buffer_dispose(data);
  //@ close ssh_session(session, server, kex_data, false);

  bool can_split = true;
  while (can_split)
  /*@ invariant 
  	ssh_session(session, server, kex_data, false) &*& integer(success, _) &*&
  	server->users_mutex |-> mutex &*& mutex(mutex, ssh_server_userlist(server)) ; @*/
  {
    struct string_buffer *before = create_string_buffer();
    struct string_buffer *after = create_string_buffer();
    //@ open ssh_session(session, server, kex_data, false);
    can_split = string_buffer_split(session->receive_buffer, "\n", before, after);
    if (can_split){
      //@ close ssh_session(session, server, kex_data, false);
      ssh_menu_command(session, before, success);
      //@ open ssh_session(session, server, kex_data, false);
      string_buffer_dispose(session->receive_buffer);
      session->receive_buffer = after;
    }else{
      string_buffer_dispose(after);
    }
    string_buffer_dispose(before);
    //@ close ssh_session(session, server, kex_data, false);
  } 
}


void ssh_protocol_loop(struct ssh_session *session, success_t *success)
/*@ requires
      [_]sodium_is_initialized() &*&
      ssh_session(session, ?server, ?kex_data, false) &*& session != 0 &*&
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
/*@ ensures
      ssh_session(session, server, kex_data, false) &*&
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      integer(success, _); @*/
{
  bool cont = true;
  while (cont && *success)
    /*@ invariant
          [_]sodium_is_initialized() &*&
          ssh_session(session, server, kex_data, false) &*& session != 0 &*&
          server->users_mutex |-> mutex &*&
          mutex(mutex, ssh_server_userlist(server)) &*&
          integer(success, _); @*/
  {
    struct string_buffer *packet = ssh_read_packet(session, success);
    if (!*success) {
      string_buffer_dispose(packet);
      return;
    }

    uint8_t req_code = ssh_buf_pop_uint8(packet, success);
    switch((int)req_code){
    case SSH_MSG_CHANNEL_REQUEST:
      ssh_channel_request(session, packet, success);
      break;
    case SSH_MSG_CHANNEL_EOF:
    case SSH_MSG_CHANNEL_CLOSE:
    case SSH_MSG_DISCONNECT:
      puts("Client requested disconnect!");
      cont = false;
      break;
    case SSH_MSG_CHANNEL_DATA:
      ssh_buf_pop_uint32(packet, success);//channel number; we have one channel and thus ignore it!
      ssh_channel_data(session, packet, success);
      break;
    case SSH_MSG_CHANNEL_OPEN:
      ssh_channel_open(session, packet, success);
      break;
    case SSH_MSG_USERAUTH_REQUEST:
      ssh_userauth_request(session, packet, success);
      break;
    case SSH_MSG_SERVICE_REQUEST:
      ssh_service_request(session, packet, success);
      break;
    // These cases are ignored.
    case SSH_MSG_IGNORE:
    case SSH_MSG_DEBUG:
    case SSH_MSG_CHANNEL_WINDOW_ADJUST:
      break;
    // Not supported! end connection
    case SSH_MSG_CHANNEL_EXTENDED_DATA:
    default:
      *success = FAILURE;
      cont = false;
      break;
    }
    string_buffer_dispose(packet);
  }
}


/*@
    predicate_family_instance thread_run_data(ssh_do_session)(struct ssh_session *session) =
        [_]sodium_is_initialized() &*& ssh_session(session, ?server, 0, true) &*& ssh_server(server) &*& session != 0;
@*/

void ssh_do_session(struct ssh_session *session)//@ : thread_run
//@ requires thread_run_data(ssh_do_session)(session);
//@ ensures true;
{
  success_t success = SUCCESS;

  puts("New connection");
  
  //@open thread_run_data(ssh_do_session)(session);
  ssh_kex(session, &success);
  if (success == SUCCESS) {
    ssh_protocol_loop(session, &success);
  }
  socket_close(session->socket);
  session->socket = NULL;
  if (success == SUCCESS){
    puts("Disconnect.");
  }else{
    puts("Disconnect with error.");
  }
  // Dispose (normally in a function, but it's easier to verify like this)
  if (session->kex_data) {
    ssh_kex_data_dispose(session->kex_data);
  }
  string_buffer_dispose(session->receive_buffer);
  string_buffer_dispose(session->logged_in_as);
  free(session->keys);
  free(session);
}

// Hint : // @ import_module zout;

int main() //@ : main_full(picosshd)
//@ requires module(picosshd, true);
//@ ensures true;
{
  // Hint: // @ open_module(); (do not forget the hint right above the main function)
  int port = 2222;
  //@ open_module();
  struct ssh_server *ssh = create_ssh_server(port);
  if (ssh == 0){
  //@open ssh_server(ssh);
    return 1;
  }
  while (true)
  //@ invariant ssh_server(ssh);
  {
    struct ssh_session *session = NULL;

    //@ close ssh_session(0);
    while (session == NULL)
    //@ invariant ssh_server(ssh) &*& ssh_session(session);
    {
    //@ open ssh_session(session);
      session = ssh_create_session(ssh);
    }
    //@close thread_run_data(ssh_do_session)(session);
    thread_start(ssh_do_session, session); //starts a runnable function which cannot be joined
  }
}

