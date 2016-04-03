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
        chars(server->host_pub_key, _, _) &*&

        chars(server->host_secret_key, _, _) &*&
        server->host_key_string_without_length |-> ?hkwl &*&
        string_buffer(hkwl, _) &*&
        server->users_mutex |-> ?mutex &*&
        mutex(mutex, ssh_server_userlist(server));
 @*/
/*@ predicate ssh_session(struct ssh_session *session) =
      session == 0 ?
        true
      :
        malloc_block_ssh_session(session) &*&
        session->server |-> _ &*&
        session->socket |-> ?socket &*&
        socket(socket) &*&
        session->kex_data |-> _ &*&
        session->keys |-> ?keys &*&
        ssh_keys(keys) &*&
        session->cipher_block_size |-> _ &*&
        session->packets_read |-> _ &*&
        session->packets_written |-> _ &*&
        session->channel_id |-> _ &*&
        session->receive_buffer |-> ?rbuffer &*&
        string_buffer(rbuffer, _) &*&
        session->logged_in_as |-> _ ;
 @*/

/*@ predicate ssh_keys(struct ssh_keys *keys) =
      keys == 0 ?
        true
      :
        malloc_block_ssh_keys(keys) &*&
        chars(keys->iv_c2s, _, _) &*&
        chars(keys->iv_s2c, _, _) &*&
        chars(keys->key_enc_c2s, _, _) &*&
        chars(keys->key_enc_s2c, _, _) &*&
        chars(keys->key_integrity_c2s, _, _) &*&
        chars(keys->key_integrity_s2c, _, _);

 @*/


/*@ predicate ssh_kex_data(struct ssh_kex_data *data) =
      malloc_block_ssh_kex_data(data) &*&
      data->client_version |-> _ &*&
      data->server_version |-> _ &*&
      data->server_kex_init |-> _ &*&
      data->client_kex_init |-> _ &*&
      chars(data->dh_server_publickey, _, _) &*&
      chars(data->dh_server_secretkey, _, _) &*&
      chars(data->dh_shared_secret, _, _) &*&
      chars(data->session_id, _, _) &*&
      chars(data->dh_hash, _, _);


 @*/

/**@

  lemma void ssh_users_add_lemma(struct ssh_user *user)
    requires ssh_users(user, ?values) &*& (last == head(tail(values))) &*& last->next |-> ?next
    &*& malloc_block_ssh_user(last_u);
    ensures ssh_users(user, append(values, con(values, last_u)));
    {
      open ssh_users(user, values);
      if(values0 != nil){
        ssh_users_add_lemma(user->next);
      }else{
        close ssh_users(last_u, nil);
      }
      close ssh_users(user, _);
    }

@*/


/*@
  predicate ssh_users_lseg(struct ssh_user *first, struct ssh_user *last, int count) =
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
      ssh_users_lseg(next, last, count - 1);
@*/



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
  user->next = server->users;
  server->users = user;
  //@close ssh_users(user, cons(user->next, _));
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
/**@ requires
      session->logged_in_as |-> _ &*&
      session->server |-> ?server &*&
      server->users_mutex |-> ?mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(username, ?us) &*&
      string_buffer(password, ?pss);
@*/
/**@ ensures
      session->server |-> server &*&
      server->users_mutex |-> mutex &*&
      mutex(mutex, ssh_server_userlist(server)) &*&
      string_buffer(username, us) &*&
      string_buffer(password, pss); @*/
{
  bool result = false;
  // Totally not secure against timing attacks.
  mutex_acquire(session->server->users_mutex);
  //@ close ssh_users(0, nil);
  //@ open ssh_server_userlist(server)();
  struct ssh_user *user = session->server->users;
  // Hint: You will need list segments (see tutorial) or Tuerk-loops (see tutorial).
  ////@ open ssh_users(user, ?userlist);
  ////@ close ssh_users(user, userlist);
  ////@ close ssh_users(?user2, nil);
  while (user != NULL)
  /*@ invariant
          session->logged_in_as |-> _ &*&
          string_buffer(username, us) &*&
          string_buffer(password, pss) &*&
          ssh_users(user, ?userlist) &*&
          ssh_users(?user2, ?userlist2) ; @*/
  {
    //@ open ssh_users(user, userlist);
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

    
    ////@ close ssh_users(user, cons(head(userlist), nil));
    user = user->next;
    
    ////@ append_assoc(userlist2, cons(user, nil), userlist);
  }
  //@ close ssh_server_userlist(server)();
  mutex_release(session->server->users_mutex);
  return result;
}


/*@ predicate_ctor ssh_server_userlist(struct ssh_server *server)() =
      server->users |-> ?user &*&
      ssh_users(user, ?userlist);
@*/


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
//@ ensures ssh_server(ssh) &*& ssh_session(result);
{
  struct ssh_session *session = malloc(sizeof(struct ssh_session));
  if (session == NULL) {
  //@close ssh_session(0);
    return NULL;
  }
  struct ssh_keys *keys = malloc(sizeof(struct ssh_keys));
  if (keys == NULL) {
    free(session);
    //@close ssh_session(0);
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
    //@ close ssh_session(session);
    return session;
  }else{
    free(session);
    free(keys);
    return NULL;
    //@close ssh_session(0);
  }
}



/**
 * TCP is a stream, so when sending packets in this stream, one has to
 * mark the packets (e.g. by putting markers between messages or prepending
 * messages with the size of it). Gets one such packet from the stream.
 * Returned buffer does not include length, padding length, padding and mac.
 */
struct string_buffer *ssh_read_packet(struct ssh_session *session, success_t *success)
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

  // Read first block.
  socket_read_chars(session->socket, session->cipher_block_size, first_block);
  int32_t first_block_length = string_buffer_get_length(first_block);
  if (first_block_length != session->cipher_block_size){
    puts("Error while reading first block of ssh packet.");
    *success = FAILURE;
    goto cleanup;
  }

  // Decrypt first block.
  char *first_block_chars = string_buffer_get_chars(first_block);
  if (session->kex_data){
    zout_stream_aes128ctr_xor(
      first_block_chars,
      first_block_chars,
      first_block_length,
      session->keys->iv_c2s,
      session->keys->key_enc_c2s);
    zout_update_iv(session->keys->iv_c2s, 1);
  }

  // Obtain lengths
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
  
  // Read the next blocks.
  
  // Hint: call the lemma div_rem((payload_length), session->cipher_block_size)
  socket_read_chars(session->socket, bytes_to_read, later_blocks);
  if (string_buffer_get_length(later_blocks) != bytes_to_read){
    puts("Sudden disconnect?");
    *success = FAILURE;
    goto cleanup;
  }

  // Decrypt these next blocks
  if (session->kex_data){
    int later_blocks_length = string_buffer_get_length(later_blocks);
    char *later_blocks_chars = string_buffer_get_chars(later_blocks);
    zout_stream_aes128ctr_xor(
          later_blocks_chars,
          later_blocks_chars,
          later_blocks_length,
          session->keys->iv_c2s,
          session->keys->key_enc_c2s);
    zout_update_iv(session->keys->iv_c2s, blocks_to_read);
  }

  string_buffer_append_string_buffer(all_blocks, first_block);
  string_buffer_append_string_buffer(all_blocks, later_blocks);
  
  // Read and check MAC
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
    zout_auth_hmacsha256(computed_mac, for_mac_computation_chars, for_mac_computation_length, session->keys->key_integrity_c2s);
    string_buffer_dispose(input_for_mac_computation);
    // Is MAC correct?
    if (memcmp(string_buffer_get_chars(mac_from_network), computed_mac, zout_auth_hmacsha256_BYTES) != 0){
      puts("Message authentication failed!");
      *success = FAILURE;
      
      goto cleanup;
    }
  }
  
  // we have read a packet and should increase the read packets counter
  if (session->packets_read == INT_MAX){
    *success = FAILURE;
    goto cleanup;
  }
  session->packets_read = session->packets_read + 1;

  // Calculate the payload we want to return.
  int all_blocks_length = string_buffer_get_length(all_blocks);
  char *all_blocks_chars = string_buffer_get_chars(all_blocks);
  string_buffer_append_chars(payload,
      all_blocks_chars,
      all_blocks_length - padding_length);
  ssh_buf_pop_uint32(payload, success); // drop payload length field
  ssh_buf_pop_uint8(payload, success); // drop padding length field

cleanup:
  string_buffer_dispose(mac_from_network);
  string_buffer_dispose(all_blocks);
  string_buffer_dispose(later_blocks);
  string_buffer_dispose(first_block);
  string_buffer_dispose(first_block_without_lengths);
  return payload;
}

void ssh_send_packet(struct ssh_session *session, struct string_buffer *payload, success_t *success)
{
  struct string_buffer *to_send = create_string_buffer();

  // Calculate lengths
  int32_t payload_length = string_buffer_get_length(payload);
  // Hint: session->cipher_block_size is 8 or 16
  // Hint: call the lemma "div_rem((payload_length), session->cipher_block_size);"
  int32_t padding_length = session->cipher_block_size - (4 + 1 + (payload_length % session->cipher_block_size));
  if (padding_length < 4){
    padding_length = padding_length + session->cipher_block_size;
  }
  if (payload_length > 1048576){
    *success = FAILURE;
    string_buffer_dispose(to_send);
    return;
  }
  int32_t packet_length = padding_length + 1 + payload_length;
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

    // Add MAC
    string_buffer_append_chars(to_send, computed_mac, zout_auth_hmacsha256_BYTES);

    string_buffer_dispose(for_mac_computation);
  }
  
  if (session->packets_written == INT_MAX){
    *success = FAILURE;
  }else{
    session->packets_written = session->packets_written + 1;
    socket_write_string_buffer(session->socket, to_send);
  }
  string_buffer_dispose(to_send);
  
}


struct string_buffer *ssh_send_kex_init(struct ssh_session *session, success_t *success)
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
{
  return ssh_read_packet(session, success);
}

struct ssh_kex_data *ssh_kex_data_create()
{
  struct ssh_kex_data *kex_data = malloc(sizeof(struct ssh_kex_data));
  if (kex_data == NULL) abort ();
  kex_data->client_version = NULL;
  kex_data->server_version = NULL;
  kex_data->server_kex_init = NULL;
  kex_data->client_kex_init = NULL;
  kex_data->dh_client_pubkey = NULL;
  return kex_data;
}

void ssh_kex_data_dispose(struct ssh_kex_data *kex)
{
  string_buffer_dispose(kex->client_version);
  string_buffer_dispose(kex->server_version);
  string_buffer_dispose(kex->server_kex_init);
  string_buffer_dispose(kex->client_kex_init);
  string_buffer_dispose(kex->dh_client_pubkey);
  free(kex);
}



struct string_buffer *ssh_kex_sign(struct ssh_server *server, struct ssh_kex_data *kex_data)
{ 
  int32_t dh_signature_length; // VeriFast: "A local variable whose address is taken must be declared at the start of a block."

  struct string_buffer *to_hash = create_string_buffer();
  ssh_buf_append_string_buf(to_hash, kex_data->client_version);
  ssh_buf_append_string_buf(to_hash, kex_data->server_version);
  ssh_buf_append_string_buf(to_hash, kex_data->client_kex_init);
  ssh_buf_append_string_buf(to_hash, kex_data->server_kex_init);
  ssh_buf_append_string_buf(to_hash, server->host_key_string_without_length);
  ssh_buf_append_string_buf(to_hash, kex_data->dh_client_pubkey);
  ssh_buf_append_string_chars(to_hash, kex_data->dh_server_publickey, zout_box_PUBLICKEYBYTES);
  ssh_buf_append_mpint(to_hash, kex_data->dh_shared_secret, zout_scalarmult_BYTES);

  // Now we know what we want to hash, so hash it:
  int to_hash_length = string_buffer_get_length(to_hash);
  char *to_hash_chars = string_buffer_get_chars(to_hash);
  zout_hash_sha256(kex_data->dh_hash, to_hash_chars, to_hash_length);

  string_buffer_dispose(to_hash);

  // Sign the hash
  char dh_signature[zout_sign_BYTES];
  zout_sign_detached(dh_signature, &dh_signature_length, kex_data->dh_hash, zout_hash_sha256_BYTES, server->host_secret_key);

  struct string_buffer *signature_buf = create_string_buffer();
  ssh_buf_append_string_c_string(signature_buf, "ssh-ed25519");
  ssh_buf_append_string_chars(signature_buf, dh_signature, dh_signature_length);
  return signature_buf;
}

void ssh_kex_calc_key(struct ssh_kex_data *kex_data, int32_t number, char *destination)
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
  struct string_buffer *to_hash = create_string_buffer();
  ssh_buf_append_mpint(to_hash, kex_data->dh_shared_secret, zout_scalarmult_BYTES);
  string_buffer_append_chars(to_hash, kex_data->dh_hash, zout_hash_sha256_BYTES);
  ssh_buf_append_byte(to_hash, (unsigned char)('A' + number));
  string_buffer_append_chars(to_hash, kex_data->session_id, zout_hash_sha256_BYTES);

  int to_hash_length = string_buffer_get_length(to_hash);
  char *to_hash_chars = string_buffer_get_chars(to_hash);
  zout_hash_sha256(destination, to_hash_chars, to_hash_length);
  string_buffer_dispose(to_hash);
}

void ssh_kex_calc_keys(struct ssh_kex_data *kex_data, struct ssh_keys *keys)
{
  ssh_kex_calc_key(kex_data, 0, keys->iv_c2s);
  ssh_kex_calc_key(kex_data, 1, keys->iv_s2c);
  ssh_kex_calc_key(kex_data, 2, keys->key_enc_c2s);
  ssh_kex_calc_key(kex_data, 3, keys->key_enc_s2c);
  ssh_kex_calc_key(kex_data, 4, keys->key_integrity_c2s);
  ssh_kex_calc_key(kex_data, 5, keys->key_integrity_s2c);
}

/**
 * Coordinate key exchange network packets and cryptographic calculations.
 */
void ssh_kex(struct ssh_session *session, success_t *success)
{
  struct ssh_kex_data *kex_data = ssh_kex_data_create();
  kex_data->client_version = ssh_recv_version(session);
  kex_data->server_version = ssh_send_version(session);
  kex_data->server_kex_init = ssh_send_kex_init(session, success);
  kex_data->client_kex_init = ssh_recv_kex_init(session, success);
  kex_data->dh_client_pubkey = ssh_read_dh_client_pubkey(session, success);
  if (string_buffer_get_length(kex_data->dh_client_pubkey) != zout_box_PUBLICKEYBYTES){
    *success = FAILURE;
  }
  if (*success == FAILURE){
    // return instead of passing unallocated memory buffers to zout.
    // cleanup by hand (instead of function call) to make verification easier
    string_buffer_dispose(kex_data->client_version);
    string_buffer_dispose(kex_data->server_version);
    string_buffer_dispose(kex_data->server_kex_init);
    string_buffer_dispose(kex_data->client_kex_init);
    string_buffer_dispose(kex_data->dh_client_pubkey);
    free(kex_data);
    return;
  }
  // Create our diffie-hellman (dh) keypair:
  zout_box_keypair(kex_data->dh_server_publickey, kex_data->dh_server_secretkey);
  // Calculate shared secret (client will also calculate this)
  char *client_dh_pubkey_chars = string_buffer_get_chars(kex_data->dh_client_pubkey);
  zout_scalarmult(kex_data->dh_shared_secret, kex_data->dh_server_secretkey, client_dh_pubkey_chars);
  
  struct string_buffer *signature = ssh_kex_sign(session->server, kex_data);

  memcpy(kex_data->session_id, kex_data->dh_hash, zout_hash_sha256_BYTES);
  ssh_send_kex_reply(session, kex_data, signature);
  string_buffer_dispose(signature);
  ssh_kex_calc_keys(kex_data, session->keys);
  // send this with the old cipher (in our case "none"):
  ssh_send_receive_newkeys(session, success);
  // switch to new cipher and keys
  // we don't support re-key-exchange, but it's easier to verify like this:
  if (session->kex_data != NULL) ssh_kex_data_dispose(session->kex_data);
  session->kex_data = kex_data;
  session->cipher_block_size = zout_stream_aes128ctr_CIPHERBLOCKBYTES;
}


void ssh_userauth_request(struct ssh_session *session, struct string_buffer *packet, success_t *success)
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
{
  struct string_buffer *username = create_string_buffer();
  struct string_buffer *password = create_string_buffer();
  bool can_split_user_pass = string_buffer_split(arguments, " ", username, password);
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
}

void ssh_menu_command(struct ssh_session *session, struct string_buffer *full_commandline, success_t *success)
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
    ssh_send_channel_msg(session, "Supported commands are: adduser sendmail readmail help.\n", NULL, success);
  }else{
    ssh_send_channel_msg(session, "Unsupported command: ``", NULL, success);
    ssh_send_channel_msg(session, "", cmd, success);
    ssh_send_channel_msg(session, "''. Type ``help'' (without quotes, followed by enter) for help.\n", NULL, success);
  }
  ssh_send_channel_msg(session, "picosshd> ", NULL, success);
  string_buffer_dispose(cmd);
  string_buffer_dispose(all_args);
}

void ssh_channel_data(struct ssh_session *session, struct string_buffer *packet, success_t *success)
{
  if (session->logged_in_as == NULL){
    // Evil ssh client tries to execute commands before being logged in
    *success = FAILURE;
    return;
  }
  struct string_buffer *data = ssh_buf_pop_string(packet, success);
  string_buffer_append_string_buffer(session->receive_buffer, data);
  string_buffer_dispose(data);
  bool can_split = true;
  while (can_split)
  {
    struct string_buffer *before = create_string_buffer();
    struct string_buffer *after = create_string_buffer();
    can_split = string_buffer_split(session->receive_buffer, "\n", before, after);
    if (can_split){
      ssh_menu_command(session, before, success);
      string_buffer_dispose(session->receive_buffer);
      session->receive_buffer = after;
    }else{
      string_buffer_dispose(after);
    }
    string_buffer_dispose(before);
  }
}


void ssh_protocol_loop(struct ssh_session *session, success_t *success)
{
  bool cont = true;
  while (cont && *success)
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
        ssh_session(session);
@*/

void ssh_do_session(struct ssh_session *session)//@ : thread_run
//@ requires thread_run_data(ssh_do_session)(session);
//@ ensures true;
{
  success_t success = SUCCESS;

  puts("New connection");
  

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

