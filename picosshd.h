#ifndef PICOSSHD_H
#define PICOSSHD_H

#include "lib/stringBuffers.h"
#include "lib/sockets.h"
#include "lib/threading.h"
#include "lib/zout.h"
#include "lib/ssh_numbers.h"


#ifndef NULL
  #define NULL 0
#endif

// VeriFast does not support dereferencing bools ("*mybool"), therefore it's an int.
typedef int success_t;
#define SUCCESS 1
#define FAILURE 0

/** Version string as sent over protocol (RFC 4253 sec. 4.2) without newlines */
#define VERSION_STR "SSH-2.0-picosshd is very cool"
/** Channel id on the server side (see RFC 4254) */
#define SSH_SERVER_CHANNEL_ID 1

typedef uint32_t* uint32ptr_t; // workaround: (uint32_t*) cast unsupported by VeriFast
typedef uint8_t* uint8ptr_t;   // workaround: (uint8_t*) cast unsupported by VeriFast


struct ssh_user {
  struct string_buffer *username;
  struct string_buffer *password;
  struct string_buffer *mail;

  struct ssh_user *next;
};

// hint: think about what is shared between threads and what is not.
struct ssh_server {
  struct server_socket* ss;
  char host_pub_key[zout_sign_PUBLICKEYBYTES];
  char host_secret_key[zout_sign_SECRETKEYBYTES];
  struct string_buffer *host_key_string_without_length;
  struct ssh_user *users;
  struct mutex *users_mutex;
};

struct ssh_kex_data {
  /* hint: either all or none of these string buffers are NULL
   * (except during key exchange)*/
  struct string_buffer *client_version;
  struct string_buffer *server_version;
  struct string_buffer *server_kex_init;
  struct string_buffer *client_kex_init;
  struct string_buffer *dh_client_pubkey; // hint: if not null, length is zout_box_PUBLICKEYBYTES
  char dh_server_publickey[zout_box_PUBLICKEYBYTES];
  char dh_server_secretkey[zout_box_SECRETKEYBYTES];
  char dh_shared_secret[zout_scalarmult_BYTES];
  char session_id[zout_hash_sha256_BYTES];
  char dh_hash[zout_hash_sha256_BYTES];
};

struct ssh_keys {
  char iv_c2s[zout_hash_sha256_BYTES];
  char iv_s2c[zout_hash_sha256_BYTES];
  char key_enc_c2s[zout_hash_sha256_BYTES];
  char key_enc_s2c[zout_hash_sha256_BYTES];
  char key_integrity_c2s[zout_hash_sha256_BYTES];
  char key_integrity_s2c[zout_hash_sha256_BYTES];
};

struct ssh_session {
  struct ssh_server *server;
  struct socket *socket;
  struct ssh_kex_data *kex_data;
  struct ssh_keys *keys;
  int32_t cipher_block_size; // not stored in kex_data because we need it before kex (cipher "none" is then used)
  int32_t packets_read;
  int32_t packets_written;
  int32_t channel_id;
  struct string_buffer *receive_buffer;
  struct string_buffer *logged_in_as;
};


#endif
