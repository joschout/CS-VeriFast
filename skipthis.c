// Functions part of picosshd but that you do not have to verify

#include "skipthis.h"
#include "picosshd.h"
#include "lib/zout.h"
#include "lib/stringBuffers.h"
#include "lib/sockets.h"
#include "lib/ssh_numbers.h"
#include "lib/threading.h"
#include <string.h>
#include <arpa/inet.h> // for htonl() and ntohl()
#include <stdio.h>

struct string_buffer *ssh_read_packet(struct ssh_session *session, success_t *success);
void ssh_send_packet(struct ssh_session *session, struct string_buffer *payload);


// Useful for debugging.
// based on: http://stackoverflow.com/questions/29242/off-the-shelf-c-hex-dump-code
void hexdump(void *ptr, int buflen)
{
  unsigned char *buf = (unsigned char*)ptr;
  int i, j;
  for (i=0; i<buflen; i+=16) {
    printf("%04x   ", i);
    for (j=0; j<16; j++)
      if (i+j < buflen)
        printf("%02x ", buf[i+j]);
      else
        printf("   ");
    printf(" ");
    for (j=0; j<16; j++)
      if (i+j < buflen)
        printf("%c", ((int)buf[i+j] >= 21 && (int)buf[i+j] <= 126) ? buf[i+j] : '.');
    printf("\n");
  }
}

void hexdump_str_buf(char *msg, struct string_buffer *str_buf)
{
  puts(msg);
  hexdump(string_buffer_get_chars(str_buf), string_buffer_get_length(str_buf));
  puts("---(end hexdump)----");
}

int32_t ssh_buf_read_uint32(struct string_buffer *buf, success_t *success)
{
  int buf_length = string_buffer_get_length(buf);
  if (buf_length < 4){
    *success = FAILURE;
    return 0;
  }
  void *chars = string_buffer_get_chars(buf); // "void*" to avoid VeriFast casting issue
  uint32_t ret_uint32 = ntohl(*((uint32ptr_t)chars));
  if (ret_uint32 > (uint32_t) 2147483647){
    *success = FAILURE;
    return -1;
  }else{
    return (int32_t) ret_uint32;
  }
}

uint8_t ssh_buf_read_uint8(struct string_buffer *buf, success_t *success)
{
  int buf_length = string_buffer_get_length(buf);
  if (buf_length < 1){
    puts("Warning: buf_read_uint8 on empty buffer");
    *success = FAILURE;
    return 0;
  }
  void *chars = string_buffer_get_chars(buf);
  return *((uint8ptr_t)chars);
}

int32_t ssh_buf_pop_uint32(struct string_buffer *buf, success_t *success)
{
  int32_t result = ssh_buf_read_uint32(buf, success);
  string_buffer_drop_front(buf, 4);
  return result;
}

struct string_buffer *ssh_buf_pop_string(struct string_buffer *buf, success_t *success)
{
  int32_t length = ssh_buf_pop_uint32(buf, success);
  struct string_buffer *result = create_string_buffer();
  int32_t buf_length = string_buffer_get_length(buf);
  if(length <= buf_length){
    char *buf_chars = string_buffer_get_chars(buf);
    string_buffer_append_chars(result, buf_chars, length);
    string_buffer_drop_front(buf, length);
    return result;
  }else{
    *success = FAILURE;
    return result;
  }
}

uint8_t ssh_buf_pop_uint8(struct string_buffer *buf, success_t *success)
{
  uint8_t result = ssh_buf_read_uint8(buf, success);
  string_buffer_drop_front(buf, 1);
  return result;
}

void ssh_buf_append_uint32(struct string_buffer *buf, int32_t val)
{
  uint32_t val_converted = htonl((uint32_t)val);
  string_buffer_append_chars(buf, (char*)(void*)(&val_converted), 4);
}

void ssh_buf_append_byte(struct string_buffer *buf, uint8_t val)
{
  string_buffer_append_chars(buf, (char*)(void*)(&val), 1);
}

void ssh_buf_append_string_buf(struct string_buffer *buf, struct string_buffer *str)
{
  int len = string_buffer_get_length(str);
  ssh_buf_append_uint32(buf, len);
  string_buffer_append_string_buffer(buf, str);
}

void ssh_buf_append_string_chars(struct string_buffer *buf, char *str, int32_t length)
{
  ssh_buf_append_uint32(buf, length);
  string_buffer_append_chars(buf, str, length);
}

void ssh_buf_append_string_c_string(struct string_buffer *buf, char *str)
{
  ssh_buf_append_uint32(buf, strlen(str));
  string_buffer_append_string(buf, str);
}


/**
 * Append an "mpint" as described in rfc4251 on page 8.
 */
void ssh_buf_append_mpint(struct string_buffer *buf, char *str, int32_t length)
{
  // hint: after obtaining the chunk character(str, _),
  // call the lemma character_to_u_character(str).
  bool should_precede_zero = *((unsigned char*)(void*)str) >= 128;
  if (should_precede_zero){
    ssh_buf_append_uint32(buf, length + 1);
    ssh_buf_append_byte(buf, 0);
  } else{
    ssh_buf_append_uint32(buf, length);
  }
  string_buffer_append_chars(buf, str, length);
}

struct string_buffer *ssh_create_host_key_string_without_length(struct ssh_server *server)
{
  struct string_buffer *host_key_string = create_string_buffer();
  ssh_buf_append_string_c_string(host_key_string, "ssh-ed25519");
  ssh_buf_append_string_chars(host_key_string, server->host_pub_key, zout_sign_ed25519_PUBLICKEYBYTES);
  return host_key_string;
}



/**
 * Receive client version string.
 * Returns this string without trailing <CR><LF>.
 */
struct string_buffer *ssh_recv_version(struct ssh_session *session)
{
  // The server can send other lines first but the client cannot (RFC 4253).
  struct string_buffer* result = create_string_buffer();
  socket_read_line(session->socket, result);
  return result;
}

/**
 * Send server ID string. This includes our SSH version number (2).
 * Returns this string without trailing <CR><LF>.
 */
struct string_buffer *ssh_send_version(struct ssh_session *session)
{
  struct string_buffer* result = create_string_buffer();
  string_buffer_append_string(result, VERSION_STR);
  // Send in one TCP packet to not break Wireshark parsing  
  socket_write_string(session->socket, VERSION_STR "\r\n");
  return result;
}


struct string_buffer *ssh_read_dh_client_pubkey(struct ssh_session *session, success_t *success)
{
  struct string_buffer *packet = ssh_read_packet(session, success);

  uint8_t msg_code = ssh_buf_pop_uint8(packet, success);
  int32_t key_length = ssh_buf_pop_uint32(packet, success);
  if (msg_code != SSH_MSG_KEX_ECDH_INIT || key_length != zout_box_PUBLICKEYBYTES){
    *success = FAILURE;
  }

  return packet; // what's left should be the key.
}


void ssh_send_kex_reply(
  struct ssh_session *session,
  struct ssh_kex_data *kex,
  struct string_buffer *signature)
{
  struct string_buffer *network_message = create_string_buffer();
  ssh_buf_append_byte(network_message, SSH_MSG_KEX_ECDH_REPLY);
  ssh_buf_append_string_buf(network_message, session->server->host_key_string_without_length);
  ssh_buf_append_string_chars(network_message, kex->dh_server_publickey, zout_box_PUBLICKEYBYTES);
  ssh_buf_append_string_buf(network_message, signature);
  ssh_send_packet(session, network_message);
  string_buffer_dispose(network_message);
}



/**
 * Sends the message that new keys are calculated.
 * This message does not contain keys itself.
 */
void ssh_send_receive_newkeys(struct ssh_session *session, success_t *success)
{
  struct string_buffer *send_newkeys_msg = create_string_buffer();
  ssh_buf_append_byte(send_newkeys_msg, SSH_MSG_NEWKEYS);
  ssh_send_packet(session, send_newkeys_msg);
  struct string_buffer *recv_newkeys_msg = ssh_read_packet(session, success);
  if ( ! string_buffer_equals(send_newkeys_msg, recv_newkeys_msg)){
    *success = FAILURE;
  }
  string_buffer_dispose(send_newkeys_msg);
  string_buffer_dispose(recv_newkeys_msg);
}


void ssh_service_request(struct ssh_session *session, struct string_buffer *packet, success_t *success)
{
  struct string_buffer *service_name = ssh_buf_pop_string(packet, success);
  if(string_buffer_equals_string(service_name, "ssh-userauth")){
    //We accept the request.
    struct string_buffer *accept_user_auth = create_string_buffer();
    ssh_buf_append_byte(accept_user_auth, SSH_MSG_SERVICE_ACCEPT);
    ssh_buf_append_string_c_string(accept_user_auth, "ssh-userauth");
    ssh_send_packet(session, accept_user_auth);
    string_buffer_dispose(accept_user_auth);

    //Sending the authentication banner.
    struct string_buffer *banner = create_string_buffer();
    ssh_buf_append_byte(banner, SSH_MSG_USERAUTH_BANNER);
    ssh_buf_append_string_c_string(banner, "picosshd here!\nUse \"ssh -p 2222 admin@HOST_NAME menu\" to connect!\n");
    ssh_buf_append_string_c_string(banner, "en");
    ssh_send_packet(session, banner);
    string_buffer_dispose(banner);
  }
  else{
    *success = FAILURE;
    puts("Client requested unkown service");
  }
  string_buffer_dispose(service_name);
}


void ssh_send_channel_msg(struct ssh_session *session, char *msg, struct string_buffer *msg_str_buf, success_t *success)
{
  struct string_buffer *buf = create_string_buffer();
  ssh_buf_append_byte(buf, SSH_MSG_CHANNEL_DATA);
  ssh_buf_append_uint32(buf, session->channel_id);
  if (msg_str_buf){
    ssh_buf_append_string_buf(buf, msg_str_buf);
  }else{
    ssh_buf_append_string_c_string(buf, msg);
  }
  ssh_send_packet(session, buf);
  string_buffer_dispose(buf);
}

void ssh_channel_open(struct ssh_session *session, struct string_buffer *packet, success_t *success)
{
  string_buffer_dispose(ssh_buf_pop_string(packet, success));//channel type
  int32_t sender_channel = ssh_buf_pop_uint32(packet, success);//sender channel
  session->channel_id = sender_channel;
  ssh_buf_pop_uint32(packet, success);//initial window size
  ssh_buf_pop_uint32(packet, success);//maximum packet size

  struct string_buffer *channel_open_confirmation = create_string_buffer();
  ssh_buf_append_byte(channel_open_confirmation, SSH_MSG_CHANNEL_OPEN_CONFIRMATION);
  ssh_buf_append_uint32(channel_open_confirmation, sender_channel);//recipient channel (for us this is the one the recipient sent as sender channel!)
  ssh_buf_append_uint32(channel_open_confirmation, SSH_SERVER_CHANNEL_ID);//channel id
  ssh_buf_append_uint32(channel_open_confirmation, 0xFFFFFFFF);//initial window size for us
  ssh_buf_append_uint32(channel_open_confirmation, 65535);//maximum packet size
  ssh_send_packet(session, channel_open_confirmation);
  string_buffer_dispose(channel_open_confirmation);
}



void ssh_menu_sendmail(struct ssh_session *session, struct string_buffer *arguments, success_t *success)
{
  struct string_buffer *username = create_string_buffer();
  struct string_buffer *message = create_string_buffer();
  bool can_split = string_buffer_split(arguments, " ", username, message);
  bool message_sent = false;
  if (can_split){
    mutex_acquire(session->server->users_mutex);
    struct ssh_user *user = session->server->users;
    while (user != NULL)
    {
      if (string_buffer_equals(user->username, username)){
        string_buffer_append_string_buffer(user->mail, session->logged_in_as);
        string_buffer_append_string(user->mail, " says: ");
        string_buffer_append_string_buffer(user->mail, message);
        string_buffer_append_string(user->mail, "\n");
        message_sent = true;
        break;
      }
      user = user->next;
    }
    mutex_release(session->server->users_mutex);
    if (!message_sent){
      ssh_send_channel_msg(session, "Error: Cannot find the user ``", NULL, success);
      ssh_send_channel_msg(session, "", username, success);
      ssh_send_channel_msg(session, "''.\n", NULL, success);
    }else{
      ssh_send_channel_msg(session, "OK, message to ``", NULL, success);
      ssh_send_channel_msg(session, "", username, success);
      ssh_send_channel_msg(session, "'' sent.\n", NULL, success);
    }
  }else{
    ssh_send_channel_msg(session, "Syntax error. Usage: sendmail USERNAME MESSAGE\n", NULL, success);
  }
  string_buffer_dispose(username);
  string_buffer_dispose(message);
}


void ssh_menu_readmail(struct ssh_session *session, struct string_buffer *arguments, success_t *success)
{
  mutex_acquire(session->server->users_mutex);
  struct ssh_user *user = session->server->users;
  while (user != NULL)
  {
    if (string_buffer_equals(user->username, session->logged_in_as)){
      if (string_buffer_equals_string(user->mail, "")){
        ssh_send_channel_msg(session, "You do not have any new mail.\n", NULL, success);
      }else{
        ssh_send_channel_msg(session, "", user->mail, success);
        string_buffer_clear(user->mail);
      }
      break;
    }
    user = user->next;
  }
  mutex_release(session->server->users_mutex);
}


void ssh_channel_request(struct ssh_session *session, struct string_buffer *packet, success_t *success)
{
  ssh_buf_pop_uint32(packet, success);//we ignore channel number
  struct string_buffer *req_str = ssh_buf_pop_string(packet, success);

  bool eq_pty = string_buffer_equals_string(req_str, "pty-req");
  bool eq_shell = string_buffer_equals_string(req_str, "shell");
  if (eq_pty || eq_shell) {
    ssh_send_channel_msg(session, "\n\r'shell' not supported. Do not forget the \"menu\" in \"ssh -p 2222 admin@HOST_NAME menu\".\n\r", NULL, success);
    *success = FAILURE;
  }else if (string_buffer_equals_string(req_str, "exec")){
    ssh_send_channel_msg(session,
      "                   _                   _         _ \n"
      "             _ __ (_) ___ ___  ___ ___| |__   __| |\n"
      "Welcome to  | '_ `| |/ __/ _ `/ __/ __| '_ ` / _` |\n"
      "            | |_) | | (_| (_) `__ `__ ` | | | (_| |\n"
      "            | .__/|_|`___`___/|___/___/_| |_|`__,_|\n"
      "            |_|                                    \n"
      "\n"
      "picosshd> ",
      NULL, success);
  }
  // do nothing on everything else.
  string_buffer_dispose(req_str);
}

