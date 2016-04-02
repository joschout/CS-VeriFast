// Definitions of functions part of picosshd but that you do not have to verify

#ifndef PICOSSHD_PART_NOT_TO_BE_VERIFIED_H
#define PICOSSHD_PART_NOT_TO_BE_VERIFIED_H

#include "picosshd.h"

int32_t ssh_buf_read_uint32(struct string_buffer *buf, success_t *success);
//@ requires string_buffer(buf, _) &*& integer(success, _);
//@ ensures string_buffer(buf, _) &*& integer(success, ?has_success) &*& has_success == SUCCESS ? result >= 0 : true;

uint8_t ssh_buf_read_uint8(struct string_buffer *buf, success_t *success);
//@ requires string_buffer(buf, _) &*& integer(success, _);
//@ ensures string_buffer(buf, _) &*& integer(success, _);

int32_t ssh_buf_pop_uint32(struct string_buffer *buf, success_t *success);
//@ requires string_buffer(buf, _) &*& integer(success, _);
//@ ensures string_buffer(buf, _) &*& integer(success, _) &*& result >= 0;

struct string_buffer *ssh_buf_pop_string(struct string_buffer *buf, success_t *success);
//@ requires string_buffer(buf, _) &*& integer(success, _);
//@ ensures string_buffer(buf, _) &*& integer(success, _) &*& string_buffer(result, _);

uint8_t ssh_buf_pop_uint8(struct string_buffer *buf, success_t *success);
//@ requires string_buffer(buf, _) &*& integer(success, _);
//@ ensures string_buffer(buf, _) &*& integer(success, _);

void ssh_buf_append_uint32(struct string_buffer *buf, int32_t val);
//@ requires string_buffer(buf, _) &*& val >= 0;
//@ ensures string_buffer(buf, _);

void ssh_buf_append_byte(struct string_buffer *buf, uint8_t val);
//@ requires string_buffer(buf, _);
//@ ensures string_buffer(buf, _);
void ssh_buf_append_string_buf(struct string_buffer *buf, struct string_buffer *str);
//@ requires string_buffer(buf, _) &*& [?f]string_buffer(str, ?cs);
//@ ensures string_buffer(buf, _) &*& [f]string_buffer(str, cs);

void ssh_buf_append_string_chars(struct string_buffer *buf, char *str, int32_t length);
//@ requires string_buffer(buf, _) &*& [?f]chars(str, ?len, ?cs) &*& len >= length;
//@ ensures string_buffer(buf, _) &*& [f]chars(str, len, cs);

void ssh_buf_append_string_c_string(struct string_buffer *buf, char *str);
//@ requires string_buffer(buf, _) &*& [?f]string(str, ?cs);
//@ ensures string_buffer(buf, _) &*& [f]string(str, cs);


/**
 * Append an "mpint" as described in rfc4251 on page 8.
 */
void ssh_buf_append_mpint(struct string_buffer *buf, char *str, int32_t length);
//@ requires string_buffer(buf, _) &*& chars(str, ?len, _) &*& len >= length  &*& length > 0;
//@ ensures string_buffer(buf, _) &*& chars(str, len, _);

struct string_buffer *ssh_create_host_key_string_without_length(struct ssh_server *server);
//@ requires [?f]chars(server->host_pub_key, zout_sign_PUBLICKEYBYTES, ?cs);
//@ ensures [f]chars(server->host_pub_key, zout_sign_PUBLICKEYBYTES, cs) &*& string_buffer(result, _);

/**
 * Receive client version string.
 * Returns this string without trailing <CR><LF>.
 */
struct string_buffer *ssh_recv_version(struct ssh_session *session);
//@ requires [?f]session->socket |-> ?socket &*& socket(socket);
//@ ensures [f]session->socket |-> socket &*& socket(socket) &*& string_buffer(result, _);


/**
 * Send server ID string. This includes our SSH version number (2).
 * Returns this string without trailing <CR><LF>.
 */
struct string_buffer *ssh_send_version(struct ssh_session *session);
//@ requires [?f]session->socket |-> ?socket &*& socket(socket);
//@ ensures [f]session->socket |-> socket &*& socket(socket) &*& string_buffer(result, _);

struct string_buffer *ssh_read_dh_client_pubkey(struct ssh_session *session, success_t *success);
//@ requires [?f]session->socket |-> ?socket &*& socket(socket) &*& integer(success, _);
//@ ensures [f]session->socket |-> socket &*& socket(socket) &*& integer(success, _) &*& string_buffer(result, _);

// NOTE: incomplete contract.
void ssh_send_kex_reply(
  struct ssh_session *session,
  struct ssh_kex_data *kex,
  struct string_buffer *signature);
//@ requires string_buffer(signature, _);
//@ ensures string_buffer(signature, _);

/**
 * Sends the message that new keys are calculated.
 * This message does not contain keys itself.
 * NOTE: incomplete contract.
 */
void ssh_send_receive_newkeys(struct ssh_session *session, success_t *success);
//@ requires integer(success, _);
//@ ensures integer(success, _);

// NOTE: incomplete contract.
void ssh_service_request(struct ssh_session *session, struct string_buffer *packet, success_t *success);
//@ requires string_buffer(packet, _) &*& integer(success, _);
//@ ensures string_buffer(packet, _) &*& integer(success, _);

/*@
predicate maybe_string_buffer(struct string_buffer *buf;) =
  buf == NULL ?
    emp
  :
    string_buffer(buf, _)
;
@*/

// NOTE: incomplete contract (calls ssh_send_packet)
void ssh_send_channel_msg(struct ssh_session *session, char *msg, struct string_buffer *msg_str_buf, success_t *success);
/*@
requires
  [?f]string(msg, ?cs)
  &*& integer(success, _)
  &*& [?fc]session->channel_id |-> ?channel_id
  &*& msg_str_buf != NULL ?
    [?fsb]string_buffer(msg_str_buf, _)
    &*& ensures
      [fsb]string_buffer(msg_str_buf, _)
      &*& [f]string(msg, cs)
      &*& integer(success, _)
      &*& [fc]session->channel_id |-> channel_id
  :
    ensures
      [f]string(msg, cs)
      &*& integer(success, _)
      &*& [fc]session->channel_id |-> channel_id;
@*/
//@ ensures true; // this ensure line is ignored

// NOTE: incomplete contract.
void ssh_channel_open(struct ssh_session *session, struct string_buffer *packet, success_t *success);
//@ requires string_buffer(packet, _) &*& integer(success, _);
//@ ensures string_buffer(packet, _) &*& integer(success, _);

// NOTE: incomplete contract.
void ssh_menu_sendmail(struct ssh_session *session, struct string_buffer *arguments, success_t *success);
//@ requires string_buffer(arguments, _) &*& integer(success, _);
//@ ensures string_buffer(arguments, _) &*& integer(success, _);

// NOTE: incomplete contract.
void ssh_menu_readmail(struct ssh_session *session, struct string_buffer *arguments, success_t *success);
//@ requires string_buffer(arguments, _) &*& integer(success, _);
//@ ensures string_buffer(arguments, _) &*& integer(success, _);

// NOTE: incomplete contract.
void ssh_channel_request(struct ssh_session *session, struct string_buffer *packet, success_t *success);
//@ requires string_buffer(packet, _) &*& integer(success, _);
//@ ensures string_buffer(packet, _) &*& integer(success, _);

/*@
lemma void division_remains_positive(int a, int b);
requires a >= 0 &*& b > 0;
ensures a / b >= 0;
@*/

#endif
