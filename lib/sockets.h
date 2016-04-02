#ifndef SOCKETS_H
#define SOCKETS_H

#include <stdbool.h>
#include <stddef.h>
#include "malloc.h"
#include "stringBuffers.h"

struct server_socket;
struct socket;

/*@
predicate server_socket(struct server_socket *serverSocket;);
predicate socket(struct socket *socket;);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires emp;
    //@ ensures result == 0 ? true : server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& result == 0 ? true : socket(result);
void socket_write_string(struct socket* socket, char* string);
    //@ requires socket(socket) &*& [?f]string(string, ?cs);
    //@ ensures socket(socket) &*& [f]string(string, cs);

void socket_write_string_buffer(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket(socket) &*& [?f]string_buffer(buffer, ?cs);
    //@ ensures socket(socket) &*& [f]string_buffer(buffer, cs);

void socket_write_chars(struct socket* socket, char* buffer, int len);
    //@ requires socket(socket) &*& [?f]chars(buffer, ?cslen, ?cs) &*& len <= cslen;
    //@ ensures socket(socket) &*& [f]chars(buffer, cslen, cs);

void socket_write_integer_as_decimal(struct socket *socket, int value);
    //@ requires socket(socket);
    //@ ensures socket(socket);
void socket_read_line(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket(socket) &*& string_buffer(buffer, ?cs);
    //@ ensures socket(socket) &*& string_buffer(buffer, cs);
    
/**
 * Puts len bytes in buffer (after clearing the buffer).
 * If resulting buffer length is less than len, an error occurred.
 */
void socket_read_chars(struct socket *socket, int len, struct string_buffer *buffer);
    //@ requires socket(socket) &*& string_buffer(buffer, _) &*& len >= 0;
    //@ ensures socket(socket) &*& string_buffer(buffer, ?cs2);

void socket_close(struct socket *socket);
    //@ requires socket(socket);
    //@ ensures emp;
#endif
