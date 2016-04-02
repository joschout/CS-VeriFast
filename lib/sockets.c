#include <stdlib.h> /* abort */
#include <string.h> /* memset */
#include <stdio.h> /* printf, perror */
#include <sys/types.h>

#ifdef WIN32

//#include <winsock.h> /* send, recv */
#include <winsock2.h>
#include <process.h> /* _exit */
typedef int ssize_t;

#ifndef __MINGW32__
#define snprintf sprintf_s
#endif

#else

#include <sys/socket.h>   /* socket(), bind(), listen(), accept() */
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h> /* fork, write, close */
#define SOCKET int
#define INVALID_SOCKET (-1)
#define SOCKADDR_IN struct sockaddr_in
#define SOCKADDR struct sockaddr

#endif

#include <stdbool.h>
#include "stringBuffers.h"
#include "sockets.h"

#ifdef WIN32
#define SEND_FLAGS 0
#else
#define SEND_FLAGS MSG_NOSIGNAL
#endif


void print_socket_error_message(char *api)
{
#ifdef WIN32
    printf("Socket API call '%s' failed: error code %d\n", api, WSAGetLastError());
#else
    perror(api);
#endif
}

SOCKET socket_create_and_listen(int port)
{
    SOCKET serverSocket = 0;
    struct sockaddr_in serverName = { 0 };
    int status = 0;

#ifdef WIN32
    {
        WSADATA windowsSocketsApiData;
        WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
    }
#endif

    serverSocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (INVALID_SOCKET == serverSocket)
    {
        //print_socket_error_message("socket()");
        return INVALID_SOCKET;
    }
    
    serverName.sin_addr.s_addr=htonl(INADDR_ANY);
    serverName.sin_family = AF_INET;
    /* network-order */
    serverName.sin_port = htons(port);

    /* SO_REUSEADDR avoid the "address in use" errors after improper program
     * termination.
     * Not sure if this works on Windows; you can safely comment it out if it
     * does not work.
     */
    int optval = 1;
    setsockopt(serverSocket, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof(optval));

    status = bind(serverSocket, (struct sockaddr *) &serverName, sizeof(serverName));
    if (INVALID_SOCKET == status)
    {
        return INVALID_SOCKET;
    }
    
    
    status = listen(serverSocket, 5);  // Allow 5 pending incoming connection requests
    if (INVALID_SOCKET == status)
    {
        return INVALID_SOCKET;
    }

    return serverSocket;
}

SOCKET socket_accept(SOCKET serverSocket)
{
    struct sockaddr_in clientName = { 0 };
    SOCKET slaveSocket;
    unsigned int clientLength = sizeof(clientName);

    (void) memset(&clientName, 0, sizeof(clientName));

    slaveSocket = accept(serverSocket, (struct sockaddr *) &clientName, &clientLength);
    if (INVALID_SOCKET == slaveSocket)
    {
        return INVALID_SOCKET;
    }
    
    return slaveSocket;
}

SOCKET socket_create(int port)
{
    SOCKET lsocket;
    SOCKADDR_IN lSockAddr;
    int status = 0;

#ifdef WIN32
    {
        WSADATA windowsSocketsApiData;
        WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
    }
#endif

    lsocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (INVALID_SOCKET == lsocket)
    {
        print_socket_error_message("socket()");
        abort();
    }

    memset(&lSockAddr,0, sizeof(lSockAddr));
    lSockAddr.sin_family = AF_INET;
    lSockAddr.sin_port = htons(port);
    lSockAddr.sin_addr.s_addr = inet_addr("127.0.0.1");
    status = connect(lsocket,(SOCKADDR *)&lSockAddr,sizeof(SOCKADDR_IN));
    if(status != 0)
    {
        print_socket_error_message("connect()");
        abort();
    }
    return lsocket;
}

struct server_socket {
    int handle;
};

struct server_socket *create_server_socket(int port)
{
    int handle;
    struct server_socket *serverSocket = malloc(sizeof(struct server_socket));
    if(serverSocket == 0) return 0;
    handle = socket_create_and_listen(port);
    if(handle == INVALID_SOCKET) {
      free(serverSocket);
      return 0;
    }
    serverSocket->handle = handle;
    return serverSocket;
}

#define READER_BUFFER_SIZE 4096

struct socket {
    int handle;
    struct reader *reader;
    struct writer *writer;
};

struct reader {
    int handle;
    char *bufferStart;
    char *bufferEnd;
    char buffer[READER_BUFFER_SIZE];
};

bool reader_read_line(struct reader *reader, struct string_buffer *buffer)
{
    string_buffer_clear(buffer);
    for (;;)
    {
        void *newline = memchr(reader->bufferStart, '\n', reader->bufferEnd - reader->bufferStart);
        if (newline != 0) {
            char *end = (char *)newline;
            if (reader->bufferStart < end && *(end - 1) == '\r')
                end--;
            string_buffer_append_chars(buffer, reader->bufferStart, end - reader->bufferStart);
            reader->bufferStart = (char *)newline + 1;
            return false;
        } else {
            string_buffer_append_chars(buffer, reader->bufferStart, reader->bufferEnd - reader->bufferStart);
            reader->bufferStart = reader->buffer;
            {
                ssize_t count = recv(reader->handle, reader->buffer, READER_BUFFER_SIZE, 0);
                if (count < 0) {
                    //print_socket_error_message("recv()");
                    //abort();
                    return true;
                }
                if (count == 0)
                    return true;
                reader->bufferEnd = reader->buffer + count;
            }
        }
    }
}

void socket_read_line(struct socket* socket, struct string_buffer* buffer) 
{
  reader_read_line(socket->reader, buffer);
}

static int min(int x, int y){
  if (x > y){
    return y;
  }else{
    return x;
  }
}

void reader_read_chars(struct reader *reader, int len, struct string_buffer *buffer)
{
  int len_to_do = len;
  string_buffer_clear(buffer);
  while (true)
  {
    int copy_amount = min(len_to_do, reader->bufferEnd - reader->bufferStart);
    string_buffer_append_chars(buffer, reader->bufferStart, copy_amount);
    len_to_do = len_to_do - copy_amount;
    if (len_to_do == 0){
      reader->bufferStart = reader->bufferStart + copy_amount;
      return; // success
    }else{
      reader->bufferStart = reader->buffer;
      ssize_t len_from_recv = recv(reader->handle, reader->buffer, READER_BUFFER_SIZE, 0);
      if (len_from_recv <= 0){
        reader->bufferEnd = reader->buffer;
        return; // error or "end of file"
      }else{
        reader->bufferEnd = reader->buffer + len_from_recv;
      }
    }
  }
}

void socket_read_chars(struct socket *socket, int len, struct string_buffer *buffer)
{
  reader_read_chars(socket->reader, len, buffer);
}

struct writer {
    int handle;
};

void writer_write_string(struct writer *writer, char *text)
{
    size_t length = strlen(text);
    send(writer->handle, text, length, SEND_FLAGS);
}

void socket_write_string(struct socket* socket, char* text)
{
  writer_write_string(socket->writer, text);
}

void writer_write_integer_as_decimal(struct writer *writer, int value)
{
    char buffer[40];
    snprintf(buffer, 40, "%d", value);
    writer_write_string(writer, buffer);
}

void socket_write_integer_as_decimal(struct socket* socket, int value)
{
  writer_write_integer_as_decimal(socket->writer, value);
}

void writer_write_pointer_as_hex(struct writer *writer, void *value)
{
    char buffer[40];
    snprintf(buffer, 40, "%p", value);
    writer_write_string(writer, buffer);
}

void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer)
{
    send(writer->handle, string_buffer_get_chars(buffer), string_buffer_get_length(buffer), SEND_FLAGS);
}

void writer_write_chars(struct writer *writer, char* buffer, int len) {
  send(writer->handle, buffer, len, SEND_FLAGS);
}

void socket_write_chars(struct socket* socket, char* buffer, int len) {
  writer_write_chars(socket->writer, buffer, len);
}

void socket_write_string_buffer(struct socket* socket, struct string_buffer* buffer) 
{
  writer_write_string_buffer(socket->writer, buffer);
}

struct socket *server_socket_accept(struct server_socket *serverSocket)
{
    struct reader* reader;
    struct writer* writer;
    struct socket* socket;
    int handle = socket_accept(serverSocket->handle);
    if(handle == INVALID_SOCKET) {
      return 0;
    }
    reader = malloc(sizeof(struct reader));
    writer = malloc(sizeof(struct writer));
    socket = malloc(sizeof(struct socket));
    if(reader == 0 || writer == 0 || socket == 0) {
      if(reader != 0) free(reader);
      if(writer != 0) free(writer);
      if(socket != 0) free(socket);
      return 0;
    }
    reader->handle = handle;
    reader->bufferStart = reader->buffer;
    reader->bufferEnd = reader->buffer;
    writer->handle = handle;
    socket->handle = handle;
    socket->reader = reader;
    socket->writer = writer;
    return socket;
}

struct socket *create_client_socket(int port)
{
    int handle = socket_create(port);
    struct reader *reader = malloc(sizeof(struct reader));
    struct writer *writer = malloc(sizeof(struct writer));
    struct socket *socket = malloc(sizeof(struct socket));
    reader->handle = handle;
    reader->bufferStart = reader->buffer;
    reader->bufferEnd = reader->buffer;
    writer->handle = handle;
    socket->handle = handle;
    socket->reader = reader;
    socket->writer = writer;
    return socket;
}

struct reader *socket_get_reader(struct socket *socket)
{
    return socket->reader;
}

struct writer *socket_get_writer(struct socket *socket)
{
    return socket->writer;
}

void socket_close(struct socket *socket)
{
#ifdef WIN32
    closesocket(socket->handle);
#else
    close(socket->handle);
#endif
    free(socket->reader);
    free(socket->writer);
    free(socket);
}
