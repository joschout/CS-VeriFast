#ifndef ZOUT_H
#define ZOUT_H

#include <stddef.h> // size_t
#include <stdint.h>

/**
 * Zout is a wrapper around the sodium cryptographic library.
 * It works around VeriFast's lack of support for unsigned long long.
 * Also, string_buffers use char while sodium uses unsigned char,
 * which makes the code and the verification more difficult.
 * The API is exactly the same except that "unsigned long long"
 * has been replaced with "int32_t", and unsigned chars parameters are
 * replaced by chars.
 *
 * Functions that do not require wrapping are not wrapped and just provided
 * a contract.
 *
 * Do not use in production!
 */

#define zout_box_PUBLICKEYBYTES 32
#define zout_box_SECRETKEYBYTES 32
#define zout_hash_sha256_BYTES 32
#define zout_sign_PUBLICKEYBYTES 32
#define zout_sign_SECRETKEYBYTES 64
#define zout_sign_ed25519_PUBLICKEYBYTES 32
#define zout_scalarmult_BYTES 32
#define zout_sign_BYTES 64
#define zout_auth_hmacsha256_BYTES 32
#define zout_auth_hmacsha256_KEYBYTES 32
#define zout_stream_aes128ctr_KEYBYTES 16
#define zout_stream_aes128ctr_NONCEBYTES 16

// AES has a block size of 16 bytes
#define zout_stream_aes128ctr_CIPHERBLOCKBYTES 16

//@ require_module zout;

//@ predicate sodium_is_initialized(;);

int sodium_init(void);
//@ requires module(zout, true);
//@ ensures [_]sodium_is_initialized();


void zout_randombytes_buf(void *buf, int32_t size);
//@ requires [_]sodium_is_initialized() &*& chars(buf, size, _) &*& size >= 0;
//@ ensures chars(buf, size, _);


/** See crypto_hash_sha256 on https://download.libsodium.org/doc/advanced/sha-2_hash_function.html */
int zout_hash_sha256(char *out, const char *in,
                       int32_t inlen);
//@ requires [_]sodium_is_initialized() &*& chars(out, zout_hash_sha256_BYTES, _) &*& [?f]chars(in, inlen, ?incs) &*& inlen >= 0;
//@ ensures chars(out, zout_hash_sha256_BYTES, _) &*& [f]chars(in, inlen, incs);

/** See crypto_box_keypair on https://download.libsodium.org/doc/public-key_cryptography/authenticated_encryption.html */
int zout_box_keypair(char *pk, char *sk);
//@ requires [_]sodium_is_initialized() &*& chars(pk, zout_box_PUBLICKEYBYTES, _) &*& chars(sk, zout_box_SECRETKEYBYTES, _);
//@ ensures chars(pk, zout_box_PUBLICKEYBYTES, _) &*& chars(sk, zout_box_SECRETKEYBYTES, _);

/**
 * See crypto_scalarmult on https://download.libsodium.org/doc/advanced/scalar_multiplication.html
 *
 * Sodium does not document the return value (its current implementation always returns 0).
 */
int
zout_scalarmult(char *q, const char *n,
                  const char *p);
/*@ requires
  [_]sodium_is_initialized()
  &*& chars(q, zout_scalarmult_BYTES, _)
  &*& [?fn]chars(n, zout_box_SECRETKEYBYTES, ?ncs)
  &*& [?fp]chars(p, zout_box_PUBLICKEYBYTES, ?pcs);
@*/
/*@ ensures
  chars(q, zout_scalarmult_BYTES, _)
  &*& [fn]chars(n, zout_box_SECRETKEYBYTES, ncs)
  &*& [fp]chars(p, zout_box_PUBLICKEYBYTES, pcs);
@*/

/** See crypto_sign_keypair on https://download.libsodium.org/doc/public-key_cryptography/public-key_signatures.html */
int
zout_sign_keypair(char *pk, char *sk);
/*@ requires
  [_]sodium_is_initialized()
  &*& chars(pk, zout_sign_PUBLICKEYBYTES, _)
  &*& chars(sk, zout_sign_SECRETKEYBYTES, _);
@*/
/*@ ensures
  chars(pk, zout_sign_PUBLICKEYBYTES, _)
  &*& chars(sk, zout_sign_SECRETKEYBYTES, _);
@*/

/** See crypto_sign_detached on https://download.libsodium.org/doc/public-key_cryptography/public-key_signatures.html */
int zout_sign_detached(char *sig, int32_t *siglen_p,
                     const char *m, int32_t mlen,
                     const char *sk);
/*@ requires
  [_]sodium_is_initialized()
  &*& chars(sig, zout_sign_BYTES, _)
  &*& integer(siglen_p, _)
  &*& [?fm]chars(m, mlen, ?mcs)
  &*& [?fsk]chars(sk, zout_sign_SECRETKEYBYTES, ?skcs)
  &*& mlen >= 0;
@*/
/*@ ensures
  chars(sig, zout_sign_BYTES, _)
  &*& integer(siglen_p, ?len) &*& len <= zout_sign_BYTES
  &*& [fm]chars(m, mlen, mcs)
  &*& [fsk]chars(sk, zout_sign_SECRETKEYBYTES, skcs);
@*/

/** See crypto_auth_hmacsha256 on https://download.libsodium.org/doc/advanced/hmac-sha2.html */
int zout_auth_hmacsha256(char *out,
                           const char *in,
                           int32_t inlen,
                           const char *k);
/*@ requires
  [_]sodium_is_initialized()
  &*& chars(out, zout_auth_hmacsha256_BYTES, _)
  &*& [?fi]chars(in, inlen, ?incs)
  &*& [?fk]chars(k, zout_auth_hmacsha256_KEYBYTES, ?kcs)
  &*& inlen >= 0;
@*/
/*@ ensures
  chars(out, zout_auth_hmacsha256_BYTES, _)
  &*& [fi]chars(in, inlen, incs)
  &*& [fk]chars(k, zout_auth_hmacsha256_KEYBYTES, kcs);
@*/

/** See crypto_stream_aes128ctr_xor on https://download.libsodium.org/doc/advanced/aes-128-ctr.html */
int zout_stream_aes128ctr_xor(char *out, const char *in,
                                int32_t inlen, const char *n,
                                const char *k);
/*@ requires
  [_]sodium_is_initialized()
  &*& chars(out, inlen, _)
  &*& out == in // let's keep the contract simple for what we need it
  &*& [?fn]chars(n, ?nlen, ?ncs) &*& nlen >= zout_stream_aes128ctr_NONCEBYTES
  &*& [?fk]chars(k, ?klen, ?kcs) &*& klen >= zout_stream_aes128ctr_KEYBYTES;
@*/
/*@ ensures
  chars(out, inlen, _)
  &*& [fn]chars(n, nlen, ncs)
  &*& [fk]chars(k, klen, kcs);
@*/

/**
 * Updates the initialization vector "iv". Do this after reading "rounds" blocks.
 */
void zout_update_iv(char *iv, int32_t rounds);
//@ requires [?f]chars(iv, ?ivlen, ?ivcs) &*& ivlen >= zout_stream_aes128ctr_NONCEBYTES &*& rounds >= 0;
//@ ensures [f]chars(iv, ivlen, ivcs);

#endif
