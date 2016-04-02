#include "zout.h"
#include <sodium.h>
int zout_hash_sha256(char *out, const char *in,
                       int32_t inlen)
{
  return crypto_hash_sha256((unsigned char*)out, (const unsigned char*)in, (unsigned long long)inlen);
}

int zout_box_keypair(char *pk, char *sk)
{
  return crypto_box_keypair((unsigned char*)pk, (unsigned char*)sk);
}

int zout_scalarmult(char *q, const char *n,
                  const char *p)
{
  return crypto_scalarmult((unsigned char*)q, (const unsigned char*)n, (const unsigned char*)p);
}

int zout_sign_keypair(char *pk, char *sk)
{
  return crypto_sign_keypair((unsigned char*)pk, (unsigned char*)sk);
}

int zout_sign_detached(char *sig, int32_t *siglen_p,
                     const char *m, int32_t mlen,
                     const char *sk)
{
  unsigned long long siglen;
  int ret = crypto_sign_detached(
      (unsigned char*) sig, &siglen,
      (const unsigned char*) m,(unsigned long long) mlen,
      (const unsigned char*) sk);
  // Per the sodium docs, siglen is at most crypto_sign_BYTES, which is 64.
  *siglen_p = (int32_t) siglen;
  return ret;
}

int zout_auth_hmacsha256(char *out,
                           const char *in,
                           int32_t inlen,
                           const char *k)
{
  return crypto_auth_hmacsha256(
      (unsigned char*)out,
      (const unsigned char*)in,
      inlen, (const unsigned char*)k);
}


int zout_stream_aes128ctr_xor(char *out, const char *in,
                                int32_t inlen, const char *n,
                                const char *k)
{
  return crypto_stream_aes128ctr_xor(
      (unsigned char*)out,
      (const unsigned char*)in,
      inlen,
      (const unsigned char*)n,
      (const unsigned char*)k);
}

/*copied from libsodium!*/
uint32_t load32_bigendian(const unsigned char *x)
{
  return
      (uint32_t) (x[3]) \
  | (((uint32_t) (x[2])) << 8) \
  | (((uint32_t) (x[1])) << 16) \
  | (((uint32_t) (x[0])) << 24)
  ;
}

/*copied from libsodium!*/
void store32_bigendian(unsigned char *x,uint32_t u)
{
  x[3] = (unsigned char)u; u >>= 8;
  x[2] = (unsigned char)u; u >>= 8;
  x[1] = (unsigned char)u; u >>= 8;
  x[0] = (unsigned char)u;
}

/**
 * Updates the initialization vector "iv". Do this after reading "rounds" blocks.
 */
void zout_update_iv(char *iv, int32_t rounds)
{
  uint32_t tmp;
  tmp = load32_bigendian((unsigned char*)(void*)(iv + 12));
  tmp += rounds;
  store32_bigendian((unsigned char*)(void*)(iv + 12), tmp);
}

void zout_randombytes_buf(void *buf, const int32_t size)
//@ requires [_]sodium_is_initialized() &*& chars(buf, size, _) &*& size >= 0;
//@ ensures chars(buf, size, _);
{
  randombytes_buf(buf, size);
}
