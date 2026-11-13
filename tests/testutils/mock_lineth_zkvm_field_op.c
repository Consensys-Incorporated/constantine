#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  uint64_t p[4];
  int supported;
  int p_is_3_mod_4;
} mock_field_desc_t;

static const mock_field_desc_t MOCK_FIELDS[8] = {
  /* 0: unused */
  {{0, 0, 0, 0}, 0, 0},
  /* 1: Secp256k1 Fp */
  {{0xfffffffefffffc2fULL, 0xffffffffffffffffULL, 0xffffffffffffffffULL, 0xffffffffffffffffULL}, 1, 1},
  /* 2: Secp256k1 Fr */
  {{0xbfd25e8cd0364141ULL, 0xbaaedce6af48a03bULL, 0xfffffffffffffffeULL, 0xffffffffffffffffULL}, 1, 0},
  /* 3: reserved (secp256r1 Fp, not wired in Constantine) */
  {{0, 0, 0, 0}, 0, 0},
  /* 4: reserved (secp256r1 Fr, not wired in Constantine) */
  {{0, 0, 0, 0}, 0, 0},
  /* 5: BN254_Snarks Fp */
  {{0x3c208c16d87cfd47ULL, 0x97816a916871ca8dULL, 0xb85045b68181585dULL, 0x30644e72e131a029ULL}, 1, 1},
  /* 6: BN254_Snarks Fr */
  {{0x43e1f593f0000001ULL, 0x2833e84879b97091ULL, 0xb85045b68181585dULL, 0x30644e72e131a029ULL}, 1, 0},
  /* 7: BLS12_381 Fr */
  {{0xffffffff00000001ULL, 0x53bda402fffe5bfeULL, 0x3339d80809a1d805ULL, 0x73eda753299d7d48ULL}, 1, 0},
};

static uint64_t g_counts[3][8];
static uint64_t g_total_calls = 0;

void mock_zkvm_field_op_reset(void) {
  memset(g_counts, 0, sizeof(g_counts));
  g_total_calls = 0;
}

uint64_t mock_zkvm_field_op_count(uint32_t op, uint32_t field) {
  if (op < 3 && field < 8) {
    return g_counts[op][field];
  }
  return 0;
}

uint64_t mock_zkvm_field_op_total(void) {
  return g_total_calls;
}

static int u256_cmp(const uint64_t a[4], const uint64_t b[4]) {
  for (int i = 3; i >= 0; --i) {
    if (a[i] < b[i]) return -1;
    if (a[i] > b[i]) return 1;
  }
  return 0;
}

static int u256_is_zero(const uint64_t a[4]) {
  return (a[0] | a[1] | a[2] | a[3]) == 0;
}

static uint64_t u256_sub(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]) {
  uint64_t borrow = 0;
  for (int i = 0; i < 4; ++i) {
    unsigned __int128 ai = a[i];
    unsigned __int128 sub = (unsigned __int128)b[i] + borrow;
    out[i] = (uint64_t)(ai - sub);
    borrow = (ai < sub) ? 1ULL : 0ULL;
  }
  return borrow;
}

static void u256_load_lt_2p(uint64_t out[4], const uint64_t raw[4], const uint64_t p[4], uint32_t field) {
  uint64_t diff[4];
  uint64_t borrow = u256_sub(diff, raw, p);
  if (borrow) {
    memcpy(out, raw, 32);
  } else {
    if (u256_cmp(diff, p) >= 0) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: operand >= 2p for field %u\n", field);
      abort();
    }
    memcpy(out, diff, 32);
  }
}

static void u256_mulmod(uint64_t out[4], const uint64_t a[4], const uint64_t b[4], const uint64_t p[4]) {
  uint64_t prod[8] = {0};
  for (int i = 0; i < 4; ++i) {
    unsigned __int128 carry = 0;
    for (int j = 0; j < 4; ++j) {
      unsigned __int128 cur = (unsigned __int128)a[i] * b[j] + prod[i + j] + carry;
      prod[i + j] = (uint64_t)cur;
      carry = cur >> 64;
    }
    prod[i + 4] = (uint64_t)carry;
  }

  uint64_t rem[5] = {0, 0, 0, 0, 0};
  for (int bit = 511; bit >= 0; --bit) {
    uint64_t in_bit = (prod[bit >> 6] >> (bit & 63)) & 1ULL;
    rem[4] = (rem[4] << 1) | (rem[3] >> 63);
    rem[3] = (rem[3] << 1) | (rem[2] >> 63);
    rem[2] = (rem[2] << 1) | (rem[1] >> 63);
    rem[1] = (rem[1] << 1) | (rem[0] >> 63);
    rem[0] = (rem[0] << 1) | in_bit;
    if (rem[4] != 0 || u256_cmp(rem, p) >= 0) {
      uint64_t borrow = u256_sub(rem, rem, p);
      rem[4] -= borrow;
    }
  }
  memcpy(out, rem, 32);
}

static void u256_powmod(uint64_t out[4], const uint64_t base[4], const uint64_t exp[4], const uint64_t p[4]) {
  uint64_t acc[4] = {1, 0, 0, 0};
  uint64_t b[4];
  memcpy(b, base, 32);
  for (int bit = 0; bit < 256; ++bit) {
    if ((exp[bit >> 6] >> (bit & 63)) & 1ULL) {
      u256_mulmod(acc, acc, b, p);
    }
    if (bit < 255) {
      u256_mulmod(b, b, b, p);
    }
  }
  memcpy(out, acc, 32);
}

uint32_t lineth_zkvm_field_op(
    uint32_t op,
    uint32_t field,
    uint64_t out[4],
    const uint64_t a[4],
    const uint64_t b[4]) {
  if (op > 2 || field >= 8 || !MOCK_FIELDS[field].supported) {
    fprintf(stderr, "mock_lineth_zkvm_field_op: unsupported op=%u field=%u\n", op, field);
    abort();
  }

  g_counts[op][field] += 1;
  g_total_calls += 1;

  const uint64_t *p = MOCK_FIELDS[field].p;
  uint64_t a_red[4], b_red[4];
  /* Copy and validate < 2p before writing out (aliasing-safe, b always read) */
  u256_load_lt_2p(a_red, a, p, field);
  u256_load_lt_2p(b_red, b, p, field);

  if (op == 0) {
    /* MUL */
    u256_mulmod(out, a_red, b_red, p);
    return 0;
  } else if (op == 1) {
    /* DIV */
    if (u256_is_zero(b_red)) {
      memset(out, 0, 32);
      return 1;
    }
    uint64_t two[4] = {2, 0, 0, 0};
    uint64_t p_minus_2[4];
    u256_sub(p_minus_2, p, two);
    uint64_t inv_b[4], res[4], chk[4];
    u256_powmod(inv_b, b_red, p_minus_2, p);
    u256_mulmod(res, a_red, inv_b, p);
    u256_mulmod(chk, res, b_red, p);
    if (u256_cmp(chk, a_red) != 0) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: DIV verification failed\n");
      abort();
    }
    memcpy(out, res, 32);
    return 0;
  } else {
    /* SQRT (p == 3 mod 4 only) */
    if (!MOCK_FIELDS[field].p_is_3_mod_4) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: SQRT unsupported on field %u\n", field);
      abort();
    }
    if (u256_is_zero(a_red)) {
      memset(out, 0, 32);
      return 0;
    }
    /* exp = (p + 1) / 4 */
    uint64_t p1[4];
    unsigned __int128 c = (unsigned __int128)p[0] + 1ULL;
    p1[0] = (uint64_t)c; c >>= 64;
    c += p[1]; p1[1] = (uint64_t)c; c >>= 64;
    c += p[2]; p1[2] = (uint64_t)c; c >>= 64;
    c += p[3]; p1[3] = (uint64_t)c; c >>= 64;
    uint64_t exp[4];
    exp[0] = (p1[0] >> 2) | (p1[1] << 62);
    exp[1] = (p1[1] >> 2) | (p1[2] << 62);
    exp[2] = (p1[2] >> 2) | (p1[3] << 62);
    exp[3] = (p1[3] >> 2) | (((uint64_t)c) << 62);

    uint64_t cand[4], sq[4];
    u256_powmod(cand, a_red, exp, p);
    u256_mulmod(sq, cand, cand, p);
    if (u256_cmp(sq, a_red) == 0) {
      memcpy(out, cand, 32);
      return 0;
    }

    uint64_t neg_a[4];
    u256_sub(neg_a, p, a_red);
    u256_powmod(cand, neg_a, exp, p);
    u256_mulmod(sq, cand, cand, p);
    if (u256_cmp(sq, neg_a) != 0) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: SQRT(-a) verification failed\n");
      abort();
    }
    memcpy(out, cand, 32);
    return 1;
  }
}
