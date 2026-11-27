#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  uint64_t p[6];
  int nlimbs;
  int supported;
  int p_is_3_mod_4;
} mock_field_desc_t;

static const mock_field_desc_t MOCK_FIELDS[9] = {
  /* 0: unused */
  {{0, 0, 0, 0, 0, 0}, 0, 0, 0},
  /* 1: Secp256k1 Fp */
  {{0xfffffffefffffc2fULL, 0xffffffffffffffffULL, 0xffffffffffffffffULL, 0xffffffffffffffffULL, 0, 0}, 4, 1, 1},
  /* 2: Secp256k1 Fr */
  {{0xbfd25e8cd0364141ULL, 0xbaaedce6af48a03bULL, 0xfffffffffffffffeULL, 0xffffffffffffffffULL, 0, 0}, 4, 1, 0},
  /* 3: reserved (secp256r1 Fp, not wired in Constantine) */
  {{0, 0, 0, 0, 0, 0}, 4, 0, 0},
  /* 4: reserved (secp256r1 Fr, not wired in Constantine) */
  {{0, 0, 0, 0, 0, 0}, 4, 0, 0},
  /* 5: BN254_Snarks Fp */
  {{0x3c208c16d87cfd47ULL, 0x97816a916871ca8dULL, 0xb85045b68181585dULL, 0x30644e72e131a029ULL, 0, 0}, 4, 1, 1},
  /* 6: BN254_Snarks Fr */
  {{0x43e1f593f0000001ULL, 0x2833e84879b97091ULL, 0xb85045b68181585dULL, 0x30644e72e131a029ULL, 0, 0}, 4, 1, 0},
  /* 7: BLS12_381 Fr */
  {{0xffffffff00000001ULL, 0x53bda402fffe5bfeULL, 0x3339d80809a1d805ULL, 0x73eda753299d7d48ULL, 0, 0}, 4, 1, 0},
  /* 8: BLS12_381 Fp */
  {{0xb9feffffffffaaabULL, 0x1eabfffeb153ffffULL, 0x6730d2a0f6b0f624ULL,
    0x64774b84f38512bfULL, 0x4b1ba7b6434bacd7ULL, 0x1a0111ea397fe69aULL}, 6, 1, 1},
};

static uint64_t g_counts[3][9];
static uint64_t g_total_calls = 0;

void mock_zkvm_field_op_reset(void) {
  memset(g_counts, 0, sizeof(g_counts));
  g_total_calls = 0;
}

uint64_t mock_zkvm_field_op_count(uint32_t op, uint32_t field) {
  if (op < 3 && field < 9) {
    return g_counts[op][field];
  }
  return 0;
}

uint64_t mock_zkvm_field_op_total(void) {
  return g_total_calls;
}

static int u_cmp(const uint64_t *a, const uint64_t *b, int n) {
  for (int i = n - 1; i >= 0; --i) {
    if (a[i] < b[i]) return -1;
    if (a[i] > b[i]) return 1;
  }
  return 0;
}

static int u_is_zero(const uint64_t *a, int n) {
  uint64_t acc = 0;
  for (int i = 0; i < n; ++i) acc |= a[i];
  return acc == 0;
}

static uint64_t u_sub(uint64_t *out, const uint64_t *a, const uint64_t *b, int n) {
  uint64_t borrow = 0;
  for (int i = 0; i < n; ++i) {
    unsigned __int128 ai = a[i];
    unsigned __int128 sub = (unsigned __int128)b[i] + borrow;
    out[i] = (uint64_t)(ai - sub);
    borrow = (ai < sub) ? 1ULL : 0ULL;
  }
  return borrow;
}

static void u_load_lt_2p(uint64_t *out, const uint64_t *raw, const uint64_t *p, int n, uint32_t field) {
  uint64_t diff[6] = {0};
  uint64_t borrow = u_sub(diff, raw, p, n);
  if (borrow) {
    memcpy(out, raw, (size_t)n * sizeof(uint64_t));
  } else {
    if (u_cmp(diff, p, n) >= 0) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: operand >= 2p for field %u\n", field);
      abort();
    }
    memcpy(out, diff, (size_t)n * sizeof(uint64_t));
  }
}

static void u_mulmod(uint64_t *out, const uint64_t *a, const uint64_t *b, const uint64_t *p, int n) {
  uint64_t prod[12] = {0};
  for (int i = 0; i < n; ++i) {
    unsigned __int128 carry = 0;
    for (int j = 0; j < n; ++j) {
      unsigned __int128 cur = (unsigned __int128)a[i] * b[j] + prod[i + j] + carry;
      prod[i + j] = (uint64_t)cur;
      carry = cur >> 64;
    }
    prod[i + n] = (uint64_t)carry;
  }

  uint64_t rem[7] = {0};
  for (int bit = 64 * 2 * n - 1; bit >= 0; --bit) {
    uint64_t in_bit = (prod[bit >> 6] >> (bit & 63)) & 1ULL;
    for (int k = n; k >= 1; --k) {
      rem[k] = (rem[k] << 1) | (rem[k - 1] >> 63);
    }
    rem[0] = (rem[0] << 1) | in_bit;
    if (rem[n] != 0 || u_cmp(rem, p, n) >= 0) {
      uint64_t borrow = u_sub(rem, rem, p, n);
      rem[n] -= borrow;
    }
  }
  memcpy(out, rem, (size_t)n * sizeof(uint64_t));
}

static void u_powmod(uint64_t *out, const uint64_t *base, const uint64_t *exp, const uint64_t *p, int n) {
  uint64_t acc[6] = {1, 0, 0, 0, 0, 0};
  uint64_t b[6] = {0};
  memcpy(b, base, (size_t)n * sizeof(uint64_t));
  int total_bits = 64 * n;
  for (int bit = 0; bit < total_bits; ++bit) {
    if ((exp[bit >> 6] >> (bit & 63)) & 1ULL) {
      u_mulmod(acc, acc, b, p, n);
    }
    if (bit + 1 < total_bits) {
      u_mulmod(b, b, b, p, n);
    }
  }
  memcpy(out, acc, (size_t)n * sizeof(uint64_t));
}

static uint64_t u_add(uint64_t *out, const uint64_t *a, const uint64_t *b, int n) {
  unsigned __int128 carry = 0;
  for (int i = 0; i < n; ++i) {
    carry += (unsigned __int128)a[i] + b[i];
    out[i] = (uint64_t)carry;
    carry >>= 64;
  }
  return (uint64_t)carry;
}

/* a >>= 1, shifting `top` (0 or 1) into the most significant bit */
static void u_shr1(uint64_t *a, uint64_t top, int n) {
  for (int i = 0; i < n - 1; ++i) {
    a[i] = (a[i] >> 1) | (a[i + 1] << 63);
  }
  a[n - 1] = (a[n - 1] >> 1) | (top << 63);
}

/* x <- x/2 mod p, x < p, p odd */
static void u_half_mod(uint64_t *x, const uint64_t *p, int n) {
  uint64_t top = 0;
  if (x[0] & 1ULL) {
    top = u_add(x, x, p, n);
  }
  u_shr1(x, top, n);
}

/* x <- x - y mod p, x, y < p */
static void u_submod(uint64_t *x, const uint64_t *y, const uint64_t *p, int n) {
  if (u_sub(x, x, y, n)) {
    u_add(x, x, p, n);
  }
}

static int u_is_one(const uint64_t *a, int n) {
  uint64_t acc = a[0] ^ 1ULL;
  for (int i = 1; i < n; ++i) acc |= a[i];
  return acc == 0;
}

/* out <- a/b mod p, with a, b < p, b != 0, p an odd prime.
 * Variable-time binary extended Euclid (Hankerson-Menezes-Vanstone,
 * Guide to ECC, Alg. 2.22) seeded with a instead of 1, so it computes
 * the quotient directly. Linear in the bit length, unlike a Fermat
 * exponentiation. */
static void u_divmod(uint64_t *out, const uint64_t *a, const uint64_t *b, const uint64_t *p, int n) {
  uint64_t u[6] = {0}, v[6] = {0}, x1[6] = {0}, x2[6] = {0};
  memcpy(u, b, (size_t)n * sizeof(uint64_t));
  memcpy(v, p, (size_t)n * sizeof(uint64_t));
  memcpy(x1, a, (size_t)n * sizeof(uint64_t));
  while (!u_is_one(u, n) && !u_is_one(v, n)) {
    while ((u[0] & 1ULL) == 0) {
      u_shr1(u, 0, n);
      u_half_mod(x1, p, n);
    }
    while ((v[0] & 1ULL) == 0) {
      u_shr1(v, 0, n);
      u_half_mod(x2, p, n);
    }
    if (u_cmp(u, v, n) >= 0) {
      u_sub(u, u, v, n);
      u_submod(x1, x2, p, n);
    } else {
      u_sub(v, v, u, n);
      u_submod(x2, x1, p, n);
    }
  }
  memcpy(out, u_is_one(u, n) ? x1 : x2, (size_t)n * sizeof(uint64_t));
}

static uint32_t mock_field_op_impl(
    uint32_t op,
    uint32_t field,
    int expected_limbs,
    uint64_t *out,
    const uint64_t *a,
    const uint64_t *b) {
  if (op > 2 || field >= 9 || !MOCK_FIELDS[field].supported || MOCK_FIELDS[field].nlimbs != expected_limbs) {
    fprintf(stderr, "mock_lineth_zkvm_field_op: unsupported op=%u field=%u (expected %d limbs)\n",
            op, field, expected_limbs);
    abort();
  }

  g_counts[op][field] += 1;
  g_total_calls += 1;

  const int n = expected_limbs;
  const size_t nbytes = (size_t)n * sizeof(uint64_t);
  const uint64_t *p = MOCK_FIELDS[field].p;
  uint64_t a_red[6] = {0}, b_red[6] = {0};
  /* Copy and validate < 2p before writing out (aliasing-safe, b always read) */
  u_load_lt_2p(a_red, a, p, n, field);
  u_load_lt_2p(b_red, b, p, n, field);

  if (op == 0) {
    u_mulmod(out, a_red, b_red, p, n);
    return 0;
  } else if (op == 1) {
    if (u_is_zero(b_red, n)) {
      memset(out, 0, nbytes);
      return 1;
    }
    uint64_t res[6] = {0}, chk[6] = {0};
    u_divmod(res, a_red, b_red, p, n);
    u_mulmod(chk, res, b_red, p, n);
    if (u_cmp(chk, a_red, n) != 0) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: DIV verification failed\n");
      abort();
    }
    memcpy(out, res, nbytes);
    return 0;
  } else {
    if (!MOCK_FIELDS[field].p_is_3_mod_4) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: SQRT unsupported on field %u\n", field);
      abort();
    }
    if (u_is_zero(a_red, n)) {
      memset(out, 0, nbytes);
      return 0;
    }
    /* exp = (p + 1) / 4 */
    uint64_t p1[6] = {0};
    unsigned __int128 c = 1ULL;
    for (int i = 0; i < n; ++i) {
      c += p[i];
      p1[i] = (uint64_t)c;
      c >>= 64;
    }
    uint64_t exp[6] = {0};
    for (int i = 0; i < n - 1; ++i) {
      exp[i] = (p1[i] >> 2) | (p1[i + 1] << 62);
    }
    exp[n - 1] = (p1[n - 1] >> 2) | (((uint64_t)c) << 62);

    uint64_t cand[6] = {0}, sq[6] = {0};
    u_powmod(cand, a_red, exp, p, n);
    u_mulmod(sq, cand, cand, p, n);
    if (u_cmp(sq, a_red, n) == 0) {
      memcpy(out, cand, nbytes);
      return 0;
    }

    uint64_t neg_a[6] = {0};
    u_sub(neg_a, p, a_red, n);
    u_powmod(cand, neg_a, exp, p, n);
    u_mulmod(sq, cand, cand, p, n);
    if (u_cmp(sq, neg_a, n) != 0) {
      fprintf(stderr, "mock_lineth_zkvm_field_op: SQRT(-a) verification failed\n");
      abort();
    }
    memcpy(out, cand, nbytes);
    return 1;
  }
}

uint32_t lineth_zkvm_field_op_256(
    uint32_t op,
    uint32_t field,
    uint64_t out[4],
    const uint64_t a[4],
    const uint64_t b[4]) {
  return mock_field_op_impl(op, field, 4, out, a, b);
}

uint32_t lineth_zkvm_field_op_384(
    uint32_t op,
    uint32_t field,
    uint64_t out[6],
    const uint64_t a[6],
    const uint64_t b[6]) {
  return mock_field_op_impl(op, field, 6, out, a, b);
}
