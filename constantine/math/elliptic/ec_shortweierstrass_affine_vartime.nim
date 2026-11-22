# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  constantine/platforms/abstractions,
  constantine/named/algebras,
  constantine/math/arithmetic,
  constantine/math/arithmetic/finite_fields_extern,
  constantine/math/extension_fields,
  ./ec_shortweierstrass_affine

# No exceptions allowed
{.push raises: [], checks: off.}

# ############################################################
#
#      Variable-time affine arithmetic for accelerated fields
#
# ############################################################
#
# With -d:CTT_EXTERN_FIELD_ACCEL (see finite_fields_extern.nim), a field
# multiplication, squaring and division a/b are each ONE accelerator call
# (on the Lineth RV64 zkVM: ~11 executed instructions including call setup),
# while a software constant-time modular addition/subtraction costs ~43
# instructions for 4 limbs (more for 6). Hence:
# - inversion-free coordinates (Jacobian/projective) trade 1 division for
#   ~5 to 10 extra multiplications AND extra additions/subtractions,
# - affine coordinates are cheaper on both counts: a division is as cheap
#   as a multiplication and they need the fewest additions.
#
#   affine add (a = 0):    λ = (y₂-y₁)/(x₂-x₁)   1 DIV          2 sub
#                          x₃ = λ² - x₁ - x₂      1 S            2 sub
#                          y₃ = λ(x₁-x₃) - y₁     1 M            2 sub
#                          3 calls + 6 add/sub
#   affine double (a = 0): λ = (x²/y)·3/2         1 S, 1 DIV, 1 M (constant 3/2)
#                          x₃ = λ² - 2x           1 S            2 sub
#                          y₃ = λ(x-x₃) - y       1 M            2 sub
#                          5 calls + 4 sub
#   vs Jacobian double 3M+4S + ~6 add/sub, mixed add 7M+4S + ~7 add/sub.
#
# Over 𝔽p2 (complex extension, BN254 and BLS12-381 G2), a/b is computed as
# a·conj(b) / N(b) with N(b) = b₀² + b₁²: 2S + 4M + 2 DIV and 3 add/sub,
# instead of a tower inversion followed by a tower multiplication.
#
# These procedures are **variable-time** and MUST only be used on public data.
# They are only meant to be dispatched to when `useAffineVartime(F)` is true,
# they remain correct (but slower) otherwise.
#
# The neutral element is encoded as (0, 0), which is not on the curve
# for a = 0 curves since b ≠ 0.

func useAffineVartime*(F: type): static bool =
  ## True if variable-time affine arithmetic is preferred over
  ## Jacobian/projective coordinates for curves over F (Fp or Fp2),
  ## i.e. the base field division is a single accelerator call.
  when F is Fp:
    F.hasExtFieldInv() and F.hasExtFieldMul() and F.Name.getCoefA() == 0
  elif F is Fp2:
    Fp[F.Name].hasExtFieldInv() and Fp[F.Name].hasExtFieldMul() and F.Name.getCoefA() == 0
  else:
    false

# Field division
# ------------------------------------------------------------

func div_vartime*(r: var Fp, a, b: Fp) {.tags:[VarTime].} =
  ## r <- a/b, 0 if b = 0. r may alias a or b.
  when Fp.hasExtFieldMul():
    r.extFieldDiv(a, b)
  else:
    var t {.noInit.}: Fp
    t.inv_vartime(b)
    r.prod(a, t)

func div_vartime*(r: var QuadraticExt, a, b: QuadraticExt) {.tags:[VarTime].} =
  ## r <- a/b, 0 if b = 0. r may alias a or b.
  when r.fromComplexExtension() and typeof(r.c0).hasExtFieldMul():
    # a/b = a·conj(b) / (b₀² + b₁²) with 𝑖² = -1
    #     = (a₀b₀ + a₁b₁)/N + (a₁b₀ - a₀b₁)/N 𝑖
    var n {.noInit.}, t {.noInit.}, u {.noInit.}, v {.noInit.}: typeof(r.c0)
    n.square(b.c0)
    t.square(b.c1)
    n += t                 # N = b₀² + b₁²
    t.prod(a.c0, b.c0)
    u.prod(a.c1, b.c1)
    t += u                 # a₀b₀ + a₁b₁
    u.prod(a.c1, b.c0)
    v.prod(a.c0, b.c1)
    u -= v                 # a₁b₀ - a₀b₁
    r.c0.div_vartime(t, n)
    r.c1.div_vartime(u, n)
  else:
    var t {.noInit.}: typeof(r)
    t.inv_vartime(b)
    r.prod(a, t)

# Helpers
# ------------------------------------------------------------

func isNeutral_vartime(P: EC_ShortW_Aff): bool {.inline.} =
  ## Short-circuiting neutral check
  P.x.isZero().bool and P.y.isZero().bool

func threeHalves(F: type Fp): F =
  ## 3/2 = (p+3)/2 (mod p), for compile-time evaluation only
  var b = F.getPrimePlus1div2()
  doAssert BaseType(b.limbs[0]) != high(BaseType)
  b.limbs[0] = SecretWord(BaseType(b.limbs[0]) + 1)
  result.fromBig(b)

func mulThreeHalves[F](a: var F) {.inline.} =
  ## a <- 3a/2
  when F is Fp:
    const k = F.threeHalves()
    a *= k
  else:
    const k = typeof(a.c0).threeHalves()
    a.c0 *= k
    a.c1 *= k

# Point operations
# ------------------------------------------------------------

func affineDouble_vartime*[F; G: static Subgroup](
       r: var EC_ShortW_Aff[F, G],
       P: EC_ShortW_Aff[F, G]) {.tags:[VarTime].} =
  ## **Variable-time** affine doubling r <- [2]P for a = 0 curves.
  ## r may alias P.
  ##
  ## This MUST NOT be used with secret data.
  static: doAssert F.Name.getCoefA() == 0
  if P.y.isZero().bool:
    # Neutral (0, 0), or 2-torsion (impossible on prime-order groups)
    r.setNeutral()
    return

  var lambda {.noInit.}, x3 {.noInit.}: F
  x3.square(P.x)
  lambda.div_vartime(x3, P.y) # x²/y
  lambda.mulThreeHalves()     # λ = 3x²/2y

  x3.square(lambda)
  x3 -= P.x
  x3 -= P.x                   # x₃ = λ² - 2x

  var t {.noInit.}: F
  t.diff(P.x, x3)
  lambda *= t
  r.y.diff(lambda, P.y)       # y₃ = λ(x - x₃) - y
  r.x = x3

func affineSumImpl_vartime[F; G: static Subgroup](
       r: var EC_ShortW_Aff[F, G],
       P, Q: EC_ShortW_Aff[F, G],
       negateQ: static bool) {.inline.} =
  ## r <- P ± Q, P and Q not neutral. r may alias P or Q.
  var num {.noInit.}, den {.noInit.}: F
  when negateQ:
    # λ = (-y₂-y₁)/(x₂-x₁) = (y₁+y₂)/(x₁-x₂)
    num.sum(P.y, Q.y)
    den.diff(P.x, Q.x)
  else:
    num.diff(Q.y, P.y)
    den.diff(Q.x, P.x)

  if den.isZero().bool:     # Same x coordinate: P = ±Q
    if num.isZero().bool:   # P = Q (P = -Q for P - Q)
      r.affineDouble_vartime(P)
    else:                   # P = -Q (P = Q for P - Q)
      r.setNeutral()
    return

  var lambda {.noInit.}: F
  lambda.div_vartime(num, den)

  num.square(lambda)
  num -= P.x
  num -= Q.x                # x₃ = λ² - x₁ - x₂

  den.diff(P.x, num)
  den *= lambda
  r.y.diff(den, P.y)        # y₃ = λ(x₁ - x₃) - y₁
  r.x = num

func affineSum_vartime*[F; G: static Subgroup](
       r: var EC_ShortW_Aff[F, G],
       P, Q: EC_ShortW_Aff[F, G]) {.tags:[VarTime].} =
  ## **Variable-time** affine addition r <- P + Q for a = 0 curves.
  ## Handles neutral inputs, P = Q and P = -Q. r may alias P or Q.
  ##
  ## This MUST NOT be used with secret data.
  static: doAssert F.Name.getCoefA() == 0
  if P.isNeutral_vartime():
    r = Q
  elif Q.isNeutral_vartime():
    r = P
  else:
    r.affineSumImpl_vartime(P, Q, negateQ = false)

func affineDiff_vartime*[F; G: static Subgroup](
       r: var EC_ShortW_Aff[F, G],
       P, Q: EC_ShortW_Aff[F, G]) {.tags:[VarTime].} =
  ## **Variable-time** affine subtraction r <- P - Q for a = 0 curves.
  ## Handles neutral inputs, P = Q and P = -Q. r may alias P or Q.
  ##
  ## This MUST NOT be used with secret data.
  static: doAssert F.Name.getCoefA() == 0
  if P.isNeutral_vartime():
    r.neg(Q)
  elif Q.isNeutral_vartime():
    r = P
  else:
    r.affineSumImpl_vartime(P, Q, negateQ = true)

{.pop.}
