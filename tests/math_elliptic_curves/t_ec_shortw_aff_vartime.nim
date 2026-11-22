# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

# Variable-time affine arithmetic (a = 0 curves) against Jacobian results.
# Runs with and without -d:CTT_EXTERN_FIELD_ACCEL:
#   nim c -r -d:release --hints:off tests/math_elliptic_curves/t_ec_shortw_aff_vartime.nim
#   nim c -r -d:release --hints:off -d:CTT_EXTERN_FIELD_ACCEL tests/math_elliptic_curves/t_ec_shortw_aff_vartime.nim
# (the accelerated build compiles the mock accelerator, which also checks
#  that operands are < 2p and counts calls)

import
  std/[unittest, times],
  constantine/platforms/abstractions,
  constantine/named/algebras,
  constantine/math/[arithmetic, extension_fields],
  constantine/math/arithmetic/finite_fields_extern,
  constantine/math/elliptic/[
    ec_shortweierstrass_affine,
    ec_shortweierstrass_affine_vartime,
    ec_shortweierstrass_jacobian,
    ec_shortweierstrass_projective,
    ec_scalar_mul,
    ec_scalar_mul_vartime],
  constantine/math/io/[io_fields, io_extfields, io_ec],
  constantine/named/zoo_subgroups,
  helpers/prng_unsafe

const CTT_EXTERN_FIELD_ACCEL {.booldefine.} = false
when CTT_EXTERN_FIELD_ACCEL and WordBitWidth == 64:
  {.compile: "../testutils/mock_lineth_zkvm_field_op.c".}
  proc mock_zkvm_field_op_reset() {.importc, cdecl.}
  proc mock_zkvm_field_op_total(): uint64 {.importc, cdecl.}

const Iters = 64

var rng: RngState
let seed = uint32(getTime().toUnix() and (1'i64 shl 32 - 1)) # unixTime mod 2^32
rng.seed(seed)
echo "\n------------------------------------------------------\n"
echo "t_ec_shortw_aff_vartime xoshiro512** seed: ", seed

func toAff[F, G](P: EC_ShortW_Jac[F, G]): EC_ShortW_Aff[F, G] =
  result.affine(P)

proc refSum[F, G](P, Q: EC_ShortW_Aff[F, G]): EC_ShortW_Aff[F, G] =
  var jP, jQ: EC_ShortW_Jac[F, G]
  jP.fromAffine(P)
  jQ.fromAffine(Q)
  jP.sum(jP, jQ)
  jP.toAff()

proc refDouble[F, G](P: EC_ShortW_Aff[F, G]): EC_ShortW_Aff[F, G] =
  var jP: EC_ShortW_Jac[F, G]
  jP.fromAffine(P)
  jP.double()
  jP.toAff()

proc negated[F, G](P: EC_ShortW_Aff[F, G]): EC_ShortW_Aff[F, G] =
  result.neg(P)

proc testAffineVartime(EC: typedesc) =
  type F = EC.F
  echo "    ", $EC, "  useAffineVartime: ", F.useAffineVartime()

  var O: EC
  O.setNeutral()

  for i in 0 ..< Iters:
    let P = rng.random_unsafe(EC)
    let Q = if i mod 2 == 0: rng.random_unsafe(EC)
            else: rng.random_highHammingWeight(EC)

    # P + Q, P - Q, 2P, also aliasing the output with each input
    let PQ = refSum(P, Q)
    let PmQ = refSum(P, Q.negated())
    let P2 = refDouble(P)
    var r {.noInit.}: EC
    r.affineSum_vartime(P, Q);    doAssert bool(r == PQ)
    r.affineSum_vartime(Q, P);    doAssert bool(r == PQ)
    r.affineDiff_vartime(P, Q);   doAssert bool(r == PmQ)
    r.affineDouble_vartime(P);    doAssert bool(r == P2)
    r = P; r.affineSum_vartime(r, Q);  doAssert bool(r == PQ)
    r = Q; r.affineSum_vartime(P, r);  doAssert bool(r == PQ)
    r = P; r.affineDiff_vartime(r, Q); doAssert bool(r == PmQ)
    r = Q; r.affineDiff_vartime(P, r); doAssert bool(r == PmQ)
    r = P; r.affineDouble_vartime(r);  doAssert bool(r == P2)

    # Exceptional cases: P + P, P + (-P), P - P, P - (-P)
    r.affineSum_vartime(P, P);            doAssert bool(r == P2)
    r.affineSum_vartime(P, P.negated());  doAssert bool(r.isNeutral())
    r.affineDiff_vartime(P, P);           doAssert bool(r.isNeutral())
    r.affineDiff_vartime(P, P.negated()); doAssert bool(r == P2)
    r = P; r.affineSum_vartime(r, r);     doAssert bool(r == P2)

    # Neutral operands
    r.affineSum_vartime(O, Q);  doAssert bool(r == Q)
    r.affineSum_vartime(P, O);  doAssert bool(r == P)
    r.affineDiff_vartime(O, Q); doAssert bool(r == Q.negated())
    r.affineDiff_vartime(P, O); doAssert bool(r == P)
    r.affineSum_vartime(O, O);  doAssert bool(r.isNeutral())
    r.affineDiff_vartime(O, O); doAssert bool(r.isNeutral())
    r.affineDouble_vartime(O);  doAssert bool(r.isNeutral())

    # Chains vs Jacobian: acc <- 2·acc ± Pₖ
    var acc = P
    var jacc: EC_ShortW_Jac[F, EC.G]
    jacc.fromAffine(P)
    for k in 0 ..< 8:
      let T = rng.random_unsafe(EC)
      var jT: EC_ShortW_Jac[F, EC.G]
      jT.fromAffine(T)
      acc.affineDouble_vartime(acc)
      jacc.double()
      if k mod 3 == 1:
        acc.affineDiff_vartime(acc, T)
        jT.neg()
      else:
        acc.affineSum_vartime(acc, T)
      jacc.sum(jacc, jT)
      doAssert bool(acc == jacc.toAff())

    # Field division
    var a, b, c: F
    a = P.x
    b = Q.y
    c.div_vartime(a, b)
    c *= b
    doAssert bool(c == a)
    c = a
    c.div_vartime(c, b); c *= b; doAssert bool(c == a)
    c = b
    c.div_vartime(a, c); c *= b; doAssert bool(c == a)
    b.setZero()
    c.div_vartime(a, b)
    doAssert bool(c.isZero())

  when CTT_EXTERN_FIELD_ACCEL and WordBitWidth == 64:
    when F is Fp:
      static: doAssert F.useAffineVartime()
      # Exact accelerator call counts on the generic paths
      let P = rng.random_unsafe(EC)
      let Q = rng.random_unsafe(EC)
      var r {.noInit.}: EC
      mock_zkvm_field_op_reset()
      r.affineSum_vartime(P, Q)
      doAssert mock_zkvm_field_op_total() == 3, $mock_zkvm_field_op_total()
      mock_zkvm_field_op_reset()
      r.affineDouble_vartime(P)
      doAssert mock_zkvm_field_op_total() == 5, $mock_zkvm_field_op_total()
      mock_zkvm_field_op_reset()
      var d {.noInit.}: F
      d.div_vartime(P.x, Q.x)
      doAssert mock_zkvm_field_op_total() == 1
    else:
      static: doAssert F.useAffineVartime()
      let a = rng.random_unsafe(F)
      let b = rng.random_unsafe(F)
      var d {.noInit.}: F
      mock_zkvm_field_op_reset()
      d.div_vartime(a, b)
      doAssert mock_zkvm_field_op_total() == 8, $mock_zkvm_field_op_total()

proc testScalarMulVartime(EC: typedesc) =
  ## scalarMul_vartime (affine accumulator when useAffineVartime)
  ## against the constant-time generic scalar multiplication,
  ## for the endomorphism, wNAF window 4 and window 3 paths.
  type F = EC.F
  const Name = F.Name
  echo "    ", $EC
  for i in 0 ..< Iters div 4:
    var P {.noInit.}: EC
    P.fromAffine(rng.random_unsafe(EC_ShortW_Aff[F, EC.G]))
    P.clearCofactor()
    let k = rng.random_unsafe(Fr[Name]).toBig()
    for bitsKept in [k.bits, 200, 100, 64, 40, 12, 8, 1, 0]:
      var s = k
      # Keep only the low `bitsKept` bits
      for w in 0 ..< s.limbs.len:
        let lo = w * WordBitWidth
        if lo >= bitsKept:
          s.limbs[w] = Zero
        elif bitsKept - lo < WordBitWidth:
          s.limbs[w] = s.limbs[w] and ((One shl (bitsKept - lo)) - One)
      var r = P
      var e = P
      r.scalarMul_vartime(s)
      e.scalarMulGeneric(s)
      doAssert bool(r == e), "scalarMul_vartime mismatch for " & $EC & " with " & $bitsKept & " bits"
    # Neutral input
    var O {.noInit.}: EC
    O.setNeutral()
    O.scalarMul_vartime(k)
    doAssert bool(O.isNeutral())

suite "Variable-time affine arithmetic for a = 0 curves" & " [" & $WordBitWidth & "-bit words]":
  test "Sum, difference, doubling and exceptional cases vs Jacobian":
    testAffineVartime(EC_ShortW_Aff[Fp[Secp256k1], G1])
    testAffineVartime(EC_ShortW_Aff[Fp[BN254_Snarks], G1])
    testAffineVartime(EC_ShortW_Aff[Fp2[BN254_Snarks], G2])
    testAffineVartime(EC_ShortW_Aff[Fp[BLS12_381], G1])
    testAffineVartime(EC_ShortW_Aff[Fp2[BLS12_381], G2])

  test "scalarMul_vartime (affine accumulator when accelerated) vs constant-time":
    testScalarMulVartime(EC_ShortW_Jac[Fp[Secp256k1], G1])
    testScalarMulVartime(EC_ShortW_Jac[Fp[BN254_Snarks], G1])
    testScalarMulVartime(EC_ShortW_Prj[Fp[BN254_Snarks], G1])
    testScalarMulVartime(EC_ShortW_Jac[Fp2[BN254_Snarks], G2])
    testScalarMulVartime(EC_ShortW_Jac[Fp[BLS12_381], G1])
    testScalarMulVartime(EC_ShortW_Prj[Fp[BLS12_381], G1])
    testScalarMulVartime(EC_ShortW_Jac[Fp2[BLS12_381], G2])
    testScalarMulVartime(EC_ShortW_Prj[Fp2[BLS12_381], G2])
