# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  # Standard library
  std/[unittest, times],
  # Internals
  constantine/named/[algebras, zoo_generators],
  constantine/math/arithmetic,
  constantine/math/io/io_fields,
  constantine/math/elliptic/[ec_shortweierstrass_affine, ec_shortweierstrass_jacobian, ec_scalar_mul_vartime],
  # Test utilities
  helpers/prng_unsafe

const Iters = 64

var rng: RngState
let seed = uint32(getTime().toUnix() and (1'i64 shl 32 - 1)) # unixTime mod 2^32
rng.seed(seed)
echo "t_ec_scalar_mul_double_base_vartime xoshiro512** seed: ", seed

proc reference[F, G](u1, u2: Fr, Q: EC_ShortW_Aff[F, G]): EC_ShortW_Jac[F, G] =
  var gen, t: EC_ShortW_Jac[F, G]
  gen.fromAffine(F.Name.getGenerator($G))
  t.fromAffine(Q)
  gen.scalarMul_doubleAdd_vartime(u1.toBig())
  t.scalarMul_doubleAdd_vartime(u2.toBig())
  result.sum_vartime(gen, t)

proc check[F, G](u1, u2: Fr, Q: EC_ShortW_Aff[F, G]) =
  var r: EC_ShortW_Jac[F, G]
  r.scalarMulDoubleBase_vartime(u1, u2, Q)
  doAssert bool(r == reference(u1, u2, Q))

proc randomPoint(F: typedesc, G: static Subgroup): EC_ShortW_Aff[F, G] =
  var k = rng.random_unsafe(Fr[F.Name])
  var P: EC_ShortW_Jac[F, G]
  P.fromAffine(F.Name.getGenerator($G))
  P.scalarMul_vartime(k.toBig())
  result.affine(P)

proc runTests(Name: static Algebra) =
  type F = Fp[Name]
  let gen = Name.getGenerator("G1")

  suite "Double-base scalar multiplication [u₁]G + [u₂]Q - " & $Name:
    test "random scalars and points":
      for _ in 0 ..< Iters:
        check(rng.random_unsafe(Fr[Name]), rng.random_unsafe(Fr[Name]), randomPoint(F, G1))

    test "sparse and dense scalars":
      for _ in 0 ..< Iters:
        check(rng.random_long01Seq(Fr[Name]), rng.random_highHammingWeight(Fr[Name]), randomPoint(F, G1))
        check(rng.random_highHammingWeight(Fr[Name]), rng.random_long01Seq(Fr[Name]), randomPoint(F, G1))

    test "zero, one and order - 1 scalars":
      var zero, one, minusOne: Fr[Name]
      zero.setZero()
      one.setOne()
      minusOne.setMinusOne()
      for u1 in [zero, one, minusOne]:
        for u2 in [zero, one, minusOne]:
          check(u1, u2, randomPoint(F, G1))

    test "Q = ±G, sums cancelling or doubling intermediate points":
      var negGen = gen
      negGen.neg()
      for _ in 0 ..< Iters:
        let u = rng.random_unsafe(Fr[Name])
        check(u, u, gen)
        check(u, u, negGen) # [u]G - [u]G = O
        check(u, rng.random_unsafe(Fr[Name]), gen)

runTests(Secp256k1) # GLV + fixed generator tables
runTests(BN254_Snarks) # generic fallback
