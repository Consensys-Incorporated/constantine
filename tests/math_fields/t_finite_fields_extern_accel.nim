# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  std/unittest,
  constantine/platforms/abstractions,
  constantine/named/algebras,
  constantine/math/arithmetic,
  constantine/math/arithmetic/[finite_fields_extern, finite_fields_double_precision],
  constantine/math/extension_fields,
  constantine/math/elliptic/[ec_shortweierstrass_affine, ec_shortweierstrass_projective, ec_shortweierstrass_jacobian, ec_scalar_mul],
  constantine/math/pairings/[pairings_generic, cyclotomic_subgroups],
  constantine/math/io/[io_bigints, io_fields, io_extfields],
  constantine/named/zoo_generators,
  constantine/hashes,
  constantine/hash_to_curve/h2c_hash_to_field,
  constantine/ethereum_evm_precompiles

when WordBitWidth == 64:
  {.compile: "../testutils/mock_lineth_zkvm_field_op.c".}

  proc mock_zkvm_field_op_reset() {.importc, cdecl.}
  proc mock_zkvm_field_op_count(op, field: uint32): uint64 {.importc, cdecl.}
  proc mock_zkvm_field_op_total(): uint64 {.importc, cdecl.}

  const
    OpMul = 0'u32
    OpDiv = 1'u32
    OpSqrt = 2'u32

  template checkPlainFieldContract(F: typedesc, expectedId: uint32, expectSqrt: bool) =
    static:
      doAssert F.extFieldId() == expectedId
      doAssert F.hasExtFieldMul()
      doAssert F.hasExtFieldInv()
      doAssert F.isPlainRepField()
      doAssert F.hasExtFieldSqrt() == expectSqrt

    # Compile-time constant via fromHex must store plain canonical limbs
    const ctVal = F.fromHex("0x123456789abcdef0112233445566778899aabbccddeeff00123456789abcdef")
    let rtBig = F.getBigInt().fromHex("0x123456789abcdef0112233445566778899aabbccddeeff00123456789abcdef")
    check bool(ctVal.mres == rtBig)
    check bool(ctVal.toBig() == rtBig)

    # 1 and -1 representation checks
    var one, minusOne: F
    one.setOne()
    minusOne.setMinusOne()
    check bool(one.isOne())
    check bool(one.mres.isOne())
    check bool(minusOne.isMinusOne())
    check bool(minusOne.mres == F.getPrimeMinus1())
    check bool(F.getOne() == one)
    check bool(F.getMinusOne() == minusOne)

    var condVal: F
    condVal.setZero()
    condVal.csetOne(CtFalse)
    check bool(condVal.isZero())
    condVal.csetOne(CtTrue)
    check bool(condVal.isOne())

    # Exact ECALL count checks
    var a = F.fromUint(123456789'u64)
    var b = F.fromUint(987654321'u64)
    var r: F

    # prod = 1 MUL ECALL
    mock_zkvm_field_op_reset()
    r.prod(a, b)
    check mock_zkvm_field_op_count(OpMul, expectedId) == 1'u64
    check mock_zkvm_field_op_total() == 1'u64
    check bool(r == F.fromUint(123456789'u64 * 987654321'u64))

    # Aliasing prod
    var aAlias = a
    aAlias.prod(aAlias, b)
    check bool(aAlias == r)

    # square = 1 MUL ECALL
    mock_zkvm_field_op_reset()
    r.square(a)
    check mock_zkvm_field_op_count(OpMul, expectedId) == 1'u64
    check mock_zkvm_field_op_total() == 1'u64
    var aSqProd: F
    aSqProd.prod(a, a)
    check bool(r == aSqProd)

    # div2 = 0 ECALLs
    mock_zkvm_field_op_reset()
    var half = a
    half.div2()
    check mock_zkvm_field_op_total() == 0'u64
    var twoHalf: F
    twoHalf.double(half)
    check bool(twoHalf == a)

    # sumprod(4) = 4 MUL ECALLs, including aliasing r with first element
    var xs = [a, b, ctVal, minusOne]
    var ys = [b, ctVal, a, one]
    mock_zkvm_field_op_reset()
    xs[0].sumprod(xs, ys)
    check mock_zkvm_field_op_count(OpMul, expectedId) == 4'u64
    check mock_zkvm_field_op_total() == 4'u64
    var manualSum, t: F
    manualSum.prod(a, b)
    t.prod(b, ctVal); manualSum += t
    t.prod(ctVal, a); manualSum += t
    t.prod(minusOne, one); manualSum += t
    check bool(xs[0] == manualSum)

    # inv(a) = 1 DIV ECALL, inv(0) == 0 = 1 DIV ECALL
    mock_zkvm_field_op_reset()
    var invA: F
    invA.inv(a)
    check mock_zkvm_field_op_count(OpDiv, expectedId) == 1'u64
    check mock_zkvm_field_op_total() == 1'u64
    var checkOne: F
    checkOne.prod(a, invA)
    check bool(checkOne.isOne())

    var zeroVal: F
    zeroVal.setZero()
    mock_zkvm_field_op_reset()
    zeroVal.inv()
    check mock_zkvm_field_op_count(OpDiv, expectedId) == 1'u64
    check bool(zeroVal.isZero())

    # pow and pow_vartime
    var p1 = a
    var p2 = a
    let expBig = F.getBigInt().fromUint(19'u64)
    p1.pow(expBig)
    p2.pow_vartime(expBig)
    var pManual = one
    for _ in 0 ..< 19:
      pManual *= a
    check bool(p1 == pManual)
    check bool(p2 == pManual)

    # pow_vartime(1) = 0 ECALLs, pow_vartime(0) == 1 with 0 ECALLs
    var pOne = a
    mock_zkvm_field_op_reset()
    pOne.pow_vartime([byte 0, 1])
    check mock_zkvm_field_op_total() == 0'u64
    check bool(pOne == a)

    var pZero = a
    mock_zkvm_field_op_reset()
    pZero.pow_vartime([byte 0, 0])
    check mock_zkvm_field_op_total() == 0'u64
    check bool(pZero.isOne())

    # SQRT checks when supported
    when expectSqrt:
      var sq: F
      sq.square(ctVal)
      mock_zkvm_field_op_reset()
      var root = sq
      let okSq = root.sqrt_if_square()
      check bool(okSq)
      check mock_zkvm_field_op_count(OpSqrt, expectedId) == 1'u64
      check mock_zkvm_field_op_total() == 1'u64
      var rootSq: F
      rootSq.square(root)
      check bool(rootSq == sq)

      # Since p == 3 mod 4, -sq (for sq != 0) is a non-square
      var nonSq: F
      nonSq.neg(sq)
      mock_zkvm_field_op_reset()
      var badRoot = nonSq
      let okNonSq = badRoot.sqrt_if_square()
      check not bool(okNonSq)
      check mock_zkvm_field_op_count(OpSqrt, expectedId) == 1'u64

      # invsqrt = 1 SQRT + 1 DIV ECALL
      mock_zkvm_field_op_reset()
      var invRoot: F
      invRoot.invsqrt(sq)
      check mock_zkvm_field_op_count(OpSqrt, expectedId) == 1'u64
      check mock_zkvm_field_op_count(OpDiv, expectedId) == 1'u64
      check mock_zkvm_field_op_total() == 2'u64
      var invRootCheck: F
      invRootCheck.square(invRoot)
      invRootCheck *= sq
      check bool(invRootCheck.isOne())

  suite "External field accelerator (-d:CTT_EXTERN_FIELD_ACCEL)":
    test "Field IDs 1, 2, 5, 6, 7 plain representation & ECALL counts":
      checkPlainFieldContract(Fp[Secp256k1], 1'u32, true)
      checkPlainFieldContract(Fr[Secp256k1], 2'u32, false)
      checkPlainFieldContract(Fp[BN254_Snarks], 5'u32, true)
      checkPlainFieldContract(Fr[BN254_Snarks], 6'u32, false)
      checkPlainFieldContract(Fr[BLS12_381], 7'u32, false)

      # Unaccelerated fields remain Montgomery (ID 0)
      static:
        doAssert Fp[BLS12_381].extFieldId() == 0'u32
        doAssert not Fp[BLS12_381].hasExtFieldMul()
        doAssert not Fp[BLS12_381].isPlainRepField()
        doAssert Fp[P256].extFieldId() == 0'u32
        doAssert Fr[P256].extFieldId() == 0'u32

    test "4-limb canonical reduction (inputs >= p and >= 4p)":
      # Secp256k1 input in [p, 2p): 0 ECALLs
      var rawSecp: BigInt[256]
      rawSecp.limbs = [SecretWord(0xfffffffefffffc35'u64), SecretWord(0xffffffffffffffff'u64),
                       SecretWord(0xffffffffffffffff'u64), SecretWord(0xffffffffffffffff'u64)]
      mock_zkvm_field_op_reset()
      let fSecp = Fp[Secp256k1].fromBig(rawSecp)
      check mock_zkvm_field_op_total() == 0'u64
      check bool(fSecp == Fp[Secp256k1].fromUint(6'u64))

      # BN254_Snarks input > 4p (CryptoFuzz regression vector): 1 MUL ECALL
      let rawBn = BigInt[254].fromHex("0xdd1119d0c5b065898a0848e21c209153f4622f06cb763e7ef00eef28b94780f8")
      mock_zkvm_field_op_reset()
      let fBn = Fp[BN254_Snarks].fromBig(rawBn)
      check mock_zkvm_field_op_count(OpMul, 5'u32) == 1'u64
      check mock_zkvm_field_op_total() == 1'u64
      const ctBn = Fp[BN254_Snarks].fromHex("0xdd1119d0c5b065898a0848e21c209153f4622f06cb763e7ef00eef28b94780f8")
      check bool(fBn == ctBn)
      check bool(fBn.mres < Fp[BN254_Snarks].getModulus())

    test "Double-precision redc2x on Fp[Secp256k1] and Fp[BN254_Snarks]":
      for (xHex, yHex) in [
        ("0x2f112233445566778899aabbccddeeff00112233445566778899aabbccddeeff",
         "0x19fedcba9876543210fedcba9876543210fedcba9876543210fedcba98765432")
      ]:
        let a1 = Fp[Secp256k1].fromHex(xHex)
        let b1 = Fp[Secp256k1].fromHex(yHex)
        var d1: FpDbl[Secp256k1]
        var r1, exp1: Fp[Secp256k1]
        d1.prod2x(a1, b1)
        r1.redc2x(d1)
        exp1.prod(a1, b1)
        check bool(r1 == exp1)

        let a5 = Fp[BN254_Snarks].fromHex(xHex)
        let b5 = Fp[BN254_Snarks].fromHex(yHex)
        var d5: FpDbl[BN254_Snarks]
        var r5, exp5: Fp[BN254_Snarks]
        d5.prod2x(a5, b5)
        r5.redc2x(d5)
        exp5.prod(a5, b5)
        check bool(r5 == exp5)

    test "BN254_Snarks extension tower (Fp2, Fp6, Fp12) and bilinearity of pairing":
      var g1 = BN254_Snarks.getGenerator("G1")
      var g2 = BN254_Snarks.getGenerator("G2")
      var p1, p2: EC_ShortW_Jac[Fp[BN254_Snarks], G1]
      var q1, q2: EC_ShortW_Jac[Fp2[BN254_Snarks], G2]
      p1.fromAffine(g1)
      q1.fromAffine(g2)
      p2 = p1
      q2 = q1

      let s1 = Fr[BN254_Snarks].fromUint(7'u64)
      let s2 = Fr[BN254_Snarks].fromUint(13'u64)
      var sProd: Fr[BN254_Snarks]
      sProd.prod(s1, s2)

      p1.scalarMul(s1.toBig())
      q1.scalarMul(s2.toBig())
      p2.scalarMul(sProd.toBig())

      var p1Aff, p2Aff: EC_ShortW_Aff[Fp[BN254_Snarks], G1]
      var q1Aff: EC_ShortW_Aff[Fp2[BN254_Snarks], G2]
      p1Aff.affine(p1)
      p2Aff.affine(p2)
      q1Aff.affine(q1)

      var gt1, gt2, gtInv, gtProd: Fp12[BN254_Snarks]
      gt1.pairing(p1Aff, q1Aff)
      gt2.pairing(p2Aff, g2)
      check bool(gt1 == gt2)

      gtInv.inv(gt1)
      gtProd.prod(gt1, gtInv)
      check bool(gtProd.isOne())

      # Cyclotomic squaring consistency
      var cycSq, stdSq: Fp12[BN254_Snarks]
      cycSq.cyclotomic_square(gt1)
      stdSq.square(gt1)
      check bool(cycSq == stdSq)

    test "Hash-to-field on Fp[Secp256k1] and Fp2[BN254_Snarks]":
      var outSecp: array[2, Fp[Secp256k1]]
      sha256.hashToField(128, outSecp, [], "abc".toOpenArrayByte(0, 2), "QUUX-V01-CS02-with-secp256k1".toOpenArrayByte(0, 27))
      check bool(outSecp[0].mres < Fp[Secp256k1].getModulus())
      check bool(outSecp[1].mres < Fp[Secp256k1].getModulus())
      check not bool(outSecp[0].isZero())

      var outBn2: array[2, Fp2[BN254_Snarks]]
      sha256.hashToField(128, outBn2, [], "abc".toOpenArrayByte(0, 2), "QUUX-V01-CS02-with-bn254g2".toOpenArrayByte(0, 25))
      check bool(outBn2[0].c0.mres < Fp[BN254_Snarks].getModulus())
      check bool(outBn2[0].c1.mres < Fp[BN254_Snarks].getModulus())
      check not bool(outBn2[0].isZero())
