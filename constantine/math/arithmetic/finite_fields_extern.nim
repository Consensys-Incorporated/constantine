# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  constantine/platforms/abstractions,
  constantine/named/properties_fields,
  ./bigints

# ############################################################
#
#              External field accelerator
#
# ############################################################

# With -d:CTT_EXTERN_FIELD_ACCEL, some operations of some 256-bit fields are
# delegated to a C function that Constantine only declares:
#
#   uint32_t lineth_zkvm_field_op(uint32_t op, uint32_t field,
#                                 uint64_t out[4], const uint64_t a[4], const uint64_t b[4]);
#
# The final link must provide it, e.g. a zkVM guest runtime that forwards it to
# the prover (lineth_accelerators.h in the Lineth monorepo).
#
#   op    0 MUL   out = a*b
#         1 DIV   out = a/b, 0 if b = 0                   (status 1 if b = 0)
#         2 SQRT  out² = a, or out² = -a if a is not a square (status 1)
#   field 1 Fp[Secp256k1]   2 Fr[Secp256k1]   5 Fp[BN254_Snarks]
#         6 Fr[BN254_Snarks]   7 Fr[BLS12_381]
#
# Operands are the 4 little-endian 64-bit limbs of the plain (not Montgomery)
# value, below 2p. The output is reduced and may alias an input; b is read for
# every op. The status is returned. SQRT needs p = 3 (mod 4) and may return
# either root.
#
# Constantine maps its operations onto these as follows:
#   - Fields with hasExtFieldMul store plain values in [0, p): prod/square are
#     MUL, inv is DIV(1, a), sqrt is SQRT.
#   - Montgomery fields store aR: inv is DIV(R², aR) = a⁻¹R, as invmod does.
#     Products and square roots stay in software (they would need 2 calls).

const CTT_EXTERN_FIELD_ACCEL {.booldefine.} = false

func lineth_zkvm_field_op(op, field: uint32, r: pointer, a, b: pointer): uint32 {.importc, cdecl.}

const
  ExtFieldMul = 0'u32
  ExtFieldDiv = 1'u32
  ExtFieldSqrt = 2'u32

template extFieldId*(F: type FF): uint32 =
  when F is Fp[Secp256k1]: 1'u32
  elif F is Fr[Secp256k1]: 2'u32
  elif F is Fp[BN254_Snarks]: 5'u32
  elif F is Fr[BN254_Snarks]: 6'u32
  elif F is Fr[BLS12_381]: 7'u32
  else: 0'u32

template hasExtFieldInv*(F: type FF): static bool =
  ## Inversion goes through the external accelerator
  CTT_EXTERN_FIELD_ACCEL and WordBitWidth == 64 and F.extFieldId() != 0

template hasExtFieldMul*(F: type FF): static bool =
  ## Multiplication and squaring go through the external accelerator.
  ## Such fields store plain values in [0, p).
  CTT_EXTERN_FIELD_ACCEL and WordBitWidth == 64 and F.extFieldId() != 0

template hasExtFieldSqrt*(F: type FF): static bool =
  ## Square roots go through the external accelerator
  F is Fp and F.hasExtFieldMul() and (F.getModulus().limbs[0].BaseType and 3) == 3

template isPlainRepField*(F: type FF): static bool =
  ## True if the field stores canonical plain values in [0, p)
  ## instead of Montgomery residues.
  F.isCrandallPrimeField() or F.hasExtFieldMul()

{.push raises: [], inline.}

func extFieldOp[F: FF](op: uint32, r: var F, a, b: F): SecretBool =
  static: doAssert sizeof(F) == 32, "the external field accelerator needs 4 limbs of 64 bits"
  SecretBool(lineth_zkvm_field_op(op, F.extFieldId(), r.addr, a.unsafeAddr, b.unsafeAddr) != 0)

func extFieldProd*[F: FF](r: var F, a, b: F) =
  ## r <- a*b
  discard extFieldOp(ExtFieldMul, r, a, b)

func extFieldInv*[F: FF](r: var F, a: F) =
  ## r <- a⁻¹, 0 if a = 0
  var num {.noInit.}: F
  when F.hasExtFieldMul():
    num.mres.setOne()
  else:
    num.mres = F.getR2modP()
  discard extFieldOp(ExtFieldDiv, r, num, a)

func extFieldSqrt*[F: FF](r: var F, a: F): SecretBool =
  ## r <- √a if a is a square (returns true), else √-a (returns false)
  not extFieldOp(ExtFieldSqrt, r, a, a)

func extFieldFromLimbs4*[F: FF](r: var F, limbs: array[4, SecretWord]) =
  ## Reduce an arbitrary 4-limb (256-bit) unsigned integer modulo p into plain [0, p).
  static:
    doAssert F.hasExtFieldMul()
    doAssert r.mres.limbs.len == 4
  when F.getSpareBits() == 0:
    # p > 2^255 (Secp256k1 Fp/Fr): any 256-bit integer is < 2p
    r.mres.limbs = limbs
    discard r.mres.csub(F.getModulus(), not(r.mres < F.getModulus()))
  else:
    # 2^129 < p < 2^255 (BN254 Fp/Fr, BLS12-381 Fr):
    # limbs = lo_128 + hi_128 * 2^128, with lo_128, hi_128, 2^128 all < p.
    static: doAssert F.bits() > 129
    var lo128, hi128, two128: F
    lo128.mres.limbs[0] = limbs[0]
    lo128.mres.limbs[1] = limbs[1]
    hi128.mres.limbs[0] = limbs[2]
    hi128.mres.limbs[1] = limbs[3]
    two128.mres.limbs[2] = SecretWord(1)
    var prodHi {.noInit.}: F
    prodHi.extFieldProd(hi128, two128)
    var overflowed = r.mres.sum(prodHi.mres, lo128.mres)
    overflowed = overflowed or not(r.mres < F.getModulus())
    discard r.mres.csub(F.getModulus(), overflowed)

{.pop.}
