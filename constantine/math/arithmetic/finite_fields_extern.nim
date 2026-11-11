# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  constantine/platforms/abstractions,
  constantine/named/[algebras, properties_fields],
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
#   field 1 Fp[Secp256k1]   2 Fr[Secp256k1]
#
# Operands are the 4 little-endian 64-bit limbs of the plain (not Montgomery)
# value, below 2p. The output is reduced and may alias an input; b is read for
# every op. The status is returned. SQRT needs p = 3 (mod 4) and may return
# either root.
#
# Constantine maps its operations onto these as follows:
#   - Crandall fields store plain values: prod/square are MUL, inv is DIV(1, a),
#     sqrt is SQRT.
#   - Montgomery fields store aR: inv is DIV(R², aR) = a⁻¹R, as invmod does.
#     Products and square roots stay in software (they would need 2 calls).

const CTT_EXTERN_FIELD_ACCEL {.booldefine.} = false

func lineth_zkvm_field_op(op, field: uint32, r: pointer, a, b: pointer): uint32 {.importc, cdecl.}

const
  ExtFieldMul = 0'u32
  ExtFieldDiv = 1'u32
  ExtFieldSqrt = 2'u32

template extFieldId(F: type FF): uint32 =
  when F is Fp[Secp256k1]: 1'u32
  elif F is Fr[Secp256k1]: 2'u32
  else: 0'u32

template hasExtFieldInv*(F: type FF): static bool =
  ## Inversion goes through the external accelerator
  CTT_EXTERN_FIELD_ACCEL and F.extFieldId() != 0

template hasExtFieldMul*(F: type FF): static bool =
  ## Multiplication and squaring go through the external accelerator
  F.hasExtFieldInv() and F.isCrandallPrimeField()

template hasExtFieldSqrt*(F: type FF): static bool =
  ## Square roots go through the external accelerator
  F.hasExtFieldMul() and (F.getModulus().limbs[0].BaseType and 3) == 3

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
  when F.isCrandallPrimeField():
    num.mres.setOne()
  else:
    num.mres = F.getR2modP()
  discard extFieldOp(ExtFieldDiv, r, num, a)

func extFieldSqrt*[F: FF](r: var F, a: F): SecretBool =
  ## r <- √a if a is a square (returns true), else √-a (returns false)
  not extFieldOp(ExtFieldSqrt, r, a, a)

{.pop.}
