# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  constantine/platforms/abstractions

# ############################################################
#
#       Lineth zkVM secp256k1 base field accelerator
#
# ############################################################

# Custom RISC-V instructions of the Lineth arithmetization (`riscv/main_fieldaccel*.zkc`):
#   custom-1 (0x2b), funct3 0b011, funct7 selects the operation
#     0 mul, 1 square, 2 inverse, 3 square root
#   rd = destination pointer, rs1 = a pointer, rs2 = b pointer (mul only)
#
# Operands are the 4 little-endian 64-bit limbs of `Fp[Secp256k1].mres`.
# Inputs may be any 256-bit value (lazily reduced), outputs are canonical (< p),
# and the destination may alias a source.
# Nothing is written back to registers, so the pointers are inputs only.
#
# Each operation is opt-in, for rv64 guests proven with an entry point that compiles it in:
#   -d:CTT_LINETH_SECP256K1_FP_MUL   multiplication and squaring
#   -d:CTT_LINETH_SECP256K1_FP_INV   inversion
#   -d:CTT_LINETH_SECP256K1_FP_SQRT  square root

const CTT_LINETH_SECP256K1_FP_MUL {.booldefine.} = false
const CTT_LINETH_SECP256K1_FP_INV {.booldefine.} = false
const CTT_LINETH_SECP256K1_FP_SQRT {.booldefine.} = false

const UseLinethSecp256k1FpMul* = CTT_LINETH_SECP256K1_FP_MUL
const UseLinethSecp256k1FpInv* = CTT_LINETH_SECP256K1_FP_INV
const UseLinethSecp256k1FpSqrt* = CTT_LINETH_SECP256K1_FP_SQRT

when (UseLinethSecp256k1FpMul or UseLinethSecp256k1FpInv or UseLinethSecp256k1FpSqrt) and
     not (defined(riscv64) and GCC_Compatible and WordBitWidth == 64):
  {.error: "The Lineth secp256k1 field accelerator needs a 64-bit RISC-V target and a GCC-compatible compiler".}

type
  LinethFp = array[4, SecretWord]

  LinethFpSqrt = object
    root: LinethFp
    isSquare: SecretWord

{.push raises: [], inline.}

func lineth_secp256k1_fp_mul*(r: var LinethFp, a, b: LinethFp) =
  ## r <- a * b (mod p)
  let pr = r.addr
  let pa = a.unsafeAddr
  let pb = b.unsafeAddr
  asm """
    .insn r 0x2b, 0b011, 0b0000000, %[r], %[a], %[b]
    :
    : [r] "r" (`pr`), [a] "r" (`pa`), [b] "r" (`pb`)
    : "memory"
  """

func lineth_secp256k1_fp_square*(r: var LinethFp, a: LinethFp) =
  ## r <- a² (mod p)
  let pr = r.addr
  let pa = a.unsafeAddr
  asm """
    .insn r 0x2b, 0b011, 0b0000001, %[r], %[a], x0
    :
    : [r] "r" (`pr`), [a] "r" (`pa`)
    : "memory"
  """

func lineth_secp256k1_fp_inv*(r: var LinethFp, a: LinethFp) =
  ## r <- a⁻¹ (mod p), and 0 if a ≡ 0 (mod p)
  let pr = r.addr
  let pa = a.unsafeAddr
  asm """
    .insn r 0x2b, 0b011, 0b0000010, %[r], %[a], x0
    :
    : [r] "r" (`pr`), [a] "r" (`pa`)
    : "memory"
  """

func lineth_secp256k1_fp_sqrt*(r: var LinethFp, a: LinethFp): SecretBool =
  ## r <- a^((p+1)/4) (mod p)
  ##
  ## Returns true and a square root of `a` if `a` is a square,
  ## otherwise false and a square root of `-a`.
  ## The instruction writes the root then a 64-bit flag.
  var res {.noInit.}: LinethFpSqrt
  let pres = res.addr
  let pa = a.unsafeAddr
  asm """
    .insn r 0x2b, 0b011, 0b0000011, %[res], %[a], x0
    :
    : [res] "r" (`pres`), [a] "r" (`pa`)
    : "memory"
  """
  r = res.root
  SecretBool(res.isSquare)

{.pop.}
