# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  constantine/named/algebras,
  constantine/math/arithmetic/finite_fields

# ############################################################
#
#           Specialized inverse square root for Secp256k1
#
# ############################################################

func invsqrt_addchain*(r: var Fp[Secp256k1], a: Fp[Secp256k1]) {.addchain.} =
  ## r <- a^((p-3)/4)
  ##
  ## (p-3)/4 = 2²⁵⁴ - 2³⁰ - 245, in binary from the most significant bit:
  ##   223 ones, 0, 22 ones, 0000, 1, 0, 11
  ## 253 squarings and 14 multiplications.
  ## Adapted from libsecp256k1's square root chain, which computes (p+1)/4 in 13 multiplications.
  var
    x2   {.noInit.}: Fp[Secp256k1]
    x3   {.noInit.}: Fp[Secp256k1]
    x6   {.noInit.}: Fp[Secp256k1]
    x9   {.noInit.}: Fp[Secp256k1]
    x11  {.noInit.}: Fp[Secp256k1]
    x22  {.noInit.}: Fp[Secp256k1]
    x44  {.noInit.}: Fp[Secp256k1]
    x88  {.noInit.}: Fp[Secp256k1]
    x176 {.noInit.}: Fp[Secp256k1]
    x220 {.noInit.}: Fp[Secp256k1]
    x223 {.noInit.}: Fp[Secp256k1]

  # xN = a^(2ᴺ - 1), a run of N ones
  x2.square(a)
  x2 *= a
  x3.square(x2)
  x3 *= a
  x6.square_repeated(x3, 3)
  x6 *= x3
  x9.square_repeated(x6, 3)
  x9 *= x3
  x11.square_repeated(x9, 2)
  x11 *= x2
  x22.square_repeated(x11, 11)
  x22 *= x11
  x44.square_repeated(x22, 22)
  x44 *= x22
  x88.square_repeated(x44, 44)
  x88 *= x44
  x176.square_repeated(x88, 88)
  x176 *= x88
  x220.square_repeated(x176, 44)
  x220 *= x44
  x223.square_repeated(x220, 3)
  x223 *= x3

  # 223 ones, 0, 22 ones
  r.square_repeated(x223, 23)
  r *= x22
  # 0000, 1
  r.square_repeated(5)
  r *= a
  # 0, 11
  r.square_repeated(3)
  r *= x2
