# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

include ./panicoverride

import
  constantine/ethereum_evm_precompiles,
  ./c_curve_decls

# The BLS12-381 scalar field, the field of EIP-4844 blob elements, with the same C API as the
# full library's `bls12_381_fr`.
type
  big255 = BigInt[255]
  bls12_381_fr = Fr[BLS12_381]

genBindingsField(big255, bls12_381_fr)
