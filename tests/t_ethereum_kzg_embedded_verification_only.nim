# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

# nim c -r -d:CTT_EMBEDDED_KZG -d:CTT_KZG_VERIFICATION_ONLY tests/t_ethereum_kzg_embedded_verification_only.nim
static:
  doAssert defined(CTT_EMBEDDED_KZG)
  doAssert defined(CTT_KZG_VERIFICATION_ONLY)

# The official EIP-4844 test vectors and the batch blinding tests,
# on a context created from the embedded verification-only trusted setup.
# The tests that need the full trusted setup are left out.
include ./t_ethereum_eip4844_deneb_kzg
include ./t_ethereum_eip4844_kzg_batch_blinding
