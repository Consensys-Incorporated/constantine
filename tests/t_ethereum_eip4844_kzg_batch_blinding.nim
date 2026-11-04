# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  # Standard library
  std/unittest,
  # Internals
  constantine/named/algebras,
  constantine/hashes,
  constantine/math/[arithmetic, ec_shortweierstrass, extension_fields],
  constantine/math/io/io_fields,
  constantine/math/polynomials/polynomials,
  constantine/serialization/[codecs_bls12_381, endians],
  constantine/ethereum_eip4844_kzg {.all.},
  # Test utilities
  ./testutils/eth_consensus_utils

# The blinding factor r of verify_blob_kzg_proof_batch and its powers cᵢ weigh the n verification sets in
#   ∑ cᵢ.πᵢ.(τ - zᵢ) = ∑ cᵢ.(Pᵢ(τ) - yᵢ)
# with πᵢ the proofs, zᵢ the opening challenges, Pᵢ the polynomials the commitments commit to
# and yᵢ the evaluations of the blobs at zᵢ.

type
  Bytes48 = array[48, byte]
  Poly = PolynomialEval[FIELD_ELEMENTS_PER_BLOB, Fr[BLS12_381], kBitReversed]

proc toBlob(poly: ref Poly): ref Blob =
  new result
  var bytes: array[BYTES_PER_FIELD_ELEMENT, byte]
  for i in 0 ..< FIELD_ELEMENTS_PER_BLOB:
    bytes.marshal(poly.evals[i], bigEndian)
    for j in 0 ..< BYTES_PER_FIELD_ELEMENT:
      result[][i*BYTES_PER_FIELD_ELEMENT + j] = bytes[j]

proc pseudoRandomPoly(seed: uint64): ref Poly =
  new result
  var x = Fr[BLS12_381].fromUint(seed)
  for i in 0 ..< FIELD_ELEMENTS_PER_BLOB:
    x.square()
    x += Fr[BLS12_381].fromUint(uint64(i+1))
    result.evals[i] = x

proc testBlindingMatchesSpecs(ctx: ptr EthereumKZGContext) =
  ## With all-zero random bytes, verify_blob_kzg_proof_batch must weigh the sets by the powers [r⁰, ..., rⁿ⁻¹]
  ## of the blinding factor of the consensus specs' verify_kzg_proof_batch:
  ##   r = hash_to_bls_field(RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ‖ uint64_be(FIELD_ELEMENTS_PER_BLOB) ‖ uint64_be(n)
  ##                         ‖ commitment₀ ‖ z₀ ‖ y₀ ‖ proof₀ ‖ ... ‖ commitmentₙ₋₁ ‖ zₙ₋₁ ‖ yₙ₋₁ ‖ proofₙ₋₁)
  ## With random bytes, it must weigh the sets by [r¹, ..., rⁿ] with r the random bytes reduced modulo the field order.
  ##
  ## The test replaces [τ]₂ of the trusted setup by the [τ]₂ that makes
  ## an arbitrary batch valid for the expected weights. Hence the batch is only valid for these weights.
  const n = 3

  let polys = [pseudoRandomPoly(1), pseudoRandomPoly(2), pseudoRandomPoly(3)]
  let blobs = new array[n, Blob]
  for i in 0 ..< n:
    blobs[][i] = polys[i].toBlob()[]

  # Commitments and proofs are arbitrary points [Pᵢ]G and [pᵢ]G
  var dlogCommitments, dlogProofs, zs, ys: array[n, Fr[BLS12_381]]
  var commitments, proofs: array[n, Bytes48]
  for i in 0 ..< n:
    dlogCommitments[i] = Fr[BLS12_381].fromUint(uint64(7919*(i+1)))
    dlogProofs[i] = Fr[BLS12_381].fromUint(uint64(104729*(i+1) + 3))

    var point {.noInit.}: EC_ShortW_Jac[Fp[BLS12_381], G1]
    var pointAff {.noInit.}: EC_ShortW_Aff[Fp[BLS12_381], G1]
    point.setGenerator()
    point.scalarMul_vartime(dlogCommitments[i])
    pointAff.affine(point)
    discard commitments[i].serialize_g1_compressed(pointAff)
    point.setGenerator()
    point.scalarMul_vartime(dlogProofs[i])
    pointAff.affine(point)
    discard proofs[i].serialize_g1_compressed(pointAff)

    zs[i].addr.fiatShamirChallenge(blobs[][i], commitments[i])
    ctx.domain_brp.evalPolyAt(ys[i], polys[i][], zs[i])

  var data: seq[byte]
  template appendBytes(bytes: openArray[byte]) =
    for b in bytes:
      data.add b
  appendBytes(RANDOM_CHALLENGE_KZG_BATCH_DOMAIN)
  appendBytes(FIELD_ELEMENTS_PER_BLOB.uint64.toBytes(bigEndian))
  appendBytes(n.uint64.toBytes(bigEndian))
  for i in 0 ..< n:
    var zBytes, yBytes: array[BYTES_PER_FIELD_ELEMENT, byte]
    zBytes.marshal(zs[i], bigEndian)
    yBytes.marshal(ys[i], bigEndian)
    appendBytes(commitments[i])
    appendBytes(zBytes)
    appendBytes(yBytes)
    appendBytes(proofs[i])
  var digest {.noInit.}: array[32, byte]
  sha256.hash(digest, data)
  var rSpecs {.noInit.}: Fr[BLS12_381]
  rSpecs.fromDigest(digest)

  var randomBytes {.noInit.}: array[32, byte]
  sha256.hash(randomBytes, "The wizard quickly jinxed the gnomes before they vaporized.")
  var rRandom {.noInit.}: Fr[BLS12_381]
  rRandom.fromDigest(randomBytes)

  proc setTau(weights: array[n, Fr[BLS12_381]]) =
    # τ.∑ cᵢ.pᵢ = ∑ cᵢ.(Pᵢ - yᵢ + zᵢ.pᵢ)
    var numerator, denominator: Fr[BLS12_381]
    numerator.setZero()
    denominator.setZero()
    for i in 0 ..< n:
      numerator += weights[i] * (dlogCommitments[i] - ys[i] + zs[i] * dlogProofs[i])
      denominator += weights[i] * dlogProofs[i]
    denominator.inv_vartime()
    let tau = numerator * denominator

    var tauG2 {.noInit.}: EC_ShortW_Jac[Fp2[BLS12_381], G2]
    tauG2.setGenerator()
    tauG2.scalarMul_vartime(tau)
    ctx.srs_monomial_g2.coefs[1].affine(tauG2)

  proc verifyBatch(randomBytes: array[32, byte]): cttEthKzgStatus =
    ctx.verify_blob_kzg_proof_batch(
      cast[ptr UncheckedArray[Blob]](blobs[][0].unsafeAddr),
      cast[ptr UncheckedArray[Bytes48]](commitments[0].addr),
      cast[ptr UncheckedArray[Bytes48]](proofs[0].addr),
      n, randomBytes)

  let allZeros = default(array[32, byte])

  setTau([Fr[BLS12_381].fromUint(1'u64), rSpecs, rSpecs * rSpecs])
  doAssert verifyBatch(allZeros) == cttEthKzg_Success
  doAssert verifyBatch(randomBytes) == cttEthKzg_VerificationFailure

  setTau([rRandom, rRandom * rRandom, rRandom * rRandom * rRandom])
  doAssert verifyBatch(randomBytes) == cttEthKzg_Success
  doAssert verifyBatch(allZeros) == cttEthKzg_VerificationFailure

when not defined(CTT_KZG_VERIFICATION_ONLY):
  proc blindingFromChallenges(z1, z2: Fr[BLS12_381], canonicalEncoding: bool): array[32, byte] =
    ## sha256(RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ‖ z₁ ‖ z₂): it only depends on the opening challenges,
    ## which are known before the proofs are chosen.
    ## The challenges are encoded either as big-endian integers or as their in-memory representation.
    var transcript {.noInit.}: sha256
    transcript.init()
    transcript.update(RANDOM_CHALLENGE_KZG_BATCH_DOMAIN)
    if canonicalEncoding:
      var bytes: array[BYTES_PER_FIELD_ELEMENT, byte]
      bytes.marshal(z1, bigEndian)
      transcript.update(bytes)
      bytes.marshal(z2, bigEndian)
      transcript.update(bytes)
    else:
      let challenges = [z1, z2]
      transcript.update(cast[ptr UncheckedArray[byte]](challenges[0].unsafeAddr).toOpenArray(0, 2*sizeof(Fr[BLS12_381])-1))
    transcript.finish(result)

  proc testForgedBatchIsRejected(ctx: ptr EthereumKZGContext) =
    ## A batch of 2 sets (blob₁, commitment₁, proof₁), (blob₂, commitment₂, proof₂)
    ## where commitment₁ does not commit to blob₁, valid if the blinding factor r
    ## is known before proof₁ and proof₂ are chosen, as c₁ = r and c₂ = r².
    ##
    ## - Set 2 is honest except for its proof π₂ = [a]G, with the scalar a chosen
    ##   such that the numerator of the batch check, a polynomial of degree < 4096
    ##     M(x) = c₁.(P₁(x) - y₁) + c₂.(P₂(x) - y₂) - c₂.a.(x - z₂)
    ##   vanishes at z₁:
    ##     a = (c₁.(P₁(z₁) - y₁) + c₂.(P₂(z₁) - y₂)) / (c₂.(z₁ - z₂))
    ## - then π₁ = [M(τ) / (c₁.(τ - z₁))]G is computable from the public setup,
    ##   as M(x) / (x - z₁) is a polynomial.
    ##
    ## Neither proof is valid by itself.
    let one = Fr[BLS12_381].fromUint(1'u64)

    let poly1 = pseudoRandomPoly(1)
    let poly2 = pseudoRandomPoly(2)
    let rogue1 = new Poly # What commitment₁ actually commits to
    rogue1[] = poly1[]
    rogue1.evals[0] += one

    let blobs = new array[2, Blob]
    blobs[][0] = poly1.toBlob()[]
    blobs[][1] = poly2.toBlob()[]

    var commitments: array[2, Bytes48]
    doAssert ctx.blob_to_kzg_commitment(commitments[0], rogue1.toBlob()[]) == cttEthKzg_Success
    doAssert ctx.blob_to_kzg_commitment(commitments[1], blobs[][1]) == cttEthKzg_Success

    var z1, z2, y1, y2: Fr[BLS12_381]
    z1.addr.fiatShamirChallenge(blobs[][0], commitments[0])
    z2.addr.fiatShamirChallenge(blobs[][1], commitments[1])
    ctx.domain_brp.evalPolyAt(y1, poly1[], z1)
    ctx.domain_brp.evalPolyAt(y2, poly2[], z2)

    proc forgeProofs(r: Fr[BLS12_381]): array[2, Bytes48] =
      let c1 = r
      let c2 = r * r

      var rogue1_z1, poly2_z1: Fr[BLS12_381]
      ctx.domain_brp.evalPolyAt(rogue1_z1, rogue1[], z1)
      ctx.domain_brp.evalPolyAt(poly2_z1, poly2[], z1)

      var a = c1 * (rogue1_z1 - y1) + c2 * (poly2_z1 - y2)
      var denominator = c2 * (z1 - z2)
      denominator.inv_vartime()
      a *= denominator

      var proof2 {.noInit.}: EC_ShortW_Jac[Fp[BLS12_381], G1]
      var proof2Aff {.noInit.}: EC_ShortW_Aff[Fp[BLS12_381], G1]
      proof2.setGenerator()
      proof2.scalarMul_vartime(a)
      proof2Aff.affine(proof2)
      discard result[1].serialize_g1_compressed(proof2Aff)

      # M(x) / (c₁.(x - z₁)), in evaluation form
      var invC1 = c1
      invC1.inv_vartime()
      let quotient = new Poly
      for i in 0 ..< FIELD_ELEMENTS_PER_BLOB:
        let omega = ctx.domain_brp.rootsOfUnity[i]
        let numerator = c1 * (rogue1.evals[i] - y1) + c2 * (poly2.evals[i] - y2) - c2 * a * (omega - z2)
        var invOmegaMinusZ1 = omega - z1
        invOmegaMinusZ1.inv_vartime()
        quotient.evals[i] = numerator * invOmegaMinusZ1 * invC1
      doAssert ctx.blob_to_kzg_commitment(result[0], quotient.toBlob()[]) == cttEthKzg_Success

    proc verifyBatch(proofs: array[2, Bytes48], randomBytes: array[32, byte]): cttEthKzgStatus =
      ctx.verify_blob_kzg_proof_batch(
        cast[ptr UncheckedArray[Blob]](blobs[][0].addr),
        cast[ptr UncheckedArray[Bytes48]](commitments[0].addr),
        cast[ptr UncheckedArray[Bytes48]](proofs[0].unsafeAddr),
        2, randomBytes)

    for canonicalEncoding in [true, false]:
      let challengesBlinding = blindingFromChallenges(z1, z2, canonicalEncoding)
      var r {.noInit.}: Fr[BLS12_381]
      r.fromDigest(challengesBlinding)
      let proofs = forgeProofs(r)

      doAssert ctx.verify_blob_kzg_proof(blobs[][0], commitments[0], proofs[0]) == cttEthKzg_VerificationFailure
      doAssert ctx.verify_blob_kzg_proof(blobs[][1], commitments[1], proofs[1]) == cttEthKzg_VerificationFailure

      # The forgery is valid when the blinding factor only depends on the opening challenges
      doAssert verifyBatch(proofs, challengesBlinding) == cttEthKzg_Success

      # but the Fiat-Shamir derivation has the proofs in its transcript
      doAssert verifyBatch(proofs, default(array[32, byte])) == cttEthKzg_VerificationFailure

suite "Ethereum Deneb Hardfork / EIP-4844 / KZG batch verification blinding factor":
  test "Fiat-Shamir blinding factor and weights are the consensus specs' ones":
    let ctx = getTrustedSetup()
    testBlindingMatchesSpecs(ctx)
    ctx.delete()

  when not defined(CTT_KZG_VERIFICATION_ONLY):
    test "A batch with a commitment that is not the blob's and proofs chosen after the challenges is rejected":
      let ctx = getTrustedSetup()
      testForgedBatchIsRejected(ctx)
      ctx.delete()
