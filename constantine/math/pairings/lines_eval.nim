# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import
  std/typetraits,
  constantine/named/algebras,
  constantine/platforms/abstractions,
  constantine/math/arithmetic,
  constantine/math/extension_fields,
  constantine/math/elliptic/[
    ec_shortweierstrass_affine,
    ec_shortweierstrass_projective
  ],
  constantine/math/io/io_extfields,
  constantine/named/zoo_constants

# No exceptions allowed
{.push raises: [].}

# ############################################################
#
#                     Lines functions
#
# ############################################################

# GT representations isomorphisms
# ===============================
#
# Given a sextic twist, we can express all elements in terms of z = SNR¹ᐟ⁶
#
# The canonical direct sextic representation uses coefficients
#
#    c₀ + c₁ z + c₂ z² + c₃ z³ + c₄ z⁴ + c₅ z⁵
#
# with z = SNR¹ᐟ⁶
#
# The cubic over quadratic towering
# ---------------------------------
#
#   (a₀ + a₁ u) + (a₂ + a₃u) v + (a₄ + a₅u) v²
#
# with u = (SNR)¹ᐟ² and v = z = u¹ᐟ³ = (SNR)¹ᐟ⁶
#
# The quadratic over cubic towering
# ---------------------------------
#
#   (b₀ + b₁x + b₂x²) + (b₃ + b₄x + b₅x²)y
#
# with x = (SNR)¹ᐟ³ and y = z = x¹ᐟ² = (SNR)¹ᐟ⁶
#
# Mapping between towering schemes
# --------------------------------
#
# canonical <=> cubic over quadratic <=> quadratic over cubic
#    c₀     <=>        a₀            <=>            b₀
#    c₁     <=>        a₂            <=>            b₃
#    c₂     <=>        a₄            <=>            b₁
#    c₃     <=>        a₁            <=>            b₄
#    c₄     <=>        a₃            <=>            b₂
#    c₅     <=>        a₅            <=>            b₅
#
# See also chapter 6.4
# - Multiplication and Squaring on Pairing-Friendly Fields
#   Augusto Jun Devegili and Colm Ó hÉigeartaigh and Michael Scott and Ricardo Dahab, 2006
#   https://eprint.iacr.org/2006/471

type
  Line*[F] = object
    ## Packed line representation over a E'(𝔽pᵏ/d)
    ## with k the embedding degree and d the twist degree
    ## i.e. for a curve with embedding degree 12 and sextic twist
    ## F is Fp2
    ##
    ## Assuming a Sextic Twist with GT in 𝔽p12
    ##
    ## Out of 6 𝔽p2 coordinates, 3 are zeroes and
    ## the non-zero coordinates depend on the twist kind.
    ##
    ## For a D-twist
    ##   in canonical coordinates over sextic polynomial [1, w, w², w³, w⁴, w⁵]
    ##   when evaluating the line at P(xₚ, yₚ)
    ##     a.yₚ + b.xₚ w + c w³
    ##
    ##   This translates in 𝔽pᵏ to
    ##     - acb000 (cubic over quadratic towering)
    ##     - a00bc0 (quadratic over cubic towering)
    ## For a M-Twist
    ##   in canonical coordinates over sextic polynomial [1, w, w², w³, w⁴, w⁵]
    ##   when evaluating the line at the twist ψ(P)(xₚw², yₚw³)
    ##     a.yₚ w³ + b.xₚ w² + c
    ##
    ##   This translates in 𝔽pᵏ to
    ##     - ca00b0 (cubic over quadratic towering)
    ##     - cb00a0 (quadratic over cubic towering)
    a*, b*, c*: F

  SexticNonResidue* = NonResidue
    ## The Sextic non-residue to build
    ## 𝔽p2 -> 𝔽p12 towering and the G2 sextic twist
    ## or
    ## 𝔽p -> 𝔽p6 towering and the G2 sextic twist
    ##
    ## Note:
    ## while the non-residues for
    ## - 𝔽p2 -> 𝔽p4
    ## - 𝔽p2 -> 𝔽p6
    ## are also sextic non-residues by construction.
    ## the non-residues for
    ## - 𝔽p4 -> 𝔽p12
    ## - 𝔽p6 -> 𝔽p12
    ## are not.

func toHex*(line: Line): string =
  result = static($line.typeof.genericHead() & '(')
  for fieldName, fieldValue in fieldPairs(line):
    when fieldName != "x":
      result.add ", "
    result.add fieldName & ": "
    result.appendHex(fieldValue)
  result.add ")"

# Line evaluation
# -----------------------------------------------------------------------

func line_update[F1, F2](line: var Line[F2], P: EC_ShortW_Aff[F1, G1]) =
  ## Update the line evaluation with P
  ## after addition or doubling
  ## P in G1
  static: doAssert F1.Name == F2.Name
  # D-Twist: line at P(xₚ, yₚ):
  #   a.yₚ + b.xₚ w + c w³
  #
  # M-Twist: line at ψ(P)(xₚw², yₚw³)
  #   a.yₚ w³ + b.xₚ w² + c
  line.a *= P.y
  line.b *= P.x

# ############################################################
#
#            Miller Loop's Line Evaluation
#             with projective coordinates
#
# ############################################################
#
# - Pairing Implementation Revisited
#   Michael Scott, 2019
#   https://eprint.iacr.org/2019/077
#
# - The Realm of the Pairings
#   Diego F. Aranha and Paulo S. L. M. Barreto
#   and Patrick Longa and Jefferson E. Ricardini, 2013
#   https://eprint.iacr.org/2013/722.pdf
#   http://sac2013.irmacs.sfu.ca/slides/s1.pdf
#
# - Efficient Implementation of Bilinear Pairings on ARM Processors
#   Gurleen Grewal, Reza Azarderakhsh,
#   Patrick Longa, Shi Hu, and David Jao, 2012
#   https://eprint.iacr.org/2012/408.pdf

# Line evaluation
# -----------------------------------------------------------------------------

# Line for a doubling
# ===================
#
# With T in homogenous projective coordinates (X, Y, Z)
# And ξ the sextic non residue to construct the towering
#
# M-Twist:
#   A = -2ξ Y.Z      [w³]
#   B = 3 X²         [w²]
#   C = 3bξ Z² - Y²  [1]
#
# D-Twist may be scaled by ξ to avoid dividing by ξ:
#   A = -2ξ Y.Z      [1]
#   C = 3ξ X²        [w]
#   B = 3b Z² - ξY²  [w³]
#
# Instead of
#   - equation 10 from The Real of pairing, Aranha et al, 2013
#   - or chapter 3 from pairing Implementation Revisited, Scott 2019
#   A = -2 Y.Z
#   B = 3 X²
#   C = 3b/ξ Z² - Y²
#
# Note: This tradeoff a division with 3 multiplication by a non-residue.
#       This is interesting for ξ has a small norm, but
#       BN254_Snarks for example is 9+𝑖
#
# A constant factor will be wiped by the final exponentiation
# as for all non-zero α ∈ GF(pᵐ)
# with
# - p odd prime
# - and gcd(α,pᵐ) = 1 (i.e. the extension field pᵐ is using irreducible polynomials)
#
# Little Fermat holds and we have
# α^(pᵐ - 1) ≡ 1 (mod pᵐ)
#
# The final exponent is of the form
# (pᵏ-1)/r
#
# A constant factor on twisted coordinates pᵏᐟᵈ
# is a constant factor on pᵏ with d the twisting degree
# and so will be elminated. QED.
#
# Line for an addition
# ====================
#
# With T in homogenous projective coordinates (X, Y, Z)
# And ξ the sextic non residue to construct the towering
#
# M-Twist:
#   A = X₁ - Z₁X₂
#   B = - (Y₁ - Z₁Y₂)
#   C = (Y₁ - Z₁Y₂) X₂ - (X₁ - Z₁X₂) Y₂
#
# D-Twist:
#   A = X₁ - Z₁X₂
#   B = - (Y₁ - Z₁Y₂)
#   C = (Y₁ - Z₁Y₂) X₂ - (X₁ - Z₁X₂) Y₂
#
# Note: There is no need for complete formula as
# we have T ∉ [Q, -Q] in the Miller loop doubling-and-add
# i.e. the line cannot be vertical

func line_eval_fused_double[Field](
       line: var Line[Field],
       T: var EC_ShortW_Prj[Field, G2]) =
  ## Fused line evaluation and elliptic point doubling
  # Grewal et al, 2012 adapted to Scott 2019 line notation

  var A {.noInit.}, B {.noInit.}, C {.noInit.}: Field
  var E {.noInit.}, F {.noInit.}, G {.noInit.}: Field

  template H: untyped = line.a
  template I: untyped = line.b
  template J: untyped = line.c

  A.prod(T.x, T.y)
  A.div2()          # A = XY/2
  B.square(T.y)     # B = Y²
  C.square(T.z)     # C = Z²

  # E = 3b'Z² = 3bξ Z² (M-Twist) or 3b/ξ Z² (D-Twist)
  when Field.Name.getSexticTwist() == M_Twist and E.fromComplexExtension():
    const b3 = 3*Field.Name.getCoefB()
    E.prod(C, b3)
    E *= SexticNonResidue
  else:
    E = C
    E.mulCheckSparse(Field.Name.getCoefB_G2_times_3())

  F.prod(E, 3)      # F = 3E = 9b'Z²
  G.sum(B, F)
  G.div2()          # G = (B+F)/2
  H.sum(T.y, T.z)
  H.square()
  H -= B
  H -= C            # H = (Y+Z)²-(B+C)= 2YZ

  I.square(T.x)
  I *= 3            # I = 3X²

  J.diff(E, B)      # J = E-B = 3b'Z² - Y²

  # In-place modification: invalidates `T.` calls
  T.x.diff(B, F)
  T.x *= A          # X₃ = A(B-F) = XY/2.(Y²-9b'Z²)
  T.y.square(G)
  E.square()
  E *= 3
  T.y -= E          # Y₃ = G² - 3E² = (Y²+9b'Z²)²/4 - 3*(3b'Z²)²
  T.z.prod(B, H)    # Z₃ = BH = Y²((Y+Z)² - (Y²+Z²)) = 2Y³Z
  H.neg()

func line_eval_fused_add[Field](
       line: var Line[Field],
       T: var EC_ShortW_Prj[Field, G2],
       Q: EC_ShortW_Aff[Field, G2]) =
  ## Fused line evaluation and elliptic point addition
  # Grewal et al, 2012 adapted to Scott 2019 line notation
  var
    A {.noInit.}: Field
    B {.noInit.}: Field
    C {.noInit.}: Field
    D {.noInit.}: Field
    E {.noInit.}: Field
    F {.noInit.}: Field
    G {.noInit.}: Field
    H {.noInit.}: Field
    I {.noInit.}: Field

  template lambda: untyped = line.a
  template theta: untyped = line.b
  template J: untyped = line.c

  A.prod(Q.y, T.z)
  B.prod(Q.x, T.z)
  theta.diff(T.y, A)  # θ = Y₁ - Z₁Y₂
  lambda.diff(T.x, B) # λ = X₁ - Z₁X₂
  C.square(theta)
  D.square(lambda)
  E.prod(D, lambda)
  F.prod(T.z, C)
  G.prod(T.x, D)
  H.double(G)
  H.diff(F, H)
  H += E
  I.prod(T.y, E)

  T.x.prod(theta, Q.x)
  T.y.prod(lambda, Q.y)
  J.diff(T.x, T.y)

  # EC addition
  T.x.prod(lambda, H)

  T.y.diff(G, H)
  T.y *= theta
  T.y -= I

  T.z *= E

  # Line evaluation
  theta.neg()

# Public line evaluation procedures
# -----------------------------------------------------------------------------

func line_double*[F1, F2](
       line: var Line[F2],
       T: var EC_ShortW_Prj[F2, G2],
       P: EC_ShortW_Aff[F1, G1]) {.meter.} =
  ## Doubling step of the Miller loop
  ## T in G2, P in G1
  ##
  ## Compute lt,t(P)
  static: doAssert F1.Name == F2.Name
  line_eval_fused_double(line, T)
  line.line_update(P)

func line_add*[F1, F2](
       line: var Line[F2],
       T: var EC_ShortW_Prj[F2, G2],
       Q: EC_ShortW_Aff[F2, G2],
       P: EC_ShortW_Aff[F1, G1]) {.meter.} =
  ## Addition step of the Miller loop
  ## T and Q in G2, P in G1
  ##
  ## Compute lt,q(P)
  static: doAssert F1.Name == F2.Name
  line_eval_fused_add(line, T, Q)
  line.line_update(P)

# ############################################################
#
#                 Sparse Multiplication
#             by lines for curves with a sextic twist
#
# ############################################################

# - Pairing Implementation Revisited
#   Michael Scott, 2019
#   https://eprint.iacr.org/2019/077
#
# - Efficient Implementation of Bilinear Pairings on ARM Processors
#   Gurleen Grewal, Reza Azarderakhsh,
#   Patrick Longa, Shi Hu, and David Jao, 2012
#   https://eprint.iacr.org/2012/408.pdf
#
# - High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves\
#   Jean-Luc Beuchat and Jorge Enrique González Díaz and Shigeo Mitsunari and Eiji Okamoto and Francisco Rodríguez-Henríquez and Tadanori Teruya, 2010\
#   https://eprint.iacr.org/2010/354
#
# - Faster Pairing Computations on Curves with High-Degree Twists
#   Craig Costello, Tanja Lange, and Michael Naehrig, 2009
#   https://eprint.iacr.org/2009/615.pdf

# ############################################################
#
#            𝔽pᵏ by line - 𝔽pᵏ quadratic over cubic
#
# ############################################################

# D-Twist
# ------------------------------------------------------------

func mul_sparse_by_line_a00bc0*[Fpk, Fpkdiv6](f: var Fpk, l: Line[Fpkdiv6]) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element coming from an D-Twist line function
  ## with a cubic over quadratic towering (𝔽p2 -> 𝔽p6 -> 𝔽p12)
  ## The sparse element is represented by a packed Line type
  ## with coordinate (a,b,c) matching 𝔽pᵏ coordinates a00bc0

  # a0b0 = (a00, a01, a02).( x, 0, 0)
  # a1b1 = (a10, a11, a12).( y, z, 0)
  #
  # r0 = a0 b0 + ξ a1 b1
  # r1 = a0 b1 + a1 b0                       (Schoolbook)
  #    = (a0 + a1) (b0 + b1) - a0 b0 - a1 b1 (Karatsuba)

  static:
    doAssert Fpk.Name.getSexticTwist() == D_Twist
    doAssert f is QuadraticExt, "This assumes 𝔽pᵏ as a quadratic extension of 𝔽pᵏᐟ²"
    doAssert f.c0 is CubicExt, "This assumes 𝔽pᵏᐟ² as a cubic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv2 = typeof(f.c0)

  when Fpk.Name.has_large_field_elem() or Fpk.Name.skipLazyReduction():
    var
      v0 {.noInit.}: Fpkdiv2
      v1 {.noInit.}: Fpkdiv2
      t  {.noInit.}: Fpkdiv6

    v1.sum(f.c0, f.c1)
    t.sum(l.a, l.b)
    v0.mul_sparse_by_xy0(v1, t, l.c)

    v1.mul_sparse_by_xy0(f.c1, l.b, l.c)

    f.c1.diff(v0, v1)

    v0.mul_sparse_by_x00(f.c0, l.a)
    f.c1 -= v0

    v1 *= NonResidue
    f.c0.sum(v0, v1)

  else: # Lazy reduction
    var
      V0 {.noInit.}: doubleprec(Fpkdiv2)
      V1 {.noInit.}: doubleprec(Fpkdiv2)
      V  {.noInit.}: doubleprec(Fpkdiv2)
      t  {.noInit.}: Fpkdiv6
      u  {.noInit.}: Fpkdiv2

    u.sum(f.c0, f.c1)
    t.sum(l.a, l.b)
    V.mul2x_sparse_by_xy0(u, t, l.c)
    V1.mul2x_sparse_by_xy0(f.c1, l.b, l.c)
    V0.mul2x_sparse_by_x00(f.c0, l.a)

    V.diff2xMod(V, V1)
    V.diff2xMod(V, V0)
    f.c1.redc2x(V)

    V1.prod2x(V1, NonResidue)
    V0.sum2xMod(V0, V1)
    f.c0.redc2x(V0)

func prod_x00yz0_x00yz0_into_abcdefghij00*[Fpk, Fpkdiv6](f: var Fpk, l0, l1: Line[Fpkdiv6]) =
  ## Multiply 2 lines together
  ## The result is sparse in f.
  # Preambule
  #
  # A sparse xy0 by xy0 multiplication in 𝔽pᵏᐟ² (cubic) would be
  #   (a0', a1', 0).(b0', b1', 0)
  #
  #   r0' = a0'b0'
  #   r1' = a0'b1 + a1'b0'
  #     or (a0'+b1')(a1'+b0')-a0'a1'-b0'b1'
  #   r2' = a1'b1
  #
  # Note¹ that the Karatsuba does not reuse terms!
  #
  # In the following equations (taken from quad extension implementation)
  # a0 = ( x , 0 , 0)
  # a1 = ( y , z , 0)
  # b0 = ( x', 0, 0)
  # b1 = ( y', z', 0)
  #
  # a0b0 = ( x, 0, 0).( x', 0 , 0) = (xx',       0,  0 )
  # a1b1 = ( y, z, 0).( y', z', 0) = (yy', yz'+zy', zz')

  # r0 = a0 b0 + ξ a1 b1
  # r1 = a0 b1 + a1 b0                       (Schoolbook)
  #    = (a0 + a1) (b0 + b1) - a0 b0 - a1 b1 (Karatsuba)
  #
  # Note² that Karatsuba doesn't help as a0 and b0 are actually very cheap (x, 0, 0)
  #
  # Replacing by the coordinates in the lower tower we get
  #
  # r0 = (xx'+ξzz', yy', yz'+zy')
  # r1 = ( x, 0, 0)( y', z', 0) + ( y , z , 0)( x', 0, 0)
  #    = (xy'+yx', xz'+zx', 0)
  #
  # Now we can apply Karasuba¹² for a total of 6 multiplications

  static:
    doAssert Fpk.Name.getSexticTwist() == D_Twist
    doAssert f is QuadraticExt, "This assumes 𝔽pᵏ as a quadratic extension of 𝔽pᵏᐟ²"
    doAssert f.c0 is CubicExt, "This assumes 𝔽pᵏᐟ² as a cubic extension of 𝔽pᵏᐟ⁶"

  var XX{.noInit.}, YY{.noInit.}, ZZ{.noInit.}: doublePrec(Fpkdiv6)

  XX.prod2x(l0.a, l1.a)
  YY.prod2x(l0.b, l1.b)
  ZZ.prod2x(l0.c, l1.c)

  var V{.noInit.}: doublePrec(Fpkdiv6)
  var t0{.noInit.}, t1{.noInit.}: Fpkdiv6

  # r0 = (xx'+ξzz', yy', yz'+zy')
  # r00 = xx'+ξzz''
  # r01 = yy'
  # r02 = yz'+zy' = (y+z)(y'+z') - yy' - zz'
  V.prod2x(ZZ, NonResidue)
  V.sum2xMod(V,XX)
  f.c0.c0.redc2x(V)

  f.c0.c1.redc2x(YY)

  t0.sum(l0.b, l0.c)
  t1.sum(l1.b, l1.c)
  V.prod2x(t0, t1)
  V.diff2xMod(V, YY)
  V.diff2xMod(V, ZZ)
  f.c0.c2.redc2x(V)

  # r1 = (xy'+yx', xz'+zx', 0)
  # r10 = xy'+yx' = (x+y)(x'+y') - xx' - yy'
  # r11 = xz'+zx' = (x+z)(x'+z') - xx' - zz'
  # r12 = 0
  t0.sum(l0.a, l0.b)
  t1.sum(l1.a, l1.b)
  V.prod2x(t0, t1)
  V.diff2xMod(V, XX)
  V.diff2xMod(V, YY)
  f.c1.c0.redc2x(V)

  t0.sum(l0.a, l0.c)
  t1.sum(l1.a, l1.c)
  V.prod2x(t0, t1)
  V.diff2xMod(V, XX)
  V.diff2xMod(V, ZZ)
  f.c1.c1.redc2x(V)

  f.c1.c2.setZero()

# M-Twist
# ------------------------------------------------------------

func mul_sparse_by_line_cb00a0*[Fpk, Fpkdiv6](f: var Fpk, l: Line[Fpkdiv6]) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element coming from an M-Twist line function
  ## with a cubic over quadratic towering (𝔽p2 -> 𝔽p6 -> 𝔽p12)
  ## The sparse element is represented by a packed Line type
  ## with coordinate (a,b,c) matching 𝔽pᵏ coordinates cb00a0

  # a0b0 = (a00, a01, a02).( z, y, 0)
  # a1b1 = (a10, a11, a12).( 0, x, 0)
  #
  # r0 = a0 b0 + ξ a1 b1
  # r1 = a0 b1 + a1 b0                       (Schoolbook)
  #    = (a0 + a1) (b0 + b1) - a0 b0 - a1 b1 (Karatsuba)

  static:
    doAssert Fpk.Name.getSexticTwist() == M_Twist
    doAssert f is QuadraticExt, "This assumes 𝔽pᵏ as a quadratic extension of 𝔽pᵏᐟ²"
    doAssert f.c0 is CubicExt, "This assumes 𝔽pᵏᐟ² as a cubic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv2 = typeof(f.c0)

  when Fpk.Name.has_large_field_elem() or Fpk.Name.skipLazyReduction():
    var
      v0 {.noInit.}: Fpkdiv2
      v1 {.noInit.}: Fpkdiv2
      t  {.noInit.}: Fpkdiv6

    v1.sum(f.c0, f.c1)
    t.sum(l.b, l.a)
    v0.mul_sparse_by_xy0(v1, l.c, t)

    v1.mul_sparse_by_0y0(f.c1, l.a)

    f.c1.diff(v0, v1)

    v0.mul_sparse_by_xy0(f.c0, l.c, l.b)
    f.c1 -= v0

    v1 *= NonResidue
    f.c0.sum(v0, v1)
  else: # Lazy reduction
    var
      V0 {.noInit.}: doubleprec(Fpkdiv2)
      V1 {.noInit.}: doubleprec(Fpkdiv2)
      V  {.noInit.}: doubleprec(Fpkdiv2)
      t  {.noInit.}: Fpkdiv6
      u  {.noInit.}: Fpkdiv2

    u.sum(f.c0, f.c1)
    t.sum(l.b, l.a)
    V.mul2x_sparse_by_xy0(u, l.c, t)
    V1.mul2x_sparse_by_0y0(f.c1, l.a)
    V0.mul2x_sparse_by_xy0(f.c0, l.c, l.b)

    V.diff2xMod(V, V1)
    V.diff2xMod(V, V0)
    f.c1.redc2x(V)

    V1.prod2x(V1, NonResidue)
    V0.sum2xMod(V0, V1)
    f.c0.redc2x(V0)

func prod_zy00x0_zy00x0_into_abcdef00ghij*[Fpk, Fpkdiv6](f: var Fpk, l0, l1: Line[Fpkdiv6]) =
  ## Multiply 2 lines together
  ## The result is sparse in f.c1.c0
  # Preambule
  #
  # A sparse xy0 by xy0 multiplication in 𝔽pᵏᐟ² (cubic) would be
  #   (a0', a1', 0).(b0', b1', 0)
  #
  #   r0' = a0'b0'
  #   r1' = a0'b1 + a1'b0'
  #     or (a0'+b1')(a1'+b0')-a0'a1'-b0'b1'
  #   r2' = a1'b1
  #
  # Note¹ that the Karatsuba does not reuse terms!
  #
  # In the following equations (taken from quad extension implementation)
  # a0 = ( z , y , 0)
  # a1 = ( 0 , x , 0)
  # b0 = ( z', y', 0)
  # b1 = ( 0 , x', 0)
  #
  # a0b0 = ( z, y, 0).(z', y', 0) = (zz', zy'+yz', yy')
  # a1b1 = ( 0, x, 0).( 0, x', 0) = (  0,       0, xx')

  # r0 = a0 b0 + ξ a1 b1
  # r1 = a0 b1 + a1 b0                       (Schoolbook)
  #    = (a0 + a1) (b0 + b1) - a0 b0 - a1 b1 (Karatsuba)
  #
  # Note² that Karatsuba doesn't help as a1 and b1 are actually very cheap (0, x, 0)
  #
  # Replacing by the coordinates in the lower tower we get
  #
  # r0 = (zz'+ξxx', zy'+z'y, yy')
  # r1 = (z, y, 0)(0, x', 0) + (z', y', 0)(0, x, 0)
  #    = (0, zx'+xz', yx'+xy')
  #
  # Now we can apply Karasuba¹² for a total of 6 multiplications

  static:
    doAssert Fpk.Name.getSexticTwist() == M_Twist
    doAssert f is QuadraticExt, "This assumes 𝔽pᵏ as a quadratic extension of 𝔽pᵏᐟ²"
    doAssert f.c0 is CubicExt, "This assumes 𝔽pᵏᐟ² as a cubic extension of 𝔽pᵏᐟ⁶"

  var XX{.noInit.}, YY{.noInit.}, ZZ{.noInit.}: doublePrec(Fpkdiv6)

  XX.prod2x(l0.a, l1.a)
  YY.prod2x(l0.b, l1.b)
  ZZ.prod2x(l0.c, l1.c)

  var V{.noInit.}: doublePrec(Fpkdiv6)
  var t0{.noInit.}, t1{.noInit.}: Fpkdiv6

  # r0 = (zz'+ξxx', zy'+z'y, yy')
  # r00 = zz'+ξxx'
  # r01 = zy'+z'y = (z+y)(z'+y') - zz' - yy'
  # r02 = yy'
  V.prod2x(XX, NonResidue)
  V.sum2xMod(V, ZZ)
  f.c0.c0.redc2x(V)

  t0.sum(l0.c, l0.b)
  t1.sum(l1.c, l1.b)
  V.prod2x(t0, t1)
  V.diff2xMod(V, ZZ)
  V.diff2xMod(V, YY)
  f.c0.c1.redc2x(V)

  f.c0.c2.redc2x(YY)

  # r1 = (0, zx'+xz', yx'+xy')
  # r10 = 0
  # r11 = zx'+xz' = (z+x)(z'+x') - zz' - xx'
  # r12 = xy'+yx' = (x+y)(x'+y') - xx' - yy'
  f.c1.c0.setZero()

  t0.sum(l0.c, l0.a)
  t1.sum(l1.c, l1.a)
  V.prod2x(t0, t1)
  V.diff2xMod(V, ZZ)
  V.diff2xMod(V, XX)
  f.c1.c1.redc2x(V)

  t0.sum(l0.a, l0.b)
  t1.sum(l1.a, l1.b)
  V.prod2x(t0, t1)
  V.diff2xMod(V, XX)
  V.diff2xMod(V, YY)
  f.c1.c2.redc2x(V)

# ############################################################
#
#          𝔽pᵏ by line - 𝔽pᵏ cubic over quadratic
#
# ############################################################

# D-Twist
# ------------------------------------------------------------

func mul_sparse_by_line_acb000*[Fpk, Fpkdiv6](f: var Fpk, l: Line[Fpkdiv6]) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element coming from an D-Twist line function.
  ## with a cubic over quadratic towering (Fp2 -> Fp4 -> Fp12)
  ## The sparse element is represented by a packed Line type
  ## with coordinate (a,b,c) matching 𝔽pᵏ coordinates acb000

  static:
    doAssert Fpk.Name.getSexticTwist() == D_Twist
    doAssert f is CubicExt, "This assumes 𝔽pᵏ as a cubic extension of 𝔽pᵏᐟ³"
    doAssert f.c0 is QuadraticExt, "This assumes 𝔽pᵏᐟ³ as a quadratic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv3 = typeof(f.c0)

  # In the following equations (taken from cubic extension implementation)
  # a = f
  # b0 = (a, c)
  # b1 = (b, 0)
  # b2 = (0, 0)
  #
  # v0 = a0 b0 = (f00, f01).(a, c)
  # v1 = a1 b1 = (f10, f11).(b, 0)
  # v2 = a2 b2 = (f20, f21).(0, 0)
  #
  # r0 = ξ ((a1 + a2) * (b1 + b2) - v1 - v2) + v0
  #    = ξ (a1 b1 + a2 b1 - v1) + v0
  #    = ξ a2 b1 + v0
  # r1 = (a0 + a1) * (b0 + b1) - v0 - v1 + ξ v2
  #    = (a0 + a1) * (b0 + b1) - v0 - v1
  # r2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
  #    = a0 b0 + a2 b0 - v0 + v1
  #    = a2 b0 + v1

  when Fpk.Name.has_large_field_elem() or Fpk.Name.skipLazyReduction():
    var b0 {.noInit.}, v0{.noInit.}, v1{.noInit.}, t{.noInit.}: Fpkdiv3

    b0.c0 = l.a
    b0.c1 = l.c

    v0.prod(f.c0, b0)
    v1.mul_sparse_by_x0(f.c1, l.b)

    # r1 = (a0 + a1) * (b0 + b1) - v0 - v1
    f.c1 += f.c0  # r1 = a0 + a1
    t = b0
    t.c0 += l.b   # t = b0 + b1
    f.c1 *= t     # r2 = (a0 + a1)(b0 + b1)
    f.c1 -= v0
    f.c1 -= v1    # r2 = (a0 + a1)(b0 + b1) - v0 - v1

    # r0 = ξ a2 b1 + v0
    f.c0.mul_sparse_by_x0(f.c2, l.b)
    f.c0 *= SexticNonResidue
    f.c0 += v0

    # r2 = a2 b0 + v1
    f.c2 *= b0
    f.c2 += v1

  else: # Lazy reduction
    var V0{.noInit.}, V1{.noInit.}, f2x{.noInit.}: doublePrec(Fpkdiv3)
    var t{.noInit.}: Fpkdiv6

    V0.prod2x_disjoint(f.c0, l.a, l.c)
    V1.mul2x_sparse_by_x0(f.c1, l.b)

    # r1 = (a0 + a1) * (b0 + b1) - v0 - v1
    f.c1.sum(f.c1, f.c0)
    t.sum(l.a, l.b)                  # b0 is (x, y)
    f2x.prod2x_disjoint(f.c1, t, l.c) # b1 is (z, 0)
    f2x.diff2xMod(f2x, V0)
    f2x.diff2xMod(f2x, V1)
    f.c1.redc2x(f2x)

    # r0 = ξ a2 b1 + v0
    f2x.mul2x_sparse_by_x0(f.c2, l.b)
    f2x.prod2x(f2x, SexticNonResidue)
    f2x.sum2xMod(f2x, V0)
    f.c0.redc2x(f2x)

    # r2 = a2 b0 + v1
    f2x.prod2x_disjoint(f.c2, l.a, l.c)
    f2x.sum2xMod(f2x, V1)
    f.c2.redc2x(f2x)

func prod_xzy000_xzy000_into_abcdefghij00*[Fpk, Fpkdiv6](f: var Fpk, l0, l1: Line[Fpkdiv6]) =
  ## Multiply 2 lines together
  ## The result is sparse in f.c1.c1
  # In the following equations (taken from cubic extension implementation)
  # a0 = ( x, z)
  # a1 = ( y, 0)
  # a2 = ( 0, 0)
  # b0 = (x', z')
  # b1 = (y', 0)
  # b2 = ( 0, 0)
  #
  # v0 = a0 b0 = (x, z).(x', z')
  # v1 = a1 b1 = (y, 0).(y',  0)
  # v2 = a2 b2 = (0, 0).( 0,  0)
  #
  # r0 = ξ ((a1 + a2) * (b1 + b2) - v1 - v2) + v0
  #    = ξ (a1 b1 + a2 b1 - v1) + v0
  #    = v0
  # r1 = (a0 + a1) * (b0 + b1) - v0 - v1 + ξ v2
  #    = (a0 + a1) * (b0 + b1) - v0 - v1
  # r2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
  #    = a0 b0 - v0 + v1
  #    = v1
  #
  # r1 is computed in 3 extra muls in the base field 𝔽pᵏᐟ⁶ (Karatsuba product in quadratic field)
  #
  # If we dive deeper:
  # r1 = a0b1 + a1b0 = (xy'+yx', zy'+yz')      (Schoolbook - 4 muls)
  # r10 = zy'+yz' = (x+y)(x'+y') - xx' - yy'
  # r11 = xy'+yx' = (z+y)(z'+y') - zz' - yy'
  #
  # The substraction are all computed as part of v0 and v1
  # hence r1 can be compute for 2 extra muls in 𝔽pᵏᐟ⁶ only

  static:
    doAssert Fpk.Name.getSexticTwist() == D_Twist
    doAssert f is CubicExt, "This assumes 𝔽pᵏ as a cubic extension of 𝔽pᵏᐟ³"
    doAssert f.c0 is QuadraticExt, "This assumes 𝔽pᵏᐟ³ as a quadratic extension of 𝔽pᵏᐟ⁶"

  when Fpk.Name.skipLazyReduction():
    # Same formulas with single-width products, see `skipLazyReduction`
    var XX{.noInit.}, YY{.noInit.}, ZZ{.noInit.}: Fpkdiv6
    var t0{.noInit.}, t1{.noInit.}: Fpkdiv6

    XX.prod(l0.a, l1.a)
    YY.prod(l0.b, l1.b)
    ZZ.prod(l0.c, l1.c)

    f.c0.c0.prod(ZZ, NonResidue)
    f.c0.c0 += XX

    t0.sum(l0.a, l0.c)
    t1.sum(l1.a, l1.c)
    f.c0.c1.prod(t0, t1)
    f.c0.c1 -= ZZ
    f.c0.c1 -= XX

    t0.sum(l0.a, l0.b)
    t1.sum(l1.a, l1.b)
    f.c1.c0.prod(t0, t1)
    f.c1.c0 -= XX
    f.c1.c0 -= YY

    t0.sum(l0.c, l0.b)
    t1.sum(l1.c, l1.b)
    f.c1.c1.prod(t0, t1)
    f.c1.c1 -= ZZ
    f.c1.c1 -= YY

    f.c2.c0 = YY
    f.c2.c1.setZero()
  else: # Lazy reduction
    var XX{.noInit.}, YY{.noInit.}, ZZ{.noInit.}: doublePrec(Fpkdiv6)

    XX.prod2x(l0.a, l1.a)
    YY.prod2x(l0.b, l1.b)
    ZZ.prod2x(l0.c, l1.c)

    var V{.noInit.}: doublePrec(Fpkdiv6)
    var t0{.noInit.}, t1{.noInit.}: Fpkdiv6

    # r0 = a0 b0 = (x, z).(x', z')
    # r00 = xx' + βzz'
    # r01 = (x+z)(x'+z') - zz' - xx'
    V.prod2x(ZZ, NonResidue)
    V.sum2xMod(V, XX)
    f.c0.c0.redc2x(V)

    t0.sum(l0.a, l0.c)
    t1.sum(l1.a, l1.c)
    V.prod2x(t0, t1)
    V.diff2xMod(V, ZZ)
    V.diff2xMod(V, XX)
    f.c0.c1.redc2x(V)

    # r10 = zy'+yz' = (x+y)(x'+y') - xx' - yy'
    # r11 = xy'+yx' = (z+y)(z'+y') - zz' - yy'
    t0.sum(l0.a, l0.b)
    t1.sum(l1.a, l1.b)
    V.prod2x(t0, t1)
    V.diff2xMod(V, XX)
    V.diff2xMod(V, YY)
    f.c1.c0.redc2x(V)

    t0.sum(l0.c, l0.b)
    t1.sum(l1.c, l1.b)
    V.prod2x(t0, t1)
    V.diff2xMod(V, ZZ)
    V.diff2xMod(V, YY)
    f.c1.c1.redc2x(V)

    # r2 = v2 = (y, 0).(y', 0) = (yy', 0)
    f.c2.c0.redc2x(YY)
    f.c2.c1.setZero()

# M-Twist
# ------------------------------------------------------------

func mul_sparse_by_line_ca00b0*[Fpk, Fpkdiv6](f: var Fpk, l: Line[Fpkdiv6]) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element coming from an M-Twist line function
  ## with a cubic over quadratic towering (Fp2 -> Fp4 -> Fp12)
  ## The sparse element is represented by a packed Line type
  ## with coordinate (a,b,c) matching 𝔽pᵏ coordinates ca00b0

  static:
    doAssert Fpk.Name.getSexticTwist() == M_Twist
    doAssert f is CubicExt, "This assumes 𝔽pᵏ as a cubic extension of 𝔽pᵏᐟ³"
    doAssert f.c0 is QuadraticExt, "This assumes 𝔽pᵏᐟ³ as a cubic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv3 = typeof(f.c0)

  # In the following equations (taken from cubic extension implementation)
  # a = f
  # b0 = (c, a)
  # b1 = (0, 0)
  # b2 = (b, 0)
  #
  # v0 = a0 b0 = (f00, f01).(c, a)
  # v1 = a1 b1 = (f10, f11).(0, 0)
  # v2 = a2 b2 = (f20, f21).(b, 0)
  #
  # r0 = ξ ((a1 + a2) * (b1 + b2) - v1 - v2) + v0
  #    = ξ (a1 b2 + a2 b2 - v2) + v0
  #    = ξ a1 b2 + v0
  # r1 = (a0 + a1) * (b0 + b1) - v0 - v1 + ξ v2
  #    = a0 b0 + a1 b0 - v0 + ξ v2
  #    = a1 b0 + ξ v2
  # r2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
  #    = (a0 + a2) * (b0 + b2) - v0 - v2

  when Fpk.Name.has_large_field_elem() or Fpk.Name.skipLazyReduction():
    var b0 {.noInit.}, v0{.noInit.}, v2{.noInit.}, t{.noInit.}: Fpkdiv3

    b0.c0 = l.c
    b0.c1 = l.a

    v0.prod(f.c0, b0)
    v2.mul_sparse_by_x0(f.c2, l.b)

    # r2 = (a0 + a2) * (b0 + b2) - v0 - v2
    f.c2 += f.c0 # r2 = a0 + a2
    t = b0
    t.c0 += l.b # t = b0 + b2
    f.c2 *= t    # r2 = (a0 + a2)(b0 + b2)
    f.c2 -= v0
    f.c2 -= v2   # r2 = (a0 + a2)(b0 + b2) - v0 - v2

    # r0 = ξ a1 b2 + v0
    f.c0.mul_sparse_by_x0(f.c1, l.b)
    f.c0 *= SexticNonResidue
    f.c0 += v0

    # r1 = a1 b0 + ξ v2
    f.c1 *= b0
    v2 *= SexticNonResidue
    f.c1 += v2

  else: # Lazy reduction
    var V0{.noInit.}, V2{.noInit.}, f2x{.noInit.}: doublePrec(Fpkdiv3)
    var t{.noInit.}: Fpkdiv6

    V0.prod2x_disjoint(f.c0, l.c, l.a)
    V2.mul2x_sparse_by_x0(f.c2, l.b)

    # r2 = (a0 + a2) * (b0 + b2) - v0 - v2
    f.c2.sum(f.c2, f.c0)
    t.sum(l.c, l.b)                  # b0 + b2 = (c+b, a)
    f2x.prod2x_disjoint(f.c2, t, l.a)
    f2x.diff2xMod(f2x, V0)
    f2x.diff2xMod(f2x, V2)
    f.c2.redc2x(f2x)

    # r0 = ξ a1 b2 + v0
    f2x.mul2x_sparse_by_x0(f.c1, l.b)
    f2x.prod2x(f2x, SexticNonResidue)
    f2x.sum2xMod(f2x, V0)
    f.c0.redc2x(f2x)

    # r1 = a1 b0 + ξ v2
    f2x.prod2x_disjoint(f.c1, l.c, l.a)
    V2.prod2x(V2, SexticNonResidue)
    f2x.sum2xMod(f2x, V2)
    f.c1.redc2x(f2x)

func prod_zx00y0_zx00y0_into_abcd00efghij*[Fpk, Fpkdiv6](f: var Fpk, l0, l1: Line[Fpkdiv6]) =
  ## Multiply 2 lines together
  ## The result is sparse in f.c1.c1
  # In the following equations (taken from cubic extension implementation)
  # a0 = ( z,  x)
  # a1 = ( 0,  0)
  # a2 = ( y,  0)
  # b0 = (z', x')
  # b1 = ( 0,  0)
  # b2 = (y',  0)
  #
  # v0 = a0 b0 = (z, x).(z', x')
  # v1 = a1 b1 = (0, 0).(0 , 0)
  # v2 = a2 b2 = (y, 0).(y', 0)
  #
  # r0 = ξ ((a1 + a2) * (b1 + b2) - v1 - v2) + v0
  #    = ξ (a1 b2 + a2 b2 - v2) + v0
  #    = v0
  # r1 = (a0 + a1) * (b0 + b1) - v0 - v1 + ξ v2
  #    = a0 b0 + a1 b0 - v0 + ξ v2
  #    = ξ v2
  # r2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
  #    = (a0 + a2) * (b0 + b2) - v0 - v2
  #
  # r2 is computed in 3 extra muls in the base field 𝔽pᵏᐟ⁶ (Karatsuba product in quadratic field)
  #
  # If we dive deeper:
  # r2 = a0b2 + a2b0 = (zy'+yz', xy'+x'y)      (Schoolbook - 4 muls)
  # r20 = zy'+z'y = (z+y)(z'+y') - zz' - yy'
  # r21 = xy'+x'y = (x+y)(x'+y') - xx' - yy'
  #
  # The substraction are all computed as part of v0 and v2
  # hence r2 can be compute for 2 extra muls in 𝔽pᵏᐟ⁶ only

  static:
    doAssert Fpk.Name.getSexticTwist() == M_Twist
    doAssert f is CubicExt, "This assumes 𝔽pᵏ as a cubic extension of 𝔽pᵏᐟ³"
    doAssert f.c0 is QuadraticExt, "This assumes 𝔽pᵏᐟ³ as a quadratic extension of 𝔽pᵏᐟ⁶"

  when Fpk.Name.skipLazyReduction():
    # Same formulas with single-width products, see `skipLazyReduction`
    var XX{.noInit.}, YY{.noInit.}, ZZ{.noInit.}: Fpkdiv6
    var t0{.noInit.}, t1{.noInit.}: Fpkdiv6

    XX.prod(l0.a, l1.a)
    YY.prod(l0.b, l1.b)
    ZZ.prod(l0.c, l1.c)

    f.c0.c0.prod(XX, NonResidue)
    f.c0.c0 += ZZ

    t0.sum(l0.c, l0.a)
    t1.sum(l1.c, l1.a)
    f.c0.c1.prod(t0, t1)
    f.c0.c1 -= ZZ
    f.c0.c1 -= XX

    f.c1.c0.setZero()
    f.c1.c1 = YY

    t0.sum(l0.c, l0.b)
    t1.sum(l1.c, l1.b)
    f.c2.c0.prod(t0, t1)
    f.c2.c0 -= ZZ
    f.c2.c0 -= YY

    t0.sum(l0.a, l0.b)
    t1.sum(l1.a, l1.b)
    f.c2.c1.prod(t0, t1)
    f.c2.c1 -= XX
    f.c2.c1 -= YY
  else: # Lazy reduction
    var XX{.noInit.}, YY{.noInit.}, ZZ{.noInit.}: doublePrec(Fpkdiv6)

    XX.prod2x(l0.a, l1.a)
    YY.prod2x(l0.b, l1.b)
    ZZ.prod2x(l0.c, l1.c)

    var V{.noInit.}: doublePrec(Fpkdiv6)
    var t0{.noInit.}, t1{.noInit.}: Fpkdiv6

    # r0 = a0 b0 = (z, x).(z', x')
    # r00 = zz' + βxx'
    # r01 = (z+x)(z'+x') - zz' - xx'
    V.prod2x(XX, NonResidue)
    V.sum2xMod(V, ZZ)
    f.c0.c0.redc2x(V)

    t0.sum(l0.c, l0.a)
    t1.sum(l1.c, l1.a)
    V.prod2x(t0, t1)
    V.diff2xMod(V, ZZ)
    V.diff2xMod(V, XX)
    f.c0.c1.redc2x(V)

    # r1 = ξ v2 = ξ(y, 0).(y', 0) = ξ(yy', 0) = (0, yy')
    f.c1.c0.setZero()
    f.c1.c1.redc2x(YY)

    # r20 = zy'+z'y = (z+y)(z'+y') - zz' - yy'
    # r21 = xy'+x'y = (x+y)(x'+y') - xx' - yy'
    t0.sum(l0.c, l0.b)
    t1.sum(l1.c, l1.b)
    V.prod2x(t0, t1)
    V.diff2xMod(V, ZZ)
    V.diff2xMod(V, YY)
    f.c2.c0.redc2x(V)

    t0.sum(l0.a, l0.b)
    t1.sum(l1.a, l1.b)
    V.prod2x(t0, t1)
    V.diff2xMod(V, XX)
    V.diff2xMod(V, YY)
    f.c2.c1.redc2x(V)

# ############################################################
#
#                    Sparse multiplication
#
# ############################################################

func mul_sparse_by_abcdefghij00_quad_over_cube*[Fpk](
       a: var Fpk, b: Fpk) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element abcdefghij00
  ## with each representing 𝔽pᵏᐟ⁶ coordinate

  static:
    doAssert Fpk.Name.getSexticTwist() == D_Twist
    doAssert a is QuadraticExt, "This assumes 𝔽pᵏ as a quadratic extension of 𝔽pᵏᐟ²"
    doAssert a.c0 is CubicExt, "This assumes 𝔽pᵏᐟ² as a cubic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv2 = typeof(a.c0)

  # In the following equations (taken from quadratic extension implementation)
  # b0 = (b00, b01, b02)
  # b1 = (b10, b11,   0)
  #
  # v0 = a0 b0 = (a00, a01, a02).(b00, b01, b02)
  # v1 = a1 b1 = (a10, a11, a12).(b10, b11,   0)
  #
  # r0 = a0 b0 + ξ a1 b1
  # r1 = (a0 + a1) (b0 + b1) - a0 b0 - a1 b1

  when Fpk.Name.has_large_field_elem() or Fpk.Name.skipLazyReduction():
    var v0 {.noInit.}, v1 {.noInit.}, v2 {.noInit.}: Fpkdiv2

    # v2 <- (a0 + a1)(b0 + b1)
    v0.sum(a.c0, a.c1)
    v1.c0.sum(b.c0.c0, b.c1.c0)
    v1.c1.sum(b.c0.c1, b.c1.c1)
    v1.c2 = b.c0.c2
    v2.prod(v0, v1)

    # v0 <- a0 b0
    # v1 <- a1 b1
    v0.prod(a.c0, b.c0)
    v1.mul_sparse_by_xy0(a.c1, b.c1.c0, b.c1.c1)

    # aliasing: a and b unneeded now

    # r1 <- (a0 + a1)(b0 + b1) - a0 b0 - a1 b1
    a.c1.diff(v2, v0)
    a.c1 -= v1

    # r0 <- a0 b0 + β a1 b1
    v1 *= NonResidue
    a.c0.sum(v0, v1)

  else: # Lazy reduction
    var V0 {.noInit.}, V1 {.noInit.}, V2 {.noInit.}: doublePrec(Fpkdiv2)
    var t0{.noInit.}, t1{.noInit.}: Fpkdiv2

    # v2 <- (a0 + a1)(b0 + b1)
    t0.sum(a.c0, a.c1)
    t1.c0.sum(b.c0.c0, b.c1.c0)
    t1.c1.sum(b.c0.c1, b.c1.c1)
    t1.c2 = b.c0.c2
    V2.prod2x(t0, t1)

    # v0 <- a0 b0
    # v1 <- a1 b1
    V0.prod2x(a.c0, b.c0)
    V1.mul2x_sparse_by_xy0(a.c1, b.c1.c0, b.c1.c1)

    # r1 <- (a0 + a1)(b0 + b1) - a0 b0 - a1 b1
    V2.diff2xMod(V2, V0)
    V2.diff2xMod(V2, V1)
    a.c1.redc2x(V2)

    # r0 <- a0 b0 + β a1 b1
    V1.prod2x(V1, NonResidue)
    V2.sum2xMod(V0, V1)
    a.c0.redc2x(V2)

func mul_sparse_by_abcdef00ghij_quad_over_cube*[Fpk](
       a: var Fpk, b: Fpk) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element abcdef00ghij
  ## with each representing 𝔽pᵏᐟ⁶ coordinate

  static:
    doAssert Fpk.Name.getSexticTwist() == M_Twist
    doAssert a is QuadraticExt, "This assumes 𝔽pᵏ as a quadratic extension of 𝔽pᵏᐟ²"
    doAssert a.c0 is CubicExt, "This assumes 𝔽pᵏᐟ² as a cubic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv2 = typeof(a.c0)

  # In the following equations (taken from quadratic extension implementation)
  # b0 = (b00, b01, b02)
  # b1 = (  0, b11, b12)
  #
  # v0 = a0 b0 = (a00, a01, a02).(b00, b01, b02)
  # v1 = a1 b1 = (a10, a11, a12).(  0, b11, b12)
  #
  # r0 = a0 b0 + ξ a1 b1
  # r1 = (a0 + a1) (b0 + b1) - a0 b0 - a1 b1

  when Fpk.Name.has_large_field_elem() or Fpk.Name.skipLazyReduction():
    var v0 {.noInit.}, v1 {.noInit.}, v2 {.noInit.}: Fpkdiv2

    # v2 <- (a0 + a1)(b0 + b1)
    v0.sum(a.c0, a.c1)
    v1.c0 = b.c0.c0
    v1.c1.sum(b.c0.c1, b.c1.c1)
    v1.c2.sum(b.c0.c2, b.c1.c2)
    v2.prod(v0, v1)

    # v0 <- a0 b0
    # v1 <- a1 b1
    v0.prod(a.c0, b.c0)
    v1.mul_sparse_by_0yz(a.c1, b.c1.c1, b.c1.c2)

    # aliasing: a and b unneeded now

    # r1 <- (a0 + a1)(b0 + b1) - a0 b0 - a1 b1
    a.c1.diff(v2, v0)
    a.c1 -= v1

    # r0 <- a0 b0 + β a1 b1
    v1 *= NonResidue
    a.c0.sum(v0, v1)

  else: # Lazy reduction
    var V0 {.noInit.}, V1 {.noInit.}, V2 {.noInit.}: doublePrec(Fpkdiv2)
    var t0{.noInit.}, t1{.noInit.}: Fpkdiv2

    # v2 <- (a0 + a1)(b0 + b1)
    t0.sum(a.c0, a.c1)
    t1.c0 = b.c0.c0
    t1.c1.sum(b.c0.c1, b.c1.c1)
    t1.c2.sum(b.c0.c2, b.c1.c2)
    V2.prod2x(t0, t1)

    # v0 <- a0 b0
    # v1 <- a1 b1
    V0.prod2x(a.c0, b.c0)
    V1.mul2x_sparse_by_0yz(a.c1, b.c1.c1, b.c1.c2)

    # r1 <- (a0 + a1)(b0 + b1) - a0 b0 - a1 b1
    V2.diff2xMod(V2, V0)
    V2.diff2xMod(V2, V1)
    a.c1.redc2x(V2)

    # r0 <- a0 b0 + β a1 b1
    V1.prod2x(V1, NonResidue)
    V2.sum2xMod(V0, V1)
    a.c0.redc2x(V2)


func mul_sparse_by_abcd00efghij_cube_over_quad*[Fpk](
       a: var Fpk, b: Fpk) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element abcd00efghij
  ## with each representing 𝔽pᵏᐟ⁶ coordinate

  static:
    doAssert Fpk.Name.getSexticTwist() == M_Twist
    doAssert a is CubicExt, "This assumes 𝔽pᵏ as a cubic extension of 𝔽pᵏᐟ³"
    doAssert a.c0 is QuadraticExt, "This assumes 𝔽pᵏᐟ³ as a quadratic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv3 = typeof(a.c0)

  # In the following equations (taken from cubic extension implementation)
  # b0 = (b00, b01)
  # b1 = (  0, b11)
  # b2 = (b20, b21)
  #
  # v0 = a0 b0 = (f00, f01).(b00, b01)
  # v1 = a1 b1 = (f10, f11).(  0, b11)
  # v2 = a2 b2 = (f20, f21).(b20, b21)
  #
  # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
  # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁ + β v₂
  # r₂ = (a₀ + a₂) * (b₀ + b₂) - v₀ - v₂ + v₁

  when Fpk.Name.skipLazyReduction():
    # Same formulas with single-width products, see `skipLazyReduction`.
    # Outputs are written so that each one only overwrites inputs no longer needed:
    # r₂ (reads a₀, a₂), then r₁ (reads a₀, a₁), then r₀ from the saved a₁ + a₂.
    var v0 {.noInit.}, v1 {.noInit.}, v2 {.noInit.}: Fpkdiv3
    var s12 {.noInit.}, t0 {.noInit.}, t1 {.noInit.}: Fpkdiv3

    v0.prod(a.c0, b.c0)
    v1.mul_sparse_by_0y(a.c1, b.c1)
    v2.prod(a.c2, b.c2)
    s12.sum(a.c1, a.c2)

    # r₂ = (a₀ + a₂) * (b₀ + b₂) - v₀ - v₂ + v₁
    t0.sum(a.c0, a.c2)
    t1.sum(b.c0, b.c2)
    a.c2.prod(t0, t1)
    a.c2 -= v0
    a.c2 -= v2
    a.c2 += v1

    # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁ + ξ v₂
    t0.sum(a.c0, a.c1)
    t1.c0 = b.c0.c0
    t1.c1.sum(b.c0.c1, b.c1.c1)             # b₁ = (  0, b11)
    a.c1.prod(t0, t1)
    a.c1 -= v0
    a.c1 -= v1
    t0.prod(v2, NonResidue)
    a.c1 += t0

    # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
    t1.c0 = b.c2.c0
    t1.c1.sum(b.c1.c1, b.c2.c1)             # b₁ = (  0, b11)
    a.c0.prod(s12, t1)
    a.c0 -= v1
    a.c0 -= v2
    a.c0 *= NonResidue
    a.c0 += v0
  else: # Lazy reduction
    var V0 {.noInit.}, V1 {.noInit.}, V2 {.noinit.}: doublePrec(Fpkdiv3)
    var t0 {.noInit.}, t1 {.noInit.}: Fpkdiv3
    var f2x{.noInit.}, g2x {.noinit.}: doublePrec(Fpkdiv3)

    V0.prod2x(a.c0, b.c0)
    V1.mul2x_sparse_by_0y(a.c1, b.c1)
    V2.prod2x(a.c2, b.c2)

    # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
    t0.sum(a.c1, a.c2)
    t1.c1.sum(b.c1.c1, b.c2.c1)             # b₁ = (  0, b11)
    f2x.prod2x_disjoint(t0, b.c2.c0, t1.c1) # (a₁ + a₂).(b₁ + b₂)
    f2x.diff2xMod(f2x, V1)
    f2x.diff2xMod(f2x, V2)
    f2x.prod2x(f2x, NonResidue)
    f2x.sum2xMod(f2x, V0)

    # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁
    t0.sum(a.c0, a.c1)
    t1.c1.sum(b.c0.c1, b.c1.c1)             # b₁ = (  0, b11)
    g2x.prod2x_disjoint(t0, b.c0.c0, t1.c1) # (a₀ + a₁).(b₀ + b₁)
    g2x.diff2xMod(g2x, V0)
    g2x.diff2xMod(g2x, V1)

    # r₂ = (a₀ + a₂) and (b₀ + b₂)
    t0.sum(a.c0, a.c2)
    t1.sum(b.c0, b.c2)

    # Now we are aliasing free

    # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
    a.c0.redc2x(f2x)

    # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁ + β v₂
    f2x.prod2x(V2, NonResidue)
    g2x.sum2xMod(g2x, f2x)
    a.c1.redc2x(g2x)

    # r₂ = (a₀ + a₂) * (b₀ + b₂) - v₀ - v₂ + v₁
    f2x.prod2x(t0, t1)
    f2x.diff2xMod(f2x, V0)
    f2x.diff2xMod(f2x, V2)
    f2x.sum2xMod(f2x, V1)
    a.c2.redc2x(f2x)

func mul_sparse_by_abcdefghij00_cube_over_quad*[Fpk](
       a: var Fpk, b: Fpk) =
  ## Sparse multiplication of an 𝔽pᵏ element
  ## by a sparse 𝔽pᵏ element abcdefghij00
  ## with each representing 𝔽pᵏᐟ⁶ coordinate

  static:
    doAssert Fpk.Name.getSexticTwist() == D_Twist
    doAssert a is CubicExt, "This assumes 𝔽pᵏ as a cubic extension of 𝔽pᵏᐟ³"
    doAssert a.c0 is QuadraticExt, "This assumes 𝔽pᵏᐟ³ as a quadratic extension of 𝔽pᵏᐟ⁶"

  type Fpkdiv3 = typeof(a.c0)

  # In the following equations (taken from cubic extension implementation)
  # b0 = (b00, b01)
  # b1 = (b10, b11)
  # b2 = (b20,   0)
  #
  # v0 = a0 b0 = (f00, f01).(b00, b01)
  # v1 = a1 b1 = (f10, f11).(b10, b11)
  # v2 = a2 b2 = (f20, f21).(b20,   0)
  #
  # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
  # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁ + β v₂
  # r₂ = (a₀ + a₂) * (b₀ + b₂) - v₀ - v₂ + v₁

  when Fpk.Name.skipLazyReduction():
    # Same formulas with single-width products, see `skipLazyReduction`.
    # Outputs are written so that each one only overwrites inputs no longer needed:
    # r₁ (reads a₀, a₁), then r₂ (reads a₀, a₂), then r₀ from the saved a₁ + a₂.
    var v0 {.noInit.}, v1 {.noInit.}, v2 {.noInit.}: Fpkdiv3
    var s12 {.noInit.}, t0 {.noInit.}, t1 {.noInit.}: Fpkdiv3

    v0.prod(a.c0, b.c0)
    v1.prod(a.c1, b.c1)
    v2.mul_sparse_by_x0(a.c2, b.c2)
    s12.sum(a.c1, a.c2)

    # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁ + ξ v₂
    t0.sum(a.c0, a.c1)
    t1.sum(b.c0, b.c1)
    a.c1.prod(t0, t1)
    a.c1 -= v0
    a.c1 -= v1
    t0.prod(v2, NonResidue)
    a.c1 += t0

    # r₂ = (a₀ + a₂) * (b₀ + b₂) - v₀ - v₂ + v₁
    t0.sum(a.c0, a.c2)
    t1.c0.sum(b.c0.c0, b.c2.c0)             # b₂ = (b20,   0)
    t1.c1 = b.c0.c1
    a.c2.prod(t0, t1)
    a.c2 -= v0
    a.c2 -= v2
    a.c2 += v1

    # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
    t1.c0.sum(b.c1.c0, b.c2.c0)             # b₂ = (b20,   0)
    t1.c1 = b.c1.c1
    a.c0.prod(s12, t1)
    a.c0 -= v1
    a.c0 -= v2
    a.c0 *= NonResidue
    a.c0 += v0
  else: # Lazy reduction
    var V0 {.noInit.}, V1 {.noInit.}, V2 {.noinit.}: doublePrec(Fpkdiv3)
    var t0 {.noInit.}, t1 {.noInit.}: Fpkdiv3
    var f2x{.noInit.}, g2x {.noinit.}: doublePrec(Fpkdiv3)

    V0.prod2x(a.c0, b.c0)
    V1.prod2x(a.c1, b.c1)
    V2.mul2x_sparse_by_x0(a.c2, b.c2)

    # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
    t0.sum(a.c1, a.c2)
    t1.c0.sum(b.c1.c0, b.c2.c0)             # b₂ = (b20,   0)
    f2x.prod2x_disjoint(t0, t1.c0, b.c1.c1) # (a₁ + a₂).(b₁ + b₂)
    f2x.diff2xMod(f2x, V1)
    f2x.diff2xMod(f2x, V2)
    f2x.prod2x(f2x, NonResidue)
    f2x.sum2xMod(f2x, V0)

    # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁
    t0.sum(a.c0, a.c1)
    t1.sum(b.c0, b.c1)
    g2x.prod2x(t0, t1)
    g2x.diff2xMod(g2x, V0)
    g2x.diff2xMod(g2x, V1)

    # r₂ = (a₀ + a₂) and (b₀ + b₂)
    t0.sum(a.c0, a.c2)
    t1.c0.sum(b.c0.c0, b.c2.c0)             # b₂ = (b20,   0)

    # Now we are aliasing free

    # r₀ = ξ ((a₁ + a₂)(b₁ + b₂) - v₁ - v₂) + v₀
    a.c0.redc2x(f2x)

    # r₁ = (a₀ + a₁) * (b₀ + b₁) - v₀ - v₁ + β v₂
    f2x.prod2x(V2, NonResidue)
    g2x.sum2xMod(g2x, f2x)
    a.c1.redc2x(g2x)

    # r₂ = (a₀ + a₂) * (b₀ + b₂) - v₀ - v₂ + v₁
    f2x.prod2x_disjoint(t0, t1.c0, b.c0.c1)
    f2x.diff2xMod(f2x, V0)
    f2x.diff2xMod(f2x, V2)
    f2x.sum2xMod(f2x, V1)
    a.c2.redc2x(f2x)

# Dispatch
# ------------------------------------------------------------

func mul_by_line*[Fpk, Fpkdiv6](f: var Fpk, line: Line[Fpkdiv6]) {.inline, meter.} =
  ## Multiply an element of Fp12 by a sparse line function
  when Fpk.Name.getSexticTwist() == D_Twist:
    when f is CubicExt:
      f.mul_sparse_by_line_acb000(line)
    else:
      f.mul_sparse_by_line_a00bc0(line)
  elif Fpk.Name.getSexticTwist() == M_Twist:
    when f is CubicExt:
      f.mul_sparse_by_line_ca00b0(line)
    else:
      f.mul_sparse_by_line_cb00a0(line)
  else:
    {.error: "A line function assumes that the curve has a twist".}

func prod_from_2_lines*[Fpk, Fpkdiv6](f: var Fpk, line0, line1: Line[Fpkdiv6]) {.inline, meter.} =
  ## Multiply 2 lines function
  ## and store the result in f
  ## f is overwritten
  when Fpk.Name.getSexticTwist() == D_Twist:
    when f is CubicExt:
      f.prod_xzy000_xzy000_into_abcdefghij00(line0, line1)
    else:
      f.prod_x00yz0_x00yz0_into_abcdefghij00(line0, line1)
  elif Fpk.Name.getSexticTwist() == M_Twist:
    when f is CubicExt:
      f.prod_zx00y0_zx00y0_into_abcd00efghij(line0, line1)
    else:
      f.prod_zy00x0_zy00x0_into_abcdef00ghij(line0, line1)
  else:
    {.error: "A line function assumes that the curve has a twist".}

func mul_by_prod_of_2_lines*[Fpk](f: var Fpk, g: Fpk) {.inline, meter.} =
  ## Multiply f by the somewhat sparse product of 2 lines
  when Fpk.Name.getSexticTwist() == D_Twist:
    when f is CubicExt:
      f.mul_sparse_by_abcdefghij00_cube_over_quad(g)
    else:
      f.mul_sparse_by_abcdefghij00_quad_over_cube(g)
  elif Fpk.Name.getSexticTwist() == M_Twist:
    when f is CubicExt:
      f.mul_sparse_by_abcd00efghij_cube_over_quad(g)
    else:
      f.mul_sparse_by_abcdef00ghij_quad_over_cube(g)
  else:
    {.error: "A line function assumes that the curve has a twist".}

func mul_by_2_lines*[Fpk, Fpkdiv6](f: var Fpk, line0, line1: Line[Fpkdiv6]) {.inline, meter.} =
  ## Multiply f*line0*line1 with lines
  ## f is updated with the result
  var t{.noInit.}: Fpk
  t.prod_from_2_lines(line0, line1)
  f.mul_by_prod_of_2_lines(t)

# func asFpk
