import ProximityPrize.SubmissionLower.Fast077
set_option Elab.async false

section PackSource_P0Defs
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0
noncomputable section

open Polynomial Matrix CoreDefinitions Code
open FrobeniusLocator
open ProximityPrize.Benchmark
open scoped BigOperators NNReal

abbrev K := Native.K
abbrev I := Native.I
abbrev Words := Fin 2 → I → K
abbrev node := IRSProfile.domain
abbrev p := Native.p
abbrev blockLength : ℕ := 262144
abbrev k : ℕ := 131072
abbrev agreement : ℕ := 180208
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev frontLimit : ℕ := 16
abbrev heightCap : ℕ := t + 1 - L - (frontLimit + 1)
abbrev lowCutoff : ℤ := 2480

abbrev radiusNumerator : ℕ := 335613951
abbrev radiusDenominator : ℕ := 1073741824
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius

abbrev scalarCap : ℕ := 242994842185459353
abbrev listCap : ℕ := 31985885925935734
abbrev rankFee : ℕ := 69853079748608
abbrev anchorFee : ℕ := 69853080027186

/-- The augmented weighted list serves both the scalar endpoint and the squared code. -/
def WeightedList : Prop :=
  ∀ word : I → K,
    let S := ReedSolomon.closePolynomialSet node word (k + 1) agreement
    S.Finite ∧ S.ncard ≤ listCap

abbrev Frac := GenericLayer.GenericField K
abbrev Bivar := Polynomial K[X]

def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius

/-- A specific genuine decoder and its same-support failure of joint extension. -/
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : K[X]
  agreement : P0.agreement ≤ support.card
  degree : decoder.degree < k
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) k support ∧ ExtendsOn node (u 1) k support)

def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def firstRank (u : Words) := GenericLayer.genericRank (ordinary u)
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)

def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u

def normalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (Normal u)

def abnormalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Normal u γ)

def TypeAtMostOne (u : Words) : Prop :=
  Principal.TypeOneSyndromes node (u 0) (u 1) k p

/-- The generator degree a retains the possible factor at infinity. -/
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : Frac[X]), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ t ∧
    ∀ P : Frac[X], P.natDegree ≤ t →
      (((twoBlock u).map (algebraMap K[X] Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ P = g * Q)

/-- The four coefficient blocks in order 0, 1, p, p+1. -/
def coefficientBlocks {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x u v : ι → F) (l t : ℕ) : Matrix (Fin 4 × Fin l) (Fin (t + 1)) F :=
  fun i j =>
    if i.1 = 0 then syndrome x u (i.2.val + j.val) else
    if i.1 = 1 then syndrome x v (i.2.val + j.val) else
    if i.1 = 2 then syndrome x u (i.2.val + j.val) ^ p else
      syndrome x v (i.2.val + j.val) ^ p

abbrev coefficientStack (u : Words) := coefficientBlocks p node (u 0) (u 1) L t

def ConstantKernel (u : Words) : Prop :=
  stackRank u = (coefficientStack u).rank

def FrontRemainder (u : Words) : Prop :=
  frontLimit < nullity u ∧ firstRank u = L ∧ ¬ TypeAtMostOne u ∧
    ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u

/-- The degree data for the two-active slice of the actual level ideal. -/
structure TwoActive (u : Words) where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≤ b
  active : b ≤ t
  inactive : t < c
  top : c ≤ k
  degreeSum : a + b + c = 2 * k + 2
  nullitySum : nullity u + a + b = 2 * (t + 1)
  level : Strata.HasLevelHilbertFunction
    (fun s j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    k a b c

def TwoActive.height {u : Words} (T : TwoActive u) := (k + 1) - T.c

abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) k T.height

/-- Inner variable is the seed Z, outer variable is the evaluation coordinate X. -/
def leftU {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (0, j))

def leftV {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (1, j))

def fixedNodes {u : Words} {T : TwoActive u} (R : Relation T) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0

def extendSeed (U : Bivar) : Frac[X] :=
  U.map (algebraMap K[X] Frac)

def IsCommonGCD {F : Type} [Field F] (G U V : F[X]) : Prop :=
  G ≠ 0 ∧ G ∣ U ∧ G ∣ V ∧ ∀ H : F[X], H ∣ U → H ∣ V → H ∣ G

def FixedLeftGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∃ G : K[X], IsCommonGCD (G.map (algebraMap K Frac))
    (extendSeed (leftU R)) (extendSeed (leftV R))

/-- Positive residual common X-degree with no constant-coefficient gcd. -/
def MovingGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ¬ FixedLeftGCD R ∧ ∃ G : Frac[X], G ≠ 0 ∧ G ∣ extendSeed (leftU R) ∧
    G ∣ extendSeed (leftV R) ∧ (fixedNodes R).card < G.natDegree

/-- The condition is on maximum X-height, and fixed divisors include multiplicity. -/
def InvalidLeft {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  max (leftU R).natDegree (leftV R).natDegree < T.height ∨
    ∃ G : K[X], G ≠ 0 ∧ G.map Polynomial.C ∣ leftU R ∧ G.map Polynomial.C ∣ leftV R ∧
      ¬ G ∣ locator node Finset.univ

def atSlope (P : Bivar) (γ : K) : K[X] := P.map (evalRingHom γ)

/-- Normal specialization attains the maximum two-sided height. Its gcd is a
squarefree product on actual nonzero errors of the specific marked decoder. -/
structure SaturatedAt {u : Words} {T : TwoActive u} (R : Relation T)
    {γ : K} (M : BadMark u γ) : Prop where
  U_ne : atSlope (leftU R) γ ≠ 0
  V_ne : atSlope (leftV R) γ ≠ 0
  degree_eq : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree =
    T.height
  gcd_errors : ∃ errors : Finset I,
    (∀ i ∈ errors, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) ∧
    IsCommonGCD (locator node errors) (atSlope (leftU R) γ) (atSlope (leftV R) γ)
  fixed_errors : ∀ i ∈ fixedNodes R, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
  valid : ¬ InvalidLeft R

def NormalSaturation {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∀ γ, Normal u γ → ∀ M : BadMark u γ, SaturatedAt R M

def seed : Bivar := Polynomial.C (R := K[X]) (Polynomial.X (R := K))
def liftX (P : K[X]) : Bivar := P.map Polynomial.C
def twist : K →+* K := frobenius K p

def amplitudeDegree (a₀ a₁ : K[X]) : ℕ := max a₀.natDegree a₁.natDegree

def sixNorm (a : K[X]) : K[X] :=
  ∏ j : Fin 6, a.map (iterateFrobenius K p j.val)

/-- The actual primitive pair and output divided by the fixed node locator.
Every normal bad decoder still has nonzero errors at all the deleted nodes. -/
structure Reduction (u : Words) (T : TwoActive u) (R : Relation T) where
  U : Bivar
  V : Bivar
  output : Bivar
  height : ℕ
  height_eq : height + (fixedNodes R).card = T.height
  max_degree : max U.natDegree V.natDegree = height
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  coprime : IsCoprime (extendSeed U) (extendSeed V)
  U_factor : leftU R = liftX (locator node (fixedNodes R)) * U
  V_factor : leftV R = liftX (locator node (fixedNodes R)) * V
  output_factor : R.output = liftX (locator node (fixedNodes R)) * output
  output_degree : output.degree < (k + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i

/-- Span dimension over K(X), with Z kept as an independent polynomial variable. -/
def columnRank (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ p * V))))

def _root_.P0_4.columnRankAt (q : ℕ) (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ q * V))))

def threeU (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ p * liftX ((β 1).map twist))

def _root_.P0_4.threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))

def _root_.P0_5.threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))

def threeV (b : K[X]) (α : Fin 2 → K[X]) : Bivar :=
  -(liftX b * (liftX (α 0) + seed * liftX (α 1)))

def sameDirection (U V U' V' : Bivar) : Prop := U * V' = V * U'

def relationOn (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ p) + Polynomial.X (R := K) ^ p * C (u 1 i ^ p)) =
      output.eval (C (node i))

def _root_.P0_4.relationOnAt (q : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ q) + Polynomial.X (R := K) ^ q * C (u 1 i ^ q)) =
      output.eval (C (node i))

def _root_.P0_5.relationOnAt (q : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ q) + Polynomial.X (R := K) ^ q * C (u 1 i ^ q)) =
      output.eval (C (node i))

/-- Rank-three canonical shape on the fixed puncture. Beta is stored before conjugation.
The cross identity ties the canonical shape to the actual reduced left pair. -/
structure RankThree (u : Words) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) where
  rank_eq : columnRank D.U D.V = 3
  α : Fin 2 → K[X]
  β : Fin 2 → K[X]
  a : K[X]
  b : K[X]
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  first_degree : a.natDegree + amplitudeDegree (β 0) (β 1) ≤ D.height
  second_degree : b.natDegree + amplitudeDegree (α 0) (α 1) ≤ D.height
  same_direction : sameDirection D.U D.V (threeU a β) (threeV b α)
  output : Bivar
  output_degree : output.degree < (k + D.height : ℕ)
  nodes : relationOn u (fixedNodes R) (threeU a β) (threeV b α) output

def Parallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α = B.β

def Nonparallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α 0 * B.β 1 - B.α 1 * B.β 0 ≠ 0

def UnitNorm {u T R D} (B : RankThree u T R D) : Prop :=
  sixNorm B.a = sixNorm B.b

/-- Translation of the finite seed by one fixed anchor and subtraction of one
degree-<k pencil. The word on deleted coordinates is the chosen zero extension. -/
structure AnchorModel (u : Words) (deleted : Finset I) where
  shift : K
  pencil₀ : K[X]
  pencil₁ : K[X]
  pencil₀_degree : pencil₀.degree < k
  pencil₁_degree : pencil₁.degree < k
  E : K[X]
  factor : K[X]
  Q : K[X]
  A₀ : K[X]
  A₁ : K[X]
  word : I → K
  word_fixed : ∀ i, twist (word i) = word i
  word_deleted : ∀ i ∈ deleted, word i = 0
  E_monic : E.Monic
  E_nodes : ∀ i, E.eval (node i) ≠ 0
  factor_nodes : ∀ i ∉ deleted, factor.eval (node i) ≠ 0
  coprime_factor : IsCoprime E factor
  offset_proper : Q.degree < E.degree
  offset_reduced : IsCoprime Q E
  adjacent_coprime : IsCoprime E (E.map twist)
  amplitudes_primitive : IsCoprime A₀ A₁
  first_amplitude_unit : IsCoprime A₀ E
  height_bound : E.natDegree + amplitudeDegree A₀ A₁ ≤ heightCap
  first_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 0 i + shift * u 1 i - pencil₀.eval (node i)) =
      factor.eval (node i) * A₀.eval (node i) * word i
  second_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 1 i - pencil₁.eval (node i)) =
      Q.eval (node i) + factor.eval (node i) * A₁.eval (node i) * word i

def AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) : ℤ :=
  (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁

def AnchorModel.label {u deleted} (M : AnchorModel u deleted) (γ : K) : K :=
  γ - M.shift

def AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) (γ : K) : K[X] :=
  M.A₀ + Polynomial.C (M.label γ) * M.A₁

def AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K}
    (B : BadMark u γ) : K[X] :=
  B.decoder - M.pencil₀ - Polynomial.C (M.label γ) * M.pencil₁

/-- The original label and original same-support decoder stay attached to its
normalized scalar polynomial. Zero retains degree minus infinity at negative w. -/
structure AnchorMark {u deleted} (M : AnchorModel u deleted) (γ : K) (S : K[X]) where
  bad : BadMark u γ
  avoids_deleted : Disjoint bad.support deleted
  scalar_fixed : S.map twist = S
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ (k : ℤ) - 1 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S

structure AnchoredFamily {u deleted} (M : AnchorModel u deleted) (Γ : Finset K) where
  scalar : K → K[X]
  mark : ∀ γ ∈ Γ, AnchorMark M γ (scalar γ)
  distinct : Set.InjOn scalar (Γ : Set K)

/-- Initial cover and first proper losses in the four O8 intervals. -/
def highPrefix (w : ℤ) : ℕ :=
  if w ≤ 3554 then 80264282550808687
  else if w ≤ 8249 then 87616551433802655
  else if w ≤ 23999 then 92455465993177915
  else 98940427318344470

def highRetained (w : ℤ) : ℕ :=
  if w ≤ 3554 then 158566694353969854
  else if w ≤ 8249 then 44828125060523543
  else if w ≤ 23999 then 27702807103641210
  else 39550082674513474

end
end P0
end PackSource_P0Defs

section PackSource_P0Bridge
set_option autoImplicit true
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false

namespace P0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
open scoped NNReal

/-- The same integer threshold governs both the scalar MCA and squared-code list. -/
theorem support_threshold :
    (Fintype.card I : ℝ) * (1 - radius) = (738127873 : ℝ) / 4096 := by
  rw [IRSProfile.card_index]
  norm_num [radius, queryRadius, claimedRadius]

theorem agreement_of_threshold {s : ℕ}
    (hs : (Fintype.card I : ℝ) * (1 - radius) ≤ s) : agreement ≤ s := by
  rw [support_threshold] at hs
  have hlt : (180207 : ℝ) < (738127873 : ℝ) / 4096 := by norm_num
  have hn : 180207 < s := by exact_mod_cast hlt.trans_le hs
  exact hn

theorem bad_slope (u : Words) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Principal.BadSlope node (u 0) (u 1) k agreement γ := by
  let : NeZero k := ⟨by decide⟩
  exact Principal.isMCA_implies_badSlope node u k agreement radius
    (fun _ hT => agreement_of_threshold hT) γ hγ

theorem bad_mark (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) (γ : K) (hγ : γ ∈ Γ) :
    Nonempty (BadMark u γ) := by
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ := bad_slope u γ (hΓ γ hγ)
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩

private theorem dyadic_mul {a i j x y u v z w e s : ℕ}
    (hi : a ^ i ≤ x * 2 ^ u) (hj : a ^ j ≤ y * 2 ^ v)
    (hc : x * y ≤ z * 2 ^ w) (he : i + j = e) (hs : u + v + w = s) :
    a ^ e ≤ z * 2 ^ s := by
  subst e
  subst s
  calc
    a ^ (i + j) = a ^ i * a ^ j := pow_add ..
    _ ≤ (x * 2 ^ u) * (y * 2 ^ v) := Nat.mul_le_mul hi hj
    _ = (x * y) * 2 ^ (u + v) := by rw [pow_add]; ac_rfl
    _ ≤ (z * 2 ^ w) * 2 ^ (u + v) := Nat.mul_le_mul_right _ hc
    _ = z * (2 ^ (u + v) * 2 ^ w) := by ac_rfl
    _ = z * 2 ^ (u + v + w) := congrArg (z * ·) (pow_add (2 : ℕ) (u + v) w).symm

/-- Upper bounds rounded in 60-bit significands. The kernel checks each
multiplication of two significands, and combines the powers symbolically. -/
private theorem complement_pow_12800 : (738127873 : ℕ) ^ 12800 ≤ 2 ^ 377079 := by
  have h1 : (738127873 : ℕ) ^ 1 ≤ 738127873 * 2 ^ 0 := by decide
  have h2 : (738127873 : ℕ) ^ 2 ≤ 544832756899504129 * 2 ^ 0 :=
    dyadic_mul h1 h1 (z := 544832756899504129) (w := 0) (e := 2)
      (s := 0) (by decide) (by decide) (by decide)
  have h4 : (738127873 : ℕ) ^ 4 ≤ 1029880115184213810 * 2 ^ 58 :=
    dyadic_mul h2 h2 (z := 1029880115184213810) (w := 58) (e := 4)
      (s := 58) (by decide) (by decide) (by decide)
  have h8 : (738127873 : ℕ) ^ 8 ≤ 919969874283452145 * 2 ^ 176 :=
    dyadic_mul h4 h4 (z := 919969874283452145) (w := 60) (e := 8)
      (s := 176) (by decide) (by decide) (by decide)
  have h16 : (738127873 : ℕ) ^ 16 ≤ 734086896815858447 * 2 ^ 412 :=
    dyadic_mul h8 h8 (z := 734086896815858447) (w := 60) (e := 16)
      (s := 412) (by decide) (by decide) (by decide)
  have h24 : (738127873 : ℕ) ^ 24 ≤ 585762194111479411 * 2 ^ 648 :=
    dyadic_mul h16 h8 (z := 585762194111479411) (w := 60) (e := 24)
      (s := 648) (by decide) (by decide) (by decide)
  have h25 : (738127873 : ℕ) ^ 25 ≤ 805347044809385059 * 2 ^ 677 :=
    dyadic_mul h24 h1 (z := 805347044809385059) (w := 29) (e := 25)
      (s := 677) (by decide) (by decide) (by decide)
  have h50 : (738127873 : ℕ) ^ 50 ≤ 1125113652562809267 * 2 ^ 1413 :=
    dyadic_mul h25 h25 (z := 1125113652562809267) (w := 59) (e := 50)
      (s := 1413) (by decide) (by decide) (by decide)
  have h100 : (738127873 : ℕ) ^ 100 ≤ 1097976511085113873 * 2 ^ 2886 :=
    dyadic_mul h50 h50 (z := 1097976511085113873) (w := 60) (e := 100)
      (s := 2886) (by decide) (by decide) (by decide)
  have h200 : (738127873 : ℕ) ^ 200 ≤ 1045650041288578153 * 2 ^ 5832 :=
    dyadic_mul h100 h100 (z := 1045650041288578153) (w := 60) (e := 200)
      (s := 5832) (by decide) (by decide) (by decide)
  have h400 : (738127873 : ℕ) ^ 400 ≤ 948359454202092955 * 2 ^ 11724 :=
    dyadic_mul h200 h200 (z := 948359454202092955) (w := 60) (e := 400)
      (s := 11724) (by decide) (by decide) (by decide)
  have h800 : (738127873 : ℕ) ^ 800 ≤ 780092704300096693 * 2 ^ 23508 :=
    dyadic_mul h400 h400 (z := 780092704300096693) (w := 60) (e := 800)
      (s := 23508) (by decide) (by decide) (by decide)
  have h1600 : (738127873 : ℕ) ^ 1600 ≤ 1055656651160749057 * 2 ^ 47075 :=
    dyadic_mul h800 h800 (z := 1055656651160749057) (w := 59) (e := 1600)
      (s := 47075) (by decide) (by decide) (by decide)
  have h3200 : (738127873 : ℕ) ^ 3200 ≤ 966597431557101649 * 2 ^ 94210 :=
    dyadic_mul h1600 h1600 (z := 966597431557101649) (w := 60) (e := 3200)
      (s := 94210) (by decide) (by decide) (by decide)
  have h6400 : (738127873 : ℕ) ^ 6400 ≤ 810385261233713585 * 2 ^ 188480 :=
    dyadic_mul h3200 h3200 (z := 810385261233713585) (w := 60) (e := 6400)
      (s := 188480) (by decide) (by decide) (by decide)
  have h12800 : (738127873 : ℕ) ^ 12800 ≤ 1139235011231369226 * 2 ^ 377019 :=
    dyadic_mul h6400 h6400 (z := 1139235011231369226) (w := 59) (e := 12800)
      (s := 377019) (by decide) (by decide) (by decide)
  refine h12800.trans ?_
  calc
    1139235011231369226 * 2 ^ 377019 ≤ 2 ^ 60 * 2 ^ 377019 :=
      Nat.mul_le_mul_right _ (by decide)
    _ = 2 ^ (60 + 377019) := (pow_add (2 : ℕ) 60 377019).symm
    _ = 2 ^ 377079 := congrArg (fun e : ℕ => (2 : ℕ) ^ e) (by decide)

theorem score_integer_cross :
    (738127873 : ℕ) ^ 12800 * 2 ^ 6921 ≤ 1073741824 ^ 12800 := by
  calc
    (738127873 : ℕ) ^ 12800 * 2 ^ 6921 ≤ (2 : ℕ) ^ 377079 * 2 ^ 6921 :=
      Nat.mul_le_mul_right _ complement_pow_12800
    _ = (2 ^ 30) ^ 12800 := by
      simp only [← pow_mul, ← pow_add]
    _ = 1073741824 ^ 12800 := congrArg (fun b : ℕ => b ^ 12800) (by decide)

theorem query_score : (1 - queryRadius) ^ IRSProfile.repetitions ≤ claimedError 6921 := by
  have hcomplement : (1 - queryRadius : ℝ≥0) = 738127873 / 1073741824 := by
    apply NNReal.coe_injective
    have hr : queryRadius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [queryRadius, claimedRadius]
    rw [NNReal.coe_sub hr]
    norm_num [queryRadius, claimedRadius]
  change (1 - queryRadius) ^ 128 ≤ claimedError 6921
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (100 : ℕ) ≠ 0)).mp
  rw [← pow_mul, Sol1.C42.claimedError_pow_100, hcomplement]
  change ((738127873 : ℝ≥0) / 1073741824) ^ 12800 ≤ 1 / (2 : ℝ≥0) ^ 6921
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast score_integer_cross

theorem query_admissible : queryRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [queryRadius, claimedRadius, IRSProfile.minRelativeDistance]

/-- Original scalar RS words lie in the proved augmented ordinary polynomial list. -/
theorem finset_scalar_list_card_le (hlist : WeightedList) (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ agreement ≤ agreementCard f w) : P.card ≤ listCap := by
  classical
  have : NeZero (k : ℕ) := ⟨by norm_num⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      ReedSolomon.closePolynomialSet node w (k + 1) agreement := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < (k + 1) := (hdegree f).trans (by norm_num)
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · refine (hP f.val f.property).2.trans (Finset.card_le_card ?_)
      intro i hi
      apply (ReedSolomon.mem_polynomialAgreementSet node w (poly f) i).mpr
      have hfw : f.val i = w i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact (heval f i).trans hfw
  obtain ⟨hfinite,hbound⟩ := hlist w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ listCap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'

theorem list_projection_room : (listCap + 1) ^ 2 ≤ Fintype.card K :=
  projection_room listCap (by decide)

/-- The actual alphabet is Fin2 -> Fin8 -> K; flattening only reindexes its rows. -/
theorem finset_squared_list_card_le (hlist : WeightedList) (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ agreement ≤ agreementCard f w) : P.card ≤ listCap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        agreement ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode agreement listCap list_projection_room
    (finset_scalar_list_card_le hlist) (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount

theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius) : agreement ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by rw [IRSProfile.card_index]; decide
  have hposR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hradius : radius =
      1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I := by
    rw [mul_comm, mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree := (Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) : ℝ) ≤ 1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I by
      rwa [← hradius])
  have hcard : Code.agree f w ≤ agreementCard f w := by
    unfold Code.agree agreementCard
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  exact (agreement_of_threshold hagree).trans hcard

/-- Transfer of the augmented scalar list cap to the actual IRS16 list. -/
theorem squared_lambda_le (hlist : WeightedList) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (listCap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ listCap := by
    apply finset_squared_list_card_le hlist w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (listCap : ℕ∞) := by exact_mod_cast hcard

def nativeBadSlopes (U : Sol1.C64.NativePair) : Finset K := by
  classical
  exact Finset.univ.filter fun γ => IsMCA (AffineLineGenerator K) IRSProfile.code γ U radius

theorem native_cap_of_scalar_cap
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) (U : Sol1.C64.NativePair) :
    (nativeBadSlopes U).card ≤ scalarCap := by
  classical
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius scalarCap
    (by rw [Sol1.C64.native_field_card]; decide)
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp) (nativeBadSlopes U)
  intro γ hγ
  change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
    IRSProfile.code z U radius) at hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [Sol1.C64.native_code_eq] at hγ
  exact hγ

theorem mca_error_le_of_scalar_cap (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius ≤
      (scalarCap : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((nativeBadSlopes U).card : ℝ) / Fintype.card K) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((scalarCap : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast native_cap_of_scalar_cap hscalar U)
        (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

private theorem error_budget :
    (scalarCap + listCap) * 2 ^ 128 ≤ (2130706433 : ℕ) ^ 6 := by decide

theorem gamma_error_le_of_scalar_cap (hlist : WeightedList)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast (squared_lambda_le hlist)
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) radius).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (listCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((scalarCap + listCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Sol1.C64.native_field_card ▸ error_budget :
      (scalarCap + listCap) * 2 ^ 128 ≤ Fintype.card K)
  have hENN : ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe, ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (scalarCap : ENNReal) / Fintype.card K + (listCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_scalar_cap hscalar) hList
    _ = ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget, ProximityGap.prizeThreshold]

/-- Scalar counting and the augmented weighted list suffice at the submitted radius. -/
theorem protocol_claim_of_scalar_cap (hlist : WeightedList)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ProtocolClaim 6921 radiusNumerator radiusDenominator where
  admissible := query_admissible
  reduction := gamma_error_le_of_scalar_cap hlist hscalar
  score := query_score

end
end P0
end PackSource_P0Bridge

section PackSource_P0Front
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0
noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

theorem firstRank_le (u : Words) : firstRank u ≤ L := by
  simpa only [firstRank, GenericLayer.genericRank, Fintype.card_fin] using
    Matrix.rank_le_card_height ((ordinary u).map (algebraMap K[X] Frac))

theorem actual_stackRank (u : Words) : stackRank u = t + 1 - nullity u := by
  have h := GenericLayer.rank_add_nullity (twoBlock u)
  simp only [Fintype.card_fin] at h
  change stackRank u + nullity u = t + 1 at h
  omega

theorem relation_height_balance {u : Words} (T : TwoActive u) :
    L + T.height + nullity u = t + 1 := by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have := T.nullitySum; omega)

theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height ≤ heightCap := by
  have h := relation_height_balance T
  have hr := hu.1
  dsimp only [L, t, heightCap, blockLength, agreement, k, frontLimit] at h hr ⊢
  omega

/-- Construct the actual primitive relation from the two-active level profile. -/
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH := relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)

theorem rank_fee_exact : L + p * heightCap = rankFee := by decide

theorem anchor_fee_exact : p * heightCap + 2 * heightCap + blockLength + 2 = anchorFee := by
  decide

theorem rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankFee := by
  classical
  have h := Strata.two_block_rank_exception_count p node (u 0) (u 1) L t (nullity u)
    (actual_stackRank u) hu.2.1 (abnormalSlopes u Γ) (fun γ hγ => by
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have hs : t + 1 - nullity u - L ≤ heightCap := by
    have hr := hu.1
    dsimp only [L, t, heightCap, blockLength, agreement, k, frontLimit] at hr ⊢
    omega
  exact h.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left p hs) L).trans_eq rank_fee_exact)

private theorem type_one_bad_count_of_syndromes {F ι : Type}
    [Field F] [Fintype ι] [DecidableEq ι] (x u v : ι → F) (hx : Function.Injective x)
    (k a p : ℕ) (hk : k ≤ Fintype.card ι) (hp : 1 < p)
    (htype : Principal.TypeOneSyndromes x u v k p)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k a γ) :
    Γ.card ≤ 1 :=
  Principal.type_one_bad_count x hx u v k a p hk hp htype Γ hΓ

theorem type_one_count (u : Words) (htype : TypeAtMostOne u)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 1 := by
  have hk : k ≤ Fintype.card I := by rw [IRSProfile.card_index]; decide
  exact type_one_bad_count_of_syndromes node (u 0) (u 1) node.injective
    k agreement p hk (by decide) htype Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))

/-- K1_3's ordinary rank bound is already generic in the dimensions. -/
theorem deficient_count (u : Words) (Γ : Finset K) (hrank : firstRank u < L)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 311279 := by
  have h := K1_3.deficient_hankel_count node (u 0) (u 1) node.injective
    k L t (firstRank u) (by rw [IRSProfile.card_index]; decide) hrank rfl Γ
    (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans (Nat.add_le_add_left (Nat.le_of_lt_succ hrank) blockLength)

/-- The homogeneous cutoff retains the generator's degree at infinity. -/
theorem principal_count (u : Words) (Γ : Finset K) (hprincipal : HomogeneousPrincipal u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 733137730879506 := by
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (t - a) = t := by omega
  let φ := algebraMap K[X] Frac
  have hcertificate : Principal.PrincipalAt
      (fun b j => φ (Principal.parameterSyndromes p node (u 0) (u 1) b j)) k a (t - a) := by
    refine { generator := g, nonzero := hg, degree_bound := hga, kernel_eq := ?_ }
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ t ∧ ((twoBlock u).map φ).mulVec (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ t :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  have h := Principal.generic_principal_bad_count_coarse φ
    (IsFractionRing.injective K[X] Frac) p (by decide) node node.injective
    Native.native_domain_fixed (u 0) (u 1) k k a (t - a)
    (by rw [IRSProfile.card_index]; decide)
    (hsum.trans_lt (show t < k by decide)) hcertificate Γ (fun γ hγ => by
      rw [hsum]
      exact bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans ((Nat.mul_le_mul_left p (Nat.add_le_add_left ha blockLength)).trans (by decide))

variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- A common coefficient-kernel vector annihilates the whole polynomial pencil. -/
private theorem coefficientKernel_annihilates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c : Fin (t + 1) → F) (hc : (coefficientBlocks p x u v L t).mulVec c = 0) :
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0 := by
  funext i
  have h0 := congrFun hc (0, i.2)
  have h1 := congrFun hc (1, i.2)
  have h2 := congrFun hc (2, i.2)
  have h3 := congrFun hc (3, i.2)
  simp only [Matrix.mulVec, dotProduct, coefficientBlocks, Fin.reduceEq,
    ite_true, ite_false, Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi : i.1 = 0
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_true, hankel, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) * c j) +
          Polynomial.X (R := F) * C (∑ j, syndrome x v (i.2.val + j.val) * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h0, h1, map_zero, mul_zero, add_zero]
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_false, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) ^ p * c j) +
          Polynomial.X (R := F) ^ p * C (∑ j, syndrome x v (i.2.val + j.val) ^ p * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h2, h3, map_zero, mul_zero, add_zero]

/-- Equal ranks give a fixed kernel of the correct dimension for the normal-fiber count. -/
private theorem constantRankCount {E : Type} [Field E]
    (φ : F[X] →+* E) (hφ : Function.Injective φ) (p : ℕ) [ExpChar F p] (hp : 1 ≤ p)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t : ℕ) (hkA : k < A) (hL : k + L = A)
    (ht : A + t = Fintype.card ι)
    (r : ℕ) (hgeneric : ((stacked p x u v L t).map φ).rank = r)
    (hconstant : (coefficientBlocks p x u v L t).rank = r)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k A γ) : Γ.card ≤ p * r := by
  let M := stacked p x u v L t
  let C₀ := coefficientBlocks p x u v L t
  let W := LinearMap.ker C₀.mulVecLin
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r hgeneric
  have hWdim : Module.finrank F W = t + 1 - r := by
    have h := LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
    change (coefficientBlocks p x u v L t).rank + Module.finrank F W = _ at h
    rw [hconstant, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hW (c : Fin (t + 1) → F) (hc : c ∈ W) :
      M.mulVec (fun j => C (c j)) = 0 :=
    coefficientKernel_annihilates p x u v L t c hc
  have hminor : (NormalFiber.pivot B).det.natDegree ≤ p * r := by
    have h := NormalFiber.minor_degree_le φ M r B (fun _ => p) (by
      intro i j
      exact (stacked_entry_natDegree p x u v L t i j).trans (by split_ifs <;> omega))
    simpa [Nat.mul_comm] using h
  exact Principal.constant_kernel_count p x hx hfixed u v k A L t (p * r) hkA hL ht
    _ B.minor_ne hminor (Principal.constantCertificateOfRowBasis φ hφ p x u v L t r B W hWdim hW)
    Γ hΓ

theorem constant_count (u : Words) (Γ : Finset K) (hu : ConstantKernel u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 174583693000721 := by
  let φ := algebraMap K[X] Frac
  have hrank : ((twoBlock u).map φ).rank = stackRank u := rfl
  have hconstant : (coefficientBlocks p node (u 0) (u 1) L t).rank = stackRank u := hu.symm
  have hcount := constantRankCount φ (IsFractionRing.injective K[X] Frac)
    p (by decide) node node.injective Native.native_domain_fixed
    (u 0) (u 1) k agreement L t (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide) (stackRank u) hrank hconstant
    Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  have hr : stackRank u ≤ t + 1 := by
    rw [actual_stackRank]
    exact Nat.sub_le _ _
  exact hcount.trans ((Nat.mul_le_mul_left p hr).trans_eq (by decide))

open K1_1

private def nativeMoments (u : Words) : Fin 2 → ℕ → Frac :=
  fun b j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) b j)

private theorem independent_nativeMoments (u : Words)
    (h : ¬ TypeAtMostOne u) : IndependentMoments (nativeMoments u) k := by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective K[X] Frac
  simpa [nativeMoments, Principal.parameterSyndromes, map_mul] using hall i j

private theorem locator_matrix (u : Words) :
    Principal.recurrenceMatrix (nativeMoments u) k t =
      (twoBlock u).map (algebraMap K[X] Frac) :=
  Principal.recurrenceMatrix_parameter (algebraMap K[X] Frac)
    p node (u 0) (u 1) k t

private theorem locator_nullity (u : Words) :
    sliceDim (nativeMoments u) k (t + 1) = nullity u := by
  rw [sliceDim_succ (nativeMoments u) k t, locator_matrix]
  rfl

private theorem principal_of_one_active (u : Words) (a : ℕ) (ha : a ≤ t)
    (hone : sliceDim (nativeMoments u) k (a+1) = 1)
    (hnull : nullity u = (t + 1)-a) : HomogeneousPrincipal u := by
  have hpos : 0 < sliceDim (nativeMoments u) k (a+1) := by omega
  have hdim : sliceDim (nativeMoments u) k (t + 1) = (t-a)+1 := by
    rw [locator_nullity]
    omega
  obtain ⟨g, hg, hdeg, hfac⟩ := principal_of_slice (nativeMoments u) k a t
    ha (by decide) hpos hdim
  refine ⟨a, g, hg, hdeg, ha, fun P hP => ?_⟩
  rw [← locator_matrix]
  exact hfac P hP

theorem two_active (u : Words) (hu : FrontRemainder u) : Nonempty (TwoActive u) := by
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) k (independent_nativeMoments u hu.2.2.1)
  have hloc := hdim (t + 1) (by decide)
  rw [locator_nullity] at hloc
  have hpos := hu.1
  have hthree : 3 * t < 2 * k + 2 := by decide
  have hinactive : t < c := by omega
  have ha : a ≤ t := by omega
  have hb : b ≤ t := by
    by_contra hb
    have hsmall := hdim (a+1) (by omega)
    exact hu.2.2.2.1 (principal_of_one_active u a ha (by omega) (by omega))
  refine ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega, ?_⟩⟩
  exact level_of_profile _ _ _ _ _ hdim

end
end P0
end PackSource_P0Front

section PackSource_P0Split
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark

/-- Universal small-nullity prefix (old K1.c2). -/
def c1 : Prop :=
  ∀ u Γ, nullity u ≤ frontLimit → BadFamily u Γ → Γ.card ≤ 181129482207495641

/-- Moving gcd, on the normal labels (old K1.c6). -/
def c2 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    MovingGCD R → NormalSaturation R → ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ 1678388363264000

/-- Normal specialization of the actual relation (old K1.c7). -/
def c3 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T), NormalSaturation R

/-- Divide out the fixed node locator and classify the columns (old K1.c8). -/
def c4 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    ¬ MovingGCD R → ¬ InvalidLeft R → NormalSaturation R →
    (∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) →
    ∃ D : Reduction u T R, columnRank D.U D.V = 4 ∨
      ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B

/-- Parallel proper norm, on the whole input (old K1.c9). -/
def c5 : Prop :=
  ∀ u (T : TwoActive u) (R : Relation T) (D : Reduction u T R) (B : RankThree u T R D),
    Parallel B → ¬ UnitNorm B → ∀ Γ, BadFamily u Γ → Γ.card ≤ t + 1

/-- Nonparallel rank three, on normal labels using the (1,1) quotient (old K1.c10). -/
def c6 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Nonparallel B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 117234678145547609

/-- Rank four, on normal labels using the eight exact weight banks (old K1.c11). -/
def c7 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    NormalSaturation R → columnRank D.U D.V = 4 →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 160381081648094588

/-- One anchor model on the normal part, after its exceptional book (old K1.c12). -/
def c8 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ anchorFee ∨
      ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ anchorFee ∧
        ∃ M : AnchorModel u (fixedNodes R), Nonempty (AnchoredFamily M (Γ \ book))

/-- M10, including its lower-order and parameter exceptions (old K1.c13). -/
def c9 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ lowCutoff →
    Γ.card ≤ 214480139679075858 + 18479566821206575

/-- O8 prefix and retained fees, including one optional chart label (old K1.c14). -/
def c10 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    Γ.card ≤ highPrefix M.overhead + highRetained M.overhead + 1

/-- The agreement-dependent source and consumer of the augmented weighted list. -/
def c11 : Prop := WeightedList

theorem mem_normalSlopes {u : Words} {Γ : Finset K} {γ : K} :
    γ ∈ normalSlopes u Γ ↔ γ ∈ Γ ∧ Normal u γ := by
  classical exact Finset.mem_filter

theorem normal_badFamily {u : Words} {Γ : Finset K} (hΓ : BadFamily u Γ) :
    BadFamily u (normalSlopes u Γ) :=
  fun γ hγ => hΓ γ (mem_normalSlopes.mp hγ).1

theorem normal_on_normalSlopes {u : Words} {Γ : Finset K} :
    ∀ γ ∈ normalSlopes u Γ, Normal u γ :=
  fun _ hγ => (mem_normalSlopes.mp hγ).2

theorem add_rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ b + rankFee := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)]
  exact Nat.add_le_add hb (rank_exceptions u hu Γ)

theorem anchored_list_count (hlist : WeightedList) {u deleted} (M : AnchorModel u deleted)
    (Γ : Finset K) (F : AnchoredFamily M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ listCap := by
  classical
  obtain ⟨hfinite, hprice⟩ := hlist M.word
  have hsub : Γ.image F.scalar ⊆ hfinite.toFinset := by
    intro P hP
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hP
    have mark := F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.scalar_degree with hz | hd
      · rw [hz, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe (k + 1)
      · have hn : (F.scalar γ).natDegree < k + 1 := by omega
        exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hn)
    · apply mark.bad.agreement.trans
      apply Finset.card_le_card
      intro i hi
      simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact mark.scalar_hits i hi
  calc
    Γ.card = (Γ.image F.scalar).card := (Finset.card_image_of_injOn F.distinct).symm
    _ ≤ hfinite.toFinset.card := Finset.card_le_card hsub
    _ = _ := (Set.ncard_eq_toFinset_card _ hfinite).symm
    _ ≤ listCap := hprice

private theorem high_with_reserve (w : ℤ) :
    highPrefix w + highRetained w + 1 + anchorFee + rankFee ≤ scalarCap := by
  unfold highPrefix highRetained
  split_ifs <;> decide

private theorem coherent_count (h8 : c8) (h9 : c9) (h10 : c10) (hlist : WeightedList)
    (u : Words) (hu : FrontRemainder u) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D) (hsat : NormalSaturation R)
    (hp : Parallel B) (hn : UnitNorm B) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ scalarCap := by
  classical
  let N := normalSlopes u Γ
  rcases h8 u hu T R D B hsat hp hn N (normal_badFamily hΓ) normal_on_normalSlopes with
    hcheap | ⟨book, hs, hb, M, ⟨F⟩⟩
  · exact (add_rank_exceptions u hu Γ _ hcheap).trans (by decide)
  · have htotal : Γ.card ≤ (N \ book).card + book.card + rankFee :=
      add_rank_exceptions u hu Γ _ (Finset.card_sdiff_add_card_eq_card hs).ge
    have hreserve (b : ℕ) (h : (N \ book).card ≤ b) : Γ.card ≤ b + anchorFee + rankFee :=
      htotal.trans (Nat.add_le_add_right (Nat.add_le_add h hb) rankFee)
    have hwmax : M.overhead ≤ (heightCap : ℤ) := by
      have hh := M.height_bound
      unfold AnchorModel.overhead
      omega
    by_cases hw₀ : M.overhead ≤ 0
    · exact (hreserve _ (anchored_list_count hlist M _ F hw₀)).trans (by decide)
    by_cases hwL : M.overhead ≤ lowCutoff
    · exact (hreserve _ (h9 u _ M _ F (by omega) hwL)).trans (by decide)
    · exact (hreserve _ (h10 u _ M _ F (by omega) hwmax)).trans (high_with_reserve M.overhead)

private theorem scalar_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) (h7 : c7) (h8 : c8) (h9 : c9) (h10 : c10) (hlist : WeightedList)
    (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ scalarCap := by
  classical
  by_cases hpref : nullity u ≤ frontLimit
  · exact (h1 u Γ hpref hΓ).trans (by decide)
  by_cases hdef : firstRank u < L
  · exact (deficient_count u Γ hdef hΓ).trans (by decide)
  by_cases htype : TypeAtMostOne u
  · exact (type_one_count u htype Γ hΓ).trans (by decide)
  by_cases hprincipal : HomogeneousPrincipal u
  · exact (principal_count u Γ hprincipal hΓ).trans (by decide)
  by_cases hconstant : ConstantKernel u
  · exact (constant_count u Γ hconstant hΓ).trans (by decide)
  have hu : FrontRemainder u :=
    ⟨Nat.lt_of_not_ge hpref, Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hdef),
      htype, hprincipal, hconstant⟩
  obtain ⟨T⟩ := two_active u hu
  let R := relation_of_two_active hu T
  have hsat := h3 u hu T R
  let N := normalSlopes u Γ
  have hN := normal_badFamily hΓ
  have hnormal := @normal_on_normalSlopes u Γ
  by_cases hmoving : MovingGCD R
  · exact (add_rank_exceptions u hu Γ _ (h2 u hu T R hmoving hsat N hN hnormal)).trans
      (by decide)
  have hnone (he : N = ∅) : Γ.card ≤ scalarCap :=
    (add_rank_exceptions u hu Γ 0 (by rw [show normalSlopes u Γ = ∅ from he]; simp)).trans
      (by decide)
  by_cases hinvalid : InvalidLeft R
  · apply hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact (hsat γ hnγ M).valid hinvalid
  by_cases hne : N.Nonempty
  · obtain ⟨γ, hγ⟩ := hne
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨D, hfour | ⟨B, hnp | hpar⟩⟩ := h4 u hu T R hmoving hinvalid hsat
      ⟨γ, hnγ, bad_mark u Γ hΓ γ hγΓ⟩
    · exact (add_rank_exceptions u hu Γ _ (h7 u hu T R D hsat hfour N hN hnormal)).trans
        (by decide)
    · exact (add_rank_exceptions u hu Γ _ (h6 u hu T R D B hsat hnp N hN hnormal)).trans
        (by decide)
    · by_cases hn : UnitNorm B
      · exact coherent_count h8 h9 h10 hlist u hu T R D B hsat hpar hn Γ hΓ
      · exact (h5 u T R D B hpar hn Γ hΓ).trans (by decide)
  · exact hnone (Finset.not_nonempty_iff_eq_empty.mp hne)

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) (h7 : c7) (h8 : c8) (h9 : c9) (h10 : c10) (h11 : c11) :
    ProtocolClaim 6921 335613951 1073741824 :=
  protocol_claim_of_scalar_cap h11 (scalar_count h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

end
end P0
end PackSource_P0Split
