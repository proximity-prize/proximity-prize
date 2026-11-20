import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Fast013
import ProximityPrize.SubmissionLower.Fast015
set_option Elab.async false

section PackSource_K1Defs
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1
noncomputable section

open Polynomial Matrix CoreDefinitions Code
open FrobeniusLocator
open ProximityPrize.Benchmark
open scoped BigOperators

abbrev K := Native.K
abbrev I := Native.I
abbrev Words := Fin 2 → I → K
abbrev node := IRSProfile.domain
abbrev p := Native.p
abbrev Frac := GenericLayer.GenericField K
abbrev Bivar := Polynomial K[X]

def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u Native.radius

/-- A specific genuine decoder and its same-support failure of joint extension. -/
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : K[X]
  agreement : 180265 ≤ support.card
  degree : decoder.degree < 131072
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) 131072 support ∧ ExtendsOn node (u 1) 131072 support)

def ordinary (u : Words) := hankel node (u 0) (u 1) 49193 81879
def twoBlock (u : Words) := stacked p node (u 0) (u 1) 49193 81879
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
  Principal.TypeOneSyndromes node (u 0) (u 1) 131072 p

/-- The generator degree a retains the possible factor at infinity. -/
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : Frac[X]), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ 81879 ∧
    ∀ P : Frac[X], P.natDegree ≤ 81879 →
      (((twoBlock u).map (algebraMap K[X] Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : Frac[X], Q.natDegree ≤ 81879 - a ∧ P = g * Q)

/-- The four coefficient blocks in order 0, 1, p, p+1. -/
def coefficientStack (u : Words) : Matrix (Fin 4 × Fin 49193) (Fin 81880) K := fun i j =>
  if i.1 = 0 then syndrome node (u 0) (i.2.val + j.val) else
  if i.1 = 1 then syndrome node (u 1) (i.2.val + j.val) else
  if i.1 = 2 then syndrome node (u 0) (i.2.val + j.val) ^ p else
    syndrome node (u 1) (i.2.val + j.val) ^ p

def ConstantKernel (u : Words) : Prop :=
  stackRank u = (coefficientStack u).rank

def FrontRemainder (u : Words) : Prop :=
  16 < nullity u ∧ firstRank u = 49193 ∧ ¬ TypeAtMostOne u ∧
    ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u

/-- The degree data for the two-active slice of the actual level ideal. -/
structure TwoActive (u : Words) where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≤ b
  active : b ≤ 81879
  inactive : 81879 < c
  top : c ≤ 131072
  degreeSum : a + b + c = 262146
  nullitySum : nullity u + a + b = 163760
  level : Strata.HasLevelHilbertFunction
    (fun s j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    131072 a b c

def TwoActive.height {u : Words} (T : TwoActive u) := 131073 - T.c

abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) 131072 T.height

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
  output_degree : output.degree < (131072 + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i

/-- Span dimension over K(X), with Z kept as an independent polynomial variable. -/
def columnRank (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ p * V))))

def _root_.K1_8.columnRankAt (q : ℕ) (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ q * V))))

def threeU (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ p * liftX ((β 1).map twist))

def _root_.K1_8.threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))

def threeV (b : K[X]) (α : Fin 2 → K[X]) : Bivar :=
  -(liftX b * (liftX (α 0) + seed * liftX (α 1)))

def sameDirection (U V U' V' : Bivar) : Prop := U * V' = V * U'

def relationOn (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ p) + Polynomial.X (R := K) ^ p * C (u 1 i ^ p)) =
      output.eval (C (node i))

def _root_.K1_8.relationOnAt (q : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
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
  output_degree : output.degree < (131072 + D.height : ℕ)
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
  pencil₀_degree : pencil₀.degree < 131072
  pencil₁_degree : pencil₁.degree < 131072
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
  height_bound : E.natDegree + amplitudeDegree A₀ A₁ ≤ 32680
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
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ 131071 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S

structure AnchoredFamily {u deleted} (M : AnchorModel u deleted) (Γ : Finset K) where
  scalar : K → K[X]
  mark : ∀ γ ∈ Γ, AnchorMark M γ (scalar γ)
  distinct : Set.InjOn scalar (Γ : Set K)

/-- Prefix (initial cover and first proper losses) in the four O8 intervals. -/
def highPrefix (w : ℤ) : ℕ :=
  if w ≤ 3554 then 132117856182247703
  else if w ≤ 8249 then 152632406338780469
  else if w ≤ 23999 then 173266420414027995
  else 200365480316570496

def highRetained (w : ℤ) : ℕ :=
  if w ≤ 3554 then 70121431814589308
  else if w ≤ 8249 then 29823540840290282
  else if w ≤ 23999 then 27620907358581545
  else 34460974021760655

end
end K1
end PackSource_K1Defs

section PackSource_K1Split
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark

/-- The only new algebra at the first five ordered tests. -/
def c1 : Prop :=
  ∀ u, FrontRemainder u → Nonempty (TwoActive u)

def c2 : Prop :=
  ∀ u Γ, nullity u ≤ 16 → BadFamily u Γ → Γ.card ≤ 181966665710181665

def c3 : Prop :=
  ∀ u Γ, firstRank u < 49193 → BadFamily u Γ → Γ.card ≤ 311336

def c4 : Prop :=
  ∀ u Γ, HomogeneousPrincipal u → BadFamily u Γ → Γ.card ≤ 733016280612825

def c5 : Prop :=
  ∀ u Γ, ConstantKernel u → BadFamily u Γ → Γ.card ≤ 174462242734040

def c6 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    MovingGCD R → NormalSaturation R → ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ 1663952278519808

def c7 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T), NormalSaturation R

def c8 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    ¬ MovingGCD R → ¬ InvalidLeft R → NormalSaturation R →
    (∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) →
    ∃ D : Reduction u T R, columnRank D.U D.V = 4 ∨
      ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B

def c9 : Prop :=
  ∀ u (T : TwoActive u) (R : Relation T) (D : Reduction u T R) (B : RankThree u T R D),
    Parallel B → ¬ UnitNorm B → ∀ Γ, BadFamily u Γ → Γ.card ≤ 81880

def c10 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Nonparallel B → ∀ Γ, BadFamily u Γ → Γ.card ≤ 122010899393484555

def c11 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    NormalSaturation R → columnRank D.U D.V = 4 →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 98688882270415481

/-- The anchor constructor on the already normal part of the original input. -/
def c12 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B → ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ 69631486557946 ∨
      ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ 69631486557946 ∧
        ∃ M : AnchorModel u (fixedNodes R), Nonempty (AnchoredFamily M (Γ \ book))

/-- M10, including its own lower-order and parameter exceptions. -/
def c13 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ 2600 →
    Γ.card ≤ 222142013343379695 + 18512789806143368

/-- O8 counts the initial/first-loss and retained strata in the same chart. -/
def c14 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    2601 ≤ M.overhead → M.overhead ≤ 32680 →
    Γ.card ≤ highPrefix M.overhead + highRetained M.overhead

theorem bad_mark (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) (γ : K) (hγ : γ ∈ Γ) :
    Nonempty (BadMark u γ) := by
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ := Strata.native_IsMCA_badSlope u γ (hΓ γ hγ)
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩

theorem mem_normalSlopes {u : Words} {Γ : Finset K} {γ : K} :
    γ ∈ normalSlopes u Γ ↔ γ ∈ Γ ∧ Normal u γ := by
  classical exact Finset.mem_filter

theorem normal_badFamily {u : Words} {Γ : Finset K} (hΓ : BadFamily u Γ) :
    BadFamily u (normalSlopes u Γ) :=
  fun γ hγ => hΓ γ (mem_normalSlopes.mp hγ).1

theorem normal_on_normalSlopes {u : Words} {Γ : Finset K} :
    ∀ γ ∈ normalSlopes u Γ, Normal u γ :=
  fun _ hγ => (mem_normalSlopes.mp hγ).2

theorem firstRank_le (u : Words) : firstRank u ≤ 49193 := by
  simpa only [firstRank, GenericLayer.genericRank, Fintype.card_fin] using
    Matrix.rank_le_card_height ((ordinary u).map (algebraMap K[X] Frac))

theorem actual_stackRank (u : Words) : stackRank u = 81880 - nullity u := by
  have h := GenericLayer.rank_add_nullity (twoBlock u)
  simp only [Fintype.card_fin] at h
  change stackRank u + nullity u = 81880 at h
  omega

theorem rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ 69631486279633 := by
  classical
  apply Strata.native_rank_exception_count node (u 0) (u 1) (nullity u)
    (by have := hu.1; omega) (actual_stackRank u) hu.2.1
  intro γ hγ
  rw [← actual_stackRank u]
  exact (Finset.mem_filter.mp hγ).2

theorem add_rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ b + 69631486279633 := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)]
  exact Nat.add_le_add hb (rank_exceptions u hu Γ)

theorem anchored_list_count {u deleted} (M : AnchorModel u deleted) (Γ : Finset K)
    (F : AnchoredFamily M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ 31911086374011223 := by
  classical
  obtain ⟨hfinite, hprice⟩ := Astra7.native_weighted_complete_list M.word
  have hsub : Γ.image F.scalar ⊆ hfinite.toFinset := by
    intro P hP
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hP
    have mark := F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.scalar_degree with hz | hd
      · rw [hz, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe (131073 : ℕ)
      · have hn : (F.scalar γ).natDegree < 131073 := by omega
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
    _ ≤ 31911086374011223 := hprice

theorem high_with_reserve (w : ℤ) :
    highPrefix w + highRetained w + (69631486279633 + 69631486557946) + 1 ≤
      234965717311168731 := by
  unfold highPrefix highRetained
  split_ifs <;> norm_num

theorem normal_part_of_coherent (h12 : c12) (h13 : c13) (h14 : c14)
    (u : Words) (hu : FrontRemainder u) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D) (hsat : NormalSaturation R)
    (hp : Parallel B) (hn : UnitNorm B)
    (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ 240794066122360642 := by
  classical
  let N := normalSlopes u Γ
  rcases h12 u hu T R D B hsat hp hn N (normal_badFamily hΓ) normal_on_normalSlopes with hcheap | ⟨book, hs, hb, M, ⟨F⟩⟩
  · exact (add_rank_exceptions u hu Γ _ hcheap).trans (by norm_num)
  · have htotal : Γ.card ≤ (N \ book).card + book.card + 69631486279633 :=
      add_rank_exceptions u hu Γ _ (Finset.card_sdiff_add_card_eq_card hs).ge
    have hwmax : M.overhead ≤ 32680 := by
      have hh := M.height_bound
      unfold AnchorModel.overhead
      omega
    by_cases hw₀ : M.overhead ≤ 0
    · have hl := anchored_list_count M _ F hw₀
      omega
    by_cases hwL : M.overhead ≤ 2600
    · have hl := h13 u _ M _ F (by omega) hwL
      omega
    · have hh := h14 u _ M _ F (by omega) hwmax
      have hbnd := high_with_reserve M.overhead
      omega

theorem short_route_bound (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6)
    (h7 : c7) (h8 : c8) (h9 : c9) (h10 : c10) (h11 : c11) (h12 : c12)
    (h13 : c13) (h14 : c14) (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ 240794066122360642 := by
  classical
  by_cases hpref : nullity u ≤ 16
  · exact (h2 u Γ hpref hΓ).trans (by norm_num)
  by_cases hdef : firstRank u < 49193
  · exact (h3 u Γ hdef hΓ).trans (by norm_num)
  by_cases htype : TypeAtMostOne u
  · exact (Native.native_type_one_MCA_count u htype Γ hΓ).trans
      (by norm_num)
  by_cases hprincipal : HomogeneousPrincipal u
  · exact (h4 u Γ hprincipal hΓ).trans (by norm_num)
  by_cases hconstant : ConstantKernel u
  · exact (h5 u Γ hconstant hΓ).trans (by norm_num)
  have hu : FrontRemainder u :=
    ⟨Nat.lt_of_not_ge hpref, Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hdef),
      htype, hprincipal, hconstant⟩
  obtain ⟨T⟩ := h1 u hu
  let R : Relation T := Strata.native_lemmaT_of_two_active_level u (nullity u)
    T.a T.b T.c (by have := hu.1; omega) T.ab T.active T.inactive T.top T.degreeSum T.nullitySum T.level
  have hsat := h7 u hu T R
  by_cases hmoving : MovingGCD R
  · have hmov := h6 u hu T R hmoving hsat (normalSlopes u Γ) (normal_badFamily hΓ)
      normal_on_normalSlopes
    have hwhole : Γ.card ≤ 1733583764799441 := add_rank_exceptions u hu Γ _ hmov
    exact hwhole.trans (by norm_num)
  by_cases hinvalid : InvalidLeft R
  · have hempty : normalSlopes u Γ = ∅ := by
      classical
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨hγΓ, hnormal⟩ := mem_normalSlopes.mp hγ
      obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
      exact (hsat γ hnormal M).valid hinvalid
    exact (add_rank_exceptions u hu Γ 0 (by rw [hempty]; simp)).trans
      (by norm_num)
  by_cases hnormal : (normalSlopes u Γ).Nonempty
  · obtain ⟨γ, hγ⟩ := hnormal
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨D, hfour | ⟨B, hnp | hpar⟩⟩ := h8 u hu T R hmoving hinvalid hsat
      ⟨γ, hnγ, bad_mark u Γ hΓ γ hγΓ⟩
    · have hreg := h11 u hu T R D hsat hfour (normalSlopes u Γ) (normal_badFamily hΓ)
        normal_on_normalSlopes
      have hwhole : Γ.card ≤ 98758513756695114 := add_rank_exceptions u hu Γ _ hreg
      have hfiled : Γ.card ≤ 124821996751784822 := hwhole.trans (by norm_num)
      exact hfiled.trans (by norm_num)
    · exact (h10 u hu T R D B hsat hnp Γ hΓ).trans (by norm_num)
    · by_cases hn : UnitNorm B
      · exact normal_part_of_coherent h12 h13 h14 u hu T R D B hsat hpar hn Γ hΓ
      · exact (h9 u T R D B hpar hn Γ hΓ).trans (by norm_num)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hnormal
    exact (add_rank_exceptions u hu Γ 0 (by rw [he]; simp)).trans
      (by norm_num)

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6)
    (h7 : c7) (h8 : c8) (h9 : c9) (h10 : c10) (h11 : c11) (h12 : c12)
    (h13 : c13) (h14 : c14) : Native.ScalarMCACap6915 := by
  intro u Γ hΓ
  exact (short_route_bound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 u Γ hΓ).trans
    (by norm_num [Astra7.weightedMCAAllowance])

end
end K1
end PackSource_K1Split
