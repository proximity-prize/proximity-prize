import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.NNRat.Floor
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ProximityPrize.SubmissionLower.Fast015
set_option autoImplicit true
section
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
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : K[X]
  agreement : 180265 ≤ support.card
  degree : decoder.degree < 131072
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) 131072 support ∧ ExtendsOn node (u 1) 131072 support)
def ordinary (u : Words) := hankel node (u 0) (u 1) 49193 81879
def twoBlock (u : Words) := stacked p node (u 0) (u 1) 49193 81879
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
def coefficientStack (u : Words) : Matrix (Fin 4 × Fin 49193) (Fin 81880) K := fun i j =>
  if i.1 = 0 then syndrome node (u 0) (i.2.val + j.val) else
  if i.1 = 1 then syndrome node (u 1) (i.2.val + j.val) else
  if i.1 = 2 then syndrome node (u 0) (i.2.val + j.val) ^ p else
    syndrome node (u 1) (i.2.val + j.val) ^ p
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
def InvalidLeft {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  max (leftU R).natDegree (leftV R).natDegree < T.height ∨
    ∃ G : K[X], G ≠ 0 ∧ G.map Polynomial.C ∣ leftU R ∧ G.map Polynomial.C ∣ leftV R ∧
      ¬ G ∣ locator node Finset.univ
def atSlope (P : Bivar) (γ : K) : K[X] := P.map (evalRingHom γ)
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
def seed : Bivar := Polynomial.C (R := K[X]) (Polynomial.X (R := K))
def liftX (P : K[X]) : Bivar := P.map Polynomial.C
def twist : K →+* K := frobenius K p
def amplitudeDegree (a₀ a₁ : K[X]) : ℕ := max a₀.natDegree a₁.natDegree
def sixNorm (a : K[X]) : K[X] :=
  ∏ j : Fin 6, a.map (iterateFrobenius K p j.val)
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
def highPrefix (w : ℤ) : ℕ :=
  if w ≤ 3554 then 132117856182247703
  else if w ≤ 8249 then 152632406338780469
  else if w ≤ 23999 then 173266420414027995
  else 200365480316570496
end
end K1
end
section
namespace K1_13
noncomputable section
open Polynomial K1
open scoped BigOperators
abbrev Geom := AlgebraicClosure K
abbrev embed := algebraMap K Geom
abbrev extend (S : K[X]) := S.map embed
abbrev Row (n : ℕ) := MvPolynomial (Fin n) Geom[X]
def jet (S : Geom[X]) {n : ℕ} (i : Fin n) : Geom[X] := hasseDeriv i.val S
def atJet {n : ℕ} (P : Row n) (S : Geom[X]) : Geom[X] :=
  MvPolynomial.eval (jet S) P
def shiftJet {n : ℕ} (P : Row n) (S : Geom[X]) : Row n :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P
def OrderAt {n : ℕ} (P : Row n) (S : Geom[X]) (d : ℕ) : Prop :=
  ∀ m ∈ (shiftJet P S).support, d ≤ m.sum (fun _ a => a)
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (133671 - i.val) * a) ≤ D
def indexDegree {n : ℕ} (P : Row n) : ℕ :=
  P.support.sup (fun m => m.sum (fun i a => i.val * a))
structure Shape where
  b : ℕ
  j : ℕ
  t : ℕ
  deriving DecidableEq
def shape (P : Row 4) : Shape := ⟨P.totalDegree, indexDegree P, P.degreeOf 3⟩
def InBox (x y : Shape) : Prop := x.b ≤ y.b ∧ x.j ≤ y.j ∧ x.t ≤ y.t
def Fits {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, 1 ≤ (a i).t ∧ 3 * (a i).t ≤ (a i).j ∧ (a i).j ≤ 3 * (a i).b) ∧
  (∑ i, (a i).b) ≤ 120 ∧ (∑ i, (a i).j) ≤ 48 ∧ (∑ i, (a i).t) ≤ 10
structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 133671
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 180265 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
structure PoleData (Γ : Finset K) (s : K → K[X]) where
  H : Geom[X]
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ 2600
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 131071 + H.natDegree
  z : K → Geom
  injective : Function.Injective z
  c : Geom[X]
  q : Geom[X]
  a₀ : Geom[X]
  a₁ : Geom[X]
  c_unit : IsCoprime c H
  q_unit : IsCoprime q H
  a₀_unit : IsCoprime a₀ H
  regular : ∀ γ ∈ Γ, IsCoprime (a₀ + C (z γ) * a₁) H
  residue : ∀ γ ∈ Γ, H ∣ c * (a₀ + C (z γ) * a₁) * extend (s γ) + C (z γ) * q
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f (90 * 180265 - 1)
def topLead (f : Row 4) (S : Geom[X]) : Geom[X] :=
  (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => if i = 3 then Polynomial.X else Polynomial.C (jet S i)) f).coeff (shape f).t
def OnFactor (f : Row 4) (S : Geom[X]) : Prop :=
  atJet f S = 0 ∧ topLead f S ≠ 0
def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ indexDegree g ≤ 48 ∧ TrueWeightLE g (90 * 180265 - 1)
structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, atJet g (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))
def Contact (w : I → K) (P : Row 4) : Prop :=
  ∀ i (S : Geom[X]), S.eval (embed (node i)) = embed (w i) →
    (Polynomial.X - C (embed (node i))) ^ 3000 ∣ atJet P S
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ 6300
  common_index : indexDegree common ≤ 2403
  residual_total : residual.totalDegree ≤ 952630000
  residual_index : indexDegree residual ≤ 322000000
def symbols (b j : ℕ) : ℕ :=
  ∑ z ∈ Finset.range (min b (j / 3) + 1),
  ∑ y ∈ Finset.range (min (b - z) ((j - 3*z) / 2) + 1),
  ∑ x ∈ Finset.range (min (b - z - y) (j - 3*z - 2*y) + 1), (b - z - y - x + 1)
def remaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then symbols (4012 - b) (1650 - j) else 0
def Shape.plus (p q : Shape) : Shape := ⟨p.b + q.b, p.j + q.j, p.t + q.t⟩
def Shape.scale (p : Shape) (k : ℕ) : Shape := ⟨k*p.b, k*p.j, k*p.t⟩
def Shape.chamber (p : Shape) : Shape := ⟨max p.b p.j, p.j, p.t⟩
def volume32 (p : Shape) : ℤ :=
  let b : ℤ := p.b
  let j : ℤ := p.j
  let t : ℤ := p.t
  8*b*j^2*t - 24*b*j*t^2 + 24*b*t^3 - 4*j^3*t + 14*j^2*t^2 - 20*j*t^3 + 9*t^4
def difference (h : Shape → ℤ) (a x : Shape) := h (x.plus a) - h x
def mixed32 (p q r s : Shape) : ℕ :=
  (difference (difference (difference (difference volume32 p) q) r) s ⟨0,0,0⟩).toNat
def ceilDiv (a b : ℕ) := (a + b - 1) / b
abbrev taylorLength : ℕ := 133672
def chart (L : ℕ) (p : Shape) : Shape :=
  let i := 2*L*(p.j - 3) + L + 3
  ⟨max (1 + 2*L*(p.b - 1)) i, i, min (2*L*(p.t - 1) + L + 1) (i / 3)⟩
def liftedChart (L : ℕ) (p : Shape) : Shape :=
  let i := 4 + (L - 5)*(p.j - 2)
  ⟨max (1 + (L - 5)*(p.b - 1)) i, i, min (2 + (L - 5)*p.t) (i / 3)⟩
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength*(p.j - 2)
  ⟨max (1 + taylorLength*(p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L+1) p
  let b := liftedChart (L+2) p
  min (mixed32 p q (chart (L+1) p) (chart (L+2) p))
    (mixed32 p q a b + (L+1) * mixed32 p q g b + (L+2) * mixed32 p q g a)
def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q : Shape := ⟨4013, 1650, 550⟩
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((81879 + 2*46594) * x.b * q.b * (chart (taylorLength+1) p).b) 46594
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2*x.t*mixed32 p p p h
  let points := mixed32 p q auxBox p + 2*x.t*mixed32 p p p p
  ceilDiv numerator l + 2*133671*x.b*q.b + ceilDiv (81879*curves + 2*46594*points) (32*46594)
def FatEligible (x : Shape) : Prop := x.b ≤ 60 ∧ x.j ≤ 32
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := ⟨952630000, 322000000, 0⟩
  let big : Shape := ⟨35007, 12106, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j+1)), max h.j (big.j+1), max 1 h.t⟩
  let divisors := ceilDiv (81879 * mixed32 p big cut h) (32*46594) +
    ceilDiv (mixed32 p big cut p) 32 + 20*p.b*h.b^2 + 5*133671*p.b*h.b + 1
  let singular := if 1 < x.t then ceilDiv (4*x.t*mixed32 p p h h) 32 + x.t*x.b^2+1 else 0
  let curves := ceilDiv (81879*mixed32 p q q h + 46594*mixed32 p q q p) (32*46594*293711590)
  let isolated := ceilDiv (3*q.j^2*(2*q.b - q.j)) (4*41481*(41481 - 33184 + 1)*1037)
  divisors + singular + curves + isolated
end
end K1_13
end
section
namespace K1_13
noncomputable section
open Polynomial K1
open scoped BigOperators
theorem trim_divisor (P : Geom[X]) (hm : P.Monic) (h : ℕ) (hh : h ≤ P.natDegree) :
    ∃ H : Geom[X], H.Monic ∧ H.natDegree = h ∧ H ∣ P := by
  classical
  have hroots : h ≤ P.roots.card := hh.trans_eq (IsAlgClosed.splits P).natDegree_eq_card_roots
  have hpos : 0 < (P.roots.powersetCard h).card := by
    rw [Multiset.card_powersetCard]
    exact Nat.choose_pos hroots
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨htle, htcard⟩ := Multiset.mem_powersetCard.mp ht
  exact ⟨_, monic_multisetProd_X_sub_C t, (natDegree_multiset_prod_X_sub_C_eq_card t).trans htcard,
    (t.prod_X_sub_C_dvd_iff_le_roots hm.ne_zero).mpr htle⟩
end
end K1_13
end
section
namespace K1_13_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
abbrev SourcePolynomial := DifferentialPolynomial Geom 3
abbrev SourceExponent := JetVariable 3 →₀ ℕ
abbrev Local := LocalPolynomial Geom 3
def topWeight (v : JetVariable 3) : ℕ :=
  v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133671) ≤ 3000 * 180265 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133671)
    ?_ (3000 * 180265 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133671) j).ne'
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
abbrev BlockIndex := Fin 4013 × Fin 4650
def offset (i : BlockIndex) : ℤ := (i.2.val : ℤ) - 1650
def blockExponents (i : BlockIndex) : Set SourceExponent :=
  { e | SourceEligible e ∧ e none < 3000 ∧
    e.weight jetDegreeWeight = i.1.val ∧ (e none : ℤ) - e.weight jetDerivativeWeight = offset i }
def BlockSpace (i : BlockIndex) : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom (blockExponents i)
instance (i : BlockIndex) : Module.Finite Geom (BlockSpace i) :=
  MvPolynomial.restrictSupport_finite
    (sourceExponents_finite.subset (fun _ h => h.1))
def originBlock (i : BlockIndex) : BlockSpace i →ₗ[Geom] Local :=
  (localConstraintAt 3000 0 0).domRestrict (BlockSpace i)
def denominator (u : ℤ) : ℤ :=
  if u < 0 then 0 else
    let q := u / 6
    let r := u % 6
    1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
      (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
def cumulative (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    denominator v - denominator (v - d - 1) - denominator (v - d - 2) -
      denominator (v - d - 3) + denominator (v - 2 * d - 3) +
      denominator (v - 2 * d - 4) + denominator (v - 2 * d - 5) -
      denominator (v - 3 * d - 6)
def cappedCount (d u cap : ℤ) : ℤ :=
  if cap < 0 then 0 else cumulative d u - cumulative (d - cap - 1) (u - 3 * (cap + 1))
structure Flag where
  degree : ℤ
  lower : ℤ
  upper : ℤ
  cap : ℤ
  order : ℤ
def factorFlag (j : Fin 11) : Flag :=
  ![⟨1,0,0,0,0⟩,⟨1,1,1,0,0⟩,⟨1,2,2,0,1⟩,⟨1,3,3,1,2⟩,
    ⟨1,0,3,1,3⟩,⟨1,0,1,0,1⟩,⟨1,0,2,0,2⟩,⟨2,1,2,0,2⟩,
    ⟨2,1,3,1,3⟩,⟨2,2,4,1,4⟩,⟨3,2,3,1,3⟩] j
def initialFlag (i : BlockIndex) : Flag :=
  ⟨min i.1.val 1650, -offset i, 1650,550,3000 - (i.1.val : ℤ) - offset i⟩
def residualFlag (F : Flag) (power : Fin 11 → ℕ) : Flag where
  degree := F.degree - ∑ j, (power j : ℤ) * (factorFlag j).degree
  lower := F.lower - ∑ j, (power j : ℤ) * (factorFlag j).lower
  upper := F.upper - ∑ j, (power j : ℤ) * (factorFlag j).upper
  cap := F.cap - ∑ j, (power j : ℤ) * (factorFlag j).cap
  order := F.order - ∑ j, (power j : ℤ) * (factorFlag j).order
def oldCount (F : Flag) : ℤ :=
  cappedCount F.degree F.upper F.cap -
    cappedCount F.degree (min F.upper (F.lower - 1)) F.cap
def targetCount (F : Flag) : ℤ :=
  let balance := F.order - 1 - F.lower + F.degree
  if balance < 0 then 0 else
    let removed := min F.degree (balance / 4) + 1
    cumulative F.degree (F.order - 1) - cumulative (F.degree - removed) (F.order - 1 - 3 * removed) -
      cumulative F.degree (F.lower - 1) + cumulative (F.degree - removed) (F.lower - 1)
def kernelLower (F : Flag) : ℤ :=
  if F.degree < 0 || F.upper < 0 || F.cap < 0 then 0 else oldCount F - targetCount F
def blockBound (i : BlockIndex) (power : Fin 11 → ℕ) : ℕ :=
  let F := initialFlag i
  if F.order ≤ 0 then 0 else
    let active := oldCount { F with upper := min F.upper (2999 - offset i) }
    let lower := max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))
    (min active (oldCount F - lower)).toNat
end
end K1_13_2
end
section
namespace K1_13_2
noncomputable section
open K1 K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open MvPolynomial (mem_support_iff)
def toRow : SourcePolynomial ≃ₐ[Geom] Row 4 :=
  MvPolynomial.optionEquivRight Geom (Fin 4)
theorem atJet_toRow (Q : SourcePolynomial) (S : Geom[X]) :
    atJet (toRow Q) S = differentialSpecialization Q S := by
  let values : Option (Fin 4) → Geom[X] := fun v => v.elim Polynomial.X (jet S)
  have h := MvPolynomial.aeval_map_optionEquivRight values Q
  have hx : values none = Polynomial.X := rfl
  have hid : (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id Geom[X] := rfl
  rw [hx, Polynomial.aeval_X_left, hid, MvPolynomial.map_id, MvPolynomial.aeval_eq_eval] at h
  have hhom : MvPolynomial.aeval values = differentialSpecializationHom (d := 3) S := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [MvPolynomial.aeval_X]
    cases v with
    | none => exact (differentialSpecialization_x (d := 3) S).symm
    | some j => exact (differentialSpecialization_jet j S).symm
  rw [hhom] at h
  exact h
def nodeMap (x y : Geom) : SourceSpace →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict SourceSpace
end
end K1_13_2
end
section
namespace K1_13_2
noncomputable section
open K1 K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def c2 : Prop :=
  ∀ i : BlockIndex, ∀ power : Fin 11 → ℕ,
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤ blockBound i power
def c3 : Prop :=
  ∃ power : BlockIndex → Fin 11 → ℕ, (∑ i, blockBound i (power i)) ≤ 344125686492134
private theorem high_monomial_vanishes (e : SourceExponent) (c : Geom) (he : 3000 ≤ e none) :
    localConstraintAt 3000 0 0 (MvPolynomial.monomial e c) = 0 := by
  change MvPolynomial.weightedTruncation (localContactWeight 3) 3000
    (MvPolynomial.bind₁ (unscaledLocalImage 3 0 0) (MvPolynomial.monomial e c)) = 0
  apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
  refine MvPolynomial.bind₁_mem_restrictWeightedOrder
    (w := fun v : JetVariable 3 => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa only [unscaledLocalImage, map_zero, zero_add, Option.elim_none] using
        (MvPolynomial.X_mem_restrictWeightedOrder (R := Geom)
          (localContactWeight 3) (localT 3) (m := 1) (by rfl))
    | some j => simp
  · exact (MvPolynomial.monomial_mem_restrictWeightedOrder _ _ _ _).mpr
      (Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he))
private theorem finrank_finset_sup_le {ι V : Type*} [AddCommGroup V] [Module Geom V]
    (p : ι → Submodule Geom V) [∀ i, Module.Finite Geom (p i)] (s : Finset ι) :
    Module.finrank Geom (s.sup p : Submodule Geom V) ≤ ∑ i ∈ s, Module.finrank Geom (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank (p i) (s.sup p)).trans
      (Nat.add_le_add_left ih _)
private theorem finrank_of_column_cover {ι : Type*} [Fintype ι]
    (f : SourcePolynomial →ₗ[Geom] Local) (p : ι → Submodule Geom Local)
    [∀ i, Module.Finite Geom (p i)] (bound : ι → ℕ)
    (hcol : ∀ e ∈ sourceExponents, ∀ c, f (MvPolynomial.monomial e c) = 0 ∨
      ∃ i, f (MvPolynomial.monomial e c) ∈ p i)
    (hbound : ∀ i, Module.finrank Geom (p i) ≤ bound i) :
    Module.finrank Geom (LinearMap.range (f.domRestrict SourceSpace)) ≤ ∑ i, bound i := by
  have cover : LinearMap.range (f.domRestrict SourceSpace) ≤ Finset.univ.sup p := by
    intro L hL
    obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp hL
    rw [← hQ]
    change f Q.1 ∈ Finset.univ.sup p
    have expand := congrArg f Q.1.as_sum
    rw [map_sum] at expand
    rw [expand]
    refine Submodule.sum_mem _ fun e he => ?_
    rcases hcol e (Q.2 he) (Q.1.coeff e) with hzero | ⟨i, hi⟩
    · rw [hzero]
      exact Submodule.zero_mem _
    · exact (Finset.le_sup (f := p) (Finset.mem_univ i)) hi
  exact (Submodule.finrank_mono cover).trans
    ((finrank_finset_sup_le p _).trans (Finset.sum_le_sum fun i _ => hbound i))
theorem origin_rank_le (power : BlockIndex → Fin 11 → ℕ) (h : c2) :
    Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ ∑ i, blockBound i (power i) := by
  classical
  let ranges : BlockIndex → Submodule Geom Local := fun i => LinearMap.range (originBlock i)
  refine finrank_of_column_cover (localConstraintAt 3000 0 0) ranges
    (fun i => blockBound i (power i)) ?_ (fun i => h i (power i))
  intro e he c
  by_cases hx : e none < 3000
  · have he' : SourceEligible e := he
    let grade := e.weight jetDegreeWeight
    let idx := e.weight jetDerivativeWeight
    have hb : grade ≤ 4012 := he'.1
    have hj : idx ≤ 1650 := he'.2.1
    let i : BlockIndex := (⟨grade, by omega⟩, ⟨e none + (1650 - idx), by omega⟩)
    have hi : e ∈ blockExponents i := by
      refine ⟨he', hx, rfl, ?_⟩
      change (e none : ℤ) - idx = ((e none + (1650 - idx) : ℕ) : ℤ) - 1650
      omega
    refine Or.inr ⟨i, ?_⟩
    have hm : MvPolynomial.monomial e c ∈ BlockSpace i := by
      unfold BlockSpace
      exact (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hi)
    exact ⟨⟨MvPolynomial.monomial e c, hm⟩, rfl⟩
  · exact Or.inl (high_monomial_vanishes e _ (Nat.le_of_not_gt hx))
end
end K1_13_2
end
