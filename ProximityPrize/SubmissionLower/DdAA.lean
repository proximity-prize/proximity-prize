import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_GCDMonoid_FinsetLemmas
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_MvPolynomial_IrreducibleQuadratic

section Merged6967_DdAA
set_option Elab.async false



set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Code.closeCodewordsRel→ oq,Finset→mD,Finset.card_image_of_injective→ oj,Finset.range→lJ,Fintype.card→n5,IsCoprime→lV,Nat.add→cy,Nat.div→nI,Nat.land→nX,Nat.mul→lI,Nat.shiftRight→nq,Nat.sub→c9
set_option autoImplicit true
section
namespace acY.Compact
set_option maxHeartbeats 2000000
open xE
private def ahf (s :Nat) (f :Nat→Nat) :Nat→Nat
 | 0=>0
 | n+1=>Nat.add (ahf s f n) (f (Nat.add s n))
end acY.Compact
end
section
namespace ju
end ju
end
section
namespace ju
def total {α:Type*} [AddMonoid α] (f :ℕ→α) :ℕ→α
 | 0=>0
 | n+1=>total f n+f n
end ju
end
section
namespace ju
open scoped BigOperators

theorem abt {α:Type*} [AddCommMonoid α] (f :ℕ→α) (n:ℕ) :
   total f n = ∑ i∈lJ n,f i:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [total,Finset.sum_range_succ,ih]
end ju
end
section
namespace i4
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem ProximityPrize.Benchmark
open yP.a92
open scoped NNReal
end
end i4
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace DdP1
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
structure a08 where
 dw:ℕ
 numerator :ℕ
 denominator :ℕ
 aou:ℕ
 mcaBound:ℕ
 listBound:ℕ
end
end DdP1
end
section
namespace bzq
open xE Finset
open scoped BigOperators
end bzq
end

end Merged6967_DdAA

section Merged6967_Fast017
set_option Elab.async false








set_option Elab.async false
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
abbrev Bivar := Polynomial (Polynomial K)
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : (Polynomial K)
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
    (fun s j => algebraMap (Polynomial K) Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
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
def extendSeed (U : Bivar) : (Polynomial Frac) :=
  U.map (algebraMap (Polynomial K) Frac)
def atSlope (P : Bivar) (γ : K) : (Polynomial K) := P.map (evalRingHom γ)
def seed : Bivar := Polynomial.C (R := (Polynomial K)) (Polynomial.X (R := K))
def liftX (P : (Polynomial K)) : Bivar := P.map Polynomial.C
def twist : K →+* K := frobenius K p
def amplitudeDegree (a₀ a₁ : (Polynomial K)) : ℕ := max a₀.natDegree a₁.natDegree
def sixNorm (a : (Polynomial K)) : (Polynomial K) :=
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
def threeU (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ p * liftX ((β 1).map twist))
def _root_.K1_8.threeUAt (q : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))
def threeV (b : (Polynomial K)) (α : Fin 2 → (Polynomial K)) : Bivar :=
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
  α : Fin 2 → (Polynomial K)
  β : Fin 2 → (Polynomial K)
  a : (Polynomial K)
  b : (Polynomial K)
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
  pencil₀ : (Polynomial K)
  pencil₁ : (Polynomial K)
  pencil₀_degree : pencil₀.degree < 131072
  pencil₁_degree : pencil₁.degree < 131072
  E : (Polynomial K)
  factor : (Polynomial K)
  Q : (Polynomial K)
  A₀ : (Polynomial K)
  A₁ : (Polynomial K)
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
def AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) (γ : K) : (Polynomial K) :=
  M.A₀ + Polynomial.C (M.label γ) * M.A₁
def AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K}
    (B : BadMark u γ) : (Polynomial K) :=
  B.decoder - M.pencil₀ - Polynomial.C (M.label γ) * M.pencil₁
structure AnchorMark {u deleted} (M : AnchorModel u deleted) (γ : K) (S : (Polynomial K)) where
  bad : BadMark u γ
  avoids_deleted : Disjoint bad.support deleted
  scalar_fixed : S.map twist = S
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ 131071 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S
structure AnchoredFamily {u deleted} (M : AnchorModel u deleted) (Γ : Finset K) where
  scalar : K → (Polynomial K)
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
abbrev extend (S : (Polynomial K)) := S.map embed
abbrev Row (n : ℕ) := MvPolynomial (Fin n) (Polynomial Geom)
def jet (S : (Polynomial Geom)) {n : ℕ} (i : Fin n) : (Polynomial Geom) := hasseDeriv i.val S
def atJet {n : ℕ} (P : Row n) (S : (Polynomial Geom)) : (Polynomial Geom) :=
  MvPolynomial.eval (jet S) P
def shiftJet {n : ℕ} (P : Row n) (S : (Polynomial Geom)) : Row n :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P
def OrderAt {n : ℕ} (P : Row n) (S : (Polynomial Geom)) (d : ℕ) : Prop :=
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
structure PoleData (Γ : Finset K) (s : K → (Polynomial K)) where
  H : (Polynomial Geom)
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ 2600
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 131071 + H.natDegree
  z : K → Geom
  injective : Function.Injective z
  c : (Polynomial Geom)
  q : (Polynomial Geom)
  a₀ : (Polynomial Geom)
  a₁ : (Polynomial Geom)
  c_unit : IsCoprime c H
  q_unit : IsCoprime q H
  a₀_unit : IsCoprime a₀ H
  regular : ∀ γ ∈ Γ, IsCoprime (a₀ + C (z γ) * a₁) H
  residue : ∀ γ ∈ Γ, H ∣ c * (a₀ + C (z γ) * a₁) * extend (s γ) + C (z γ) * q
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f (90 * 180265 - 1)
def topLead (f : Row 4) (S : (Polynomial Geom)) : (Polynomial Geom) :=
  (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => if i = 3 then Polynomial.X else Polynomial.C (jet S i)) f).coeff (shape f).t
def OnFactor (f : Row 4) (S : (Polynomial Geom)) : Prop :=
  atJet f S = 0 ∧ topLead f S ≠ 0
def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ indexDegree g ≤ 48 ∧ TrueWeightLE g (90 * 180265 - 1)
structure Cover {n : ℕ} (Γ : Finset K) (s : K → (Polynomial K))
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, atJet g (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))
def Contact (w : I → K) (P : Row 4) : Prop :=
  ∀ i (S : (Polynomial Geom)), S.eval (embed (node i)) = embed (w i) →
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
def FatEligible (x : Shape) : Prop := x.b ≤ 60 ∧ x.j ≤ 32
end
end K1_13
end
section
namespace K1_13
noncomputable section
open Polynomial K1
open scoped BigOperators
theorem trim_divisor (P : (Polynomial Geom)) (hm : P.Monic) (h : ℕ) (hh : h ≤ P.natDegree) :
    ∃ H : (Polynomial Geom), H.Monic ∧ H.natDegree = h ∧ H ∣ P := by
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
theorem atJet_toRow (Q : SourcePolynomial) (S : (Polynomial Geom)) :
    atJet (toRow Q) S = differentialSpecialization Q S := by
  let values : Option (Fin 4) → (Polynomial Geom) := fun v => v.elim Polynomial.X (jet S)
  have h := MvPolynomial.aeval_map_optionEquivRight values Q
  have hx : values none = Polynomial.X := rfl
  have hid : (AlgHom.id Geom (Polynomial Geom)).toRingHom = RingHom.id (Polynomial Geom) := rfl
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
theorem finrank_finset_sup_le {ι V : Type*} [AddCommGroup V] [Module Geom V]
    (p : ι → Submodule Geom V) [∀ i, Module.Finite Geom (p i)] (s : Finset ι) :
    Module.finrank Geom (s.sup p : Submodule Geom V) ≤ ∑ i ∈ s, Module.finrank Geom (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank (p i) (s.sup p)).trans
      (Nat.add_le_add_left ih _)
end
end K1_13_2
end

end Merged6967_Fast017

section Merged6967_PortFoundation
set_option Elab.async false

set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
abbrev K := FrobeniusLocator.Native.K
abbrev Node := FrobeniusLocator.Native.I
abbrev node := ProximityPrize.Benchmark.IRSProfile.domain
abbrev p : ℕ := 2130706433
abbrev n : ℕ := 262144
abbrev k : ℕ := 131072
abbrev N : ℕ := 131071
abbrev Jet := Sigma fun _ : ℕ => Sigma fun _ : ℕ => ℕ
def Jet.a (j : Jet) : ℕ := j.2.2
def Jet.b (j : Jet) : ℕ := j.2.1
def Jet.c (j : Jet) : ℕ := j.1
def Jet.q (j : Jet) : ℕ := j.a + j.b + j.c
def Jet.v (j : Jet) : ℕ := j.b + 2 * j.c
structure Source where
  m : ℕ
  B : ℕ
  J : ℕ
  C : ℕ
  E : Finset Jet
def fullBox (B J C : ℕ) : Finset Jet :=
  (Finset.range (C + 1)).sigma fun c =>
    (Finset.range (J - 2*c + 1)).sigma fun b => Finset.range (B - (b+c) + 1)
structure ShapeOK (s : Source) : Prop where
  multiplicity : 0 < s.m
  top_pos : 0 < s.C
  index_top : 2*s.C ≤ s.J
  total_index : s.J ≤ s.B
  characteristic : max N (s.B*(s.B-1)) < p
  support : ∀ j ∈ s.E, j.q ≤ s.B ∧ j.v ≤ s.J ∧ j.c ≤ s.C
  lower : ∀ j ∈ s.E, 0 < j.a → (⟨j.c, j.b, j.a-1⟩ : Jet) ∈ s.E
def errors (A : ℕ) := n - A
def gap (A : ℕ) := A - N
structure AgreementOK (A : ℕ) : Prop where
  gt_degree : N < A
  lt_length : A < n
  one_le_beta : gap A ≤ errors A
  beta_lt_two : errors A < 2 * gap A
def width (A : ℕ) (s : Source) (j : Jet) := s.m*A - N*j.q + j.v
abbrev ColumnIndex (A : ℕ) (s : Source) := (j : s.E) × Fin (width A s j.val)
def column (A : ℕ) (s : Source) (i : ColumnIndex A s) : SourceColumn 2 :=
  ⟨i.2.val, i.1.val.a, ![i.1.val.b, i.1.val.c]⟩
def Surplus (A : ℕ) (s : Source) (R : ℕ) : Prop :=
  n*R + N*(∑ j ∈ s.E, j.q) < s.m*A*s.E.card + ∑ j ∈ s.E, j.v
def originRank (A : ℕ) (s : Source) : ℕ :=
  (localConstraintMatrix s.m (fun _ : Unit => (0 : ZMod p)) (fun _ => 0) (column A s)).rank
def stackRank (A : ℕ) (s : Source) (w : Node → K) : ℕ :=
  (localConstraintMatrix s.m (fun i => node i) w (column A s)).rank
def blockRows (m q : ℕ) (g : ℤ) : Finset Jet :=
  ((Finset.range (q+1)).sigma fun c =>
    (Finset.range (q-c+1)).sigma fun b => {q-(b+c)}).filter fun j : Jet =>
      0 ≤ g + (j.v : ℤ) + 3*(j.a : ℤ) ∧ g + (j.v : ℤ) + 3*(j.a : ℤ) < (m : ℤ)
def blockCols (s : Source) (q : ℕ) (g : ℤ) : Finset Jet :=
  s.E.filter fun j => j.q = q ∧ 0 ≤ g + (j.v : ℤ)
def blockEntry (row col : Jet) : ZMod p :=
  if col.b ≤ row.b ∧ col.c ≤ row.c ∧ row.a + (row.b-col.b) + (row.c-col.c) = col.a
  then (-1)^(row.c-col.c) * (col.a.choose row.a : ℕ) * ((col.a-row.a).choose (row.b-col.b) : ℕ)
  else 0
def blockMatrix (s : Source) (q : ℕ) (g : ℤ) :
    Matrix (blockRows s.m q g) (blockCols s q g) (ZMod p) :=
  fun r c => blockEntry r.val c.val
def prefixRank (s : Source) (cut : ℕ) : ℕ :=
  ∑ q ∈ Finset.range cut, ∑ u ∈ Finset.range (s.m+s.J-q),
    (blockMatrix s q ((u : ℤ) - s.J)).rank
def SilentTail (s : Source) (cut : ℕ) : Prop :=
  ∀ j ∈ s.E, cut ≤ j.q → s.m ≤ j.a
def RankCertificate (A : ℕ) (s : Source) (R : ℕ) : Prop :=
  originRank A s ≤ R ∨ ∃ cut ≤ s.B+1, SilentTail s cut ∧ prefixRank s cut ≤ R
def t : ℕ := max (2*k-7) (k-2)
def t₁ : ℕ := 2*k-5
def a₀ (s : Source) := 1 + t*(s.B-1)
def D (s : Source) := t*(s.J-2) + k-1
def e (s : Source) := min (t*(s.C-1) + k-2) (D s / 2)
def R₂ (s : Source) :=
  (s.C*D s + e s*s.J - 2*s.C*e s)*(2*a₀ s - D s) +
    e s*(D s-e s)*(2*s.B-s.J)
def H (s : Source) := max s.B ((2*s.C-1)*s.B - s.C^2)
def I₁ (s : Source) := max s.J ((2*s.C-1)*s.J - 2*s.C^2)
def a₁ (s : Source) := 1+t₁*(H s-1)
def d₁ (s : Source) := min (a₁ s) (t₁*(I₁ s-1)+k-1)
def R₁ (s : Source) := H s*d₁ s + I₁ s*a₁ s - I₁ s*d₁ s
abbrev close (A : ℕ) (w : Node → K) := ReedSolomon.closePolynomialSet node w k A
def ScalarList (A cap : ℕ) : Prop :=
  ∀ w : Node → K, (close A w).Finite ∧ (close A w).ncard ≤ cap
def indexWeight {r : ℕ} : JetVariable r → ℕ := fun j => j.elim 0 Fin.val
def OrderTwo (s : Source) (Q : DifferentialPolynomial K 2) : Prop :=
  Q ≠ 0 ∧ jetTotalDegree Q ≤ s.B ∧ Q.weightedTotalDegree indexWeight ≤ s.J ∧
    jetDegree Q (Fin.last 2) ≤ s.C
def OrderOne (s : Source) (Q : DifferentialPolynomial K 1) : Prop :=
  Q ≠ 0 ∧ jetTotalDegree Q ≤ H s ∧ jetDegree Q (Fin.last 1) ≤ I₁ s
def RegularRoot {r : ℕ} (Q : DifferentialPolynomial K r) (f : (Polynomial K)) : Prop :=
  ∃ G : DifferentialPolynomial K r, Irreducible G ∧ G ∣ Q ∧
    differentialSpecialization G f = 0 ∧ differentialSpecialization (separant G (Fin.last r)) f ≠ 0
abbrev FX := FractionRing (Polynomial K)
abbrev Geo := AlgebraicClosure FX
abbrev CoeffRing := MvPolynomial (Fin k) Geo
abbrev InitialRing (r : ℕ) := MvPolynomial (Fin (r+1)) Geo
def embed : K →+* Geo :=
  (algebraMap FX Geo).comp ((algebraMap (Polynomial K) FX).comp Polynomial.C)
def center : Geo := algebraMap FX Geo (algebraMap (Polynomial K) FX Polynomial.X)
def coeffPoint (f : (Polynomial K)) (i : Fin k) : Geo := embed (f.coeff i.val)
def readJet (y : Fin k → Geo) (j : ℕ) : Geo :=
  ∑ i : Fin k, (i.val.choose j : Geo) * center^(i.val-j) * y i
structure Chart (r : ℕ) where
  equation : InitialRing r
  denominator : InitialRing r
  numerator : Fin k → InitialRing r
def Chart.locus {r} (T : Chart r) : Set (Fin (r+1) → Geo) :=
  {u | MvPolynomial.eval u T.equation = 0 ∧ MvPolynomial.eval u T.denominator ≠ 0}
def Chart.output {r} (T : Chart r) (u : Fin (r+1) → Geo) (i : Fin k) : Geo :=
  MvPolynomial.eval u (T.numerator i) / MvPolynomial.eval u T.denominator
def Chart.imageSet {r} (T : Chart r) := T.output '' T.locus
def Chart.ideal {r} (T : Chart r) : Ideal CoeffRing := MvPolynomial.vanishingIdeal Geo T.imageSet
structure ChartOK {r} (T : Chart r) : Prop where
  irreducible : Irreducible T.equation
  nonvanishing : ¬ T.equation ∣ T.denominator
  recover : ∀ u ∈ T.locus, ∀ j : Fin (r+1), readJet (T.output u) j.val = u j
structure Family (r : ℕ) where
  count : ℕ
  chart : Fin count → Chart r
def inBand₁ (s : Source) (P : InitialRing 1) : Prop :=
  P.totalDegree ≤ a₁ s ∧ P.degreeOf (Fin.last 1) ≤ d₁ s
structure Family₁ (s : Source) (F : Family 1) : Prop where
  count : F.count ≤ H s
  chart_ok : ∀ i, ChartOK (F.chart i)
  total : (∑ i, (F.chart i).equation.totalDegree) ≤ H s
  index : (∑ i, (F.chart i).equation.degreeOf (Fin.last 1)) ≤ I₁ s
  bands : ∀ i, inBand₁ s (F.chart i).denominator ∧ ∀ j, inBand₁ s ((F.chart i).numerator j)
def CoversRegular {r} (F : Family r) (Q : DifferentialPolynomial K r) : Prop :=
  ∀ f : (Polynomial K), f.degree < k → RegularRoot Q f → ∃ i, coeffPoint f ∈ (F.chart i).imageSet
structure ImageDegrees {r} (F : Family r) (budget : ℕ) : Prop where
  prime : ∀ i, (F.chart i).ideal.IsPrime
  dimension : ∀ i, (MvPolynomial.affineHilbertPolynomial (F.chart i).ideal).natDegree = r
  total : (∑ i, MvPolynomial.affineDegree (F.chart i).ideal) ≤ (budget : ℚ)
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Finset
open scoped BigOperators
theorem mem_fullBox {B J C : ℕ} (hBJ : J ≤ B) (hJC : 2*C ≤ J) (j : Jet) :
    j ∈ fullBox B J C ↔ j.q ≤ B ∧ j.v ≤ J ∧ j.c ≤ C := by
  rcases j with ⟨c, b, a⟩
  simp only [fullBox, mem_sigma, mem_range, Jet.q, Jet.v, Jet.c, Jet.b, Jet.a]
  omega
end
end CJ0
end
section
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
abbrev agreement : ℕ := 180217
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev frontLimit : ℕ := 16
abbrev heightCap : ℕ := t + 1 - L - (frontLimit + 1)
abbrev lowCutoff : ℤ := 2480
abbrev Frac := GenericLayer.GenericField K
abbrev Bivar := Polynomial (Polynomial K)
structure BadMark (u : Words) (γ : K) where
  support : Finset I
  decoder : (Polynomial K)
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
def TypeAtMostOne (u : Words) : Prop :=
  Principal.TypeOneSyndromes node (u 0) (u 1) k p
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : (Polynomial Frac)), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ t ∧
    ∀ P : (Polynomial Frac), P.natDegree ≤ t →
      (((twoBlock u).map (algebraMap (Polynomial K) Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : (Polynomial Frac), Q.natDegree ≤ t - a ∧ P = g * Q)
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
    (fun s j => algebraMap (Polynomial K) Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    k a b c
def TwoActive.height {u : Words} (T : TwoActive u) := (k + 1) - T.c
abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) k T.height
def leftU {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (0, j))
def leftV {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (1, j))
def fixedNodes {u : Words} {T : TwoActive u} (R : Relation T) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0
def extendSeed (U : Bivar) : (Polynomial Frac) :=
  U.map (algebraMap (Polynomial K) Frac)
def IsCommonGCD {F : Type} [Field F] (G U V : (Polynomial F)) : Prop :=
  G ≠ 0 ∧ G ∣ U ∧ G ∣ V ∧ ∀ H : (Polynomial F), H ∣ U → H ∣ V → H ∣ G
def atSlope (P : Bivar) (γ : K) : (Polynomial K) := P.map (evalRingHom γ)
def seed : Bivar := Polynomial.C (R := (Polynomial K)) (Polynomial.X (R := K))
def liftX (P : (Polynomial K)) : Bivar := P.map Polynomial.C
def twist : K →+* K := frobenius K p
def amplitudeDegree (a₀ a₁ : (Polynomial K)) : ℕ := max a₀.natDegree a₁.natDegree
def sixNorm (a : (Polynomial K)) : (Polynomial K) :=
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
  output_degree : output.degree < (k + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
def columnRank (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ p * V))))
def _root_.P0_4.columnRankAt (q : ℕ) (U V : Bivar) : ℕ :=
  Module.finrank Frac (Submodule.span Frac (Set.range fun j : Fin 4 =>
    extendSeed (Polynomial.Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ q * V))))
def threeU (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ p * liftX ((β 1).map twist))
def _root_.P0_4.threeUAt (q : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))
def _root_.P0_5.threeUAt (q : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) : Bivar :=
  liftX a * (liftX ((β 0).map twist) + seed ^ q * liftX ((β 1).map twist))
def threeV (b : (Polynomial K)) (α : Fin 2 → (Polynomial K)) : Bivar :=
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
structure RankThree (u : Words) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) where
  rank_eq : columnRank D.U D.V = 3
  α : Fin 2 → (Polynomial K)
  β : Fin 2 → (Polynomial K)
  a : (Polynomial K)
  b : (Polynomial K)
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
structure AnchorModel (u : Words) (deleted : Finset I) where
  shift : K
  pencil₀ : (Polynomial K)
  pencil₁ : (Polynomial K)
  pencil₀_degree : pencil₀.degree < k
  pencil₁_degree : pencil₁.degree < k
  E : (Polynomial K)
  factor : (Polynomial K)
  Q : (Polynomial K)
  A₀ : (Polynomial K)
  A₁ : (Polynomial K)
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
def AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) (γ : K) : (Polynomial K) :=
  M.A₀ + Polynomial.C (M.label γ) * M.A₁
def AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K}
    (B : BadMark u γ) : (Polynomial K) :=
  B.decoder - M.pencil₀ - Polynomial.C (M.label γ) * M.pencil₁
structure AnchorMark {u deleted} (M : AnchorModel u deleted) (γ : K) (S : (Polynomial K)) where
  bad : BadMark u γ
  avoids_deleted : Disjoint bad.support deleted
  scalar_fixed : S.map twist = S
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ (k : ℤ) - 1 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S
structure AnchoredFamily {u deleted} (M : AnchorModel u deleted) (Γ : Finset K) where
  scalar : K → (Polynomial K)
  mark : ∀ γ ∈ Γ, AnchorMark M γ (scalar γ)
  distinct : Set.InjOn scalar (Γ : Set K)
def highPrefix (w : ℤ) : ℕ :=
  if w ≤ 3554 then 72330561486509196
  else if w ≤ 8249 then 83625638374831363
  else if w ≤ 23999 then 88272853155571659
  else 94479354514532614
end
end P0
end
section
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
open scoped NNReal
theorem dyadic_mul {a i j x y u v z w e s : ℕ}
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
end
end P0
end

end Merged6967_PortFoundation
