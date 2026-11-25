import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false

-- merged module PoleMoment2Jet
section Merged_PoleMoment2Jet

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

/-!
# 2-Jet Grouped Pole Moment Framework (`PoleMoment2Jet`)

Wires the kernel-checked 2-jet grouped pole moment core into the repository's Mathlib setting:
- `Shape2`, `JetPolys2`, `TrueSource2`, `forward2`, `Shaped2`, `PoleTest2`
- `transfer_dvd_2jet` and `linear_pole_dvd_2jet` (valid in EVERY field / characteristic)
- `poleMatrix2`, `diagEntry_upper_triangular`, `nonzero_minor_2jet` (determinant = 1 via unit-upper-triangularity)
- `minor_power_2jet`, `minorGrade_le_2jet`, `bounded_pole_minors_2jet`
- `c1_2jet`: plugs `bounded_pole_minors_2jet` directly into `UpperBranch1.lean`'s generic `P1_7_1_1_2.proof` (`P1_7_1_1.c2`)
- `simple_rank_le_2jet`: global 2-jet pole rank bound for any `SimplePoles h H lift`
-/

namespace PoleMoment2Jet
noncomputable section

open Polynomial Matrix Finset
open K1_14 (L triangle)
open K1_14_1 (SeedPoly SeedField seedWeight otherBlock PoleData CRTLift poleProduct rawBlock crtPolynomial)
open K1_14_1_7 (Seed SeedFrac Exponent SeedWindow residue SimplePoles seedWindow_read)
open P1_7_1_1 (OneSeedFrac oneResidue BoundedMinors)
open scoped BigOperators Matrix Polynomial

/-! ## 1. 2-Jet Shape and Combinatorial Pole Counts -/

structure Shape2 where
  m : ℕ
  B : ℕ
  J : ℕ
  C : ℕ
  U : ℕ
  deriving DecidableEq, Repr

def jetIdx (e₁ e₂ : ℕ) : ℕ := e₁ + 2 * e₂

def IsCol (s : Shape2) (t q e₁ e₂ : ℕ) : Prop :=
  e₁ + e₂ ≤ q ∧ e₂ ≤ s.C ∧ jetIdx e₁ e₂ ≤ s.J ∧
    s.J ≤ t + jetIdx e₁ e₂ ∧ t + jetIdx e₁ e₂ < s.B + 2 * s.J

def IsRow (s : Shape2) (t r b₁ b₂ : ℕ) : Prop :=
  b₁ + b₂ ≤ r ∧ b₂ ≤ s.C ∧ jetIdx b₁ b₂ ≤ s.J ∧
    s.J ≤ t + r + jetIdx b₁ b₂ ∧ t + r + jetIdx b₁ b₂ < s.B + 2 * s.J

def IsPivot (s : Shape2) (t q e₁ e₂ : ℕ) : Prop :=
  IsCol s t q e₁ e₂ ∧ IsRow s t q e₁ e₂

instance (s : Shape2) (t q e₁ e₂ : ℕ) : Decidable (IsCol s t q e₁ e₂) := by
  unfold IsCol jetIdx; infer_instance

instance (s : Shape2) (t r b₁ b₂ : ℕ) : Decidable (IsRow s t r b₁ b₂) := by
  unfold IsRow jetIdx; infer_instance

instance (s : Shape2) (t q e₁ e₂ : ℕ) : Decidable (IsPivot s t q e₁ e₂) := by
  unfold IsPivot; infer_instance

abbrev Offset2 (s : Shape2) := Fin (s.B + 2 * s.J)
abbrev Grade2 (s : Shape2) := Fin (s.B + 1)
abbrev Shift2 (s : Shape2) (q : Grade2 s) := Fin (s.B - q.val + 1)

def gradeSlots2 (s : Shape2) (q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (s.J + 1)) ×ˢ (Finset.range (s.C + 1))).filter fun p =>
    p.1 + p.2 ≤ q ∧ p.2 ≤ s.C ∧ jetIdx p.1 p.2 ≤ s.J

theorem mem_gradeSlots2 {s : Shape2} {q : ℕ} {p : ℕ × ℕ} :
    p ∈ gradeSlots2 s q ↔ p.1 + p.2 ≤ q ∧ p.2 ≤ s.C ∧ jetIdx p.1 p.2 ≤ s.J := by
  simp only [gradeSlots2, Finset.mem_filter, Finset.mem_product, Finset.mem_range, jetIdx]
  constructor
  · intro h; exact h.2
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h1, h2, h3⟩

abbrev GradeSlot2 (s : Shape2) (q : ℕ) := { p : ℕ × ℕ // p ∈ gradeSlots2 s q }

def colSlots2 (s : Shape2) (t q : ℕ) : Finset (ℕ × ℕ) :=
  (gradeSlots2 s q).filter fun p => IsCol s t q p.1 p.2

def pivotSlots2 (s : Shape2) (t q : ℕ) : Finset (ℕ × ℕ) :=
  (gradeSlots2 s q).filter fun p => IsPivot s t q p.1 p.2

theorem mem_colSlots2 {s : Shape2} {t q : ℕ} {p : ℕ × ℕ} :
    p ∈ colSlots2 s t q ↔ IsCol s t q p.1 p.2 := by
  simp only [colSlots2, Finset.mem_filter, mem_gradeSlots2]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h⟩⟩

theorem mem_pivotSlots2 {s : Shape2} {t q : ℕ} {p : ℕ × ℕ} :
    p ∈ pivotSlots2 s t q ↔ IsPivot s t q p.1 p.2 := by
  simp only [pivotSlots2, Finset.mem_filter, mem_gradeSlots2]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1⟩, h⟩⟩

abbrev ColSlot2 (s : Shape2) (t : Offset2 s) (q : Grade2 s) :=
  { p : ℕ × ℕ // p ∈ colSlots2 s t.val q.val }

abbrev PivotSlot2 (s : Shape2) (t : Offset2 s) (q : Grade2 s) :=
  { p : ℕ × ℕ // p ∈ pivotSlots2 s t.val q.val }

abbrev Column2 (s : Shape2) (t : Offset2 s) :=
  Σ q : Grade2 s, ColSlot2 s t q

abbrev Pivot2 (s : Shape2) (t : Offset2 s) :=
  Σ q : Grade2 s, PivotSlot2 s t q

def columnCount2 (s : Shape2) (t q : ℕ) : ℕ := (colSlots2 s t q).card
def pivotCount2 (s : Shape2) (t q : ℕ) : ℕ := (pivotSlots2 s t q).card

def poleRows2 (s : Shape2) : ℕ :=
  ∑ q ∈ Finset.range (s.B + 1), (s.B + s.J - q) * (gradeSlots2 s q).card

def poleCredit2 (h : ℕ) (s : Shape2) : ℕ :=
  triangle s.U * (2 * h) * poleRows2 s

def largestGradeSum2 (s : Shape2) (t R : ℕ) : ℕ :=
  (Finset.range (s.B + 1)).inf' Finset.nonempty_range_add_one fun k =>
    R * k + ∑ q ∈ Finset.range (s.B + 1), (q - k) * columnCount2 s t q

def offsetMoment2 (s : Shape2) (t : ℕ) : ℕ :=
  let R := ∑ q ∈ Finset.range (s.B + 1), pivotCount2 s t q
  largestGradeSum2 s t R - ∑ q ∈ Finset.range (s.B + 1), q * pivotCount2 s t q

def groupedPoleMoment2 (s : Shape2) : ℕ :=
  ∑ t ∈ Finset.range (s.B + 2 * s.J), offsetMoment2 s t

/-! ## 2. Subset Dichotomy and Exact Bijection `AllPivots2 ≃ AllLocalRows2` -/

theorem isRow_imp_isCol_of_ge (s : Shape2) {t q b₁ b₂ : ℕ}
    (ht : s.J ≤ t) (hr : IsRow s t q b₁ b₂) : IsCol s t q b₁ b₂ := by
  rcases hr with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, by omega, by omega⟩

theorem isCol_imp_isRow_of_lt (s : Shape2) {t q e₁ e₂ : ℕ}
    (ht : t < s.J) (hq : q ≤ s.B) (hc : IsCol s t q e₁ e₂) : IsRow s t q e₁ e₂ := by
  rcases hc with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, by omega, by omega⟩

abbrev AllPivots2 (s : Shape2) := Σ t : Offset2 s, Pivot2 s t
abbrev LocalRow2 (s : Shape2) (q : ℕ) := Fin (s.B + s.J - q) × GradeSlot2 s q
abbrev AllLocalRows2 (s : Shape2) := Σ q : Grade2 s, LocalRow2 s q.val

private def toLocal2 (s : Shape2) (r : AllPivots2 s) : AllLocalRows2 s :=
  let t := r.1
  let q := r.2.1
  let e := r.2.2.1
  have hp : IsPivot s t.val q.val e.1 e.2 := mem_pivotSlots2.mp r.2.2.2
  have hx : t.val + jetIdx e.1 e.2 - s.J < s.B + s.J - q.val := by
    have := hp.1.2.2.2.1
    have := hp.2.2.2.2.2
    omega
  ⟨q, ⟨t.val + jetIdx e.1 e.2 - s.J, hx⟩, ⟨e, mem_gradeSlots2.mpr ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩⟩⟩

private def ofLocal2 (s : Shape2) (r : AllLocalRows2 s) : AllPivots2 s :=
  let q := r.1
  let x := r.2.1
  let e := r.2.2.1
  have hg := mem_gradeSlots2.mp r.2.2.2
  have hq : q.val ≤ s.B := Nat.lt_succ_iff.mp q.isLt
  have hx : x.val < s.B + s.J - q.val := x.isLt
  let tVal := x.val + s.J - jetIdx e.1 e.2
  have htLt : tVal < s.B + 2 * s.J := by dsimp [tVal]; omega
  let t : Offset2 s := ⟨tVal, htLt⟩
  have hp : IsPivot s t.val q.val e.1 e.2 := by
    refine ⟨⟨hg.1, hg.2.1, hg.2.2, ?_, ?_⟩, ⟨hg.1, hg.2.1, hg.2.2, ?_, ?_⟩⟩ <;>
      · dsimp [t, tVal, q, x, e] at hg hq hx ⊢; omega
  ⟨t, q, ⟨e, mem_pivotSlots2.mpr hp⟩⟩

private theorem ofLocal2_toLocal2 (s : Shape2) (r : AllPivots2 s) :
    ofLocal2 s (toLocal2 s r) = r := by
  rcases r with ⟨t, q, ⟨e, he⟩⟩
  have hp : IsPivot s t.val q.val e.1 e.2 := mem_pivotSlots2.mp he
  have h1 := hp.1.2.2.1
  have h2 := hp.1.2.2.2.1
  have ht : t.val + jetIdx e.1 e.2 - s.J + s.J - jetIdx e.1 e.2 = t.val := by omega
  have hmk : ∀ (t' : Offset2 s) (h' : e ∈ pivotSlots2 s t'.val q.val),
      t' = t → (⟨t', q, ⟨e, h'⟩⟩ : AllPivots2 s) = ⟨t, q, ⟨e, he⟩⟩ := by
    rintro _ _ rfl; rfl
  exact hmk _ _ (Fin.ext ht)

private theorem toLocal2_ofLocal2 (s : Shape2) (r : AllLocalRows2 s) :
    toLocal2 s (ofLocal2 s r) = r := by
  rcases r with ⟨q, x, ⟨e, he⟩⟩
  have hg := mem_gradeSlots2.mp he
  have hx : x.val + s.J - jetIdx e.1 e.2 + jetIdx e.1 e.2 - s.J = x.val := by omega
  refine Sigma.ext rfl (heq_of_eq (Prod.ext (Fin.ext hx) (Subtype.ext rfl)))

private theorem allPivots2_card (s : Shape2) :
    Fintype.card (AllPivots2 s) = poleRows2 s := by
  classical
  have e : AllPivots2 s ≃ AllLocalRows2 s :=
    ⟨toLocal2 s, ofLocal2 s, ofLocal2_toLocal2 s, toLocal2_ofLocal2 s⟩
  rw [Fintype.card_congr e]
  simp only [AllLocalRows2, LocalRow2, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, poleRows2]
  exact Fin.sum_univ_eq_sum_range (fun q => (s.B + s.J - q) * (gradeSlots2 s q).card) (s.B + 1)

def rowIndex2 (s : Shape2) : Fin (poleRows2 s) ≃ AllPivots2 s :=
  (Fintype.equivFinOfCardEq (allPivots2_card s)).symm

theorem rowIndex2_sum (s : Shape2) (d : ∀ t : Offset2 s, Pivot2 s t → ℕ)
    (hd : ∀ t, (∑ r, d t r) ≤ offsetMoment2 s t.val) :
    (∑ k, d (rowIndex2 s k).1 (rowIndex2 s k).2) ≤ groupedPoleMoment2 s := by
  calc
    _ = ∑ k : AllPivots2 s, d k.1 k.2 :=
      Fintype.sum_equiv (rowIndex2 s) _ _ (fun _ => rfl)
    _ = ∑ t : Offset2 s, ∑ r, d t r := Fintype.sum_sigma _
    _ ≤ ∑ t : Offset2 s, offsetMoment2 s t.val :=
      Finset.sum_le_sum fun t _ => hd t
    _ = groupedPoleMoment2 s := Fin.sum_univ_eq_sum_range _ _

/-! ## 3. Unit-Upper-Triangular Diagonal Block (`diagEntry`) -/

def diagEntry (b₁ b₂ e₁ e₂ : ℕ) : ℕ :=
  if b₂ ≤ e₂ ∧ e₂ ≤ b₁ + b₂ ∧ b₁ + b₂ ≤ e₁ + e₂ then
    e₂.choose b₂ * e₁.choose (b₁ + b₂ - e₂)
  else 0

theorem diagEntry_self (e₁ e₂ : ℕ) : diagEntry e₁ e₂ e₁ e₂ = 1 := by
  have hc : e₂ ≤ e₂ ∧ e₂ ≤ e₁ + e₂ ∧ e₁ + e₂ ≤ e₁ + e₂ := ⟨le_rfl, by omega, le_rfl⟩
  simp only [diagEntry, hc, and_self, ite_true, Nat.add_sub_cancel, Nat.choose_self, mul_one]

theorem diagEntry_eq_zero_of_lt {b₁ b₂ e₁ e₂ : ℕ}
    (hlt : jetIdx e₁ e₂ < jetIdx b₁ b₂) : diagEntry b₁ b₂ e₁ e₂ = 0 := by
  have hnot : ¬ (b₂ ≤ e₂ ∧ e₂ ≤ b₁ + b₂ ∧ b₁ + b₂ ≤ e₁ + e₂) := by
    intro ⟨h1, _, h3⟩
    unfold jetIdx at hlt
    omega
  simp only [diagEntry, hnot, ite_false]

theorem diagEntry_eq_zero_of_eq_ne {b₁ b₂ e₁ e₂ : ℕ}
    (heq : jetIdx e₁ e₂ = jetIdx b₁ b₂) (hne : (b₁, b₂) ≠ (e₁, e₂)) :
    diagEntry b₁ b₂ e₁ e₂ = 0 := by
  have hnot : ¬ (b₂ ≤ e₂ ∧ e₂ ≤ b₁ + b₂ ∧ b₁ + b₂ ≤ e₁ + e₂) := by
    intro ⟨h1, _, h3⟩
    unfold jetIdx at heq
    apply hne
    have hb₂ : b₂ = e₂ := by omega
    have hb₁ : b₁ = e₁ := by omega
    rw [hb₁, hb₂]
  simp only [diagEntry, hnot, ite_false]

theorem diagEntry_upper_triangular {b₁ b₂ e₁ e₂ : ℕ}
    (hnz : diagEntry b₁ b₂ e₁ e₂ ≠ 0) :
    (b₁ = e₁ ∧ b₂ = e₂) ∨ jetIdx b₁ b₂ < jetIdx e₁ e₂ := by
  by_cases hlt : jetIdx b₁ b₂ < jetIdx e₁ e₂
  · exact Or.inr hlt
  · by_cases hgt : jetIdx e₁ e₂ < jetIdx b₁ b₂
    · exact absurd (diagEntry_eq_zero_of_lt hgt) hnz
    · have heq : jetIdx e₁ e₂ = jetIdx b₁ b₂ := by omega
      by_cases hp : (b₁, b₂) = (e₁, e₂)
      · exact Or.inl ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
      · exact absurd (diagEntry_eq_zero_of_eq_ne heq hp) hnz

theorem diagEntry_cond_of_ne_zero {b₁ b₂ e₁ e₂ : ℕ}
    (hnz : diagEntry b₁ b₂ e₁ e₂ ≠ 0) :
    b₂ ≤ e₂ ∧ e₂ ≤ b₁ + b₂ ∧ b₁ + b₂ ≤ e₁ + e₂ ∧ jetIdx b₁ b₂ ≤ jetIdx e₁ e₂ := by
  by_cases hc : b₂ ≤ e₂ ∧ e₂ ≤ b₁ + b₂ ∧ b₁ + b₂ ≤ e₁ + e₂
  · refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
    unfold jetIdx; omega
  · exfalso; apply hnz; simp [diagEntry, hc]

/-! ## 4. 2-Jet Polynomial Ring, `forward2`, `transfer_dvd_2jet`, `linear_pole_dvd_2jet` -/

abbrev JetPolys2 (R : Type) [Semiring R] :=
  Polynomial (Polynomial (Polynomial (Polynomial R)))

abbrev TrueSource2 (R : Type) [CommSemiring R] := JetPolys2 (Seed R)

def jetConstant2 {R : Type*} [CommSemiring R] :
    R →+* Polynomial (Polynomial (Polynomial R)) :=
  Polynomial.C.comp (Polynomial.C.comp Polynomial.C)

def substitute2 {R A : Type*} [CommSemiring R] [CommSemiring A]
    (base : R →+* A) (y0 y1 y2 : A) : Polynomial (Polynomial (Polynomial R)) →+* A :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom base y0) y1) y2

@[simp] theorem substitute2_base {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y0 y1 y2 : A) (p : R) :
    substitute2 f y0 y1 y2 (jetConstant2 p) = f p := by
  simp [substitute2, jetConstant2]

@[simp] theorem substitute2_y0 {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y0 y1 y2 : A) :
    substitute2 f y0 y1 y2 (C (C (Polynomial.X (R := R)))) = y0 := by
  simp [substitute2]

@[simp] theorem substitute2_y1 {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y0 y1 y2 : A) :
    substitute2 f y0 y1 y2 (C (Polynomial.X (R := R[X]))) = y1 := by
  simp [substitute2]

@[simp] theorem substitute2_y2 {R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (y0 y1 y2 : A) :
    substitute2 f y0 y1 y2 (Polynomial.X (R := R[X][X])) = y2 := by
  simp [substitute2]

theorem jetHom2_ext {R A : Type*} [CommSemiring R] [CommSemiring A]
    {f g : Polynomial (Polynomial (Polynomial R)) →+* A}
    (hbase : ∀ p : R, f (jetConstant2 p) = g (jetConstant2 p))
    (hy0 : f (C (C Polynomial.X)) = g (C (C Polynomial.X)))
    (hy1 : f (C Polynomial.X) = g (C Polynomial.X))
    (hy2 : f Polynomial.X = g Polynomial.X) : f = g := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · exact hbase
      · exact hy0
    · exact hy1
  · exact hy2

def sourceCoeff2 {R : Type} [CommSemiring R] (P : TrueSource2 R)
    (e₂ e₁ e₀ a : ℕ) (e : Exponent) : R :=
  ((((P.coeff e₂).coeff e₁).coeff e₀).coeff a).coeff e

def Shaped2 {R : Type} [CommSemiring R] (s : Shape2) (P : TrueSource2 R) : Prop :=
  ∀ e₂ e₁ e₀ a e, sourceCoeff2 P e₂ e₁ e₀ a e ≠ 0 →
    e₀ + e₁ + e₂ ≤ s.B ∧ jetIdx e₁ e₂ ≤ s.J ∧ e₂ ≤ s.C ∧ seedWeight e ≤ s.U

private def substituteJets2 {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y0 y1 y2 : A) : Polynomial (Polynomial (Polynomial S)) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom (eval₂AlgHom base y0 (fun _ => Commute.all _ _))
    y1 (fun _ => Commute.all _ _)) y2 (fun _ => Commute.all _ _)

def forward2 {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X]) :
    TrueSource2 F →ₐ[F] JetPolys2 (SeedFrac F) :=
  let H' := H.map (algebraMap F (SeedFrac F))
  let c : (SeedFrac F)[X] →+* JetPolys2 (SeedFrac F) := jetConstant2
  let rawY0 : JetPolys2 (SeedFrac F) := C (C (Polynomial.X (R := (SeedFrac F)[X])))
  let rawY1 : JetPolys2 (SeedFrac F) := C (Polynomial.X (R := (SeedFrac F)[X][X]))
  let rawY2 : JetPolys2 (SeedFrac F) := Polynomial.X
  let coeffs : (Seed F)[X] →ₐ[F] (SeedFrac F)[X] :=
    Polynomial.mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F))
  let base := (IsScalarTower.toAlgHom F (SeedFrac F)[X] (JetPolys2 (SeedFrac F))).comp coeffs
  substituteJets2 base
    (c H' * rawY0 + c lift)
    (c H' * rawY1 + c H'.derivative * rawY0 + c lift.derivative)
    (c H' * rawY2 + c H'.derivative * rawY1 + c (hasseDeriv 2 H') * rawY0 + c (hasseDeriv 2 lift))

def PoleTest2 {F : Type} [Field F] (s : Shape2) (H : F[X])
    (lift : (SeedFrac F)[X]) (P : TrueSource2 F) : Prop :=
  (jetConstant2 ((H.map (algebraMap F (SeedFrac F))) ^ (s.B + s.J)) :
    JetPolys2 (SeedFrac F)) ∣ forward2 H lift P

theorem forward2_as_substitute {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X]) :
    let h := H.map (algebraMap F (SeedFrac F))
    let c : (SeedFrac F)[X] →+* JetPolys2 (SeedFrac F) := jetConstant2
    let y0 : JetPolys2 (SeedFrac F) := C (C Polynomial.X)
    let y1 : JetPolys2 (SeedFrac F) := C Polynomial.X
    let y2 : JetPolys2 (SeedFrac F) := Polynomial.X
    (forward2 H lift).toRingHom = substitute2
      (c.comp (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F))))
      (c h * y0 + c lift)
      (c h * y1 + c h.derivative * y0 + c lift.derivative)
      (c h * y2 + c h.derivative * y1 + c (hasseDeriv 2 h) * y0 + c (hasseDeriv 2 lift)) := by
  rfl

private theorem hasseDeriv_two_C {R : Type*} [CommRing R] (a : R) :
    hasseDeriv 2 (C a) = 0 := by
  ext n
  simp [hasseDeriv_coeff]

private theorem hasseDeriv_two_X_sub_C {R : Type*} [CommRing R] (a : R) :
    hasseDeriv 2 (Polynomial.X - C a) = 0 := by
  ext n
  simp [hasseDeriv_coeff, coeff_X]

private theorem hasseDeriv_two_mul_linear {R : Type*} [CommRing R] (a : R) (u : R[X]) :
    hasseDeriv 2 ((Polynomial.X - C a) * u) =
      (Polynomial.X - C a) * hasseDeriv 2 u + u.derivative := by
  rw [hasseDeriv_mul]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  have h0 : hasseDeriv 0 (Polynomial.X - C a) = Polynomial.X - C a := by
    simp [hasseDeriv_zero]
  have h1 : hasseDeriv 1 (Polynomial.X - C a) = 1 := by
    rw [hasseDeriv_one', derivative_sub, derivative_X, derivative_C, sub_zero]
  have h2 : hasseDeriv 2 (Polynomial.X - C a) = 0 := hasseDeriv_two_X_sub_C a
  have hu1 : hasseDeriv 1 u = u.derivative := by rw [hasseDeriv_one']
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, h0, h1, h2, hu1, one_mul,
    zero_mul, add_zero]

/-- 2-Jet Pole Transfer Divisibility (`transfer_dvd_2jet`): valid in EVERY field & characteristic. -/
theorem transfer_dvd_2jet {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X])
    (α : F) (z : SeedFrac F) (N : ℕ) (P : TrueSource2 F)
    (hH : H.eval α = 0) (hz : lift.eval (algebraMap F (SeedFrac F) α) = z)
    (hd : (jetConstant2 ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys2 (SeedFrac F)) ∣ forward2 (Polynomial.X - C α) (C z) P) :
    (jetConstant2 ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys2 (SeedFrac F)) ∣ forward2 H lift P := by
  let a := algebraMap F (SeedFrac F) α
  let x : (SeedFrac F)[X] := Polynomial.X - C a
  let h := H.map (algebraMap F (SeedFrac F))
  have hh : x ∣ h := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [x, a, h, Polynomial.IsRoot, hH]
  have hl : x ∣ lift - C z := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [x, a, Polynomial.IsRoot, hz]
  obtain ⟨u, hu⟩ := hh
  obtain ⟨δ, hδ⟩ := hl
  have hlift : lift = x * δ + C z := by rw [← hδ, sub_add_cancel]
  let c : (SeedFrac F)[X] →+* JetPolys2 (SeedFrac F) := jetConstant2
  let y0 : JetPolys2 (SeedFrac F) := C (C Polynomial.X)
  let y1 : JetPolys2 (SeedFrac F) := C Polynomial.X
  let y2 : JetPolys2 (SeedFrac F) := Polynomial.X
  let E := substitute2 c
    (c u * y0 + c δ)
    (c u * y1 + c u.derivative * y0 + c δ.derivative)
    (c u * y2 + c u.derivative * y1 + c (hasseDeriv 2 u) * y0 + c (hasseDeriv 2 δ))
  have hx1 : x.derivative = 1 := by simp [x]
  have hx2 : hasseDeriv 2 x = 0 := hasseDeriv_two_X_sub_C a
  have hmap : (Polynomial.X - C α).map (algebraMap F (SeedFrac F)) = x := by simp [x, a]
  have hnorm := forward2_as_substitute (Polynomial.X - C α) (C z)
  dsimp only at hnorm
  simp only [hmap, hx1, hx2, derivative_C, hasseDeriv_two_C, map_one, map_zero,
    one_mul, zero_mul, add_zero] at hnorm
  have he : E.comp (forward2 (Polynomial.X - C α) (C z)).toRingHom =
      (forward2 H lift).toRingHom := by
    rw [hnorm, forward2_as_substitute]
    apply jetHom2_ext
    · intro g; simp [E, c]
    · change E _ = _
      simp only [substitute2_y0]
      change E (c x * y0 + c (C z)) = c h * y0 + c lift
      rw [map_add, map_mul, hu, hlift]
      simp only [E, c, y0, substitute2_base, substitute2_y0, map_mul, map_add]
      ring
    · change E _ = _
      simp only [substitute2_y1]
      change E (c x * y1 + y0) = c h * y1 + c h.derivative * y0 + c lift.derivative
      rw [map_add, map_mul, hu, hlift, derivative_add, derivative_mul, derivative_mul,
        derivative_C, hx1]
      simp only [E, c, y0, y1, substitute2_base, substitute2_y0, substitute2_y1,
        map_mul, map_add, map_one, map_zero]
      ring
    · change E _ = _
      simp only [substitute2_y2]
      change E (c x * y2 + y1) =
        c h * y2 + c h.derivative * y1 + c (hasseDeriv 2 h) * y0 + c (hasseDeriv 2 lift)
      rw [map_add, map_mul, hu, hlift, derivative_mul, hx1,
        map_add (hasseDeriv 2), hasseDeriv_two_C, add_zero,
        hasseDeriv_two_mul_linear a u, hasseDeriv_two_mul_linear a δ]
      simp only [E, c, y0, y1, y2, substitute2_base, substitute2_y0, substitute2_y1, substitute2_y2,
        map_mul, map_add, map_one]
      ring
  have hp := map_dvd E hd
  rw [show E (jetConstant2 (x ^ N)) = jetConstant2 (x ^ N) from substitute2_base ..] at hp
  exact (DFunLike.congr_fun he P) ▸ hp

def centered2 {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    TrueSource2 F →+* JetPolys2 (SeedFrac F) :=
  let xα := algebraMap F (SeedFrac F) α
  let coeffs := (Polynomial.taylorAlgHom xα).toRingHom.comp
    (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F)))
  substitute2 (jetConstant2.comp coeffs)
    (C (C Polynomial.X) + jetConstant2 (C z))
    (C Polynomial.X)
    Polynomial.X

def zeroSubst2 {R : Type} [CommSemiring R] : JetPolys2 R →+* JetPolys2 R :=
  let x := jetConstant2 (Polynomial.X (R := R))
  let y0 : JetPolys2 R := C (C Polynomial.X)
  let y1 : JetPolys2 R := C Polynomial.X
  substitute2 jetConstant2 (x * y0) (x * y1 + y0) (x * Polynomial.X + y1)

private def undoTaylor2 {R : Type} [CommRing R] (a : R) : JetPolys2 R →+* JetPolys2 R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom
    (Polynomial.taylorAlgHom (-a)).toRingHom))

private theorem undoTaylor2_base {R : Type} [CommRing R] (a : R) (g : R[X]) :
    undoTaylor2 a (jetConstant2 g) = jetConstant2 (Polynomial.taylor (-a) g) := by
  simp [undoTaylor2, jetConstant2]

private theorem undoTaylor2_y0 {R : Type} [CommRing R] (a : R) :
    undoTaylor2 a (C (C (Polynomial.X (R := R[X])))) = C (C Polynomial.X) := by
  simp [undoTaylor2]

private theorem undoTaylor2_y1 {R : Type} [CommRing R] (a : R) :
    undoTaylor2 a (C (Polynomial.X (R := R[X][X]))) = C Polynomial.X := by
  simp [undoTaylor2]

private theorem undoTaylor2_y2 {R : Type} [CommRing R] (a : R) :
    undoTaylor2 a (Polynomial.X (R := R[X][X][X])) = Polynomial.X := by
  simp [undoTaylor2]

theorem linear_pole_dvd_2jet {F : Type} [Field F] (α : F) (z : SeedFrac F) (N : ℕ)
    (P : TrueSource2 F)
    (hd : (jetConstant2 ((Polynomial.X (R := SeedFrac F)) ^ N) :
      JetPolys2 (SeedFrac F)) ∣ zeroSubst2 (centered2 α z P)) :
    (jetConstant2 ((Polynomial.X - C (algebraMap F (SeedFrac F) α)) ^ N) :
      JetPolys2 (SeedFrac F)) ∣ forward2 (Polynomial.X - C α) (C z) P := by
  let a := algebraMap F (SeedFrac F) α
  let x : (SeedFrac F)[X] := Polynomial.X - C a
  have hx1 : x.derivative = 1 := by simp [x]
  have hx2 : hasseDeriv 2 x = 0 := hasseDeriv_two_X_sub_C a
  have ht : Polynomial.taylor (-a) Polynomial.X = x := by simp [x, sub_eq_add_neg]
  have hmap : (Polynomial.X - C α).map (algebraMap F (SeedFrac F)) = x := by simp [x, a]
  have hnorm := forward2_as_substitute (Polynomial.X - C α) (C z)
  dsimp only at hnorm
  simp only [hmap, hx1, hx2, derivative_C, hasseDeriv_two_C, map_one, map_zero,
    one_mul, zero_mul, add_zero] at hnorm
  have he : (undoTaylor2 a).comp (zeroSubst2.comp (centered2 α z)) =
      (forward2 (Polynomial.X - C α) (C z)).toRingHom := by
    rw [hnorm]
    apply jetHom2_ext
    · intro g
      simp only [RingHom.comp_apply, centered2, zeroSubst2, substitute2_base, undoTaylor2_base,
        coe_mapRingHom]
      change jetConstant2 (Polynomial.taylor (-a) (Polynomial.taylor a _)) = jetConstant2 _
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    · simp only [RingHom.comp_apply, centered2, zeroSubst2, substitute2_y0, map_add,
        substitute2_base, map_mul, undoTaylor2_base, ht, undoTaylor2_y0, Polynomial.taylor_C]
    · simp only [RingHom.comp_apply, centered2, zeroSubst2, substitute2_y1, map_add,
        map_mul, undoTaylor2_base, ht, undoTaylor2_y0, undoTaylor2_y1]
    · simp only [RingHom.comp_apply, centered2, zeroSubst2, substitute2_y2, map_add,
        map_mul, undoTaylor2_base, ht, undoTaylor2_y1, undoTaylor2_y2]
  have hp := map_dvd (undoTaylor2 a) hd
  rw [undoTaylor2_base, Polynomial.taylor_pow, ht] at hp
  exact (DFunLike.congr_fun he P) ▸ hp

/-! ## 5. 2-Jet `packGrades2`, `localSlots2`, `zeroGrade2`, and Exact Expansions -/

private def slot2 {R : Type} [CommSemiring R] (a : R[X]) (e₀ e₁ e₂ : ℕ) : JetPolys2 R :=
  jetConstant2 a * (C (C (Polynomial.X (R := R[X])))) ^ e₀ *
    (C (Polynomial.X (R := R[X][X]))) ^ e₁ * Polynomial.X ^ e₂

def packGrades2 {R : Type} [CommSemiring R] (s : Shape2)
    (f : (q : Grade2 s) → GradeSlot2 s q.val → R[X]) : JetPolys2 R :=
  ∑ q : Grade2 s, ∑ e : GradeSlot2 s q.val,
    slot2 (f q e) (q.val - e.1.1 - e.1.2) e.1.1 e.1.2

def inputTaylor2 {F : Type} [Field F] (α : F) (P : TrueSource2 F)
    (e₂ e₁ e₀ : ℕ) : (Seed F)[X] :=
  Polynomial.taylor (algebraMap F (Seed F) α) (((P.coeff e₂).coeff e₁).coeff e₀)

def inputTaylorCoeff2 {F : Type} [Field F] (α : F) (e₂ e₁ e₀ t : ℕ) :
    TrueSource2 F →ₗ[F] Seed F :=
  ((Polynomial.lcoeff (Seed F) t).restrictScalars F).comp
    (((Polynomial.taylor (algebraMap F (Seed F) α)).restrictScalars F).comp
      (((Polynomial.lcoeff ((Seed F)[X]) e₀).restrictScalars F).comp
        (((Polynomial.lcoeff ((Seed F)[X][X]) e₁).restrictScalars F).comp
          ((Polynomial.lcoeff ((Seed F)[X][X][X]) e₂).restrictScalars F))))

theorem inputTaylorCoeff2_apply {F : Type} [Field F] (α : F) (e₂ e₁ e₀ t : ℕ) (P : TrueSource2 F) :
    inputTaylorCoeff2 α e₂ e₁ e₀ t P = (inputTaylor2 α P e₂ e₁ e₀).coeff t := rfl

def inputOrdinate2 {s : Shape2} (q : Grade2 s) (e : GradeSlot2 s q.val) (p : Shift2 s q) : ℕ :=
  q.val - e.1.1 - e.1.2 + p.val

def localSlots2 {F : Type} [Field F] (s : Shape2) (α : F) (z : SeedFrac F)
    (P : TrueSource2 F) (q : Grade2 s) (e : GradeSlot2 s q.val) : (SeedFrac F)[X] :=
  ∑ p : Shift2 s q,
    C ((Nat.choose (inputOrdinate2 q e p) (q.val - e.1.1 - e.1.2) : SeedFrac F) * z ^ p.val) *
      (inputTaylor2 α P e.1.2 e.1.1 (inputOrdinate2 q e p)).map (algebraMap (Seed F) (SeedFrac F))

def zeroGrade2 {E : Type} [CommSemiring E] (s : Shape2) (q : ℕ)
    (f : GradeSlot2 s q → E[X]) (b : GradeSlot2 s q) : E[X] :=
  ∑ e : GradeSlot2 s q,
    if diagEntry b.1.1 b.1.2 e.1.1 e.1.2 ≠ 0 then
      f e * C (diagEntry b.1.1 b.1.2 e.1.1 e.1.2 : E) *
        Polynomial.X ^ (q + jetIdx b.1.1 b.1.2 - jetIdx e.1.1 e.1.2)
    else 0

private theorem coeff_zeroGrade2 {E : Type} [CommSemiring E] (s : Shape2) (q : ℕ)
    (f : GradeSlot2 s q → E[X]) (b : GradeSlot2 s q) (l : ℕ) :
    (zeroGrade2 s q f b).coeff l =
      ∑ e : GradeSlot2 s q,
        if diagEntry b.1.1 b.1.2 e.1.1 e.1.2 ≠ 0 ∧
            q + jetIdx b.1.1 b.1.2 - jetIdx e.1.1 e.1.2 ≤ l then
          (diagEntry b.1.1 b.1.2 e.1.1 e.1.2 : E) *
            (f e).coeff (l - (q + jetIdx b.1.1 b.1.2 - jetIdx e.1.1 e.1.2))
        else 0 := by
  unfold zeroGrade2
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : diagEntry b.1.1 b.1.2 e.1.1 e.1.2 ≠ 0
  · rw [ite_eq_left hd, Polynomial.coeff_mul_X_pow']
    by_cases hl : q + jetIdx b.1.1 b.1.2 - jetIdx e.1.1 e.1.2 ≤ l
    · rw [ite_eq_left hl, ite_eq_left ⟨hd, hl⟩, Polynomial.coeff_mul_C, mul_comm]
    · rw [ite_eq_right hl, ite_eq_right (fun h => hl h.2)]
  · rw [ite_eq_right hd, ite_eq_right (fun h => hd h.1), Polynomial.coeff_zero]

private theorem coeff_slot2 {R : Type} [CommSemiring R] (a : R[X]) (e₀ e₁ e₂ b₀ b₁ b₂ : ℕ) :
    (((slot2 a e₀ e₁ e₂).coeff b₂).coeff b₁).coeff b₀ =
      if b₂ = e₂ ∧ b₁ = e₁ ∧ b₀ = e₀ then a else 0 := by
  unfold slot2 jetConstant2
  simp only [RingHom.comp_apply]
  have h1 : (C (C (C a)) * C (C Polynomial.X) ^ e₀ * C Polynomial.X ^ e₁ : JetPolys2 R) =
      C (C (C a * Polynomial.X ^ e₀) * Polynomial.X ^ e₁) := by
    simp only [map_mul, map_pow]
  rw [h1, Polynomial.coeff_C_mul_X_pow]
  by_cases h2 : b₂ = e₂
  · subst h2
    simp only [true_and, ite_true, Polynomial.coeff_C_mul_X_pow]
    by_cases h1' : b₁ = e₁
    · subst h1'
      simp only [true_and, ite_true, Polynomial.coeff_C_mul_X_pow]
    · simp [h1']
  · simp [h2]

private theorem packGrades2_coeff {R : Type} [CommSemiring R] (s : Shape2)
    (f : (q : Grade2 s) → GradeSlot2 s q.val → R[X]) (e₀ e₁ e₂ : ℕ)
    (hB : e₀ + e₁ + e₂ ≤ s.B) (hJ : jetIdx e₁ e₂ ≤ s.J) (hC : e₂ ≤ s.C) :
    (((packGrades2 s f).coeff e₂).coeff e₁).coeff e₀ =
      f ⟨e₀ + e₁ + e₂, Nat.lt_succ_of_le hB⟩
        ⟨(e₁, e₂), mem_gradeSlots2.mpr ⟨by show e₁ + e₂ ≤ e₀ + e₁ + e₂; omega, hC, hJ⟩⟩ := by
  classical
  unfold packGrades2
  simp only [Polynomial.finsetSum_coeff, coeff_slot2]
  let q0 : Grade2 s := ⟨e₀ + e₁ + e₂, Nat.lt_succ_of_le hB⟩
  let e0 : GradeSlot2 s q0.val :=
    ⟨(e₁, e₂), mem_gradeSlots2.mpr ⟨by show e₁ + e₂ ≤ e₀ + e₁ + e₂; omega, hC, hJ⟩⟩
  rw [Finset.sum_eq_single q0]
  · rw [Finset.sum_eq_single e0]
    · have hsub : q0.val - e0.1.1 - e0.1.2 = e₀ := by dsimp [q0, e0]; omega
      simp [q0, e0, hsub]
    · intro e _ hne
      apply ite_eq_right
      intro ⟨h2, h1, _⟩
      apply hne
      exact Subtype.ext (Prod.ext h1.symm h2.symm)
    · intro h; exact absurd (Finset.mem_univ e0) h
  · intro q _ hne
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    intro ⟨h2, h1, h0⟩
    have hg := (mem_gradeSlots2.mp e.2).1
    apply hne
    apply Fin.ext
    dsimp [q0]
    omega
  · intro h; exact absurd (Finset.mem_univ q0) h

private theorem packGrades2_coeff_eq_zero {R : Type} [CommSemiring R] (s : Shape2)
    (f : (q : Grade2 s) → GradeSlot2 s q.val → R[X]) (e₀ e₁ e₂ : ℕ)
    (h : ¬ (e₀ + e₁ + e₂ ≤ s.B ∧ jetIdx e₁ e₂ ≤ s.J ∧ e₂ ≤ s.C)) :
    (((packGrades2 s f).coeff e₂).coeff e₁).coeff e₀ = 0 := by
  unfold packGrades2
  simp only [Polynomial.finsetSum_coeff, coeff_slot2]
  apply Finset.sum_eq_zero
  intro q _
  apply Finset.sum_eq_zero
  intro e _
  apply ite_eq_right
  intro ⟨h2, h1, h0⟩
  have hg := mem_gradeSlots2.mp e.2
  have hq : q.val ≤ s.B := Nat.lt_succ_iff.mp q.isLt
  apply h
  subst h2; subst h1
  exact ⟨by omega, hg.2.2, hg.2.1⟩

private theorem centered2_coeff {F : Type} [Field F] (α : F) (z : SeedFrac F)
    (P : TrueSource2 F) (e₂ e₁ e₀ N : ℕ)
    (hN : ((P.coeff e₂).coeff e₁).natDegree < N) :
    (((centered2 α z P).coeff e₂).coeff e₁).coeff e₀ =
      ∑ n ∈ Finset.range N,
        C ((n.choose e₀ : SeedFrac F) * z ^ (n - e₀)) *
          (inputTaylor2 α P e₂ e₁ n).map (algebraMap (Seed F) (SeedFrac F)) := by
  let xα := algebraMap F (SeedFrac F) α
  let baseF : (Seed F)[X] →+* (SeedFrac F)[X] :=
    (Polynomial.taylorAlgHom xα).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap (Seed F) (SeedFrac F)))
  have hbase_taylor (g : (Seed F)[X]) :
      baseF g = (Polynomial.taylor (algebraMap F (Seed F) α) g).map (algebraMap (Seed F) (SeedFrac F)) := by
    simp only [baseF, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.taylorAlgHom_apply, Polynomial.coe_mapRingHom, Polynomial.taylor_apply]
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    simp [xα, IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F)]
  let g1 : (Seed F)[X][X] →+* (SeedFrac F)[X][X] :=
    eval₂RingHom (Polynomial.C.comp baseF) (Polynomial.X + C (C z))
  have hcent : centered2 α z P = P.map (Polynomial.mapRingHom g1) := by
    have h : centered2 α z = Polynomial.mapRingHom (Polynomial.mapRingHom g1) := by
      apply jetHom2_ext
      · intro a
        simp only [centered2, substitute2_base, RingHom.comp_apply]
        simp [jetConstant2, g1, baseF, xα]
      · simp [centered2, jetConstant2, g1]
      · simp [centered2, g1]
      · simp [centered2]
    exact DFunLike.congr_fun h P
  rw [hcent, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  let Q := (P.coeff e₂).coeff e₁
  change (g1 Q).coeff e₀ = _
  rw [show Q = ∑ n ∈ Finset.range N, C (Q.coeff n) * Polynomial.X ^ n by
    conv_lhs => rw [Polynomial.as_sum_range' Q N hN]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial]]
  simp only [map_sum, map_mul, map_pow, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro n _
  have hC : g1 (C (Q.coeff n)) = C (baseF (Q.coeff n)) := by simp [g1]
  have hX : g1 Polynomial.X = Polynomial.X + C (C z) := by simp [g1]
  rw [hC, hX, add_pow, Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (Polynomial.X ^ k * (C (C z)) ^ (n - k) * ((n.choose k : ℕ) : (SeedFrac F)[X][X])).coeff e₀ =
        if k = e₀ then C (z ^ (n - e₀) * (n.choose e₀ : SeedFrac F)) else 0 := by
    intro k _
    rw [← map_pow (Polynomial.C (R := (SeedFrac F)[X])), ← map_pow (Polynomial.C (R := SeedFrac F)),
      mul_assoc, ← map_natCast (Polynomial.C (R := (SeedFrac F)[X])),
      ← map_natCast (Polynomial.C (R := SeedFrac F)), ← map_mul, ← map_mul,
      mul_comm (Polynomial.X ^ k), Polynomial.coeff_C_mul_X_pow]
    by_cases hk : k = e₀
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  rw [Finset.sum_congr rfl hterm]
  by_cases hle : e₀ ≤ n
  · rw [Finset.sum_eq_single e₀]
    · simp only [ite_true]
      rw [hbase_taylor, mul_comm (z ^ (n - e₀)), mul_comm]
      simp only [map_mul, map_pow]
      rfl
    · intro k _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)) h
  · rw [Finset.sum_eq_zero]
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hle)]
    · intro k hk
      have hne : k ≠ e₀ := by have := Finset.mem_range.mp hk; omega
      simp [hne]

theorem centered2_eq_packGrades2 {F : Type} [Field F] (s : Shape2) (α : F) (z : SeedFrac F)
    (P : TrueSource2 F) (hP : Shaped2 s P) :
    centered2 α z P = packGrades2 s (localSlots2 s α z P) := by
  have hslot_zero : ∀ e₂ e₁ e₀, ¬ (e₀ + e₁ + e₂ ≤ s.B ∧ jetIdx e₁ e₂ ≤ s.J ∧ e₂ ≤ s.C) →
      ((P.coeff e₂).coeff e₁).coeff e₀ = 0 := by
    intro e₂ e₁ e₀ hnot
    apply Polynomial.ext; intro a
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hne
    have hs := hP e₂ e₁ e₀ a e hne
    exact hnot ⟨hs.1, hs.2.1, hs.2.2.1⟩
  apply Polynomial.ext; intro e₂
  apply Polynomial.ext; intro e₁
  apply Polynomial.ext; intro e₀
  have hN : ((P.coeff e₂).coeff e₁).natDegree < s.B + 1 := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact hslot_zero e₂ e₁ n (by omega)
  by_cases h : e₀ + e₁ + e₂ ≤ s.B ∧ jetIdx e₁ e₂ ≤ s.J ∧ e₂ ≤ s.C
  · rcases h with ⟨hB, hJ, hC⟩
    rw [packGrades2_coeff s _ e₀ e₁ e₂ hB hJ hC, centered2_coeff α z P e₂ e₁ e₀ (s.B + 1) hN]
    let term (n : ℕ) := C ((n.choose e₀ : SeedFrac F) * z ^ (n - e₀)) *
      (inputTaylor2 α P e₂ e₁ n).map (algebraMap (Seed F) (SeedFrac F))
    change (∑ n ∈ Finset.range (s.B + 1), term n) = _
    have hsplit := Finset.sum_range_add term e₀ (s.B - (e₀ + e₁ + e₂) + 1)
    have htail : ∑ n ∈ Finset.Ico (e₀ + (s.B - (e₀ + e₁ + e₂) + 1)) (s.B + 1), term n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hz : ((P.coeff e₂).coeff e₁).coeff n = 0 := hslot_zero e₂ e₁ n (by omega)
      simp [term, inputTaylor2, hz]
    have hfull : ∑ n ∈ Finset.range (s.B + 1), term n =
        ∑ n ∈ Finset.range (e₀ + (s.B - (e₀ + e₁ + e₂) + 1)), term n := by
      rw [← Finset.sum_range_add_sum_Ico term (show e₀ + (s.B - (e₀ + e₁ + e₂) + 1) ≤ s.B + 1 by omega),
        htail, add_zero]
    rw [hfull, hsplit]
    have hzero : ∑ n ∈ Finset.range e₀, term n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [term, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
    rw [hzero, zero_add, ← Fin.sum_univ_eq_sum_range (fun p => term (e₀ + p))]
    unfold localSlots2
    apply Finset.sum_congr rfl
    intro p _
    have hsub : e₀ + e₁ + e₂ - e₁ - e₂ = e₀ := by omega
    simp only [term, inputOrdinate2, hsub, Nat.add_sub_cancel_left]
  · rw [packGrades2_coeff_eq_zero s _ e₀ e₁ e₂ h, centered2_coeff α z P e₂ e₁ e₀ (s.B + 1) hN]
    apply Finset.sum_eq_zero
    intro n _
    by_cases hlt : n < e₀
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · have hz : ((P.coeff e₂).coeff e₁).coeff n = 0 := hslot_zero e₂ e₁ n (by omega)
      simp [inputTaylor2, hz]

private theorem zeroSubst2_slot {R : Type} [CommSemiring R] (a : R[X]) (e₀ e₁ e₂ : ℕ) :
    zeroSubst2 (slot2 a e₀ e₁ e₂) =
      ∑ k₂ ∈ Finset.range (e₂ + 1), ∑ k₁ ∈ Finset.range (e₁ + 1),
        slot2 (a * C ((e₂.choose k₂ * e₁.choose k₁ : ℕ) : R) *
          Polynomial.X ^ (e₀ + k₁ + k₂))
          (e₀ + (e₁ - k₁)) (k₁ + (e₂ - k₂)) k₂ := by
  simp only [slot2, map_mul, map_pow, zeroSubst2, substitute2_base,
    substitute2_y0, substitute2_y1, substitute2_y2]
  rw [add_pow, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k₂ _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k₁ _
  simp only [mul_pow, pow_add, map_mul, map_natCast, Nat.cast_mul]
  ring

private theorem zeroSubst2_grade_slot {E : Type} [CommSemiring E] (s : Shape2) (q : ℕ)
    (f : GradeSlot2 s q → E[X]) (e : GradeSlot2 s q) :
    zeroSubst2 (slot2 (f e) (q - e.1.1 - e.1.2) e.1.1 e.1.2) =
      ∑ b : GradeSlot2 s q,
        if diagEntry b.1.1 b.1.2 e.1.1 e.1.2 ≠ 0 then
          slot2 (f e * C (diagEntry b.1.1 b.1.2 e.1.1 e.1.2 : E) *
            Polynomial.X ^ (q + jetIdx b.1.1 b.1.2 - jetIdx e.1.1 e.1.2))
            (q - b.1.1 - b.1.2) b.1.1 b.1.2
        else 0 := by
  classical
  have he := mem_gradeSlots2.mp e.2
  rw [zeroSubst2_slot]
  let Kset := (Finset.range (e.1.2 + 1)) ×ˢ (Finset.range (e.1.1 + 1))
  let φ : ℕ × ℕ → ℕ × ℕ := fun k => (k.2 + (e.1.2 - k.1), k.1)
  have hφ_mem : ∀ k ∈ Kset, φ k ∈ gradeSlots2 s q := by
    intro k hk
    have hk1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hk).1)
    have hk2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hk).2)
    exact mem_gradeSlots2.mpr (by dsimp [φ, jetIdx] at he ⊢; omega)
  let G (b : ℕ × ℕ) : JetPolys2 E :=
    if diagEntry b.1 b.2 e.1.1 e.1.2 ≠ 0 then
      slot2 (f e * C (diagEntry b.1 b.2 e.1.1 e.1.2 : E) *
        Polynomial.X ^ (q + jetIdx b.1 b.2 - jetIdx e.1.1 e.1.2))
        (q - b.1 - b.2) b.1 b.2
    else 0
  have hsum_sub : (∑ b : GradeSlot2 s q, G b.1) = ∑ b ∈ gradeSlots2 s q, G b := by
    rw [← Finset.sum_coe_sort (gradeSlots2 s q) G]
  change (∑ k₂ ∈ Finset.range (e.1.2 + 1), ∑ k₁ ∈ Finset.range (e.1.1 + 1), _) =
    ∑ b : GradeSlot2 s q, G b.1
  rw [hsum_sub, ← Finset.sum_product']
  have himg_sub : Kset.image φ ⊆ gradeSlots2 s q := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨k, hk, rfl⟩
    exact hφ_mem k hk
  have hzero_out : ∀ b ∈ gradeSlots2 s q, b ∉ Kset.image φ → G b = 0 := by
    intro b _ hnot
    dsimp only [G]
    apply ite_eq_right
    intro hnz
    exfalso
    apply hnot
    have hc := diagEntry_cond_of_ne_zero hnz
    refine Finset.mem_image.mpr ⟨(b.2, b.1 + b.2 - e.1.2), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · exact Prod.ext (by dsimp [φ]; omega) rfl
  rw [← Finset.sum_subset himg_sub hzero_out]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hk).1)
    have hk2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hk).2)
    have hc : k.1 ≤ e.1.2 ∧ e.1.2 ≤ (k.2 + (e.1.2 - k.1)) + k.1 ∧
        (k.2 + (e.1.2 - k.1)) + k.1 ≤ e.1.1 + e.1.2 := by omega
    have hsub1 : k.2 + (e.1.2 - k.1) + k.1 - e.1.2 = k.2 := by omega
    have hdiag : diagEntry (φ k).1 (φ k).2 e.1.1 e.1.2 = e.1.2.choose k.1 * e.1.1.choose k.2 := by
      dsimp [φ, diagEntry]
      rw [ite_eq_left hc, hsub1]
    have hnz : diagEntry (φ k).1 (φ k).2 e.1.1 e.1.2 ≠ 0 := by
      rw [hdiag]
      exact Nat.mul_ne_zero (Nat.choose_pos hk1).ne' (Nat.choose_pos hk2).ne'
    dsimp only [G]
    rw [ite_eq_left hnz, hdiag]
    have hexp1 : q - e.1.1 - e.1.2 + k.2 + k.1 = q + jetIdx (φ k).1 (φ k).2 - jetIdx e.1.1 e.1.2 := by
      dsimp [φ, jetIdx]; omega
    have hexp2 : q - e.1.1 - e.1.2 + (e.1.1 - k.2) = q - (φ k).1 - (φ k).2 := by
      dsimp [φ]; omega
    rw [hexp1, hexp2]
  · intro k₁ hk₁ k₂ hk₂ heq
    have ha1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hk₁).1)
    have ha2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hk₂).1)
    have h2 : k₁.1 = k₂.1 := congrArg Prod.snd heq
    have h1 : k₁.2 + (e.1.2 - k₁.1) = k₂.2 + (e.1.2 - k₂.1) := congrArg Prod.fst heq
    exact Prod.ext h2 (by omega)

theorem zeroSubst2_packGrades2 {E : Type} [CommSemiring E] (s : Shape2)
    (f : (q : Grade2 s) → GradeSlot2 s q.val → E[X]) :
    zeroSubst2 (packGrades2 s f) = packGrades2 s (fun q b => zeroGrade2 s q.val (f q) b) := by
  unfold packGrades2
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [zeroSubst2_grade_slot s q.val (f q)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [zeroGrade2, slot2, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

theorem zeroSubst2_dvd_of_zeroGrade2 {F : Type} [Field F] (s : Shape2)
    (f : (q : Grade2 s) → GradeSlot2 s q.val → (SeedFrac F)[X])
    (h : ∀ (q : Grade2 s) (b : GradeSlot2 s q.val),
      (Polynomial.X (R := SeedFrac F)) ^ (s.B + s.J) ∣ zeroGrade2 s q.val (f q) b) :
    (jetConstant2 ((Polynomial.X (R := SeedFrac F)) ^ (s.B + s.J)) :
      JetPolys2 (SeedFrac F)) ∣ zeroSubst2 (packGrades2 s f) := by
  rw [zeroSubst2_packGrades2, packGrades2]
  apply Finset.dvd_sum; intro q _
  apply Finset.dvd_sum; intro b _
  unfold slot2
  have hc : (jetConstant2 ((Polynomial.X (R := SeedFrac F)) ^ (s.B + s.J)) :
      JetPolys2 (SeedFrac F)) ∣ jetConstant2 (zeroGrade2 s q.val (f q) b) :=
    _root_.map_dvd jetConstant2 (h q b)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _) _

/-! ## 6. 2-Jet `poleMatrix2`, `nonzero_minor_2jet`, `bounded_pole_minors_2jet` -/

def poleMatrix2 {R : Type} [CommSemiring R] (s : Shape2) (t : Offset2 s) (z : R) :
    Matrix (Pivot2 s t) (Column2 s t) R :=
  fun r u =>
    if r.1.val ≤ u.1.val ∧ u.2.1.1 + u.2.1.2 ≤ r.1.val then
      ((diagEntry r.2.1.1 r.2.1.2 u.2.1.1 u.2.1.2 : R) *
        ((u.1.val - u.2.1.1 - u.2.1.2).choose (r.1.val - u.2.1.1 - u.2.1.2) : R)) *
      z ^ (u.1.val - r.1.val)
    else 0

def columnOrder2 {s : Shape2} {t : Offset2 s} (u : Column2 s t) : ℕ :=
  t.val + jetIdx u.2.1.1 u.2.1.2 - s.J

def input2 {F : Type} [Field F] (α : F) {s : Shape2} {t : Offset2 s} (u : Column2 s t) :
    TrueSource2 F →ₗ[F] Seed F :=
  inputTaylorCoeff2 α u.2.1.2 u.2.1.1 (u.1.val - u.2.1.1 - u.2.1.2) (columnOrder2 u)

private def minorGrade2 {s : Shape2} {t : Offset2 s} (e : Pivot2 s t ↪ Column2 s t) : ℕ :=
  (∑ r, (e r).1.val) - ∑ r : Pivot2 s t, r.1.val

private theorem minorGrade_le_2jet {s : Shape2} {t : Offset2 s} (e : Pivot2 s t ↪ Column2 s t) :
    minorGrade2 e ≤ offsetMoment2 s t.val := by
  classical
  have hpivot : (∑ r : Pivot2 s t, r.1.val) =
      ∑ q ∈ Finset.range (s.B + 1), q * pivotCount2 s t.val q := by
    simp only [Pivot2, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, Nat.cast_id]
    change (∑ q : Grade2 s, pivotCount2 s t.val q.val * q.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun q => pivotCount2 s t.val q * q) (s.B + 1)]
    simp only [Nat.mul_comm (pivotCount2 s t.val _) _]
  unfold minorGrade2 offsetMoment2
  rw [hpivot]
  apply Nat.sub_le_sub_right
  unfold largestGradeSum2
  apply Finset.le_inf'
  intro k _
  have hexcess : (∑ r, ((e r).1.val - k)) ≤ ∑ u : Column2 s t, (u.1.val - k) := by
    calc
      _ = ∑ u ∈ Finset.univ.map e, (u.1.val - k) :=
        (Finset.sum_map (Finset.univ : Finset (Pivot2 s t)) e (fun u => u.1.val - k)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  calc
    (∑ r, (e r).1.val) ≤ ∑ r, (k + ((e r).1.val - k)) :=
      Finset.sum_le_sum fun r _ => by omega
    _ ≤ Fintype.card (Pivot2 s t) * k + ∑ u : Column2 s t, (u.1.val - k) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact Nat.add_le_add_left hexcess _
    _ = _ := by
      simp only [Pivot2, Column2, Fintype.sum_sigma, Fintype.card_sigma, Fintype.card_coe,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      change (∑ q : Grade2 s, pivotCount2 s t.val q.val) * k +
          (∑ q : Grade2 s, columnCount2 s t.val q.val * (q.val - k)) = _
      rw [Fin.sum_univ_eq_sum_range (fun q => pivotCount2 s t.val q) (s.B + 1),
        Fin.sum_univ_eq_sum_range (fun q => columnCount2 s t.val q * (q - k)) (s.B + 1)]
      simp only [Nat.mul_comm (columnCount2 s t.val _) (_ - _)]

private theorem minor_power_2jet {R : Type} [CommRing R] {s : Shape2} {t : Offset2 s}
    (e : Pivot2 s t ↪ Column2 s t) (z : R) :
    ((poleMatrix2 s t z).submatrix id e).det =
      ((poleMatrix2 s t (1 : R)).submatrix id e).det * z ^ minorGrade2 e := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.submatrix_apply, id_eq, mul_assoc]
  congr 1
  by_cases hgood : ∀ i, (σ i).1.val ≤ (e i).1.val
  · have he (i : Pivot2 s t) :
        poleMatrix2 s t z (σ i) (e i) = poleMatrix2 s t (1 : R) (σ i) (e i) *
          z ^ ((e i).1.val - (σ i).1.val) := by
      by_cases hj : (e i).2.1.1 + (e i).2.1.2 ≤ (σ i).1.val <;>
        simp [poleMatrix2, hgood i, hj]
    have hw : (∑ i, ((e i).1.val - (σ i).1.val)) = minorGrade2 e := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hgood i), minorGrade2,
        Equiv.sum_comp σ (fun r : Pivot2 s t => r.1.val)]
    simp only [he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  · push Not at hgood
    obtain ⟨i, hi⟩ := hgood
    have hz (v : R) : poleMatrix2 s t v (σ i) (e i) = 0 := by
      simp [poleMatrix2, not_le_of_gt hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hz z),
      Finset.prod_eq_zero (Finset.mem_univ i) (hz 1), zero_mul]

/-- Canonical pivot-to-column inclusion `Pivot2 s t ↪ Column2 s t`. -/
def pivotEmb2 (s : Shape2) (t : Offset2 s) : Pivot2 s t ↪ Column2 s t where
  toFun r := ⟨r.1, ⟨r.2.1, mem_colSlots2.mpr (mem_pivotSlots2.mp r.2.2).1⟩⟩
  inj' := by
    rintro ⟨q, ⟨p, hp⟩⟩ ⟨q', ⟨p', hp'⟩⟩ h
    have hq : q = q' := congrArg Sigma.fst h
    subst hq
    have hp_eq : p = p' := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    subst hp_eq
    rfl

private def pivotKey2 {s : Shape2} {t : Offset2 s} (r : Pivot2 s t) : ℕ :=
  (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + r.2.1.2

private theorem pivotKey2_injective {s : Shape2} {t : Offset2 s} :
    Function.Injective (pivotKey2 (s := s) (t := t)) := by
  intro r u heq
  have hr := (mem_pivotSlots2.mp r.2.2).1
  have hu := (mem_pivotSlots2.mp u.2.2).1
  have hrc : r.2.1.2 < s.C + 1 := Nat.lt_succ_of_le hr.2.1
  have huc : u.2.1.2 < s.C + 1 := Nat.lt_succ_of_le hu.2.1
  have hrj : jetIdx r.2.1.1 r.2.1.2 < s.J + 1 := Nat.lt_succ_of_le hr.2.2.1
  have huj : jetIdx u.2.1.1 u.2.1.2 < s.J + 1 := Nat.lt_succ_of_le hu.2.2.1
  have hsplit : ∀ a a' b b' M : ℕ, b < M → b' < M → a * M + b = a' * M + b' → a = a' ∧ b = b' := by
    intro a a' b b' M hb hb' h
    have ha : a = a' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (a + 1) * M ≤ a' * M := Nat.mul_le_mul_right M hlt
        linarith
      · have : (a' + 1) * M ≤ a * M := Nat.mul_le_mul_right M hgt
        linarith
    subst ha
    exact ⟨rfl, by omega⟩
  have ⟨hdiv1, hmod1⟩ := hsplit _ _ _ _ (s.C + 1) hrc huc heq
  have ⟨hdiv2, hmod2⟩ := hsplit _ _ _ _ (s.J + 1) hrj huj hdiv1
  have hq : r.1 = u.1 := Fin.ext hdiv2
  have hb1 : r.2.1.1 = u.2.1.1 := by unfold jetIdx at hmod2; omega
  have hp : r.2.1 = u.2.1 := Prod.ext hb1 hmod1
  rcases r with ⟨rq, ⟨rp, hrp⟩⟩
  rcases u with ⟨uq, ⟨up, hup⟩⟩
  dsimp at hq hp
  subst hq; subst hp; rfl

/-- Determinant = 1 on the canonical pivot submatrix over EVERY commutative ring!
    Eliminates `pascal_minor`, `pascal_spans`, and `s.B < K1.p`. -/
theorem canonical_minor_det_eq_one {R : Type} [CommRing R] (s : Shape2) (t : Offset2 s) (z : R) :
    ((poleMatrix2 s t z).submatrix id (pivotEmb2 s t)).det = 1 := by
  classical
  let A := (poleMatrix2 s t z).submatrix id (pivotEmb2 s t)
  have htri : A.BlockTriangular pivotKey2 := by
    intro r u hlt
    change poleMatrix2 s t z r (pivotEmb2 s t u) = 0
    unfold poleMatrix2
    dsimp only [pivotEmb2, Function.Embedding.coeFn_mk]
    by_cases hcond : r.1.val ≤ u.1.val ∧ u.2.1.1 + u.2.1.2 ≤ r.1.val
    · rw [ite_eq_left hcond]
      have hru : r.1.val = u.1.val := by
        by_contra hne
        have h1 : r.1.val < u.1.val := lt_of_le_of_ne hcond.1 hne
        have hrj : jetIdx r.2.1.1 r.2.1.2 < s.J + 1 :=
          Nat.lt_succ_of_le (mem_pivotSlots2.mp r.2.2).1.2.2.1
        have hrc : r.2.1.2 < s.C + 1 :=
          Nat.lt_succ_of_le (mem_pivotSlots2.mp r.2.2).1.2.1
        have hkey : pivotKey2 r < pivotKey2 u := by
          unfold pivotKey2
          have hstep : r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2 < u.1.val * (s.J + 1) := by
            calc r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2
              < r.1.val * (s.J + 1) + (s.J + 1) := by omega
              _ = (r.1.val + 1) * (s.J + 1) := by ring
              _ ≤ u.1.val * (s.J + 1) := Nat.mul_le_mul_right _ h1
          have hstep2 : (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + r.2.1.2 <
              (u.1.val * (s.J + 1)) * (s.C + 1) := by
            calc (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + r.2.1.2
              < (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + (s.C + 1) := by omega
              _ = (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2 + 1) * (s.C + 1) := by ring
              _ ≤ (u.1.val * (s.J + 1)) * (s.C + 1) := Nat.mul_le_mul_right _ hstep
          have : (u.1.val * (s.J + 1)) * (s.C + 1) ≤
              (u.1.val * (s.J + 1) + jetIdx u.2.1.1 u.2.1.2) * (s.C + 1) + u.2.1.2 := by
            exact le_trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
          omega
        exact (not_lt_of_gt hlt) hkey
      have hdiag0 : diagEntry r.2.1.1 r.2.1.2 u.2.1.1 u.2.1.2 = 0 := by
        by_contra hnz
        rcases diagEntry_upper_triangular hnz with ⟨h1, h2⟩ | hltj
        · have heq : r = u := by
            rcases r with ⟨rq, ⟨rp, hrp⟩⟩
            rcases u with ⟨uq, ⟨up, hup⟩⟩
            have hqf : rq = uq := Fin.ext hru
            have hpf : rp = up := Prod.ext h1 h2
            subst hqf; subst hpf; rfl
          exact lt_irrefl _ (heq ▸ hlt)
        · have hrc : r.2.1.2 < s.C + 1 := Nat.lt_succ_of_le (mem_pivotSlots2.mp r.2.2).1.2.1
          have hkey : pivotKey2 r < pivotKey2 u := by
            unfold pivotKey2
            have hmul : r.1.val * (s.J + 1) = u.1.val * (s.J + 1) := congrArg (· * (s.J + 1)) hru
            have hstep : (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + r.2.1.2 <
                (u.1.val * (s.J + 1) + jetIdx u.2.1.1 u.2.1.2) * (s.C + 1) := by
              calc (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + r.2.1.2
                < (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2) * (s.C + 1) + (s.C + 1) := by omega
                _ = (r.1.val * (s.J + 1) + jetIdx r.2.1.1 r.2.1.2 + 1) * (s.C + 1) := by ring
                _ ≤ (u.1.val * (s.J + 1) + jetIdx u.2.1.1 u.2.1.2) * (s.C + 1) :=
                    Nat.mul_le_mul_right _ (by omega)
            omega
          exact (not_lt_of_gt hlt) hkey
      simp [hdiag0]
    · rw [ite_eq_right hcond]
  change A.det = 1
  rw [htri.det]
  apply Finset.prod_eq_one
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨r, _, rfl⟩
  let f : Unit ≃ { u : Pivot2 s t // pivotKey2 u = pivotKey2 r } :=
    { toFun := fun _ => ⟨r, rfl⟩
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun u => Subtype.ext (pivotKey2_injective u.2).symm }
  rw [← Matrix.det_submatrix_equiv_self f, Matrix.det_unique]
  change poleMatrix2 s t z r (pivotEmb2 s t r) = 1
  have hr := (mem_pivotSlots2.mp r.2.2).1.1
  unfold poleMatrix2 pivotEmb2
  simp only [Function.Embedding.coeFn_mk, le_rfl, hr, and_self, ite_true, diagEntry_self,
    Nat.choose_self, Nat.sub_self, Nat.cast_one, pow_zero, mul_one]

theorem nonzero_minor_2jet {R : Type} [Field R] (s : Shape2) (t : Offset2 s) (z : R) :
    ∃ e : Pivot2 s t ↪ Column2 s t, ((poleMatrix2 s t z).submatrix id e).det ≠ 0 := by
  refine ⟨pivotEmb2 s t, ?_⟩
  rw [canonical_minor_det_eq_one]
  exact one_ne_zero

set_option maxHeartbeats 600000 in
/-- 2-Jet Bounded Minors Theorem: plugs DIRECTLY into `UpperBranch1.lean`'s `P1_7_1_1_2.proof`! -/
theorem bounded_pole_minors_2jet (F : Type) [Field F] (s : Shape2) (t : Offset2 s) (a b c : F)
    (hb : b ≠ 0) :
    BoundedMinors (poleMatrix2 s t (oneResidue a b c)) (offsetMoment2 s t.val) := by
  let δ := offsetMoment2 s t.val
  let N : F[X] := C a * Polynomial.X
  let D : F[X] := C b + C c * Polynomial.X
  let f := algebraMap F[X] (OneSeedFrac F)
  have hc (u : F) : f (C u) = algebraMap F (OneSeedFrac F) u :=
    (IsScalarTower.algebraMap_apply F F[X] (OneSeedFrac F) u).symm
  have hD : D ≠ 0 := by
    intro hz
    apply hb
    simpa [D] using congrArg (fun p : F[X] => p.coeff 0) hz
  have hDf : f D ≠ 0 := by
    simpa only [f, map_zero] using (IsFractionRing.injective F[X] (OneSeedFrac F)).ne hD
  have hz : oneResidue a b c = f N / f D := by
    simp only [oneResidue, N, D, map_mul, map_add, hc]
    rfl
  have hNdeg : N.natDegree ≤ 1 :=
    (Polynomial.natDegree_mul_le (p := C a) (q := Polynomial.X)).trans (by simp)
  have hDdeg : D.natDegree ≤ 1 := by
    unfold D
    rw [Polynomial.natDegree_C_add]
    exact Polynomial.natDegree_mul_le.trans (by simp)
  refine ⟨nonzero_minor_2jet s t _, f D ^ δ, pow_ne_zero _ hDf, ?_⟩
  intro e
  let d := minorGrade2 e
  let m := ((poleMatrix2 s t (1 : F)).submatrix id e).det
  have hd : d ≤ δ := minorGrade_le_2jet e
  let g := C m * N ^ d * D ^ (δ - d)
  refine ⟨g, ?_, ?_⟩
  · have hNd : (N ^ d).natDegree ≤ d :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left d hNdeg)
    have hDd : (D ^ (δ - d)).natDegree ≤ δ - d :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (δ - d) hDdeg)
    have hg := Polynomial.natDegree_mul_le (p := C m * N ^ d) (q := D ^ (δ - d))
    have hm := Polynomial.natDegree_mul_le (p := C m) (q := N ^ d)
    rw [Polynomial.natDegree_C, zero_add] at hm
    change (C m * N ^ d * D ^ (δ - d)).natDegree ≤ δ
    omega
  · have hmapped : ((poleMatrix2 s t (1 : F)).submatrix id e).map (algebraMap F (OneSeedFrac F)) =
        (poleMatrix2 s t (1 : OneSeedFrac F)).submatrix id e := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, poleMatrix2, apply_ite, map_zero,
        map_mul, map_natCast, map_pow, map_one]
      split_ifs <;> rfl
    have hm : f (C m) = ((poleMatrix2 s t (1 : OneSeedFrac F)).submatrix id e).det := by
      rw [hc]
      change (algebraMap F (OneSeedFrac F)) ((poleMatrix2 s t (1 : F)).submatrix id e).det = _
      rw [RingHom.map_det]
      exact congrArg Matrix.det hmapped
    have hpow : f D ^ δ * (f N / f D) ^ d = f N ^ d * f D ^ (δ - d) := by
      calc
        _ = f N ^ d * (f D ^ δ / f D ^ d) := by rw [div_pow]; ring
        _ = _ := by
          congr 1
          apply (div_eq_iff (pow_ne_zero _ hDf)).2
          rw [← pow_add, Nat.sub_add_cancel hd]
    rw [minor_power_2jet, hz]
    change f (C m * N ^ d * D ^ (δ - d)) =
      f D ^ δ * (((poleMatrix2 s t (1 : OneSeedFrac F)).submatrix id e).det * (f N / f D) ^ d)
    rw [map_mul, map_mul, map_pow, map_pow, hm, mul_left_comm (f D ^ δ), hpow]
    ac_rfl

/-! ## 7. Local Spanning (`c1_2jet_local`), Polynomial Tests, and `c1_2jet` via `P1_7_1_1_2.proof` -/

private def translatedCoeff2 {F : Type} [Field F] {s : Shape2}
    (α : F) (z : SeedFrac F) (P : TrueSource2 F) (q : Grade2 s) (e₁ e₂ x : ℕ) : SeedFrac F :=
  ∑ p : Shift2 s q,
    (((q.val - e₁ - e₂ + p.val).choose (q.val - e₁ - e₂) : SeedFrac F) * z ^ p.val) *
      algebraMap (Seed F) (SeedFrac F) (inputTaylorCoeff2 α e₂ e₁ (q.val - e₁ - e₂ + p.val) x P)

private theorem localSlots2_coeff {F : Type} [Field F] (s : Shape2)
    (α : F) (z : SeedFrac F) (P : TrueSource2 F) (q : Grade2 s) (e : GradeSlot2 s q.val) (x : ℕ) :
    (localSlots2 s α z P q e).coeff x = translatedCoeff2 α z P q e.1.1 e.1.2 x := by
  simp only [localSlots2, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map,
    inputOrdinate2, translatedCoeff2, inputTaylorCoeff2_apply]

private theorem sum_embedding2 {A D M : Type*} [Fintype A] [Fintype D] [AddCommMonoid M]
    (e : A ↪ D) (f : D → M) (h : ∀ d, (∀ a, e a ≠ d) → f d = 0) :
    ∑ d, f d = ∑ a, f (e a) := by
  classical
  rw [← Finset.sum_map Finset.univ e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  exact h d fun a ha => hd (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, ha⟩)

private def gradeShift2 (s : Shape2) (q : Grade2 s) : Shift2 s q ↪ Grade2 s where
  toFun p := ⟨q.val + p.val, by have := q.isLt; have := p.isLt; omega⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

private def colLift2 {s : Shape2} {t : Offset2 s} {q q' : Grade2 s} (hqq : q.val ≤ q'.val) :
    ColSlot2 s t q ↪ ColSlot2 s t q' where
  toFun u := ⟨u.1, mem_colSlots2.mpr (by
    have hu := mem_colSlots2.mp u.2
    exact ⟨Nat.le_trans hu.1 hqq, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2⟩)⟩
  inj' a b h := Subtype.ext (by simpa using congrArg Subtype.val h)

private theorem pivot_read_2jet {F : Type} [Field F] (s : Shape2) (t : Offset2 s)
    (α : F) (z : SeedFrac F) (P : TrueSource2 F) (q : Grade2 s) (b : PivotSlot2 s t q) :
    (poleMatrix2 s t z *ᵥ (fun u => algebraMap (Seed F) (SeedFrac F) (input2 α u P))) ⟨q, b⟩ =
      ∑ u : ColSlot2 s t q, (diagEntry b.1.1 b.1.2 u.1.1 u.1.2 : SeedFrac F) *
        translatedCoeff2 α z P q u.1.1 u.1.2 (t.val + jetIdx u.1.1 u.1.2 - s.J) := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  let f (q' : Grade2 s) (u : ColSlot2 s t q') :=
    poleMatrix2 s t z ⟨q, b⟩ ⟨q', u⟩ *
      algebraMap (Seed F) (SeedFrac F) (input2 α ⟨q', u⟩ P)
  change (∑ q', ∑ u, f q' u) = _
  rw [sum_embedding2 (gradeShift2 s q) (fun q' => ∑ u, f q' u)]
  · simp only [translatedCoeff2, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    let q' := gradeShift2 s q p
    have hqq : q.val ≤ q'.val := Nat.le_add_right _ _
    change (∑ u, f q' u) = _
    rw [sum_embedding2 (colLift2 (s := s) (t := t) hqq) (f q')]
    · apply Finset.sum_congr rfl
      intro u _
      have hu := mem_colSlots2.mp u.2
      have hu1 := hu.1
      have hp : q'.val - q.val = p.val := by change q.val + p.val - q.val = p.val; omega
      have hOrd : q'.val - u.1.1 - u.1.2 = q.val - u.1.1 - u.1.2 + p.val := by
        change q.val + p.val - u.1.1 - u.1.2 = q.val - u.1.1 - u.1.2 + p.val; omega
      change (if q.val ≤ q'.val ∧ u.1.1 + u.1.2 ≤ q.val then
        ((diagEntry b.1.1 b.1.2 u.1.1 u.1.2 : SeedFrac F) *
          ((q'.val - u.1.1 - u.1.2).choose (q.val - u.1.1 - u.1.2) : SeedFrac F)) *
        z ^ (q'.val - q.val) else 0) *
        algebraMap (Seed F) (SeedFrac F)
          (inputTaylorCoeff2 α u.1.2 u.1.1 (q'.val - u.1.1 - u.1.2) (t.val + jetIdx u.1.1 u.1.2 - s.J) P) = _
      rw [ite_eq_left ⟨hqq, hu.1⟩, hp, hOrd]
      ring
    · intro u hu
      have hnot : ¬ u.1.1 + u.1.2 ≤ q.val := by
        intro hle
        have huc := mem_colSlots2.mp u.2
        exact hu ⟨u.1, mem_colSlots2.mpr ⟨hle, huc.2.1, huc.2.2.1, huc.2.2.2.1, huc.2.2.2.2⟩⟩
          (Subtype.ext rfl)
      simp [f, poleMatrix2, hnot]
  · intro q' hq'
    have hl : ¬ q.val ≤ q'.val := by
      intro hqq
      let p : Shift2 s q := ⟨q'.val - q.val, by have := q'.isLt; omega⟩
      exact hq' p (Fin.ext (by change q.val + (q'.val - q.val) = q'.val; omega))
    apply Finset.sum_eq_zero
    intro u _
    have hz : poleMatrix2 s t z ⟨q, b⟩ ⟨q', u⟩ = 0 := by
      unfold poleMatrix2; exact ite_eq_right fun h => hl h.1
    simp only [f, hz, zero_mul]

private def colToGrade2 (s : Shape2) (t : Offset2 s) (q : Grade2 s) :
    ColSlot2 s t q ↪ GradeSlot2 s q.val where
  toFun u := ⟨u.1, mem_gradeSlots2.mpr (by
    have hu := mem_colSlots2.mp u.2; exact ⟨hu.1, hu.2.1, hu.2.2.1⟩)⟩
  inj' a b h := Subtype.ext (by simpa using congrArg Subtype.val h)

private theorem coeff_read_2jet {F : Type} [Field F] (s : Shape2) (t : Offset2 s)
    (α : F) (z : SeedFrac F) (P : TrueSource2 F) (q : Grade2 s)
    (b : GradeSlot2 s q.val) (l : ℕ) (hl : l < s.B + s.J)
    (ht : t.val + q.val + jetIdx b.1.1 b.1.2 = l + s.J) :
    (zeroGrade2 s q.val (localSlots2 s α z P q) b).coeff l =
      ∑ u : ColSlot2 s t q, (diagEntry b.1.1 b.1.2 u.1.1 u.1.2 : SeedFrac F) *
        translatedCoeff2 α z P q u.1.1 u.1.2 (t.val + jetIdx u.1.1 u.1.2 - s.J) := by
  classical
  rw [coeff_zeroGrade2, sum_embedding2 (colToGrade2 s t q)]
  · apply Finset.sum_congr rfl
    intro u _
    have hu := mem_colSlots2.mp u.2
    by_cases hd : diagEntry b.1.1 b.1.2 u.1.1 u.1.2 ≠ 0
    · have hcond := diagEntry_cond_of_ne_zero hd
      have hq_ge : jetIdx u.1.1 u.1.2 ≤ q.val + jetIdx b.1.1 b.1.2 := by
        have h1 := hu.1; have h2 := hcond.2.1; unfold jetIdx; omega
      have hu1 := hu.2.2.2.1
      have hle : q.val + jetIdx b.1.1 b.1.2 - jetIdx u.1.1 u.1.2 ≤ l := by omega
      have hx : l - (q.val + jetIdx b.1.1 b.1.2 - jetIdx u.1.1 u.1.2) =
          t.val + jetIdx u.1.1 u.1.2 - s.J := by omega
      dsimp only [colToGrade2, Function.Embedding.coeFn_mk]
      rw [ite_eq_left ⟨hd, hle⟩, hx, localSlots2_coeff]
    · push Not at hd
      simp [colToGrade2, hd]
  · intro e he
    split_ifs with h
    · exfalso
      have hcond := diagEntry_cond_of_ne_zero h.1
      have heg := mem_gradeSlots2.mp e.2
      have hq_ge : jetIdx e.1.1 e.1.2 ≤ q.val + jetIdx b.1.1 b.1.2 := by
        have h1 := heg.1; have h2 := hcond.2.1; unfold jetIdx; omega
      have hcol : IsCol s t.val q.val e.1.1 e.1.2 :=
        ⟨heg.1, heg.2.1, heg.2.2, by omega, by omega⟩
      exact he ⟨e.1, mem_colSlots2.mpr hcol⟩ (Subtype.ext rfl)
    · rfl

/-- When `t < J`, `IsPivot = IsCol` and unit-upper-triangularity forces `v = 0` on every column! -/
private theorem unit_upper_tri_vanish {E : Type} [Field E] (s : Shape2) (t : Offset2 s)
    (ht : t.val < s.J) (q : Grade2 s) (v : ColSlot2 s t q → E)
    (hzero : ∀ b : PivotSlot2 s t q,
      ∑ u : ColSlot2 s t q, (diagEntry b.1.1 b.1.2 u.1.1 u.1.2 : E) * v u = 0) :
    ∀ u : ColSlot2 s t q, v u = 0 := by
  have hgen : ∀ n : ℕ, ∀ u : ColSlot2 s t q, s.J - jetIdx u.1.1 u.1.2 ≤ n → v u = 0 := by
    intro n
    induction n with
    | zero =>
      intro u hu
      have huc := mem_colSlots2.mp u.2
      have hq : q.val ≤ s.B := Nat.lt_succ_iff.mp q.isLt
      let b : PivotSlot2 s t q :=
        ⟨u.1, mem_pivotSlots2.mpr ⟨huc, isCol_imp_isRow_of_lt s ht hq huc⟩⟩
      have hb := hzero b
      rw [Finset.sum_eq_single u] at hb
      · simpa [b, diagEntry_self] using hb
      · intro w _ hne
        have hwc := mem_colSlots2.mp w.2
        have h0 : diagEntry b.1.1 b.1.2 w.1.1 w.1.2 = 0 := by
          by_contra hnz
          rcases diagEntry_upper_triangular hnz with ⟨h1, h2⟩ | hlt
          · exact hne (Subtype.ext (Prod.ext h1.symm h2.symm))
          · have : jetIdx w.1.1 w.1.2 ≤ s.J := hwc.2.2.1
            dsimp [b] at hlt; omega
        simp [h0]
      · intro h; exact absurd (Finset.mem_univ u) h
    | succ n ih =>
      intro u hu
      have huc := mem_colSlots2.mp u.2
      have hq : q.val ≤ s.B := Nat.lt_succ_iff.mp q.isLt
      let b : PivotSlot2 s t q :=
        ⟨u.1, mem_pivotSlots2.mpr ⟨huc, isCol_imp_isRow_of_lt s ht hq huc⟩⟩
      have hb := hzero b
      rw [Finset.sum_eq_single u] at hb
      · simpa [b, diagEntry_self] using hb
      · intro w _ hne
        by_cases hnz : diagEntry b.1.1 b.1.2 w.1.1 w.1.2 = 0
        · simp [hnz]
        · rcases diagEntry_upper_triangular hnz with ⟨h1, h2⟩ | hlt
          · exact absurd (Subtype.ext (Prod.ext h1.symm h2.symm)) hne
          · have hw0 : v w = 0 := ih w (by dsimp [b] at hlt; omega)
            simp [hw0]
      · intro h; exact absurd (Finset.mem_univ u) h
  intro u
  exact hgen s.J u (Nat.sub_le _ _)

/-- 2-Jet Local Spanning Theorem (`c1_2jet_local`): NO `PascalSpans` or `s.B < K1.p` needed! -/
theorem c1_2jet_local {F : Type} [Field F] (s : Shape2) (α : F) (z : SeedFrac F)
    (P : TrueSource2 F)
    (hm : ∀ t : Offset2 s, poleMatrix2 s t z *ᵥ
      (fun u => algebraMap (Seed F) (SeedFrac F) (input2 α u P)) = 0)
    (q : Grade2 s) (b : GradeSlot2 s q.val) :
    (Polynomial.X (R := SeedFrac F)) ^ (s.B + s.J) ∣
      zeroGrade2 s q.val (localSlots2 s α z P q) b := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro l hl
  have hbg := mem_gradeSlots2.mp b.2
  by_cases ht : q.val + jetIdx b.1.1 b.1.2 ≤ l + s.J
  · let t : Offset2 s := ⟨l + s.J - (q.val + jetIdx b.1.1 b.1.2), by omega⟩
    have ht' : t.val + q.val + jetIdx b.1.1 b.1.2 = l + s.J := by dsimp [t]; omega
    rw [coeff_read_2jet s t α z P q b l hl ht']
    by_cases hge : s.J ≤ t.val
    · have hrow : IsRow s t.val q.val b.1.1 b.1.2 :=
        ⟨hbg.1, hbg.2.1, hbg.2.2, by omega, by omega⟩
      let bp : PivotSlot2 s t q :=
        ⟨b.1, mem_pivotSlots2.mpr ⟨isRow_imp_isCol_of_ge s hge hrow, hrow⟩⟩
      have hr := congrFun (hm t) ⟨q, bp⟩
      rw [pivot_read_2jet] at hr
      exact hr
    · have hlt : t.val < s.J := lt_of_not_ge hge
      let v : ColSlot2 s t q → SeedFrac F := fun u =>
        translatedCoeff2 α z P q u.1.1 u.1.2 (t.val + jetIdx u.1.1 u.1.2 - s.J)
      have hv0 : ∀ u : ColSlot2 s t q, v u = 0 :=
        unit_upper_tri_vanish s t hlt q v fun bp => by
          have hr := congrFun (hm t) ⟨q, bp⟩
          rw [pivot_read_2jet] at hr
          exact hr
      apply Finset.sum_eq_zero
      intro u _
      simp [v, hv0 u]
  · rw [coeff_zeroGrade2]
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    intro ⟨hd, hle⟩
    have heg := mem_gradeSlots2.mp e.2
    have hJ : jetIdx e.1.1 e.1.2 ≤ s.J := heg.2.2
    omega

/-! ## 8. Polynomial Tests and Main Theorem `c1_2jet` (Plugging into `UpperBranch1`'s `P1_7_1_1_2.proof`) -/

private def seedMap2 (F : Type) [Field F] (side : Fin 2) : F[X] →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (Polynomial.toMvPolynomial side).toRingHom

private def fractionSeedMap2 (F : Type) [Field F] (side : Fin 2) :
    OneSeedFrac F →+* SeedFrac F :=
  IsFractionRing.lift (g := seedMap2 F side)
    ((IsFractionRing.injective (Seed F) (SeedFrac F)).comp
      (Polynomial.toMvPolynomial_injective side))

private theorem fractionSeedMap2_polynomial {F : Type} [Field F] (side : Fin 2) (g : F[X]) :
    fractionSeedMap2 F side (algebraMap F[X] (OneSeedFrac F) g) =
      algebraMap (Seed F) (SeedFrac F) (g.toMvPolynomial side) := by
  rw [fractionSeedMap2, IsFractionRing.lift_algebraMap]; rfl

private theorem fractionSeedMap2_scalar {F : Type} [Field F] (side : Fin 2) (a : F) :
    fractionSeedMap2 F side (algebraMap F (OneSeedFrac F) a) = algebraMap F (SeedFrac F) a := by
  rw [IsScalarTower.algebraMap_apply F F[X] (OneSeedFrac F), fractionSeedMap2_polynomial]
  change algebraMap (Seed F) (SeedFrac F) ((Polynomial.C a).toMvPolynomial side) = _
  rw [Polynomial.toMvPolynomial_C]
  exact (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) a).symm

private theorem fractionSeedMap2_residue {F : Type} [Field F] (side : Fin 2) (a b c : F) :
    fractionSeedMap2 F side (oneResidue a b c) = residue side a b c := by
  simp only [oneResidue, residue, map_div₀, map_add, map_mul, fractionSeedMap2_scalar,
    fractionSeedMap2_polynomial, Polynomial.toMvPolynomial_X]

def polynomialTest2 {F : Type} [Field F] {s : Shape2} {t : Offset2 s}
    (α : F) (side : Fin 2) (v : Column2 s t → F[X]) : TrueSource2 F →ₗ[F] Seed F :=
  ∑ u, (v u).toMvPolynomial side • input2 α u

private theorem polynomialTest2_apply {F : Type} [Field F] {s : Shape2} {t : Offset2 s}
    (α : F) (side : Fin 2) (v : Column2 s t → F[X]) (P : TrueSource2 F) :
    polynomialTest2 α side v P = ∑ u, (v u).toMvPolynomial side * input2 α u P := by
  simp only [polynomialTest2, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

private theorem taylor2_seed_degree {F : Type} [Field F] (s : Shape2) (α : F)
    (P : TrueSource2 F) (hP : Shaped2 s P) (e₂ e₁ e₀ t : ℕ) :
    (inputTaylorCoeff2 α e₂ e₁ e₀ t P).totalDegree ≤ s.U := by
  have hc (a : ℕ) : ((((P.coeff e₂).coeff e₁).coeff e₀).coeff a).totalDegree ≤ s.U := by
    apply Finset.sup_le
    intro e he
    exact (hP e₂ e₁ e₀ a e (MvPolynomial.mem_support_iff.mp he)).2.2.2
  rw [inputTaylorCoeff2_apply, inputTaylor2, Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  rw [Polynomial.hasseDeriv_coeff]
  have he :
      ((k + t).choose t : Seed F) * (((P.coeff e₂).coeff e₁).coeff e₀).coeff (k + t) *
          (algebraMap F (Seed F) α) ^ k =
        MvPolynomial.C (((k + t).choose t : F) * α ^ k) *
          (((P.coeff e₂).coeff e₁).coeff e₀).coeff (k + t) := by
    simp only [MvPolynomial.algebraMap_eq, map_mul, map_pow, map_natCast]
    ring
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hc (k + t))

private theorem side_degrees2 {F : Type} [Field F] (side : Fin 2) (p : F[X]) :
    (p.toMvPolynomial side).degreeOf (otherBlock side) ≤ 0 ∧
    (p.toMvPolynomial side).totalDegree ≤ p.natDegree := by
  classical
  have hsum : p.toMvPolynomial side =
      ∑ k ∈ p.support, MvPolynomial.C (p.coeff k) * MvPolynomial.X side ^ k := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
      Polynomial.toMvPolynomial_X]
  have hne : otherBlock side ≠ side := by fin_cases side <;> decide
  rw [hsum]
  constructor
  · refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    simpa [MvPolynomial.degreeOf_X_of_ne hne] using
      MvPolynomial.degreeOf_pow_le (otherBlock side) (MvPolynomial.X (R := F) side) k
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact ((MvPolynomial.totalDegree_pow (MvPolynomial.X (R := F) side) k).trans
      (by simp)).trans (Polynomial.le_natDegree_of_mem_supp k hk)

private theorem seedWeight_add2 (side : Fin 2) (e : Exponent) :
    e side + e (otherBlock side) = seedWeight e := by
  unfold seedWeight
  rw [Finsupp.sum_fintype _ _ (by simp)]
  fin_cases side <;> simp [otherBlock, Fin.sum_univ_two, add_comm]

private theorem window_sum2 {F : Type} [Field F] {ι : Type*} [Fintype ι] {U d : ℕ}
    {side : Fin 2} (f : ι → Seed F) (hf : ∀ i, SeedWindow U d side (f i)) :
    SeedWindow U d side (∑ i, f i) := by
  intro e he
  rw [MvPolynomial.coeff_sum] at he
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  exact hf i e hi

theorem polynomialTest2_window {F : Type} [Field F] {s : Shape2} {t : Offset2 s}
    (α : F) (side : Fin 2) (v : Column2 s t → F[X]) {d : ℕ}
    (hd : ∀ u, (v u).natDegree ≤ d) {P : TrueSource2 F} (hP : Shaped2 s P) :
    SeedWindow s.U d side (polynomialTest2 α side v P) := by
  rw [polynomialTest2_apply]
  apply window_sum2
  intro u
  let f := (v u).toMvPolynomial side
  let g := input2 α u P
  have hf := side_degrees2 side (v u)
  have hg : g.totalDegree ≤ s.U := taylor2_seed_degree s α P hP _ _ _ _
  have hother : (f * g).degreeOf (otherBlock side) ≤ s.U := by
    refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    exact (Nat.add_le_add hf.1 ((MvPolynomial.degreeOf_le_totalDegree g _).trans hg)).trans_eq
      (Nat.zero_add _)
  have htotal : (f * g).totalDegree ≤ s.U + d :=
    (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (hf.2.trans (hd u)) hg).trans_eq (Nat.add_comm _ _))
  intro e he
  have hMem : e ∈ (f * g).support := MvPolynomial.mem_support_iff.mpr he
  refine ⟨(MvPolynomial.le_degreeOf_of_mem_support _ hMem).trans hother, ?_⟩
  rw [seedWeight_add2 side e]
  exact (show seedWeight e ≤ _ from MvPolynomial.le_totalDegree hMem).trans htotal

theorem polynomialTests2_to_poleMatrix2 {F : Type} [Field F] {s : Shape2} (t : Offset2 s)
    (α : F) (side : Fin 2) (a b c : F) (P : TrueSource2 F)
    (Q : Matrix (Pivot2 s t) (Column2 s t) F[X])
    (L : Matrix (Pivot2 s t) (Pivot2 s t) (OneSeedFrac F))
    (hL : poleMatrix2 s t (oneResidue a b c) = L * Q.map (algebraMap F[X] (OneSeedFrac F)))
    (hz : ∀ r, polynomialTest2 α side (Q r) P = 0) :
    poleMatrix2 s t (residue side a b c) *ᵥ
      (fun u => algebraMap (Seed F) (SeedFrac F) (input2 α u P)) = 0 := by
  let f := fractionSeedMap2 F side
  let V : Column2 s t → SeedFrac F := fun u => algebraMap (Seed F) (SeedFrac F) (input2 α u P)
  let Q' : Matrix (Pivot2 s t) (Column2 s t) (SeedFrac F) := Q.map (seedMap2 F side)
  have hM : (poleMatrix2 s t (oneResidue a b c)).map f = poleMatrix2 s t (residue side a b c) := by
    ext r u
    simp only [Matrix.map_apply, poleMatrix2, f, apply_ite, map_zero, map_mul, map_natCast,
      map_pow, fractionSeedMap2_residue]
    split_ifs <;> rfl
  have hQ : (Q.map (algebraMap F[X] (OneSeedFrac F))).map f = Q' := by
    ext r u
    exact fractionSeedMap2_polynomial side (Q r u)
  have hV : Q' *ᵥ V = 0 := by
    funext r
    change (∑ u, algebraMap (Seed F) (SeedFrac F) ((Q r u).toMvPolynomial side) *
      algebraMap (Seed F) (SeedFrac F) (input2 α u P)) = 0
    have hh := congrArg (algebraMap (Seed F) (SeedFrac F)) (hz r)
    simpa only [polynomialTest2_apply, map_sum, map_mul, map_zero] using hh
  change poleMatrix2 s t (residue side a b c) *ᵥ V = 0
  rw [← hM, hL, Matrix.map_mul, hQ, ← Matrix.mulVec_mulVec, hV, Matrix.mulVec_zero]

/-- Main 2-Jet Local Pole Moment Theorem (`c1_2jet`):
    Directly invokes `UpperBranch1.lean`'s generic `P1_7_1_1_2.proof` (`P1_7_1_1.c2`)
    on `bounded_pole_minors_2jet`. Valid in EVERY field & characteristic (no `s.B < K1.p`!). -/
theorem c1_2jet (F : Type) [Field F] (s : Shape2)
    (H : F[X]) (lift : (SeedFrac F)[X]) (α : F) (side : Fin 2) (a b c : F)
    (hH : H.eval α = 0) (hb : b ≠ 0)
    (hz : lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c) :
    ∃ d : Fin (poleRows2 s) → ℕ,
      (∑ r, d r) ≤ groupedPoleMoment2 s ∧
      ∃ tests : Fin (poleRows2 s) → TrueSource2 F →ₗ[F] Seed F,
        (∀ r P, Shaped2 s P → SeedWindow s.U (d r) side (tests r P)) ∧
        ∀ P, Shaped2 s P → (∀ r, tests r P = 0) →
          (jetConstant2 ((Polynomial.X (R := SeedFrac F) -
              Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B + s.J)) :
            JetPolys2 (SeedFrac F)) ∣ forward2 H lift P := by
  classical
  have hRows (t : Offset2 s) :=
    P1_7_1_1_2.proof F (Pivot2 s t) (Column2 s t) _ _ (bounded_pole_minors_2jet F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t : Offset2 s) (r : Pivot2 s t) := polynomialTest2 α side (Q t r)
  let e := rowIndex2 s
  refine ⟨fun k => d (e k).1 (e k).2, rowIndex2_sum s d hsum,
    fun k => tests (e k).1 (e k).2, ?_, ?_⟩
  · intro k P hP
    exact polynomialTest2_window α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t : Offset2 s) (r : Pivot2 s t) : tests t r P = 0 := by
      let testAt (k : AllPivots2 s) := tests k.1 k.2 P
      have hk : testAt (e (e.symm ⟨t, r⟩)) = 0 := hzero (e.symm ⟨t, r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z := residue side a b c
    have hslots := c1_2jet_local s α z P
      (fun t => polynomialTests2_to_poleMatrix2 t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd := zeroSubst2_dvd_of_zeroGrade2 s (localSlots2 s α z P) hslots
    rw [← centered2_eq_packGrades2 s α z P hP] at hd
    exact transfer_dvd_2jet H lift α z (s.B + s.J) P hH hz
      (linear_pole_dvd_2jet α z (s.B + s.J) P hd)

/-! ## 9. Global 2-Jet Pole Rank Bound (`simple_rank_le_2jet`) -/

private theorem poleTest2_of_local {F : Type} [Field F] (s : Shape2) {h : ℕ}
    {H : F[X]} {lift : (SeedFrac F)[X]} (G : SimplePoles h H lift)
    (P : TrueSource2 F)
    (hd : ∀ t, (jetConstant2 ((Polynomial.X (R := SeedFrac F) -
        Polynomial.C (algebraMap F (SeedFrac F) (G.root t))) ^ (s.B + s.J)) :
      JetPolys2 (SeedFrac F)) ∣ forward2 H lift P) :
    PoleTest2 s H lift P := by
  let r : Fin (2 * h) → (SeedFrac F)[X] := fun t =>
    Polynomial.X - Polynomial.C (algebraMap F (SeedFrac F) (G.root t))
  have hr : Pairwise (Function.onFun IsCoprime r) :=
    Polynomial.pairwise_coprime_X_sub_C
      ((algebraMap F (SeedFrac F)).injective.comp G.distinct)
  have hcop : Pairwise (Function.onFun IsCoprime
      (fun t => (jetConstant2 (r t ^ (s.B + s.J)) : JetPolys2 (SeedFrac F)))) := by
    intro t u hne
    exact ((hr hne).pow).map jetConstant2
  have hp := Fintype.prod_dvd_of_coprime hcop hd
  have hprod : H.map (algebraMap F (SeedFrac F)) = ∏ t, r t := by
    rw [G.factorization, Polynomial.map_prod]
    simp [r]
  unfold PoleTest2
  rw [hprod, ← Finset.prod_pow, map_prod]
  exact hp

private abbrev ScalarRow2 {h : ℕ} (s : Shape2) (d : Fin (2 * h) → Fin (poleRows2 s) → ℕ) :=
  Σ t : Fin (2 * h), Σ r : Fin (poleRows2 s), Fin (triangle s.U + (s.U + 1) * d t r)

private theorem scalarRow2_card_le {h : ℕ} (s : Shape2)
    (d : Fin (2 * h) → Fin (poleRows2 s) → ℕ) (hd : ∀ t, (∑ r, d t r) ≤ groupedPoleMoment2 s) :
    Fintype.card (ScalarRow2 s d) ≤ poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s := by
  classical
  simp only [ScalarRow2, Fintype.card_sigma, Fintype.card_fin]
  calc
    (∑ t : Fin (2 * h), ∑ r : Fin (poleRows2 s), (triangle s.U + (s.U + 1) * d t r)) ≤
        ∑ _ : Fin (2 * h), (poleRows2 s * triangle s.U + (s.U + 1) * groupedPoleMoment2 s) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hd t)) _
    _ = poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (2 * h) * (poleRows2 s * triangle s.U + (s.U + 1) * groupedPoleMoment2 s) = _
      unfold poleCredit2
      ring

private theorem shaped2_combination {F ι : Type} [Field F] [Fintype ι] {s : Shape2}
    {P : ι → TrueSource2 F} (hP : ∀ k, Shaped2 s (P k)) (v : ι → F) :
    Shaped2 s (Fintype.linearCombination F P v) := by
  intro e₂ e₁ e₀ a e hne
  rw [Fintype.linearCombination_apply] at hne
  simp only [sourceCoeff2, Polynomial.finsetSum_coeff, Polynomial.coeff_smul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul] at hne
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact hP k e₂ e₁ e₀ a e (right_ne_zero_of_mul hk)

/-- Global 2-Jet Simple-Poles Rank Bound (`simple_rank_le_2jet`):
    exact 2-jet analog of `UpperBranch1.P1_7_1.simple_rank_le`, valid in EVERY field! -/
theorem simple_rank_le_2jet {F ι : Type} [Field F] [Fintype ι] {h : ℕ}
    {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) (s : Shape2) (P : ι → TrueSource2 F)
    (hP : ∀ k, Shaped2 s (P k)) {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest2 s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s := by
  classical
  have ht (t : Fin (2 * h)) := c1_2jet F s H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
    (G.vanishes t) (G.b_ne t) (G.centre t)
  choose d hd tests hwindow htest using ht
  have hread (t : Fin (2 * h)) (r : Fin (poleRows2 s)) := seedWindow_read F s.U (d t r) (G.side t)
  choose read hread using hread
  let f : (ι → F) →ₗ[F] (ScalarRow2 s d → F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2).comp (read r.1 r.2.1)).comp
        ((tests r.1 r.2.1).comp (Fintype.linearCombination F P))
  have hker : LinearMap.ker f ≤ LinearMap.ker M.mulVecLin := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest2_of_local s G
    intro t
    have hv' := shaped2_combination hP v
    apply htest t _ hv'
    intro r
    apply hread t r _ (hwindow t r _ hv')
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t, r, k⟩
  have hn := Submodule.finrank_mono hker
  have hr : Module.finrank F (LinearMap.range f) ≤
      poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s := by
    refine (LinearMap.range f).finrank_le.trans ?_
    rw [Module.finrank_pi]
    exact scalarRow2_card_le s d hd
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

#print axioms transfer_dvd_2jet
#print axioms linear_pole_dvd_2jet
#print axioms canonical_minor_det_eq_one
#print axioms bounded_pole_minors_2jet
#print axioms c1_2jet
#print axioms simple_rank_le_2jet

end
end PoleMoment2Jet

end Merged_PoleMoment2Jet

-- merged module PoleBound2Jet
section Merged_PoleBound2Jet

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1600000

/-!
# Global 2-Jet Pole Rank Bound (`PoleBound2Jet`)

Completes Piece 1 by connecting `PoleMoment2Jet.simple_rank_le_2jet` to
`PortHighBase.regular_deformation` and `Fast065.specialization_rank_le`, delivering:
- `Source2`, `ambient2`, `physical2`, `poleSpace2`, `contacted2`, `complete2`
- `matrix_of_columns_2jet` (`K1_14_1_7_4` 2-jet analog)
- `pole_bound_2jet`:
    `Module.finrank L (contacted2 h word s W) ≤`
      `poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s +`
        `Module.finrank L (complete2 Crt word s W)`
-/

namespace PoleBound2Jet
noncomputable section

open Polynomial Matrix Finset
open K1 (I)
open K1_14 (L triangle)
open K1_14_1 (SeedPoly SeedField seedWeight PoleData CRTLift poleProduct rawBlock crtPolynomial nodeL)
open K1_14_1_7 (Seed SeedFrac Exponent Parameter GenericField specialPoint genericPoint liftAt
  RegularDeformation specialization_rank_le)
open PoleMoment2Jet
open scoped BigOperators Matrix Polynomial

open P0_10_1_1 (regular_deformation)

abbrev Source2 := TrueSource2 L
abbrev RawSource2 := JetPolys2 SeedField

def coeffAt2 (P : Source2) (e₂ e₁ e₀ a : ℕ) (e : Fin 2 →₀ ℕ) : L :=
  sourceCoeff2 P e₂ e₁ e₀ a e

def trueEligible2 (h : ℕ) (s : Shape2) (W e₂ e₁ e₀ a : ℕ) (e : Fin 2 →₀ ℕ) : Prop :=
  e₀ + e₁ + e₂ ≤ s.B ∧ jetIdx e₁ e₂ ≤ s.J ∧ e₂ ≤ s.C ∧ seedWeight e ≤ s.U ∧
    a + (e₀ + e₁ + e₂) * (131071 + h) ≤ W + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂

def ambient2 (h : ℕ) (s : Shape2) (W : ℕ) : Submodule L Source2 where
  carrier := {P | ∀ e₂ e₁ e₀ a e, ¬ trueEligible2 h s W e₂ e₁ e₀ a e → coeffAt2 P e₂ e₁ e₀ a e = 0}
  zero_mem' := by simp [coeffAt2, sourceCoeff2]
  add_mem' := by
    intro P Q hP hQ e₂ e₁ e₀ a e he
    have hp := hP e₂ e₁ e₀ a e he
    have hq := hQ e₂ e₁ e₀ a e he
    unfold coeffAt2 sourceCoeff2 at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro b P hP e₂ e₁ e₀ a e he
    have hp := hP e₂ e₁ e₀ a e he
    unfold coeffAt2 sourceCoeff2 at hp ⊢
    simp [Polynomial.coeff_smul, hp]

private def substituteJets2L {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring A] [Algebra R S] [Algebra R A]
    (base : S →ₐ[R] A) (y0 y1 y2 : A) : Polynomial (Polynomial (Polynomial S)) →ₐ[R] A :=
  eval₂AlgHom (eval₂AlgHom (eval₂AlgHom base y0 (fun _ => Commute.all _ _))
    y1 (fun _ => Commute.all _ _)) y2 (fun _ => Commute.all _ _)

/-- 2-Jet physical Hasse contact evaluation at node `(x, r)`:
    `X ↦ X + x`, `Y₀ ↦ r + X * Y₁ + X² * Y₂ + η`, `Y₁ ↦ Y₁`, `Y₂ ↦ Y₂`. -/
def atPhysical2 (x r : L) : Source2 →ₐ[L] Source2 :=
  let c : SeedPoly[X] →+* Source2 := jetConstant2
  let base : SeedPoly[X] →ₐ[L] SeedPoly[X] :=
    eval₂AlgHom (IsScalarTower.toAlgHom L SeedPoly SeedPoly[X])
      (Polynomial.X (R := SeedPoly) + (@Polynomial.C SeedPoly _) (MvPolynomial.C x))
      (fun _ => Commute.all _ _)
  let y0 : Source2 := C (C (Polynomial.X (R := SeedPoly[X])))
  let y1 : Source2 := C (Polynomial.X (R := SeedPoly[X][X]))
  let y2 : Source2 := Polynomial.X
  substituteJets2L (R := L) (S := SeedPoly[X]) (A := Source2)
    ((IsScalarTower.toAlgHom L SeedPoly[X] Source2).comp base)
    (c ((@Polynomial.C SeedPoly _) (MvPolynomial.C r)) +
      c (Polynomial.X (R := SeedPoly)) * y1 -
      c ((Polynomial.X (R := SeedPoly)) ^ 2) * y2 + y0)
    y1 y2

theorem atPhysical2_as_substitute (x r : L) :
    (atPhysical2 x r).toRingHom =
      PoleMoment2Jet.substitute2
        (jetConstant2.comp (eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C (MvPolynomial.C x))))
        (jetConstant2 (Polynomial.C (MvPolynomial.C r)) +
          jetConstant2 Polynomial.X * C Polynomial.X -
          jetConstant2 (Polynomial.X ^ 2) * Polynomial.X +
          C (C Polynomial.X))
        (C Polynomial.X) Polynomial.X := by
  rfl

def physical2 (word : I → L) (s : Shape2) : Submodule L Source2 where
  carrier := {P | ∀ i a b e₁ e₂ e, a + 3 * b < s.m →
    coeffAt2 (atPhysical2 (nodeL i) (word i) P) e₂ e₁ b a e = 0}
  zero_mem' := by simp [coeffAt2, sourceCoeff2]
  add_mem' := by
    intro P Q hP hQ i a b e₁ e₂ e he
    have hp := hP i a b e₁ e₂ e he
    have hq := hQ i a b e₁ e₂ e he
    unfold coeffAt2 sourceCoeff2 at hp hq ⊢
    simp [hp, hq]
  smul_mem' := by
    intro c P hP i a b e₁ e₂ e he
    have hp := hP i a b e₁ e₂ e he
    unfold coeffAt2 sourceCoeff2 at hp ⊢
    simp [Polynomial.coeff_smul, hp]

def poleSpace2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (s : Shape2) : Submodule L Source2 where
  carrier := {P | PoleTest2 s (poleProduct D) (crtPolynomial Crt) P}
  zero_mem' := by simp [PoleTest2]
  add_mem' := by
    intro P Q hP hQ
    change _ ∣ forward2 _ _ (P + Q)
    rw [map_add]
    exact dvd_add hP hQ
  smul_mem' := by
    intro b P hP
    change _ ∣ forward2 _ _ (b • P)
    rw [map_smul, Algebra.smul_def]
    exact dvd_mul_of_dvd_right hP _

def contacted2 (h : ℕ) (word : I → L) (s : Shape2) (W : ℕ) : Submodule L Source2 :=
  ambient2 h s W ⊓ physical2 word s

def complete2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : Submodule L Source2 :=
  contacted2 h word s W ⊓ poleSpace2 Crt s

theorem contacted2_shaped {h : ℕ} {word : I → L} {s : Shape2} {W : ℕ}
    {P : Source2} (hP : P ∈ contacted2 h word s W) : Shaped2 s P := by
  intro e₂ e₁ e₀ a e hn
  have he : trueEligible2 h s W e₂ e₁ e₀ a e := by
    by_contra hf
    exact hn (hP.1 e₂ e₁ e₀ a e hf)
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1⟩

private abbrev CoeffBox2 (B M U : ℕ) :=
  Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (M + 1) × (Fin 2 → Fin (U + 1))

theorem contacted2_finite (h : ℕ) (word : I → L) (s : Shape2) (W : ℕ) :
    Module.Finite L (contacted2 h word s W) := by
  let M := W + (s.B + s.J) * (2 * h) + s.J
  let f : contacted2 h word s W →ₗ[L] (CoeffBox2 s.B M s.U → L) :=
    LinearMap.pi fun u =>
      { toFun := fun P =>
          coeffAt2 P.1 u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val
            (Finsupp.equivFunOnFinite.symm (fun k => (u.2.2.2.2 k).val))
        map_add' := fun P Q => by simp [coeffAt2, sourceCoeff2]
        map_smul' := fun c P => by simp [coeffAt2, sourceCoeff2] }
  have hzero : ∀ Q : contacted2 h word s W, f Q = 0 → Q = 0 := by
    intro Q hQ
    apply Subtype.ext
    change Q.1 = 0
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    change coeffAt2 Q.1 e₂ e₁ e₀ a e = 0
    by_cases he : trueEligible2 h s W e₂ e₁ e₀ a e
    · obtain ⟨hB, hJ, _, hU, hW⟩ := he
      have hM : a ≤ M := by dsimp [M]; omega
      have hU' (k : Fin 2) : e k ≤ s.U := by
        apply le_trans _ hU
        rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      let u : CoeffBox2 s.B M s.U :=
        (⟨e₂, by omega⟩, ⟨e₁, by omega⟩, ⟨e₀, by omega⟩, ⟨a, by omega⟩,
          fun k => ⟨e k, Nat.lt_succ_of_le (hU' k)⟩)
      have hz := congrFun hQ u
      change coeffAt2 Q.1 e₂ e₁ e₀ a (Finsupp.equivFunOnFinite.symm (fun k => e k)) = 0 at hz
      exact (Finsupp.equivFunOnFinite.symm_apply_apply e) ▸ hz
    · exact Q.2.1 e₂ e₁ e₀ a e he
  apply Module.Finite.of_injective f
  intro P Q hPQ
  apply sub_eq_zero.mp
  exact hzero (P - Q) (by rw [map_sub, hPQ, sub_self])

/-! ## Parameter Specialization & `matrix_of_columns_2jet` -/

def jetMap2 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    JetPolys2 R →+* JetPolys2 S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom f)))

def mapSource2 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    TrueSource2 R →+* TrueSource2 S :=
  jetMap2 (MvPolynomial.map f)

theorem shaped2_map {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {s : Shape2} {P : TrueSource2 R} (hP : Shaped2 s P) : Shaped2 s (mapSource2 f P) := by
  intro e₂ e₁ e₀ a e hne
  apply hP e₂ e₁ e₀ a e
  intro hz
  apply hne
  unfold sourceCoeff2 at hz ⊢
  unfold mapSource2 jetMap2
  simp only [coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.coeff_map, hz, map_zero]

private def seedAt {F : Type} [Field F] (point : Parameter →+* F) :
    Seed Parameter →+* SeedFrac F :=
  (algebraMap (Seed F) (SeedFrac F)).comp (MvPolynomial.map point)

private def scalarJet2 {R : Type} [CommSemiring R] (d : R) : JetPolys2 R :=
  jetConstant2 (Polynomial.C d)

private def rawY0 {R : Type} [CommSemiring R] : JetPolys2 R := C (C (Polynomial.X (R := R[X])))
private def rawY1 {R : Type} [CommSemiring R] : JetPolys2 R := C (Polynomial.X (R := R[X][X]))
private def rawY2 {R : Type} [CommSemiring R] : JetPolys2 R := Polynomial.X

private def clearedY0 {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys2 R :=
  scalarJet2 d * (jetConstant2 H * rawY0) + jetConstant2 N

private def clearedY1 {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys2 R :=
  scalarJet2 d * (jetConstant2 H * rawY1 + jetConstant2 H.derivative * rawY0) +
    jetConstant2 N.derivative

private def clearedY2 {R : Type} [CommSemiring R] (H N : R[X]) (d : R) : JetPolys2 R :=
  scalarJet2 d * (jetConstant2 H * rawY2 + jetConstant2 H.derivative * rawY1 +
      jetConstant2 (hasseDeriv 2 H) * rawY0) +
    jetConstant2 (hasseDeriv 2 N)

private def cleared2 (s : Shape2) (H : Parameter[X]) (N : (Seed Parameter)[X])
    (d : Seed Parameter) (P : Source2) : TrueSource2 Parameter :=
  let h := H.map (MvPolynomial.C (σ := Fin 2))
  let y0 := clearedY0 h N d
  let y1 := clearedY1 h N d
  let y2 := clearedY2 h N d
  ∑ e₂ ∈ P.support, ∑ e₁ ∈ (P.coeff e₂).support, ∑ e₀ ∈ ((P.coeff e₂).coeff e₁).support,
    scalarJet2 d ^ (s.B - (e₀ + e₁ + e₂)) *
      (jetConstant2 ((((P.coeff e₂).coeff e₁).coeff e₀).map (MvPolynomial.map (Polynomial.C (R := L)))) *
        y0 ^ e₀ * y1 ^ e₁ * y2 ^ e₂)

private theorem eval_expansion2 {A T : Type} [CommSemiring A] [CommSemiring T]
    (f : JetPolys2 A →+* T) (P : JetPolys2 A) :
    f P = ∑ e₂ ∈ P.support, ∑ e₁ ∈ (P.coeff e₂).support, ∑ e₀ ∈ ((P.coeff e₂).coeff e₁).support,
      f (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) *
        f rawY0 ^ e₀ * f rawY1 ^ e₁ * f rawY2 ^ e₂ := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow]
  apply Finset.sum_congr rfl; intro e₂ _
  conv_lhs => rw [(P.coeff e₂).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro e₁ _
  conv_lhs => rw [((P.coeff e₂).coeff e₁).as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul, jetConstant2, RingHom.comp_apply,
    rawY0, rawY1, rawY2]

private theorem degree_of_shaped2 {s : Shape2} {P : Source2} (hP : Shaped2 s P)
    {e₂ e₁ e₀ : ℕ} (h0 : e₀ ∈ ((P.coeff e₂).coeff e₁).support) : e₀ + e₁ + e₂ ≤ s.B := by
  have hn : ((P.coeff e₂).coeff e₁).coeff e₀ ≠ 0 := Polynomial.mem_support_iff.mp h0
  by_contra hb
  apply hn
  apply Polynomial.ext; intro a
  apply MvPolynomial.ext; intro e
  simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra he
  exact hb (hP e₂ e₁ e₀ a e he).1

private theorem map_abscissa {F : Type} [Field F] (point : Parameter →+* F) (H : Parameter[X]) :
    (H.map (MvPolynomial.C (σ := Fin 2))).map (seedAt point) =
      (H.map point).map (algebraMap F (SeedFrac F)) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  apply RingHom.ext; intro a
  simp [seedAt, IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F)]

private theorem jetMap2_const {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : R[X]) : jetMap2 f (jetConstant2 p) = jetConstant2 (p.map f) := by
  simp [jetMap2, jetConstant2]

private theorem jetMap2_scalar {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : R) : jetMap2 f (scalarJet2 a) = scalarJet2 (f a) := by
  simp [scalarJet2, jetMap2_const]

private theorem jetMap2_rawY0 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    jetMap2 f rawY0 = rawY0 := by simp [jetMap2, rawY0]

private theorem jetMap2_rawY1 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    jetMap2 f rawY1 = rawY1 := by simp [jetMap2, rawY1]

private theorem jetMap2_rawY2 {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    jetMap2 f rawY2 = rawY2 := by simp [jetMap2, rawY2]

private theorem cleared2_specializes {F : Type} [Field F] (point : Parameter →+* F)
    (s : Shape2) (H : Parameter[X]) (N : (Seed Parameter)[X]) (d : Seed Parameter)
    (hd : MvPolynomial.map point d ≠ 0) (P : Source2) (hP : Shaped2 s P) :
    jetMap2 (seedAt point) (cleared2 s H N d P) =
      scalarJet2 (seedAt point d) ^ s.B *
        forward2 (H.map point) (liftAt point N d)
          (mapSource2 (point.comp (Polynomial.C (R := L))) P) := by
  let sd := seedAt point d
  have hsd : sd ≠ 0 := by
    intro hz
    exact hd (IsFractionRing.injective (Seed F) (SeedFrac F) (hz.trans (map_zero _).symm))
  let hp := (H.map point).map (algebraMap F (SeedFrac F))
  let lp := liftAt point N d
  have hlift_mul : C sd * lp = N.map (seedAt point) := by
    unfold lp liftAt
    rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    change C (sd * sd⁻¹) * N.map (seedAt point) = N.map (seedAt point)
    rw [mul_inv_cancel₀ hsd, map_one, one_mul]
  have hlift_der : C sd * lp.derivative = (N.derivative).map (seedAt point) := by
    rw [← Polynomial.derivative_C_mul, hlift_mul, Polynomial.derivative_map]
  have hlift_h2 : C sd * hasseDeriv 2 lp = (hasseDeriv 2 N).map (seedAt point) := by
    have hmul : hasseDeriv 2 (C sd * lp) = C sd * hasseDeriv 2 lp := by
      rw [← Polynomial.smul_eq_C_mul, map_smul, Polynomial.smul_eq_C_mul]
    rw [← hmul, hlift_mul, Polynomial.hasseDeriv_map]
  have hmapH : (H.map (MvPolynomial.C (σ := Fin 2))).map (seedAt point) = hp :=
    map_abscissa point H
  have hy0 : jetMap2 (seedAt point) (clearedY0 (H.map (MvPolynomial.C (σ := Fin 2))) N d) =
      scalarJet2 sd * (jetConstant2 hp * rawY0 + jetConstant2 lp) := by
    rw [clearedY0, map_add, map_mul, map_mul, jetMap2_scalar, jetMap2_const, jetMap2_const,
      jetMap2_rawY0, hmapH, ← hlift_mul, map_mul]
    exact (mul_add _ _ _).symm
  have hy1 : jetMap2 (seedAt point) (clearedY1 (H.map (MvPolynomial.C (σ := Fin 2))) N d) =
      scalarJet2 sd * (jetConstant2 hp * rawY1 + jetConstant2 hp.derivative * rawY0 +
        jetConstant2 lp.derivative) := by
    rw [clearedY1, map_add, map_mul, map_add, map_mul, map_mul, jetMap2_scalar, jetMap2_const,
      jetMap2_const, jetMap2_const, jetMap2_rawY0, jetMap2_rawY1, ← Polynomial.derivative_map,
      hmapH, ← hlift_der, map_mul]
    exact (mul_add _ _ _).symm
  have hy2 : jetMap2 (seedAt point) (clearedY2 (H.map (MvPolynomial.C (σ := Fin 2))) N d) =
      scalarJet2 sd * (jetConstant2 hp * rawY2 + jetConstant2 hp.derivative * rawY1 +
        jetConstant2 (hasseDeriv 2 hp) * rawY0 + jetConstant2 (hasseDeriv 2 lp)) := by
    rw [clearedY2, map_add, map_mul, map_add, map_add, map_mul, map_mul, map_mul, jetMap2_scalar,
      jetMap2_const, jetMap2_const, jetMap2_const, jetMap2_const, jetMap2_rawY0, jetMap2_rawY1,
      jetMap2_rawY2, ← Polynomial.derivative_map, ← Polynomial.hasseDeriv_map, hmapH, ← hlift_h2,
      map_mul]
    exact (mul_add _ _ _).symm
  let Fhom := (forward2 (H.map point) lp).toRingHom.comp
    (mapSource2 (point.comp (Polynomial.C (R := L))))
  have hFbase (q : SeedPoly[X]) :
      Fhom (jetConstant2 q) =
        jetConstant2 ((q.map (MvPolynomial.map (Polynomial.C (R := L)))).map (seedAt point)) := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ (jetConstant2 q)) = _
    rw [forward2_as_substitute, mapSource2, jetMap2_const, substitute2_base]
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 2
    apply MvPolynomial.ringHom_ext
    · intro a; simp [seedAt]
    · intro j; simp [seedAt]
  have hFy0 : Fhom rawY0 = jetConstant2 hp * rawY0 + jetConstant2 lp := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ rawY0) = _
    rw [forward2_as_substitute]
    simp [mapSource2, jetMap2, rawY0, hp, lp]
  have hFy1 : Fhom rawY1 = jetConstant2 hp * rawY1 + jetConstant2 hp.derivative * rawY0 +
      jetConstant2 lp.derivative := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ rawY1) = _
    rw [forward2_as_substitute]
    simp [mapSource2, jetMap2, rawY0, rawY1, hp, lp]
  have hFy2 : Fhom rawY2 = jetConstant2 hp * rawY2 + jetConstant2 hp.derivative * rawY1 +
      jetConstant2 (hasseDeriv 2 hp) * rawY0 + jetConstant2 (hasseDeriv 2 lp) := by
    change (forward2 (H.map point) lp).toRingHom (mapSource2 _ rawY2) = _
    rw [forward2_as_substitute]
    simp [mapSource2, jetMap2, rawY0, rawY1, rawY2, hp, lp]
  change _ = scalarJet2 sd ^ s.B * Fhom P
  rw [eval_expansion2 Fhom P, Finset.mul_sum]
  unfold cleared2
  simp only [map_sum, map_mul, map_pow, hy0, hy1, hy2]
  apply Finset.sum_congr rfl; intro e₂ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e₀ h0
  have hB : e₀ + e₁ + e₂ ≤ s.B := degree_of_shaped2 hP h0
  have hpow : scalarJet2 sd ^ (s.B - (e₀ + e₁ + e₂)) *
      (scalarJet2 sd ^ e₀ * scalarJet2 sd ^ e₁ * scalarJet2 sd ^ e₂) =
      scalarJet2 sd ^ s.B := by
    rw [← pow_add, ← pow_add, ← pow_add, Nat.sub_add_cancel hB]
  have hc : jetMap2 (seedAt point) (scalarJet2 d) = scalarJet2 sd := by
    simp [jetMap2, scalarJet2, jetConstant2, sd]
  have hb : jetMap2 (seedAt point)
      (jetConstant2 ((((P.coeff e₂).coeff e₁).coeff e₀).map (MvPolynomial.map (Polynomial.C (R := L))))) =
      Fhom (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) := by
    rw [hFbase]
    simp [jetMap2, jetConstant2]
  rw [hc, hb, ← hFy0, ← hFy1, ← hFy2]
  simp only [mul_pow]
  calc
    scalarJet2 sd ^ (s.B - (e₀ + e₁ + e₂)) *
        (Fhom (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) *
          (scalarJet2 sd ^ e₀ * Fhom rawY0 ^ e₀) *
          (scalarJet2 sd ^ e₁ * Fhom rawY1 ^ e₁) *
          (scalarJet2 sd ^ e₂ * Fhom rawY2 ^ e₂)) =
      (scalarJet2 sd ^ (s.B - (e₀ + e₁ + e₂)) *
        (scalarJet2 sd ^ e₀ * scalarJet2 sd ^ e₁ * scalarJet2 sd ^ e₂)) *
        (Fhom (jetConstant2 (((P.coeff e₂).coeff e₁).coeff e₀)) *
          Fhom rawY0 ^ e₀ * Fhom rawY1 ^ e₁ * Fhom rawY2 ^ e₂) := by ring
    _ = _ := by rw [hpow]

private abbrev Row2 := ℕ × ℕ × ℕ × ℕ × Exponent

private def readRow2 {R : Type} [CommRing R] (Q : TrueSource2 R) (G : (Seed R)[X]) (r : Row2) : R :=
  (((((Q.coeff r.1).coeff r.2.1).coeff r.2.2.1) %ₘ G).coeff r.2.2.2.1).coeff r.2.2.2.2

private def rowsOfColumn2 (Q : TrueSource2 Parameter) (G : (Seed Parameter)[X]) : Finset Row2 :=
  Q.support.biUnion fun e₂ => (Q.coeff e₂).support.biUnion fun e₁ =>
    ((Q.coeff e₂).coeff e₁).support.biUnion fun e₀ =>
      let p := (((Q.coeff e₂).coeff e₁).coeff e₀) %ₘ G
      p.support.biUnion fun a => (p.coeff a).support.image fun e => (e₂, e₁, e₀, a, e)

private theorem mem_rowsOfColumn2 (Q : TrueSource2 Parameter) (G : (Seed Parameter)[X])
    (r : Row2) (hr : readRow2 Q G r ≠ 0) : r ∈ rowsOfColumn2 Q G := by
  obtain ⟨e₂, e₁, e₀, a, e⟩ := r
  refine Finset.mem_biUnion.mpr ⟨e₂, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨e₁, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨e₀, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨a, Polynomial.mem_support_iff.mpr (fun h => hr (by simp [readRow2, h])), ?_⟩
  exact Finset.mem_image.mpr ⟨e, MvPolynomial.mem_support_iff.mpr hr, rfl⟩

private theorem readRow2_map {F : Type} [Field F] (point : Parameter →+* F)
    (Q : TrueSource2 Parameter) {G : (Seed Parameter)[X]} (hG : G.Monic) (r : Row2) :
    readRow2 (mapSource2 point Q) (G.map (MvPolynomial.map point)) r = point (readRow2 Q G r) := by
  simp only [readRow2, mapSource2, jetMap2, coe_mapRingHom, Polynomial.coeff_map,
    ← map_modByMonic (MvPolynomial.map point) hG, MvPolynomial.coeff_map]

private def readRow2Linear {F : Type} [Field F] (G : (Seed F)[X]) (r : Row2) :
    TrueSource2 F →ₗ[F] F :=
  (MvPolynomial.lcoeff F r.2.2.2.2).comp <|
    ((Polynomial.lcoeff (Seed F) r.2.2.2.1).restrictScalars F).comp <|
    ((Polynomial.modByMonicHom G).restrictScalars F).comp <|
    ((Polynomial.lcoeff (Seed F)[X] r.2.2.1).restrictScalars F).comp <|
    ((Polynomial.lcoeff (Seed F)[X][X] r.2.1).restrictScalars F).comp <|
    (Polynomial.lcoeff (Seed F)[X][X][X] r.1).restrictScalars F

private theorem readRow2_sum {F ι : Type} [Field F] [Fintype ι]
    (Q : ι → TrueSource2 F) (v : ι → F) (G : (Seed F)[X]) (r : Row2) :
    readRow2 (∑ k, v k • Q k) G r = ∑ k, v k * readRow2 (Q k) G r := by
  change readRow2Linear G r (∑ k, v k • Q k) = ∑ k, v k • readRow2Linear G r (Q k)
  simp only [map_sum, map_smul]

private theorem dvd_iff_read2 {F : Type} [Field F] (Q : TrueSource2 F)
    {G : (Seed F)[X]} (hG : G.Monic) :
    (jetConstant2 (G.map (algebraMap (Seed F) (SeedFrac F))) : JetPolys2 (SeedFrac F)) ∣
      jetMap2 (algebraMap (Seed F) (SeedFrac F)) Q ↔
      ∀ r, readRow2 Q G r = 0 := by
  let f := algebraMap (Seed F) (SeedFrac F)
  have h : (jetConstant2 (G.map f) : JetPolys2 (SeedFrac F)) ∣ jetMap2 f Q ↔
      ∀ e₂ e₁ e₀, (((Q.coeff e₂).coeff e₁).coeff e₀) %ₘ G = 0 := by
    simp only [jetConstant2, RingHom.comp_apply, C_dvd_iff_dvd_coeff,
      jetMap2, coe_mapRingHom, Polynomial.coeff_map]
    apply forall_congr'; intro e₂
    apply forall_congr'; intro e₁
    apply forall_congr'; intro e₀
    rw [← modByMonic_eq_zero_iff_dvd (hG.map f), ← map_modByMonic f hG,
      Polynomial.map_eq_zero_iff (IsFractionRing.injective (Seed F) (SeedFrac F))]
  rw [h]
  constructor
  · intro hz r; simp [readRow2, hz]
  · intro hz e₂ e₁ e₀
    apply Polynomial.ext; intro a
    rw [Polynomial.coeff_zero]
    apply MvPolynomial.ext; intro e
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact hz (e₂, e₁, e₀, a, e)

private theorem matrix_of_columns_2jet {ι : Type} [Fintype ι]
    (Q : ι → TrueSource2 Parameter) (G : (Seed Parameter)[X]) (hG : G.Monic) :
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      ∀ (F : Type) [Field F] (point : Parameter →+* F) (v : ι → F),
        (M.map point).mulVec v = 0 ↔
          (jetConstant2 (G.map (seedAt point)) : JetPolys2 (SeedFrac F)) ∣
            ∑ k, v k • jetMap2 (seedAt point) (Q k) := by
  classical
  let rows := Finset.univ.biUnion fun k => rowsOfColumn2 (Q k) G
  let e : Fin rows.card ≃ ↥rows := (Fintype.equivFinOfCardEq (Fintype.card_coe rows)).symm
  let M : Matrix (Fin rows.card) ι Parameter := fun r k => readRow2 (Q k) G (e r).val
  refine ⟨rows.card, M, ?_⟩
  intro F _ point v
  let inc := algebraMap (Seed F) (SeedFrac F)
  let incAlg : TrueSource2 F →ₐ[F] JetPolys2 (SeedFrac F) :=
    mapAlgHom (mapAlgHom (mapAlgHom (mapAlgHom (IsScalarTower.toAlgHom F (Seed F) (SeedFrac F)))))
  let G' := G.map (MvPolynomial.map point)
  let Q' : ι → TrueSource2 F := fun k => mapSource2 point (Q k)
  let q := ∑ k, v k • Q' k
  have hcomp (k : ι) : incAlg (Q' k) = jetMap2 (seedAt point) (Q k) := by
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    simp only [incAlg, Q', mapSource2, jetMap2, coe_mapRingHom, Polynomial.coeff_map,
      Polynomial.coeff_mapAlgHom_apply, seedAt, RingHom.comp_apply]
    rfl
  have hq : jetMap2 inc q = ∑ k, v k • jetMap2 (seedAt point) (Q k) := by
    change incAlg (∑ k, v k • Q' k) = _
    simp only [map_sum, map_smul, hcomp]
  have hGmap : G.map (seedAt point) = G'.map inc := by
    dsimp only [G', seedAt, inc]
    exact (Polynomial.map_map (MvPolynomial.map point) (algebraMap (Seed F) (SeedFrac F)) G).symm
  rw [← hq, hGmap, dvd_iff_read2 q (hG.map _)]
  have hread (r : Row2) : readRow2 q G' r = ∑ k, v k * point (readRow2 (Q k) G r) := by
    rw [readRow2_sum]
    simp only [Q', G', readRow2_map point _ hG]
  have heval (r : Fin rows.card) : ((M.map point).mulVec v) r = readRow2 q G' (e r).val := by
    rw [hread]
    change ∑ k, point (readRow2 (Q k) G (e r).val) * v k = _
    simp only [mul_comm]
  change (M.map point).mulVec v = 0 ↔ ∀ r, readRow2 q G' r = 0
  constructor
  · intro hv r
    by_cases hr : r ∈ rows
    · have he := congrFun hv (e.symm ⟨r, hr⟩)
      rw [heval] at he
      simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using he
    · rw [hread]
      apply Finset.sum_eq_zero; intro k _
      have hz : readRow2 (Q k) G r = 0 := by
        by_contra hn
        exact hr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, mem_rowsOfColumn2 _ _ _ hn⟩)
      rw [hz, map_zero, mul_zero]
  · intro hv
    funext r
    exact (heval r).trans (hv (e r).val)

private theorem deformation_matrix_2jet {h : ℕ} {D : PoleData h} {Crt : CRTLift D}
    (E : RegularDeformation D Crt) (s : Shape2) {ι : Type} [Fintype ι]
    (P : ι → Source2) (hP : ∀ k, Shaped2 s (P k)) :
    ∃ n : ℕ, ∃ M : Matrix (Fin n) ι Parameter,
      (∀ v : ι → L, (M.map specialPoint).mulVec v = 0 ↔
        PoleTest2 s (poleProduct D) (crtPolynomial Crt) (Fintype.linearCombination L P v)) ∧
      ∀ v : ι → GenericField, (M.map genericPoint).mulVec v = 0 ↔
        PoleTest2 s (E.H.map genericPoint) (liftAt genericPoint E.num E.den)
          (Fintype.linearCombination GenericField
            (fun k => mapSource2 (genericPoint.comp (Polynomial.C (R := L))) (P k)) v) := by
  classical
  let G := (E.H.map (MvPolynomial.C (σ := Fin 2))) ^ (s.B + s.J)
  obtain ⟨n, M, hM⟩ := matrix_of_columns_2jet (fun k => cleared2 s E.H E.num E.den (P k)) G
    ((E.monic.map _).pow _)
  have fibre {F : Type} [Field F] (point : Parameter →+* F)
      (hd : MvPolynomial.map point E.den ≠ 0) (v : ι → F) :
      (M.map point).mulVec v = 0 ↔
        PoleTest2 s (E.H.map point) (liftAt point E.num E.den)
          (Fintype.linearCombination F
            (fun k => mapSource2 (point.comp (Polynomial.C (R := L))) (P k)) v) := by
    let f := forward2 (E.H.map point) (liftAt point E.num E.den)
    let d := scalarJet2 (seedAt point E.den)
    have hu : IsUnit d := by
      have hn : seedAt point E.den ≠ 0 := by
        intro hzero
        exact hd (IsFractionRing.injective (Seed F) (SeedFrac F) (hzero.trans (map_zero _).symm))
      exact (isUnit_iff_ne_zero.mpr hn).map (jetConstant2.comp Polynomial.C)
    rw [hM F point v]
    simp only [cleared2_specializes point s E.H E.num E.den hd _ (hP _)]
    have hsum : (∑ k, v k • (d ^ s.B * f (mapSource2 (point.comp (Polynomial.C (R := L))) (P k)))) =
        d ^ s.B * f (Fintype.linearCombination F
          (fun k => mapSource2 (point.comp (Polynomial.C (R := L))) (P k)) v) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
    have hG : G.map (seedAt point) =
        ((E.H.map point).map (algebraMap F (SeedFrac F))) ^ (s.B + s.J) := by
      simp only [G, Polynomial.map_pow, map_abscissa]
    rw [hsum, (hu.pow s.B).dvd_mul_left, hG]
    rfl
  refine ⟨n, M, ?_, fibre genericPoint E.genericDen⟩
  intro v
  have hpoint : specialPoint.comp (Polynomial.C (R := L)) = RingHom.id L := by
    ext a; simp [specialPoint]
  have hmap (Q : Source2) : mapSource2 (RingHom.id L) Q = Q := by
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    simp only [mapSource2, jetMap2, coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.map_id]
  simpa only [E.specialH, E.specialLift, hpoint, hmap] using fibre specialPoint E.specialDen v

/-- Main Global 2-Jet Pole Rank Bound (`pole_bound_2jet`):
    exact 2-jet analog of `UpperBranch1.P1_7_1.pole_bound` — without `s.B < K1.p`! -/
theorem pole_bound_2jet {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape2) (W : ℕ) :
    Module.finrank L (contacted2 h word s W) ≤
      poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s +
        Module.finrank L (complete2 Crt word s W) := by
  classical
  obtain ⟨E⟩ := regular_deformation hpos hchar D Crt
  let A := contacted2 h word s W
  let _ : Module.Finite L A := contacted2_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source2 := fun k => basis k
  have hP (k : Fin d) : Shaped2 s (P k) := contacted2_shaped (basis k).property
  obtain ⟨n, M, hspecial, hg⟩ := deformation_matrix_2jet E s P hP
  let embed := genericPoint.comp (Polynomial.C (R := L))
  have hgen := simple_rank_le_2jet E.genericPoles s _
    (fun k => shaped2_map embed (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source2) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source2) ∈ complete2 Crt word s W := by
    have hv := (hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete2 Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete2 Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete2 Crt word s W => (x : Source2)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega

#print axioms pole_bound_2jet

end
end PoleBound2Jet

end Merged_PoleBound2Jet
