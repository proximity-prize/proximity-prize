import ProximityPrize.SubmissionLower.Rect52RegularSmall
import ProximityPrize.SubmissionLower.Rect51TangentSupport
import ProximityPrize.SubmissionLower.Rect51ProperTariff

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000

namespace Rect52Regular
noncomputable section
open Polynomial Finset
open P1 (K I node p)
open High52 (agreement degreeAt quotientOrder asLooseModel asLooseFamily AnchorModel AnchoredFamily
  RegularCount FixedWord)
open HighCore82706Tangent (Input ResidueLift Factors FlatSections componentMarks mem_componentMarks
  root_component)
open K1_14 (L Equation atMark graphEval)
open K1_14_4 (seedDegree seedDegree_le_iff)
open Rect51Tangent (Axes)
open scoped BigOperators

abbrev Chart {u del Γ} (h : ℕ) (M : AnchorModel u del) (F : AnchoredFamily M Γ) (H : L[X]) :=
  Effective70Poles.Chart h (asLooseModel M) (asLooseFamily M F) H

/-- Bounds for an effective block height that can exceed the model overhead. -/
structure Window {u : P1.Words} {del : Finset I} (M : AnchorModel u del) (lo hi h : ℕ) : Prop where
  positive : 0 < h
  lower : lo ≤ h
  upper : h ≤ hi
  hi_cap : hi ≤ 33463
  overhead : M.overhead.toNat ≤ h

abbrev seedSum (v : Axes) : ℕ := v 0 + v 1

theorem seed_bound {f : Equation} {v : Axes} (h : Rect51Tangent.SeedBound f v) :
    K1_14.SeedBound f (seedSum v) := by
  intro j
  apply Finset.sup_le
  intro m hm
  have h₀ := MvPolynomial.degreeOf_le_iff.mp (h j 0) m hm
  have h₁ := MvPolynomial.degreeOf_le_iff.mp (h j 1) m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  exact Nat.add_le_add h₀ h₁

/-- The proper component count used by the rectangular retained tariff. -/
def ProperCounter : Prop :=
  ∀ (A : ℕ) (J : Input), 4 ≤ J.e → A ≤ 262144 → degreeAt J.hi < A →
    quotientOrder J.lo ≤ A → ∀ {v : Axes}, Rect51Tangent.SeedBound J.f v →
    (∀ γ ∈ J.marks, ∃ T : Finset I, A ≤ T.card ∧
      ∀ i ∈ T, (J.family.scalar γ).eval (node i) = J.model.word i) →
    ∀ {B : ResidueLift J} (D : Factors J B),
      (componentMarks J D.proper).card ≤ Rect51Proper.properFee A J.lo J.hi J.e (v 0) (v 1)

def regularFee (lo hi e : ℕ) (v : Axes) : ℕ :=
  Rect51Proper.properFee agreement lo hi e (v 0) (v 1) + High52.flatFee hi (seedSum v) + e

def wholeFee (lo hi e : ℕ) (v : Axes) : ℕ :=
  High52.singularFee e (seedSum v) + regularFee lo hi e v

private theorem flat_sections (J : Input) (B : ResidueLift J) (D : Factors J B) :
    ∀ j, FlatSections J (D.flat j) := by
  intro j
  obtain ⟨E⟩ := HighCore82706Tangent_4.of_children
    HighCore82706Tangent_4_1.proof HighCore82706Tangent_4_2.proof J B D j
  exact HighCore82706Tangent_5.of_children HighCore82706Tangent_5_1.proof
    HighCore82706Tangent_5_2.proof J B D j E

/-- Add all flat factors to an existing bound for the proper factor. -/
theorem count_of_proper (J : Input) (hd : degreeAt J.hi < agreement)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    {B : ResidueLift J} (D : Factors J B) {fee : ℕ}
    (hp : (componentMarks J D.proper).card ≤ fee) :
    J.marks.card ≤ fee + High52.flatFee J.hi J.v + J.e := by
  classical
  let U := fun j => componentMarks J (D.flat j)
  have hcov : J.marks ⊆ componentMarks J D.proper ∪ univ.biUnion U := by
    intro γ hγ
    rcases root_component J D hγ with ht | ⟨j, hu⟩
    · exact mem_union.mpr (Or.inl (mem_componentMarks.mpr ⟨hγ, ht⟩))
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j, mem_univ _, mem_componentMarks.mpr ⟨hγ,hu⟩⟩))
  have hc := (card_le_card hcov).trans (card_union_le _ _)
  have hf := card_biUnion_le.trans (High52_5.flat_count J hd hword D (flat_sections J B D))
  change (univ.biUnion U).card ≤ High52.flatFee J.hi J.v + J.e at hf
  omega

private theorem regular_via_input {u : P1.Words} {del : Finset I} {Γ : Finset K} {lo hi h v fee : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : Window M lo hi h)
    (hshift : M.shift ∉ Γ) {H : L[X]} (hH : Chart h M F H)
    {f : Equation} (hf : High52.Reduced f) (he : 3 ≤ f.natDegree)
    (hpos : 0 < seedDegree f) (hseed : K1_14.SeedBound f v)
    (hsep : High52.singularDegree f.natDegree v < p)
    (hflat : f.natDegree * degreeAt hi + v < p)
    (method : ∀ J : Input, J.lo = lo → J.hi = hi → J.f = f → J.v = v →
      FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) → J.marks.card ≤ fee) :
    RegularCount M F f fee := by
  intro T hT hreg
  have hell : 0 < quotientOrder h := by
    change 0 < 131071-h
    have hbd := hw.upper.trans hw.hi_cap
    omega
  have hd : degreeAt hi ≤ 164534 := Nat.add_le_add_left hw.hi_cap 131071
  have hgap : degreeAt hi < HighCore82706.agreement := hd.trans_lt (by decide)
  let J : Input := {
    words := u, deleted := del, model := asLooseModel M, labels := Γ, family := asLooseFamily M F
    shift_out := hshift, height := h, overhead_le_height := hw.overhead, block := H, chart := hH
    marks := T, marks_sub := hT, f := f, regular := hreg, reduced := hf, sheets := he, seed_pos := hpos
    v := v, seed_bound := hseed, lo := lo, hi := hi, lower := hw.lower, upper := hw.upper
    positive := hw.positive, quotient_pos := hell, agreement_gap := hgap
    factorial_guard := (Nat.succ_le_of_lt hgap).trans_lt (by decide)
    separant_guard := hsep, flat_guard := hflat }
  have hweak := HighCore82706Tangent.fixed_word J (Finset.Subset.refl J.marks)
  have hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) :=
    ⟨hweak.distinct, hweak.degree, fun γ hγ => by
      let m := F.mark γ (hT hγ)
      exact ⟨m.bad.support,m.bad.agreement,m.scalar_hits⟩⟩
  exact method J rfl rfl rfl rfl hword

private theorem actual_gap (J : Input) : degreeAt J.hi < agreement :=
  J.agreement_gap.trans_le (by decide)

theorem count_regular_rect (proper : ProperCounter)
    {u : P1.Words} {del : Finset I} {Γ : Finset K} {lo hi h : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : Window M lo hi h)
    (hshift : M.shift ∉ Γ) {H : L[X]} (hH : Chart h M F H) {f : Equation}
    (hf : High52.Reduced f) (he : 4 ≤ f.natDegree) (hpos : 0 < seedDegree f)
    {v : Axes} (hv : Rect51Tangent.SeedBound f v)
    (hsep : High52.singularDegree f.natDegree (seedSum v) < p)
    (hflat : f.natDegree * degreeAt hi + seedSum v < p) :
    RegularCount M F f (regularFee lo hi f.natDegree v) := by
  refine regular_via_input M F hw hshift hH hf (by omega) hpos (seed_bound hv) hsep hflat ?_
  intro J hlo hhi hJf hJv hword
  have hd := actual_gap J
  have hJseed : Rect51Tangent.SeedBound J.f v := by rwa [hJf]
  have hJe : 4 ≤ J.e := by change 4 ≤ J.f.natDegree; rwa [hJf]
  have hL : quotientOrder J.lo ≤ agreement := (Nat.sub_le _ _).trans (by decide)
  obtain ⟨B⟩ := HighCore82706Tangent_1.proof J
  obtain ⟨D⟩ := HighCore82706Tangent_2.proof J B
  have hp := proper agreement J hJe (by decide) hd hL hJseed hword.hits D
  have ht := count_of_proper J hd hword D hp
  have heq : J.e = f.natDegree := congrArg Polynomial.natDegree hJf
  simpa only [regularFee, hlo, hhi, hJv, heq] using ht

theorem count_regular_triangular {u : P1.Words} {del : Finset I} {Γ : Finset K} {lo hi h v : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : Window M lo hi h)
    (hshift : M.shift ∉ Γ) {H : L[X]} (hH : Chart h M F H) {f : Equation}
    (hf : High52.Reduced f) (he : 3 ≤ f.natDegree) (hpos : 0 < seedDegree f)
    (hv : K1_14.SeedBound f v) (hsep : High52.singularDegree f.natDegree v < p)
    (hflat : f.natDegree * degreeAt hi + v < p) :
    RegularCount M F f (High52.tangentFee lo hi f.natDegree v) := by
  refine regular_via_input M F hw hshift hH hf he hpos hv hsep hflat ?_
  intro J hlo hhi hJf hJv hword
  obtain ⟨B⟩ := HighCore82706Tangent_1.proof J
  obtain ⟨D⟩ := HighCore82706Tangent_2.proof J B
  have lift := HighCore82706Tangent_3_1.of_children HighCore82706Tangent_3_1_1.proof HighCore82706_5_1.proof
  have profiles := HighCore82706_5_2.of_children HighCore82706_5_2_1.proof HighCore82706_5_2_2.proof
  have mixed := HighCore82706Tangent_3_2.of_children HighCore82706Tangent_3_2_1.proof
    HighCore82706Tangent_3_2_2.proof HighCore82706Tangent_3_2_3.proof profiles
    HighCore82706Tangent_3_2_5.proof HighCore82706Tangent_3_2_6.proof
  have shorten := HighCore82706Tangent_3_3.of_children HighCore82706Tangent_3_3_1.proof
    HighCore82706Tangent_3_3_2.proof
  obtain ⟨C⟩ := HighCore82706Tangent_3.of_children lift mixed shorten J B D
  have ht := High52_5.count J (actual_gap J) hword C (flat_sections J B D)
  have heq : J.e = f.natDegree := congrArg Polynomial.natDegree hJf
  simpa only [hlo,hhi,hJv,heq] using ht

/-- Charge singular roots by the stock resultant bound and use the fixed-word count when possible. -/
theorem count_with_singular {u : P1.Words} {del : Finset I} {Γ : Finset K} {f : Equation} {v fee : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hf : High52.Reduced f)
    (hs : K1_14.SeedBound f v) (hsep : High52.singularDegree f.natDegree v < p)
    (hfixed : f.natDegree ≤ fee) (regular : 0 < seedDegree f → RegularCount M F f fee)
    (T : Finset K) (hT : T ⊆ Γ)
    (roots : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) :
    T.card ≤ High52.singularFee f.natDegree v + fee := by
  classical
  by_cases hzero : seedDegree f = 0
  · exact (High52Model.fixed_count M F T hT hf.1 ((seedDegree_le_iff f 0).mp hzero.le) roots).trans
      (hfixed.trans (Nat.le_add_left _ _))
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  have hb : bad ⊆ T := filter_subset _ _
  have hbad := High52Model.resultant_count M hf hs hsep bad (fun _ hγ => (mem_filter.mp hγ).2)
  change bad.card ≤ High52.singularFee f.natDegree v at hbad
  have hreg : ∀ γ ∈ T \ bad, High52.regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht,hn⟩ := mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (roots γ ht) (fun hz => hn (mem_filter.mpr ⟨ht,hz⟩))
  have hc := regular (Nat.pos_of_ne_zero hzero) _ (sdiff_subset.trans hT) hreg
  have hpartition := card_sdiff_add_card_eq_card hb
  omega

theorem count_roots_rect (proper : ProperCounter)
    {u : P1.Words} {del : Finset I} {Γ : Finset K} {lo hi h : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : Window M lo hi h)
    (hshift : M.shift ∉ Γ) {H : L[X]} (hH : Chart h M F H) {f : Equation}
    (hf : High52.Reduced f) (he : 4 ≤ f.natDegree)
    {v : Axes} (hv : Rect51Tangent.SeedBound f v)
    (hsep : High52.singularDegree f.natDegree (seedSum v) < p)
    (hflat : f.natDegree * degreeAt hi + seedSum v < p)
    (T : Finset K) (hT : T ⊆ Γ)
    (roots : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) :
    T.card ≤ wholeFee lo hi f.natDegree v :=
  count_with_singular M F hf (seed_bound hv) hsep (Nat.le_add_left _ _)
    (fun hpos => count_regular_rect proper M F hw hshift hH hf he hpos hv hsep hflat) T hT roots

/-- Count all roots of each triangular fallback grade using the stock tariff. -/
theorem count_roots_triangular {u : P1.Words} {del : Finset I} {Γ : Finset K} {lo hi h v : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : Window M lo hi h)
    (hshift : M.shift ∉ Γ) {H : L[X]} (hH : Chart h M F H) {f : Equation}
    (hf : High52.Reduced f)
    (hv : K1_14.SeedBound f v) (hsep : High52.singularDegree f.natDegree v < p)
    (hflat : f.natDegree * degreeAt hi + v < p)
    (T : Finset K) (hT : T ⊆ Γ)
    (roots : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) :
    T.card ≤ High52.wholePrice lo hi f.natDegree v := by
  by_cases hz : v = 0
  · subst v
    exact (High52Model.fixed_count M F T hT hf.1 hv roots).trans_eq (by simp [High52.wholePrice])
  by_cases hsmall : f.natDegree ≤ 2
  · rw [High52.wholePrice, ite_eq_right hz, ite_eq_left hsmall]
    exact count_with_singular M F hf hv hsep (Nat.le_add_left _ _)
        (fun _ => Rect52RegularSmall.persistent_count M F hw.positive hw.lower hw.upper hw.hi_cap
          hw.overhead hH hf hv) T hT roots
  · rw [High52.wholePrice, ite_eq_right hz, ite_eq_right hsmall]
    exact count_with_singular M F hf hv hsep (Nat.le_add_left _ _)
        (fun hpos => count_regular_triangular M F hw hshift hH hf (by omega) hpos hv hsep hflat)
          T hT roots

#print axioms count_roots_rect
#print axioms count_roots_triangular
end
end Rect52Regular
