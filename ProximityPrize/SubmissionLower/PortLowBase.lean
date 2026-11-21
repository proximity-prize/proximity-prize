import ProximityPrize.SubmissionLower.Low27Definitions
import ProximityPrize.SubmissionLower.LowPrimary6921Source
import ProximityPrize.SubmissionLower.SharpBudget6929
set_option Elab.async false

section PackSource_P0_9_1Defs
set_option autoImplicit true
namespace P0_9_1
noncomputable section

open K1_13 (Geom)
open P0_9 (physicalDegree anchorCutoff)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The small physical bank with the high-grade cap on non-value jets. -/
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight physicalDegree) ≤ anchorCutoff

def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

def anchorLocal (center received : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 center received).domRestrict anchorSpace

end
end P0_9_1
end PackSource_P0_9_1Defs

section PackSource_P0_9_1Rank
set_option autoImplicit true
namespace P0_9_1
noncomputable section

open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open scoped BigOperators

open private exponent_le_of_mem_translation_monomial from ProximityPrize.SubmissionLower.Fast064

private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 90)

/-- All centered terms of abscissa exponent at least 90 vanish in the contact projection. -/
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 90 ≤ u none) :
    localConstraintAt 90 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 90 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega

private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 90 0 0 (truncateX Q) = localConstraintAt 90 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 90 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 90 <;> simp [hx]
    · by_cases hx : u none < 90 <;> simp [hx, coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]

private theorem centered_old_eligible {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : AnchorEligible u) (hx : v none < 90) :
    K1_13_1.AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg, hidx, hf, htail, _⟩ := hu
  have hcap : 48 - (u.some.degree - 113 + 1) / 2 ≤ 48 - (v.some.degree - 113 + 1) / 2 := by
    omega
  refine ⟨hd.trans hdeg, hi.trans hidx, (h _).trans hf, ?_, ?_⟩
  · exact (add_le_add (add_le_add (h _) (h _)) (h _)).trans (htail.trans hcap)
  · have hw := Finsupp.weight_le_weight
      (w := fun j : Fin 4 => 133671 - j.val) (w' := fun _ => 133671)
      (fun j => Nat.sub_le _ _) v.some
    have he : v.some.weight (fun _ => 133671) = 133671 * v.some.degree := by
      simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
        Finset.mul_sum, Nat.mul_comm]
    rw [he] at hw
    have hweight : differentialWeight (d := 3) 133671 =
        fun j => j.elim 1 (fun i => 133671 - i.val) := by
      funext j
      cases j <;> rfl
    rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
    calc
      _ ≤ 89 + 133671 * 120 :=
        Nat.add_le_add (Nat.le_of_lt_succ hx)
          (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
      _ ≤ _ := by decide

private theorem centered_in_old_space (x y : Geom) (Q : anchorSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      K1_13_1.anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered_old_eligible
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim

private theorem old_rank : K1_13_1.c1 :=
  K1_13_1_1.of_children K1_13_1_1_1.proof K1_13_1_1_2.proof K1_13_1_1_3.proof

theorem rank_local (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 9198441 := by
  have hpositive (j : JetVariable 3) : differentialWeight 133671 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133671 - j.val ≠ 0
      omega
  have : Module.Finite Geom K1_13_1.anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : anchorSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict anchorSpace
  let tr : anchorSpace →ₗ[Geom] K1_13_1.anchorSpace :=
    f.codRestrict K1_13_1.anchorSpace (centered_in_old_space x y)
  have h : anchorLocal x y = (K1_13_1.anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 90 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 90 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX, localConstraintAt_eq_zero_globalPointTranslation]
  rw [h]
  exact (LinearMap.finrank_range_comp_le_left (K1_13_1.anchorLocal 0 0) tr).trans (K1_13_1_1.sharpRank 0 0)

end
end P0_9_1
end PackSource_P0_9_1Rank

section PackSource_P0_9_1Count
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 2000

namespace P0_9_1

open K1_13 (Geom)
open PolynomialDifferential
open scoped BigOperators

private abbrev Exponent := JetVariable 3 →₀ ℕ

private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c

/-- Largest total jet degree for derivative exponents a, b, c. -/
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 120 (113 + 2 * (48 - (a + b + c)))

private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)

private def firstWidth (a b c : ℕ) : ℕ :=
  90 * 180130 - 133542 * gradeCeiling a b c + indexWeight a b c

/-- The grade falls by j from its ceiling, so each step adds 133542 abscissa slots. -/
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133542 * j

private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x

@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]

@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]

private theorem exponent_coordinates (u : Exponent) :
    exponent (u none) (u (some 0)) (u (some 1)) (u (some 2)) (u (some 3)) = u := by
  ext i
  cases i with
  | none => simp
  | some i => fin_cases i <;> simp

private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

private theorem true_weight (x v a b c : ℕ) :
    (exponent x v a b c).weight (differentialWeight 133542) =
      x + (v * 133542 + a * 133541 + b * 133540 + c * 133539) := by
  have hw : differentialWeight (d := 3) 133542 = fun i =>
      i.elim 1 (fun k => 133542 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw, exponent, Finsupp.weight_optionElim, jet_weight]
  simp

private theorem eligible_exponent (x v a b c : ℕ) :
    AnchorEligible (exponent x v a b c) ↔
      c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133542 * (v + (a + b + c)) < 90 * 180130 + indexWeight a b c := by
  unfold AnchorEligible gradeCeiling indexWeight
  rw [show P0_9.physicalDegree = 133542 from rfl,
    Finsupp.degree_eq_weight_one, jet_weight, jet_weight, true_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  change (v + a + b + c ≤ 120 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 48 ∧
    c ≤ 10 ∧ a + b + c ≤ 48 - (v + a + b + c - 113 + 1) / 2 ∧
    x + (v * 133542 + a * 133541 + b * 133540 + c * 133539) ≤ 90 * 180130 - 1) ↔ _
  by_cases h : a + b + c = 0 <;> omega

private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133542 * (gradeCeiling a b c - j) < 90 * 180130 + indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 120 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega

/-- The coordinates in order are the third, second, and first derivative exponents,
the drop from the grade ceiling, and the abscissa exponent. -/
private abbrev Slot :=
  Σ c : Fin 11, Σ b : Fin ((48 - 3 * c.val) / 2 + 1),
    Σ a : Fin (48 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)

private abbrev Eligible := {u : Exponent // AnchorEligible u}

private theorem slot_bounds (c b a j x : ℕ) :
    (c < 11 ∧ b < (48 - 3 * c) / 2 + 1 ∧ a < 48 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
      x < abscissaWidth a b c j) := by
  unfold indexWeight gradeSlots
  omega

private noncomputable def slotExponent (q : Slot) : Eligible := by
  rcases q with ⟨c, b, a, j, x⟩
  refine ⟨exponent x (gradeCeiling a b c - j - (a.val + b.val + c.val)) a b c, ?_⟩
  obtain ⟨hc, hi, hj, hx⟩ := (slot_bounds c b a j x).mp
    ⟨c.isLt, b.isLt, a.isLt, j.isLt, x.isLt⟩
  have hg : gradeCeiling a b c - j - (a.val + b.val + c.val) + (a.val + b.val + c.val) =
      gradeCeiling a b c - j := by omega
  rw [eligible_exponent, hg]
  exact ⟨hc, hi, by omega, (width_iff a b c j x (by omega)).mp hx⟩

private theorem slotExponent_injective : Function.Injective slotExponent := by
  rintro ⟨⟨c, hc⟩, ⟨b, hb⟩, ⟨a, ha⟩, ⟨j, hj⟩, ⟨x, hx⟩⟩
    ⟨⟨c', hc'⟩, ⟨b', hb'⟩, ⟨a', ha'⟩, ⟨j', hj'⟩, ⟨x', hx'⟩⟩ h
  have ec : c = c' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 3)) h
  have eb : b = b' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 2)) h
  have ea : a = a' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 1)) h
  have ex : x = x' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val none) h
  subst c'
  subst b'
  subst a'
  subst x'
  have ev : gradeCeiling a b c - j - (a + b + c) =
      gradeCeiling a b c - j' - (a + b + c) := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 0)) h
  have ej : j = j' := by
    change j < gradeSlots a b c at hj
    change j' < gradeSlots a b c at hj'
    unfold gradeSlots at hj hj'
    omega
  subst j'
  rfl

private theorem slotExponent_surjective : Function.Surjective slotExponent := by
  intro u
  let x := u.val none
  let v := u.val (some 0)
  let a := u.val (some 1)
  let b := u.val (some 2)
  let c := u.val (some 3)
  have he : exponent x v a b c = u.val := exponent_coordinates u.val
  obtain ⟨hc, hi, hg, hx⟩ := (eligible_exponent x v a b c).mp (he.symm ▸ u.property)
  let j := gradeCeiling a b c - (v + (a + b + c))
  have hj : j ≤ gradeCeiling a b c := Nat.sub_le _ _
  have hj' : gradeCeiling a b c - j = v + (a + b + c) := by
    dsimp [j]
    omega
  obtain ⟨hc', hb', ha', hj'', hx'⟩ := (slot_bounds c b a j x).mpr
    ⟨hc, hi, by dsimp [j]; omega, (width_iff a b c j x hj).mpr (hj'.symm ▸ hx)⟩
  refine ⟨⟨⟨c, hc'⟩, ⟨b, hb'⟩, ⟨a, ha'⟩, ⟨j, hj''⟩, ⟨x, hx'⟩⟩, Subtype.ext ?_⟩
  change exponent x (gradeCeiling a b c - j - (a + b + c)) a b c = u.val
  have hv : gradeCeiling a b c - j - (a + b + c) = v := by omega
  rwa [hv]

private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n

private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]

private theorem sumRange_eq_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range, sumRange_eq]

private def tripleCount (a b c : ℕ) : ℕ :=
  let n := gradeSlots a b c
  n * firstWidth a b c + 133542 * (n * (n - 1) / 2)

private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]

private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (48 - 3 * c - 2 * b + 1)

private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((48 - 3 * c) / 2 + 1)

private theorem slot_card : Fintype.card Slot = sumRange sliceCount 11 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem totalCount : sumRange sliceCount 11 = 2411350415801 := by
  decide +kernel

/-- Exact dimension of the order-90 anchor bank. -/
theorem anchor_finrank : Module.finrank Geom anchorSpace = 2411350415801 := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  let b := MvPolynomial.basisRestrictSupport Geom {u : Exponent | AnchorEligible u}
  exact (Module.finrank_eq_card_basis (b.reindex e.symm)).trans (slot_card.trans totalCount)

end P0_9_1
end PackSource_P0_9_1Count

section PackSource_P0_9_1Proof
set_option autoImplicit true
namespace P0_9_1
noncomputable section

open PolynomialDifferential ReedSolomon.HiddenDerivative
open P0 (K I node agreement)
open P0_9 (Messages TrueWeightLE physicalDegree anchorCutoff LowerRow SmallFactor Cover)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial

open private coeff_flatten atJet_unflatten anchorLead_term fits_of_prod from ProximityPrize.SubmissionLower.Fast040

private theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb

private theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl

private theorem anchor_bounds (Q : anchorSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨120, 48, 10⟩ ∧
      TrueWeightLE (MvPolynomial.optionEquivRight Geom (Fin 4) Q) anchorCutoff := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, AnchorEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 10
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1
  · apply (trueWeight_iff P).mpr
    rw [AlgEquiv.symm_apply_apply, ← differentialWeight_eq,
      MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    exact fun m h => (hQ h).2.2.2.2

private theorem exists_anchor (w : I → K) :
    ∃ Q : Row 4, Q ≠ 0 ∧ InBox (shape Q) ⟨120, 48, 10⟩ ∧
      TrueWeightLE Q anchorCutoff ∧
      ∀ Γ s, Messages w Γ s → ∀ γ ∈ Γ, atJet Q (extend (s γ)) = 0 := by
  let localRows (i : I) := anchorLocal (embed (node i)) (embed (w i))
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (localRows i))) ≤
      2411316117504 := by
    calc
      _ ≤ ∑ _ : I, (9198441 : ℕ) := Finset.sum_le_sum fun i _ => rank_local _ _
      _ = _ := by simp
  have hDim : 2411316117504 < Module.finrank Geom anchorSpace := by
    rw [anchor_finrank]
    decide
  obtain ⟨Q, hQ, hlocal⟩ :=
    LinearMap.exists_ne_zero_of_sum_finrank_range_lt localRows (hr.trans_lt hDim)
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  obtain ⟨hbox, hweight⟩ := anchor_bounds Q
  refine ⟨P, hP, hbox, hweight, ?_⟩
  intro Γ s hm γ hγ
  obtain ⟨T, hT, hhit⟩ := hm.hits γ hγ
  have hdeg : differentialWeightedDegree physicalDegree (Q : DifferentialPolynomial Geom 3) <
      90 * agreement := by
    have h := (trueWeight_iff P).mp hweight
    rw [AlgEquiv.symm_apply_apply] at h
    rw [differentialWeightedDegree, differentialWeight_eq]
    exact lt_of_le_of_lt h (by decide : anchorCutoff < 90 * agreement)
  have hS : (extend (s γ)).natDegree ≤ physicalDegree :=
    Polynomial.natDegree_map_le.trans (hm.degree γ hγ)
  rw [atJet_unflatten]
  refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i => embed (node i)) (fun i => embed (w i)) T hdeg
    (fun i _ => hlocal i) _ hS
    ((RingHom.injective embed).comp node.injective).injOn hT ?_
  intro i hi
  rw [Polynomial.eval_map, Polynomial.eval₂_hom, hhit i hi]

section FactorCover

open MvPolynomial UniqueFactorizationMonoid

open K1_13_1 (topView)

private theorem anchorLead_support_weight (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, ∀ w : Fin 4 → ℕ, w 3 * (shape P).t + m.weight (fun i => w i.castSucc) = u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m := by
    exact (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, fun w => ?_⟩
  · let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
    have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
    have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
      · simp [w']
    have hweight : (m.optionElim k).weight w' = u.weight w := by
      rw [← he]
      simp only [Finsupp.weight_apply, smul_eq_mul]
      rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
      simp only [hw]
    rw [Finsupp.weight_optionElim] at hweight
    rw [← K1_13_1.topView_degree]
    simpa only [k, w', Option.elim_none, Option.elim_some, Nat.mul_comm] using hweight

private theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · rw [← weightedTotalDegree_one, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := (le_weightedTotalDegree (1 : Fin 4 → ℕ) hu)
    rw [weightedTotalDegree_one] at hab
    exact (h (1 : Fin 4 → ℕ)).trans (hab.trans hbox.1)
  · rw [indexDegree_eq, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := le_weightedTotalDegree (fun i => i.val) hu
    rw [← indexDegree_eq] at hab
    exact (h (fun i => i.val)).trans (hab.trans hbox.2.1)
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle

private theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))

private theorem cover_of_anchor {Γ : Finset K} {s : K → K[X]} (P : Row 4)
    (hP : P ≠ 0) (hbox : InBox (shape P) ⟨120, 48, 10⟩)
    (hw : TrueWeightLE P anchorCutoff)
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0) :
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT : ∀ q ∈ T, q ∈ A ∧ 0 < (shape q).t := by
    intro q hq
    simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  have hd : (∏ i, f i) ∣ P := by
    have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  refine ⟨n, anchorLead P, f, ⟨lower_of_anchor P hP hbox hw, ?_, ?_,
    fits_of_prod P hP hbox f (fun i => (hfi i).2) hd, ?_, ?_, ?_⟩⟩
  · intro i
    exact factor_small hP hbox hw (irreducible_of_normalized_factor _ (hfi i).1)
      (hfi i).2 (dvd_of_mem_normalizedFactors (hfi i).1)
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · have hsum := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1)
        Finset.univ f hP hd
    simp only [weightedTotalDegree_piSingle] at hsum
    rw [← weightedTotalDegree_one, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨v, hv, h⟩ := anchorLead_support_weight P m hm
    have hl := le_weightedTotalDegree (1 : Fin 4 → ℕ) hv
    rw [weightedTotalDegree_one] at hl
    have hb := hbox.1
    have he := h (1 : Fin 4 → ℕ)
    simp only [Pi.one_apply, one_mul] at he
    have hsum' : (∑ i, (shape (f i)).t) ≤ (shape P).t := hsum
    have hb' : P.totalDegree ≤ 120 := hb
    rw [← he] at hl
    change (shape P).t + m.weight (1 : Fin 3 → ℕ) ≤ P.totalDegree at hl
    exact Nat.le_sub_of_add_le (by omega)
  · have hsum := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1)
        Finset.univ f hP hd
    simp only [weightedTotalDegree_piSingle] at hsum
    rw [indexDegree_eq, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨v, hv, h⟩ := anchorLead_support_weight P m hm
    have hl := le_weightedTotalDegree (fun i : Fin 4 => i.val) hv
    rw [← indexDegree_eq] at hl
    have hb := hbox.2.1
    have he := h (fun i => i.val)
    have hsum' : (∑ i, (shape (f i)).t) ≤ (shape P).t := hsum
    have hb' : indexDegree P ≤ 48 := hb
    rw [← he] at hl
    change 3 * (shape P).t + m.weight (fun i : Fin 3 => i.val) ≤ indexDegree P at hl
    exact Nat.le_sub_of_add_le (by omega)
  · intro γ hγ
    let S := extend (s γ)
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ eval (jet S) A.prod at hdiv
      rw [hz γ hγ, zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hSA
    obtain ⟨q, hq, hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R, hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR, anchorLead_mul, atJet, map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq, hqt⟩
    let j := e.symm ⟨q, hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hqT⟩)
    exact ⟨j, by rw [hj, OnFactor, ← eval_anchorLead]; exact ⟨hqS, hqlead⟩⟩

end FactorCover

theorem proof : P0_9.c1 := by
  intro w Γ s hm
  obtain ⟨P, hP, hb, hw, hz⟩ := exists_anchor w
  exact cover_of_anchor P hP hb hw (hz Γ s hm)

end
end P0_9_1
end PackSource_P0_9_1Proof

namespace P0_9_2
theorem proof : P0_9.c2 := LowPrimary6921.primary_rank
end P0_9_2


section PackSource_P0_9_3Defs
set_option autoImplicit true
namespace P0_9_3

noncomputable section

open P0 (I K)
open P0_9 (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)

/-- The ordinary jet order forced by the reserve above cutoff T. -/
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1

/-- The full contact space through cutoff T in the single primary box. -/
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P

end

end P0_9_3
end PackSource_P0_9_3Defs

section PackSource_P0_9_3Filtration
set_option autoImplicit true
namespace P0_9_3

noncomputable section

open Polynomial
open P0 (I K node)
open P0_9 (TrueWeightLE physicalDegree primaryBox primaryCutoff PrimaryRank sourceRank)
open K1_13 (Geom embed Row InBox shape indexDegree Contact jet atJet)
open K1_13_3 (Symbol symbolAt)
open scoped BigOperators

set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false

private abbrev Exponent := Fin 4 →₀ ℕ

private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)

private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩

private def jetEval (S : Geom[X]) : Row 4 →ₗ[Geom] Geom[X] :=
  (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars Geom

private theorem jetEval_apply (S : Geom[X]) (P : Row 4) : jetEval S P = atJet P S := by
  rfl

private theorem dvd_smul_poly (d P : Geom[X]) (c : Geom) (h : d ∣ P) :
    d ∣ c • P := by
  rw [Polynomial.smul_eq_C_mul]
  exact h.mul_left _

private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)

/-- There are 4013 possible values for each exponent, from 0 through 4012. -/
private def coefficientArray (T : ℕ) :
    Row 4 →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff Geom u.2.val).comp
      ((MvPolynomial.lcoeff Geom[X] (Finsupp.equivFunOnFinite.symm (fun i => (u.1 i).val))
        : Row 4 →ₗ[Geom[X]] Geom[X]).restrictScalars Geom)

private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz

private def symbolLinear (x : Geom) : Row 4 →ₗ[Geom] Symbol :=
  ({ symbolAt x with
      commutes' := by
        intro a
        change MvPolynomial.map (evalRingHom x) (MvPolynomial.C (Polynomial.C a)) =
          MvPolynomial.C a
        simp } : Row 4 →ₐ[Geom] Symbol).toLinearMap

private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype

private def linearFactor (x : Geom) : Geom[X] := (Polynomial.X : Geom[X]) - Polynomial.C x

private theorem linearFactor_ne (x : Geom) : linearFactor x ≠ 0 := X_sub_C_ne_zero x

private theorem linearFactor_degree (x : Geom) : (linearFactor x).natDegree = 1 :=
  natDegree_X_sub_C x

private theorem divide_specialization (P : Row 4) (x : Geom) (hP : symbolAt x P = 0) :
    ∃ Q : Row 4, MvPolynomial.C (linearFactor x) * Q = P := by
  let Q : Row 4 := AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange.linearMap (divByMonicHom (linearFactor x)) (AddMonoidAlgebra.coeff P))
  refine ⟨Q, MvPolynomial.ext _ _ fun m => ?_⟩
  have hroot : (P.coeff m).eval x = 0 := by
    have h := congrArg (fun B : Symbol => B.coeff m) hP
    change (symbolAt x P).coeff m = (0 : Symbol).coeff m at h
    rw [symbolAt, MvPolynomial.coeff_map] at h
    exact h
  rw [MvPolynomial.coeff_C_mul]
  change (linearFactor x) * ((P.coeff m) /ₘ (linearFactor x)) = P.coeff m
  exact mul_divByMonic_eq_iff_isRoot.mpr hroot

private theorem support_linear_mul (x : Geom) (P : Row 4) :
    (MvPolynomial.C (linearFactor x) * P).support = P.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]
  exact mul_ne_zero_iff.trans (and_iff_right (linearFactor_ne x))

private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    omega
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff

private theorem zero_cutoff_kernel (w : I → K) (x : Geom) :
    LinearMap.ker (bankEval w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : TrueWeightLE P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega

private theorem kernel_finrank (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval w x (T + 1))) =
      Module.finrank Geom (bank w T) := by
  let L : bank w T →ₗ[Geom] (LinearMap.ker (bankEval w x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank w (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank w T).subtype)
      (fun P => (mul_cutoff_iff w x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        simp [symbolAt, linearFactor])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval w x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff w x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm

/-- The image at a nonphysical abscissa loses exactly the preceding cutoff
at each step, and the zero cutoff has injective specialization. -/
theorem cutoff_rank (w : I → K) (x : Geom) (hr : PrimaryRank w)
    (hx : ∀ i : I, x ≠ embed (node i)) :
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i)) := by
  classical
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval w x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank w T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w 0) (V₂ := Symbol) (bankEval w x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w (T + 1)) (V₂ := Symbol) (bankEval w x (T + 1))
        rw [kernel_finrank w x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank w primaryCutoff)) :=
      LinearIndependent.of_comp (bank w primaryCutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval w x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]

end

end P0_9_3
end PackSource_P0_9_3Filtration

section PackSource_P0_9_3Split
set_option autoImplicit true
namespace P0_9_3

noncomputable section

open Polynomial
open P0 (I K node agreement)
open P0_9 (Messages SmallFactor ProperCut TrueWeightLE physicalDegree primaryBox
  primaryCutoff layerWidth layerNeed sourceRank)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree remaining)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators

/-- Contact and the reserve force ordinary multiplicity along one message. -/
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → BankRow w T P →
    ∀ S : Geom[X], S.natDegree ≤ physicalDegree →
      (∃ H : Finset I, agreement ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)

/-- A top Hasse partial at the exact factor exponent gives the proper cutter. -/
def c2 : Prop :=
  ∀ (f P : Row 4) (Γ : Finset K) (s : K → K[X]) (d a : ℕ),
    SmallFactor f →
    InBox (shape P) primaryBox → TrueWeightLE P primaryCutoff →
    (∀ γ ∈ Γ, OrderAt P (extend (s γ)) d) →
    a < d → f ^ a ∣ P → (¬ f ^ (a + 1) ∣ P) →
    ProperCut f Γ s (d - a)

private theorem exists_fresh {n : ℕ} (f : Fin n → Row 4) :
    ∃ x : Geom, (∀ i : I, x ≠ embed (node i)) ∧
      ∀ i, (symbolAt x (f i)).support = (f i).support := by
  classical
  let nodes : Finset Geom := Finset.univ.image (fun i : I => embed (node i))
  let roots : Finset Geom := Finset.univ.biUnion (fun i : Fin n =>
    (f i).support.biUnion (fun m => ((f i).coeff m).roots.toFinset))
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (nodes ∪ roots)
  rw [Finset.mem_union, not_or] at hx
  refine ⟨x, ?_, fun i => Finset.Subset.antisymm (MvPolynomial.support_map_subset _ _) ?_⟩
  · intro i h
    exact hx.1 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at ⊢
    change (MvPolynomial.map (evalRingHom x) (f i)).coeff m ≠ 0
    rw [MvPolynomial.coeff_map]
    intro heval
    have hroot : x ∈ ((f i).coeff m).roots :=
      (Polynomial.mem_roots (MvPolynomial.mem_support_iff.mp hm)).mpr heval
    exact hx.2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨m, hm, Multiset.mem_toFinset.mpr hroot⟩⟩)

private theorem specialization_bounds (x : Geom) (P : Row 4)
    (hP : InBox (shape P) primaryBox) :
    (symbolAt x P).totalDegree ≤ 4012 ∧ symbolIndex (symbolAt x P) ≤ 1650 := by
  have h : (symbolAt x P).support ⊆ P.support := MvPolynomial.support_map_subset _ _
  exact ⟨(Finset.sup_mono h).trans hP.1, (Finset.sup_mono h).trans hP.2.1⟩

/-- Choose the least availability that forces the required powers at all cutoffs. -/
private theorem exists_availability (hc : c1) (hd : c2)
    {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s)
    {f : Row 4} (hf : SmallFactor f) :
    ∃ l : ℕ, (∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P) ∧
      (0 < l → ProperCut f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨primaryCutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder T ≤ primaryCutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder T := by
    by_contra! hlt
    have heq : requiredOrder T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder T - (l - 1) = (requiredOrder T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder T) := by
    intro γ hγ
    apply hc w T P hT hP
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · obtain ⟨H, hcard, hH⟩ := hm.hits γ hγ
      refine ⟨H, hcard, fun i hi => ?_⟩
      rw [extend, eval_map, eval₂_at_apply, hH i hi]
  have hweight : TrueWeightLE P primaryCutoff := fun m hm => (hP.2.1 m hm).trans hT
  have hcut := hd f P Γ s (requiredOrder T) (requiredOrder T - l) hf hP.1
    hweight horder (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder T - (requiredOrder T - l) = l := by omega
  rwa [heq] at hcut

private theorem sum_by_layer (W E : ℕ) (hE : 0 < E) (cost : ℕ → ℕ) :
    (∑ T ∈ Finset.range (W + 1), cost ((W - T) / E)) ≤
      E * ∑ k ∈ Finset.range (1 + W / E), cost k := by
  let S := Finset.range (W + 1)
  let R := Finset.range (1 + W / E)
  let U := Finset.range E
  let pair (T : ℕ) : ℕ × ℕ := ((W - T) / E, (W - T) % E)
  have hmem : ∀ T ∈ S, pair T ∈ R ×ˢ U := by
    intro T _
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by
        change (W - T) / E < 1 + W / E
        have h : (W - T) / E ≤ W / E := Nat.div_le_div_right (Nat.sub_le W T)
        omega),
      Finset.mem_range.mpr (Nat.mod_lt _ hE)⟩
  have hinj : Set.InjOn pair (↑S : Set ℕ) := by
    intro T hT V hV h
    have hT' : T < W + 1 := Finset.mem_range.mp hT
    have hV' : V < W + 1 := Finset.mem_range.mp hV
    have he : W - T = W - V := by
      have ht := Nat.mod_add_div (W - T) E
      have hv := Nat.mod_add_div (W - V) E
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      change (W - T) / E = (W - V) / E at hfst
      change (W - T) % E = (W - V) % E at hsnd
      rw [hsnd, hfst, hv] at ht
      exact ht.symm
    omega
  calc
    _ ≤ ∑ p ∈ R ×ˢ U, cost p.1 := by
      refine Finset.sum_le_sum_of_injOn pair hinj ?_ (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
      intro p hp
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
      exact hmem T hT
    _ = _ := by rw [Finset.sum_product, Finset.mul_sum]; simp [U, R]

theorem of_children (h1 : c1) (h2 : c2) : P0_9.c3 := by
  classical
  intro w Γ s hm hr n g f hf
  choose l hl hcut using fun i => exists_availability h1 h2 hm (hf.factors i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  obtain ⟨r, hrank, hfamilies⟩ := cutoff_rank w x hr hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hf.factors i).1.ne_zero hzero
  let cost (k : ℕ) :=
    remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := (hf.factors j).1
        have hk := (hf.factors k).1
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hf.different j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    simpa only [cost, a, requiredOrder, hb, hj] using hbound
  have hsum : sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k :=
    hrank.trans ((Finset.sum_le_sum fun T hT =>
      hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  refine ⟨l, ?_, hcut⟩
  change layerNeed ≤ ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k
  have hceil : layerWidth * (layerNeed - 1) < sourceRank := by decide
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k) ≤
      layerNeed - 1 := by omega
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left layerWidth hpred))

end

end P0_9_3
end PackSource_P0_9_3Split

section PackSource_P0_9_3_1Proof
set_option autoImplicit true
set_option maxRecDepth 12000

namespace P0_9_3_1

noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (I K node agreement)
open P0_9 (TrueWeightLE physicalDegree primaryCutoff layerWidth)
open P0_9_3 (BankRow requiredOrder)
open K1_13 (Geom embed Row jet)
open K1_13_3_1 (line)
open scoped BigOperators
open private eval_line line_contacts_zero from ProximityPrize.SubmissionLower.Fast074
open private order_of_locator_lines from ProximityPrize.SubmissionLower.Fast074

private def Bounded (Q : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j

private theorem bounded_mul {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega

private theorem bounded_C (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]

private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

private theorem bounded_pow {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf

/-- The coefficient of line parameter degree `j` spends at most `j` extra layers. -/
private theorem line_degree (P : Row 4) (S U : Geom[X]) (T : ℕ)
    (hP : TrueWeightLE P T) (hS : S.natDegree ≤ physicalDegree)
    (hU : U.natDegree ≤ agreement + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := physicalDegree - i.val
  let F (i : Fin 4) : Polynomial Geom[X] :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physicalDegree := (Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth : agreement + 3 = layerWidth + physicalDegree := by decide
      change agreement + 3 - i.val ≤ (physicalDegree - i.val) + layerWidth
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm layerWidth]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_C (P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)

/-- Contact at an exact agreement set kills the coefficients below the reserve. -/
private theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : Geom[X])
    (hP : BankRow w T P) (hS : S.natDegree ≤ physicalDegree)
    (A : Finset I) (hA : A.card = agreement)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth * j ≤ primaryCutoff) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ agreement + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hP.2.2
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hP.2.1 hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) (by decide)) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree

theorem proof : P0_9_3.c1 := by
  intro w T P hT hP S hS hits
  obtain ⟨H, hH, hhits⟩ := hits
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hP hS A hA (fun i hi => hhits i (hAH hi)) V hV j
  have hj' : j ≤ (primaryCutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (primaryCutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  calc
    T + layerWidth * j ≤ T + layerWidth * ((primaryCutoff - T) / layerWidth) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
    _ ≤ T + (primaryCutoff - T) := Nat.add_le_add_left hq T
    _ = primaryCutoff := Nat.add_sub_of_le hT

end

end P0_9_3_1
end PackSource_P0_9_3_1Proof

section PackSource_P0_9_3_2Proof
set_option autoImplicit true
namespace P0_9_3_2

noncomputable section

open Polynomial
open P0_9 (SmallFactor ProperCut TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree shiftJet jet)

private abbrev Exponent := Fin 4 →₀ ℕ

/-- Translate the top jet by a formal parameter, holding all coefficients
and the other jets fixed. -/
private def translateTop : Row 4 →+* Polynomial (Row 4) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    Polynomial.C (MvPolynomial.X i) + if i = 3 then Polynomial.X else 0

private def topHasse (a : ℕ) (P : Row 4) : Row 4 :=
  (translateTop P).coeff a

private theorem translate_independent (m : Exponent) (c : Geom[X]) (hm : m 3 = 0) :
    translateTop (MvPolynomial.monomial m c) = Polynomial.C (MvPolynomial.monomial m c) := by
  rw [translateTop, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul]
  simp only [RingHom.comp_apply]
  congr 1
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ 3 := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi) hm
  simp [hne]

private theorem translate_top_pow_coeff (n a : ℕ) :
    ((Polynomial.C (MvPolynomial.X (3 : Fin 4) : Row 4) + Polynomial.X) ^ n).coeff a =
      MvPolynomial.C (↑(n.choose a) : Geom[X]) * MvPolynomial.X 3 ^ (n - a) := by
  rw [add_comm, ← Polynomial.taylor_X_pow, Polynomial.taylor_coeff,
    Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp [Polynomial.eval_monomial]

private theorem erase_top_add (u : Exponent) :
    u.erase 3 + Finsupp.single 3 (u 3) = u := by
  ext i
  by_cases hi : i = 3
  · subst i
    simp
  · simp [Finsupp.erase_ne hi, Finsupp.single_eq_of_ne hi]

private theorem topHasse_monomial (a : ℕ) (u : Exponent) (c : Geom[X]) :
    topHasse a (MvPolynomial.monomial u c) =
      MvPolynomial.monomial (u.erase 3 + Finsupp.single 3 (u 3 - a)) (↑((u 3).choose a) * c) := by
  have hu : MvPolynomial.monomial u c =
      MvPolynomial.monomial (u.erase 3) c * MvPolynomial.X 3 ^ (u 3) := by
    rw [← MvPolynomial.monomial_add_single, erase_top_add]
  have hx : translateTop (MvPolynomial.X 3) =
      Polynomial.C (MvPolynomial.X 3) + Polynomial.X := by simp [translateTop]
  unfold topHasse
  rw [hu, map_mul, map_pow, translate_independent _ _ Finsupp.erase_same, hx,
    Polynomial.coeff_C_mul, translate_top_pow_coeff, ← mul_assoc]
  rw [mul_comm (MvPolynomial.monomial (u.erase 3) c), MvPolynomial.C_mul_monomial,
    ← MvPolynomial.monomial_add_single]

private theorem apply_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a : Exponent) 3 = m 3 + a := by simp

private theorem topHasse_coeff (a : ℕ) (P : Row 4) (m : Exponent) :
    (topHasse a P).coeff m =
      ↑((m 3 + a).choose a) * P.coeff (m + Finsupp.single 3 a) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [topHasse_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases ha : a ≤ u 3
    · have hcancel : (u.erase 3 + Finsupp.single 3 (u 3 - a)) + Finsupp.single 3 a = u := by
        rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel ha, erase_top_add]
      have heq : u.erase 3 + Finsupp.single 3 (u 3 - a) = m ↔
          u = m + Finsupp.single 3 a := by
        constructor
        · intro h
          rw [← h, hcancel]
        · intro h
          exact add_right_cancel (hcancel.trans h)
      simp only [heq]
      by_cases h : u = m + Finsupp.single 3 a
      · have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        simp only [h3, ite_eq_left h]
      · simp [h]
    · have hne : u ≠ m + Finsupp.single 3 a := by
        intro h
        have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        omega
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]
      simp [hne]
  | add P Q hP hQ =>
    simp only [topHasse, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at hP hQ ⊢
    rw [hP, hQ, mul_add]

private theorem source_support {a : ℕ} {P : Row 4} {m : Exponent}
    (hm : m ∈ (topHasse a P).support) : m + Finsupp.single 3 a ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, topHasse_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)

private theorem sum_add_top (w : Fin 4 → ℕ) (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun i k => w i * k) =
      m.sum (fun i k => w i * k) + w 3 * a := by
  rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
    Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _)]

private theorem total_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun _ k => k) = m.sum (fun _ k => k) + a := by
  simpa only [one_mul] using sum_add_top (fun _ => 1) m a

private theorem topHasse_bounds (a : ℕ) (P : Row 4)
    (hb : InBox (shape P) primaryBox) (hw : TrueWeightLE P primaryCutoff) :
    InBox (shape (topHasse a P)) primaryBox ∧
      TrueWeightLE (topHasse a P) primaryCutoff := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ 4012
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    change _ ≤ 4012 at hp
    omega
  · change indexDegree (topHasse a P) ≤ 1650
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Exponent => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    change _ ≤ 1650 at hp
    omega
  · change (topHasse a P).degreeOf 3 ≤ 550
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    change _ ≤ 550 at hp
    omega
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hcoeff := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : Geom[X])) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hcoeff
    refine (Nat.add_le_add_right hcoeff _).trans (le_trans ?_ hp)
    exact Nat.add_le_add_left (Nat.le_add_right _ _) _

private def shiftHom (S : Geom[X]) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))

private theorem translate_shift (S : Geom[X]) :
    translateTop.comp (shiftHom S) = (Polynomial.mapRingHom (shiftHom S)).comp translateTop := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [translateTop, shiftHom]
  · intro i
    simp only [RingHom.comp_apply, shiftHom, translateTop, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C]
    by_cases hi : i = 3
    · simp only [hi, ite_true, Polynomial.map_X]
      exact add_right_comm _ _ _
    · simp only [hi, ite_false, Polynomial.map_zero, add_zero]

private theorem topHasse_order (a d : ℕ) (P : Row 4) (S : Geom[X])
    (h : OrderAt P S d) : OrderAt (topHasse a P) S (d - a) := by
  have he := RingHom.congr_fun (translate_shift S) P
  change translateTop (shiftJet P S) = (translateTop P).map (shiftHom S) at he
  have hs : topHasse a (shiftJet P S) = shiftJet (topHasse a P) S := by
    change (translateTop (shiftJet P S)).coeff a =
      shiftHom S ((translateTop P).coeff a)
    rw [he, Polynomial.coeff_map]
  intro m hm
  rw [← hs] at hm
  have hd := h _ (source_support hm)
  rw [total_add_top] at hd
  omega

private theorem topHasse_one_not_dvd (f : Row 4) (hf : SmallFactor f) :
    ¬ f ∣ topHasse 1 f := by
  classical
  have hpos : 0 < f.degreeOf 3 := hf.2.1
  have hsmall : f.degreeOf 3 < K1.p :=
    (show f.degreeOf 3 ≤ 10 from hf.2.2.1.2.2).trans_lt (by decide)
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : Geom[X]) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hg0
  rw [hg, h] at hdeg
  omega

private theorem topHasse_zero (P : Row 4) : topHasse 0 P = P := by
  ext m
  simp [topHasse_coeff]

/-- The first possible coefficient after extracting one parameter from
each of the a factors. -/
private theorem coeff_X_mul_pow {R : Type*} [CommSemiring R]
    (V W : Polynomial R) (a : ℕ) :
    ((Polynomial.X * V) ^ a * W).coeff a = (V.coeff 0) ^ a * W.coeff 0 := by
  rw [mul_pow, mul_assoc]
  calc
    _ = (V ^ a * W).coeff 0 := by
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V ^ a * W) a 0
    _ = _ := by
      change Polynomial.constantCoeff (V ^ a * W) =
        Polynomial.constantCoeff V ^ a * Polynomial.constantCoeff W
      rw [map_mul, map_pow]

/-- In the quotient by the prime factor, the constant term of its translate
vanishes and the first coefficient survives. -/
private theorem exact_hasse_not_dvd {R : Type*} [CommRing R]
    (T : R →+* Polynomial R) (T0 : ∀ G, (T G).coeff 0 = G)
    (f P : R) (a : ℕ) (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) : ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := hdiv
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hzero (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hconstant (G : R) : (tr G).coeff 0 = reduce G := by rw [hcoeff, T0]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hcoeff, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    calc
      _ = (tr (f ^ a * U)).coeff a := (hcoeff _ _).symm
      _ = (V.coeff 0) ^ a * (tr U).coeff 0 := by
        rw [map_mul, map_pow, hV]
        exact coeff_X_mul_pow V (tr U) a
      _ = _ := by rw [hfirst, hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))

/-- The Hasse partial at the exact exponent is a proper cutter of the factor. -/
theorem proof : P0_9_3.c2 := by
  intro f P Γ s d a hf hb hw hord _ hdiv hexact
  obtain ⟨hbox, hweight⟩ := topHasse_bounds a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf.1
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp (topHasse_one_not_dvd f hf) hdiv hexact
  exact ⟨topHasse a P, hproper, hbox, hweight, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩

end

end P0_9_3_2
end PackSource_P0_9_3_2Proof
