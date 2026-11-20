import ProximityPrize.SubmissionLower.Fast073
import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.LowFat6921
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
namespace LowAnchor6921
noncomputable section
open K1 K1_13 PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight 133518) ≤ 90 * 180169 - 1 ∧
    u.weight (differentialWeight 133671) ≤ 90 * 180265 - 1

/-- All abscissa powers up to the true-weight cutoff are included. -/
def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

/-- The translated backward-Taylor constraint map, keeping only orders below 90.
ArkLib's error variable has weight 3 because it occurs in the substitution as `T * E`. -/
def anchorLocal (center received : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 center received).domRestrict anchorSpace

private abbrev Exponent := JetVariable 3 →₀ ℕ

private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c

/-- Largest total jet degree for derivative exponents a, b, c. -/
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 120 (113 + 2 * (48 - (a + b + c)))

private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)

private def firstWidth (a b c : ℕ) : ℕ :=
  90 * 180169 - 133518 * gradeCeiling a b c + indexWeight a b c

private def oldWidth (a b c : ℕ) : ℕ :=
  90 * 180265 - 133671 * gradeCeiling a b c + indexWeight a b c

/-- Retain precisely the abscissa positions allowed by both true-weight bounds. -/
private def abscissaWidth (a b c j : ℕ) : ℕ :=
  min (firstWidth a b c + 133518 * j) (oldWidth a b c + 133671 * j)

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
    (exponent x v a b c).weight (differentialWeight 133518) =
      x + (v * 133518 + a * 133517 + b * 133516 + c * 133515) := by
  have hw : differentialWeight (d := 3) 133518 = fun i =>
      i.elim 1 (fun k => 133518 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw, exponent, Finsupp.weight_optionElim, jet_weight]
  simp

private theorem old_true_weight (x v a b c : ℕ) :
    (exponent x v a b c).weight (differentialWeight 133671) =
      x + (v * 133671 + a * 133670 + b * 133669 + c * 133668) := by
  have hw : differentialWeight (d := 3) 133671 = fun i =>
      i.elim 1 (fun k => 133671 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw, exponent, Finsupp.weight_optionElim, jet_weight]
  simp


private theorem eligible_exponent (x v a b c : ℕ) :
    AnchorEligible (exponent x v a b c) ↔
      c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        (x + 133518 * (v + (a + b + c)) < 90 * 180169 + indexWeight a b c ∧
         x + 133671 * (v + (a + b + c)) < 90 * 180265 + indexWeight a b c) := by
  unfold AnchorEligible gradeCeiling indexWeight
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, true_weight, old_true_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  change (v + a + b + c ≤ 120 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 48 ∧
    c ≤ 10 ∧ a + b + c ≤ 48 - (v + a + b + c - 113 + 1) / 2 ∧
    (x + (v * 133518 + a * 133517 + b * 133516 + c * 133515) ≤ 90 * 180169 - 1 ∧
      x + (v * 133671 + a * 133670 + b * 133669 + c * 133668) ≤ 90 * 180265 - 1)) ↔ _
  by_cases h : a + b + c = 0 <;> omega

private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      (x + 133518 * (gradeCeiling a b c - j) < 90 * 180169 + indexWeight a b c ∧
       x + 133671 * (gradeCeiling a b c - j) < 90 * 180265 + indexWeight a b c) := by
  have hgrade : gradeCeiling a b c ≤ 120 := min_le_left _ _
  unfold abscissaWidth firstWidth oldWidth
  rw [lt_min_iff]
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
  let m := min n (gradeCeiling a b c - 56)
  m * oldWidth a b c + 133671 * (m * (m-1) / 2) +
    ((n-m) * (firstWidth a b c + 133518*m) + 133518 * ((n-m)*((n-m)-1)/2))

private theorem arith_sum (n u t : ℕ) :
    (∑ j ∈ Finset.range n, (u+t*j)) = n*u+t*(n*(n-1)/2) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
  simp

private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  let n := gradeSlots a b c
  let m := min n (gradeCeiling a b c - 56)
  have hm : m ≤ n := min_le_left _ _
  have hsum := Finset.sum_range_add (f := abscissaWidth a b c) m (n-m)
  rw [Nat.add_sub_of_le hm] at hsum
  change (∑ j ∈ Finset.range n, abscissaWidth a b c j) = _
  rw [hsum]
  have hg : gradeCeiling a b c ≤ 120 := min_le_left _ _
  have hfirst : (∑ j ∈ Finset.range m, abscissaWidth a b c j) =
      ∑ j ∈ Finset.range m, (oldWidth a b c + 133671*j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h : j < gradeCeiling a b c - 56 :=
      (Finset.mem_range.mp hj).trans_le (min_le_right _ _)
    unfold abscissaWidth
    rw [min_eq_right]
    unfold firstWidth oldWidth
    omega
  have htail : (∑ j ∈ Finset.range (n-m), abscissaWidth a b c (m+j)) =
      ∑ j ∈ Finset.range (n-m), (firstWidth a b c + 133518*m + 133518*j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := Finset.mem_range.mp hj
    have hh : m = gradeCeiling a b c - 56 := by
      dsimp [m] at *
      omega
    unfold abscissaWidth
    rw [min_eq_left]
    · omega
    · unfold firstWidth oldWidth
      omega
  rw [hfirst, htail, arith_sum, arith_sum]
  rfl

private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => sumRange (fun a => tripleCount a b c) (48 - 3 * c - 2 * b + 1))
    ((48 - 3 * c) / 2 + 1)

private theorem slot_card : Fintype.card Slot = sumRange sliceCount 11 := by
  simp only [Slot, sliceCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem totalCount : sumRange sliceCount 11 = 2412075334184 := by
  decide +kernel

/-- Exact dimension of the order-90 anchor bank. -/
theorem anchor_finrank : Module.finrank Geom anchorSpace = 2412075334184 := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  let b := MvPolynomial.basisRestrictSupport Geom {u : Exponent | AnchorEligible u}
  exact (Module.finrank_eq_card_basis (b.reindex e.symm)).trans (slot_card.trans totalCount)

private theorem in_old {u : Exponent} (hu : AnchorEligible u) :
    K1_13_1.AnchorEligible u :=
  ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.2⟩

private theorem subspace : anchorSpace ≤ K1_13_1.anchorSpace := by
  intro P hP
  rw [anchorSpace, MvPolynomial.mem_restrictSupport_iff] at hP
  rw [K1_13_1.anchorSpace, MvPolynomial.mem_restrictSupport_iff]
  exact fun i hi => in_old (hP hi)

open private anchor_bounds atJet_unflatten from ProximityPrize.SubmissionLower.Fast040

theorem cover (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s) :
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f := by
  classical
  let maps (i : I) := anchorLocal (embed (node i)) (embed (w i))
  have old : K1_13_1.c1 := K1_13_1_1.of_children
    K1_13_1_1_1.proof K1_13_1_1_2.proof K1_13_1_1_3.proof
  letI : Module.Finite Geom K1_13_1.anchorSpace :=
    Module.finite_of_finrank_pos (by rw [K1_13_1_2.anchor_finrank]; decide)
  have localRank (i : I) : Module.finrank Geom (maps i).range ≤ 9199626 := by
    apply le_trans _ (old (embed (node i)) (embed (w i)))
    apply Submodule.finrank_mono
    rintro _ ⟨Q, rfl⟩
    exact ⟨⟨Q.val, subspace Q.property⟩, rfl⟩
  have total : (∑ i, Module.finrank Geom (maps i).range) < Module.finrank Geom anchorSpace := by
    calc
      _ ≤ ∑ _ : I, 9199626 := Finset.sum_le_sum fun i _ => localRank i
      _ < _ := by rw [anchor_finrank]; simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]
  obtain ⟨Q, hne, hcontact⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt maps total
  let oldQ : K1_13_1.anchorSpace := ⟨Q.val, subspace Q.property⟩
  let P := MvPolynomial.optionEquivRight Geom (Fin 4) Q.val
  obtain ⟨hbox,hw⟩ := anchor_bounds oldQ
  apply K1_13_1.cover_of_anchor P _ hbox hw
  · intro γ hγ
    obtain ⟨T,hT,hval⟩ := hm.hits γ hγ
    have hweight : differentialWeightedDegree 133518 Q.val < 90*180169 := by
      unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
      apply (Finset.sup_lt_iff (by decide : 0 < 90*180169)).2
      intro u hu
      have h := ((MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property) hu
      exact lt_of_le_of_lt h.2.2.2.2.1 (by decide : 90*180169-1 < 90*180169)
    have hdeg : (extend (s γ)).natDegree ≤ 133518 :=
      Polynomial.natDegree_map_le.trans ((hm.degree γ hγ).trans (by decide))
    rw [atJet_unflatten]
    refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
      (fun i => embed (node i)) (fun i => embed (w i)) T hweight
      (fun i _ => hcontact i) _ hdeg ((RingHom.injective embed).comp node.injective).injOn hT ?_
    intro i hi
    rw [extend, Polynomial.eval_map, Polynomial.eval₂_hom, hval i hi]
  · intro hz
    exact hne (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (hz.trans (map_zero _).symm)))

end
end LowAnchor6921
