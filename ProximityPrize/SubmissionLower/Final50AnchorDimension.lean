import ProximityPrize.SubmissionLower.Final50AnchorColumns
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Final50AnchorDimension
open Final50AnchorSpace Final50AnchorColumns
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

/- Count the abscissa powers using the monomial parametrization in P0_9_1. -/
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 132 (gradeLimit (a + b + c))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private def firstWidth (a b c : ℕ) : ℕ :=
  99 * 179886 - 133484 * gradeCeiling a b c + 2 * indexWeight a b c
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133484 * j
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
private theorem eligible_exponent (x v a b c : ℕ) :
    ColumnEligible (exponent x v a b c) ↔
      c ≤ 14 ∧ indexWeight a b c ≤ 55 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133484 * (v + (a + b + c)) < 99 * 179886 + 2 * indexWeight a b c := by
  unfold ColumnEligible jdeg jidx jdiff gradeCeiling indexWeight
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  simp only [exponent_none, Matrix.cons_val_one]
  have ht : ![v,a,b,c] (2 : Fin 4) = b := rfl
  have hf : ![v,a,b,c] (3 : Fin 4) = c := rfl
  rw [ht,hf,show ![a,b,c] (0 : Fin 3) = a by rfl]
  change (v + a + b + c ≤ 132 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 55 ∧
    c ≤ 14 ∧ v + a + b + c ≤ gradeLimit (a + b + c) ∧
    x + 133484 * (v + a + b + c) < 99 * 179886 + 2 * (v * 0 + a * 1 + b * 2 + c * 3)) ↔ _
  omega
private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133484 * (gradeCeiling a b c - j) < 99 * 179886 + 2 * indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 132 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega
private abbrev Slot :=
  Σ c : Fin 15, Σ b : Fin ((55 - 3 * c.val) / 2 + 1),
    Σ a : Fin (55 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)
private abbrev Eligible := {u : Exponent // ColumnEligible u}
private theorem slot_bounds (c b a j x : ℕ) :
    (c < 15 ∧ b < (55 - 3 * c) / 2 + 1 ∧ a < 55 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 14 ∧ indexWeight a b c ≤ 55 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
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
  n * firstWidth a b c + 133484 * (n * (n - 1) / 2)
private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]
private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (55 - 3 * c - 2 * b + 1)
private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((55 - 3 * c) / 2 + 1)
private theorem slot_card : Fintype.card Slot = sumRange sliceCount 15 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]
private def totals : List ℕ := [619191880532, 560762278378, 504343373320, 450788967184, 399412925520, 351083655454, 305100817870, 262347558678, 222109200612, 185283761850, 151142093492, 120597219468, 92905385760, 68994667200, 48107729320]

private theorem slice_value (i : Fin 15) : sliceCount i = totals[i.val]! := by
  fin_cases i <;> decide +kernel

private theorem totalCount : sumRange sliceCount 15 = 4342171514638 := by
  rw [sumRange_eq_fin]
  calc
    _ = ∑ c : Fin 15, totals[c.val]! := Finset.sum_congr rfl fun c _ => slice_value c
    _ = _ := by rw [← sumRange_eq_fin]; decide +kernel


theorem eligible_card : Nonempty (Eligible ≃ Fin 4342171514638) := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  exact ⟨e.symm.trans ((Fintype.equivFin Slot).trans (finCongr (slot_card.trans totalCount)))⟩

#print axioms eligible_card
end Final50AnchorDimension
