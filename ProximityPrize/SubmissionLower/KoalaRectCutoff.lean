import ProximityPrize.SubmissionLower.KoalaRectPoleBalance
import ProximityPrize.SubmissionLower.UpperBranch5

set_option Elab.async false

-- merged module KoalaRectPosition
section Merged_KoalaRectPosition

-- merged module KoalaRectSource
section Merged_KoalaRectSource

set_option Elab.async false

namespace KoalaRect
noncomputable section
open Polynomial K1_14 K1_14_1 K1_14_1_7
open K1 (I)
open scoped BigOperators
open K1_14_1 (centerCoeff centerCoeff_eval)

def rectShaped {F : Type} [Field F] (U : Fin 2 → ℕ) (P : TrueSource F) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → ∀ z, e z ≤ U z

def seedSupport {F : Type} [Field F] (U : Fin 2 → ℕ) : Submodule F (TrueSource F) where
  carrier := {P | rectShaped U P}
  zero_mem' := by simp [rectShaped, sourceCoeff]
  add_mem' := by
    intro P Q hP hQ j i a e hne z
    by_contra hb
    have hP0 : sourceCoeff P j i a e = 0 := by
      by_contra hz
      exact hb (hP j i a e hz z)
    have hQ0 : sourceCoeff Q j i a e = 0 := by
      by_contra hz
      exact hb (hQ j i a e hz z)
    apply hne
    change ((((P + Q).coeff j).coeff i).coeff a).coeff e = 0
    simp only [Polynomial.coeff_add, AddMonoidAlgebra.coeff_add]
    change sourceCoeff P j i a e + sourceCoeff Q j i a e = 0
    rw [hP0, hQ0, add_zero]
  smul_mem' := by
    intro c P hP j i a e hne z
    apply hP j i a e _ z
    intro hz
    apply hne
    simp [sourceCoeff, Polynomial.coeff_smul, show (((P.coeff j).coeff i).coeff a).coeff e = 0 from hz]

abbrev rectAmbient (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  ambient h s W ⊓ seedSupport U

abbrev rectContacted (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  contacted h word s W ⊓ seedSupport U

abbrev rectComplete {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  complete Crt word s W ⊓ seedSupport U

def rectEvaluated {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule FX Jet :=
  Submodule.span FX (centerEval '' (rectComplete Crt word s W U : Set Source))

theorem rectEvaluated_le {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectEvaluated Crt word s W U ≤ evaluated Crt word s W :=
  Submodule.span_mono (Set.image_mono inf_le_left)

theorem rectEvaluated_axis {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape} {W : ℕ} {U : Fin 2 → ℕ} {P : Jet} (hP : P ∈ rectEvaluated Crt word s W U)
    (j i : ℕ) (z : Fin 2) : ((P.coeff j).coeff i).degreeOf z ≤ U z := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro e he
  by_contra hb
  have hsub : rectEvaluated Crt word s W U ≤ LinearMap.ker (centerCoeff j i e) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply centerCoeff_eval
    intro a
    by_contra hz
    exact hb (hQ.2 j i a e hz z)
  exact (MvPolynomial.mem_support_iff.mp he) (LinearMap.mem_ker.mp (hsub hP))

abbrev AxisIndex (U : Fin 2 → ℕ) := ∀ z : Fin 2, Fin (U z + 1)

def axisExponent {U : Fin 2 → ℕ} (e : AxisIndex U) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => (e z).val)

@[simp] theorem axisExponent_apply {U : Fin 2 → ℕ} (e : AxisIndex U) (z : Fin 2) :
    axisExponent e z = (e z).val := by simp [axisExponent]

def area (U : Fin 2 → ℕ) := (U 0 + 1) * (U 1 + 1)

theorem axis_card (U : Fin 2 → ℕ) : Fintype.card (AxisIndex U) = area U := by
  simp [AxisIndex, Fintype.card_pi, Fin.prod_univ_two, area]

theorem exists_axisIndex {U : Fin 2 → ℕ} (e : Fin 2 →₀ ℕ) (he : ∀ z, e z ≤ U z) :
    ∃ a : AxisIndex U, axisExponent a = e :=
  ⟨fun z => ⟨e z, Nat.lt_succ_of_le (he z)⟩, by ext z; simp⟩

theorem axisExponent_injective (U : Fin 2 → ℕ) : Function.Injective (axisExponent (U := U)) := by
  intro a b h
  funext z
  apply Fin.ext
  simpa using congrArg (fun e : Fin 2 →₀ ℕ => e z) h

open K1_14_1_5 (trueWidth lt_trueWidth_iff trueWidth_eq_add seedWeight_eq Exponents monomialAt coeffAt_monomialAt)

private abbrev RectIndex (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :=
  Σ q : Fin (s.B + 1), Σ j : Fin (min q.val s.J + 1),
    Fin (trueWidth h s W q.val j.val) × AxisIndex U

private def rectExponents {h : ℕ} {s : Shape} {W : ℕ} {U : Fin 2 → ℕ}
    (k : RectIndex h s W U) : Exponents :=
  (k.2.1.val, k.1.val - k.2.1.val, k.2.2.1.val, axisExponent k.2.2.2)

private theorem rectExponents_injective (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Function.Injective (rectExponents (h := h) (s := s) (W := W) (U := U)) := by
  rintro ⟨q, j, a, b⟩ ⟨q', j', a', b'⟩ he
  obtain ⟨hj, hi, ha, hb⟩ : j.val = j'.val ∧ q.val - j.val = q'.val - j'.val ∧
      a.val = a'.val ∧ axisExponent b = axisExponent b' := by simpa [rectExponents] using he
  have hqj := (Nat.le_of_lt_succ j.isLt).trans (min_le_left _ _)
  have hq'j' := (Nat.le_of_lt_succ j'.isLt).trans (min_le_left _ _)
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hje : j = j' := Fin.ext hj
  subst j'
  have hae : a = a' := Fin.ext ha
  subst a'
  have hbe := axisExponent_injective U hb
  subst b'
  rfl

private theorem rectExponents_exists {h : ℕ} {s : Shape} {W j i a : ℕ}
    {U : Fin 2 → ℕ} {e : Fin 2 →₀ ℕ} (hE : trueEligible h s W j i a e)
    (hU : ∀ z, e z ≤ U z) : ∃ k : RectIndex h s W U, rectExponents k = (j, i, a, e) := by
  obtain ⟨hq, hj, _, ha⟩ := hE
  obtain ⟨b, hb⟩ := exists_axisIndex e hU
  let q : Fin (s.B + 1) := ⟨i + j, by omega⟩
  let v : Fin (min q.val s.J + 1) := ⟨j, Nat.lt_succ_of_le (le_min (by dsimp [q]; omega) hj)⟩
  let x : Fin (trueWidth h s W q.val v.val) := ⟨a, (lt_trueWidth_iff h s W _ _ _).mpr ha⟩
  exact ⟨⟨q, v, x, b⟩, by simp [rectExponents, q, v, x, hb]⟩

private def rectMonomial {h : ℕ} {s : Shape} {W : ℕ} {U : Fin 2 → ℕ}
    (hbox : U 0 + U 1 ≤ s.U) (k : RectIndex h s W U) : rectAmbient h s W U := by
  refine ⟨monomialAt (rectExponents k), ?_, ?_⟩
  · intro j i a e he
    rw [coeffAt_monomialAt (rectExponents k) (j,i,a,e), ite_eq_right]
    intro hEq
    apply he
    change trueEligible h s W (j,i,a,e).1 (j,i,a,e).2.1 (j,i,a,e).2.2.1 (j,i,a,e).2.2.2
    rw [← hEq]
    rcases k with ⟨q, v, x, b⟩
    have hq := q.isLt
    have hv := v.isLt
    have hvq := min_le_left q.val s.J
    have hvJ := min_le_right q.val s.J
    have hvq' : q.val - v.val + v.val = q.val := by omega
    have hboxv := Nat.add_le_add (Nat.le_of_lt_succ (b 0).isLt) (Nat.le_of_lt_succ (b 1).isLt)
    simp only [rectExponents, trueEligible, hvq', seedWeight_eq, axisExponent_apply]
    exact ⟨by omega, by omega, hboxv.trans hbox, (lt_trueWidth_iff h s W _ _ _).mp x.isLt⟩
  · intro j i a e hz z
    change coeffAt _ j i a e ≠ 0 at hz
    rw [coeffAt_monomialAt (rectExponents k) (j,i,a,e)] at hz
    split_ifs at hz with he
    · change (j,i,a,e).2.2.2 z ≤ U z
      rw [← he]
      exact Nat.le_of_lt_succ (k.2.2.2 z).isLt
    · exact (hz rfl).elim

private def rectCoordinates (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    rectAmbient h s W U →ₗ[L] (RectIndex h s W U → L) where
  toFun P k := coeffAt P (rectExponents k).1 (rectExponents k).2.1
    (rectExponents k).2.2.1 (rectExponents k).2.2.2
  map_add' P Q := by funext k; simp [coeffAt]
  map_smul' c P := by funext k; simp [coeffAt, Polynomial.coeff_smul]

private def rectCoordinateEquiv (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hbox : U 0 + U 1 ≤ s.U) : rectAmbient h s W U ≃ₗ[L] (RectIndex h s W U → L) := by
  classical
  refine LinearEquiv.ofBijective (rectCoordinates h s W U) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    apply MvPolynomial.ext
    intro e
    change coeffAt P j i a e = coeffAt Q j i a e
    by_cases he : trueEligible h s W j i a e
    · by_cases hb : ∀ z, e z ≤ U z
      · obtain ⟨k, hk⟩ := rectExponents_exists he hb
        have hval := congrFun hPQ k
        change coeffAt P (rectExponents k).1 (rectExponents k).2.1 (rectExponents k).2.2.1
          (rectExponents k).2.2.2 = coeffAt Q (rectExponents k).1 (rectExponents k).2.1
            (rectExponents k).2.2.1 (rectExponents k).2.2.2 at hval
        simpa only [hk] using hval
      · have hzero (R : rectAmbient h s W U) : coeffAt R j i a e = 0 := by
          by_contra hne
          exact hb (R.property.2 j i a e hne)
        rw [hzero P, hzero Q]
    · exact (P.property.1 j i a e he).trans (Q.property.1 j i a e he).symm
  · intro f
    refine ⟨∑ k, f k • rectMonomial hbox k, ?_⟩
    funext d
    have hmono (k : RectIndex h s W U) : rectCoordinates h s W U (rectMonomial hbox k) d =
        if k = d then 1 else 0 := by
      change coeffAt (monomialAt (rectExponents k)) (rectExponents d).1 (rectExponents d).2.1
        (rectExponents d).2.2.1 (rectExponents d).2.2.2 = _
      simp only [coeffAt_monomialAt, (rectExponents_injective h s W U).eq_iff]
    rw [map_sum]
    simp [Finset.sum_apply, hmono, mul_ite]

theorem rectAmbient_finrank (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hbox : U 0 + U 1 ≤ s.U) :
    Module.finrank L (rectAmbient h s W U) = area U * shapeSum s (trueWidth h s W) := by
  rw [(rectCoordinateEquiv h s W U hbox).finrank_eq, Module.finrank_pi]
  unfold RectIndex shapeSum
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, axis_card, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact Nat.mul_comm _ _

end
end KoalaRect

end Merged_KoalaRectSource

-- merged module KoalaRectCharge
section Merged_KoalaRectCharge

namespace KoalaRect
open K1_14 (Shape shapeSum)

def rectSlots (U d : Fin 2 → ℕ) (r : ℕ) : ℕ :=
  (U 0 + 1 - r*d 0) * (U 1 + 1 - r*d 1)

def rectGain (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*A+j - q*(131071-h)
    let c := rectSlots U d
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

def rectDebit (h nodes moment : ℕ) (U : Fin 2 → ℕ) : ℕ :=
  area U * nodes + h*(U 0+U 1+2)*moment

theorem rectSlots_zero (U d : Fin 2 → ℕ) : rectSlots U d 0 = area U := by
  simp [rectSlots, area]

theorem rectSlots_antitone (U d : Fin 2 → ℕ) : Antitone (rectSlots U d) :=
  fun _ _ h => Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _)
    (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _)

end KoalaRect

end Merged_KoalaRectCharge

-- merged module KoalaRectPosition
section Merged_KoalaRectPosition

set_option Elab.async false

namespace KoalaRect
open Finset
open K1_14 (Shape shapeSum)
open K1_14_4 (gradeWidth)
open scoped BigOperators
open K1_14_4 (sum_slot_drops sum_interval power_threshold shapeSum_swap)

def rectPower (A h : ℕ) (s : Shape) (W : ℕ) : ℕ := 1 + (s.m*A-1-W)/(2*h)

def rectKept (U d : Fin 2 → ℕ) (g r : ℕ) : ℕ := if r ≤ g then rectSlots U d r else 0

def rectCapacity (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then rectKept U d ((q-j)/E) (rectPower A h s W-j) else 0

def rectGrade (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W j : ℕ) : ℕ :=
  let r := rectPower A h s W-j
  (gradeWidth (131071-h) s.B W j-r*E)*rectSlots U d r

private theorem rectGrade_sum (k B W j r E : ℕ) (U d : Fin 2 → ℕ) (hk : 0 < k) (he : 0 < E) :
    (gradeWidth k B W j-r*E)*rectSlots U d r =
      ∑ q ∈ Ico j (B+1), if q*k ≤ W+j then rectKept U d ((q-j)/E) r else 0 := by
  have hq (q : ℕ) : q*k ≤ W+j ↔ q < (W+j)/k + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk]
  have hr (q : ℕ) : r ≤ (q-j)/E ↔ r*E ≤ q-j := Nat.le_div_iff_mul_le he
  have hI : (Ico j (B+1)).filter (fun q => q*k ≤ W+j ∧ r ≤ (q-j)/E) =
      Ico (j+r*E) (min (B+1) ((W+j)/k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, hq, hr, lt_min_iff]
    omega
  simp_rw [rectKept, ← ite_and]
  rw [← sum_filter, hI, sum_const, Nat.nsmul_eq_mul, Nat.card_Ico, gradeWidth, Nat.sub_sub]

theorem rectCapacity_eq (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) (W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), rectGrade A h s E U d W j) = rectCapacity A h s E U d W := by
  rw [rectCapacity, ← shapeSum_swap]
  exact sum_congr rfl fun j _ => rectGrade_sum _ _ _ _ _ _ _ _ hk he

private theorem rectPosition_sum (top step t j g : ℕ) (U d : Fin 2 → ℕ)
    (hj : j ≤ t) (hs : 0 < step) :
    (∑ W ∈ range top, if t ≤ W+j then rectKept U d g (1+(top-1-W)/step-j) else 0) +
    ((∑ a ∈ range g, (rectSlots U d a - rectSlots U d (a+1)) * (top+j-t-step*(j+a))) +
      rectSlots U d g * (top+j-t-step*(j+g))) =
    area U * (top+j-t) := by
  let C := rectKept U d g
  let L W := 1+(top-1-W)/step-j
  have hmono : Antitone C := by
    intro a b hab
    by_cases hb : b ≤ g
    · simpa only [C, rectKept, ite_eq_left hb, ite_eq_left (hab.trans hb)] using
        rectSlots_antitone U d hab
    · simp [C, rectKept, hb]
  have hmin (l : ℕ) : C (min (g+1) l) = C l := by
    by_cases hl : l ≤ g+1
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega)]
      simp [C, rectKept, show ¬ g+1 ≤ g by omega, show ¬ l ≤ g by omega]
  have hsplit :
      (∑ a ∈ range (g+1), (C a - C (a+1)) * (top+j-t-step*(j+a))) =
        (∑ a ∈ range g, (rectSlots U d a - rectSlots U d (a+1)) * (top+j-t-step*(j+a))) +
        rectSlots U d g * (top+j-t-step*(j+g)) := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro a ha
      simp [C, rectKept, (mem_range.mp ha).le, Nat.succ_le_of_lt (mem_range.mp ha)]
    · simp [C, rectKept, show ¬ g+1 ≤ g by omega]
  rw [← hsplit]
  change (∑ W ∈ range top, if t ≤ W+j then C (L W) else 0) + _ = _
  have hzero : C 0 = area U := by simp [C, rectKept, rectSlots_zero]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range (g+1)), ← sum_add_distrib]
  have hbase := sum_interval top j t 0 (C 0) hj
  rw [Nat.sub_zero] at hbase
  rw [← hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W+j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops C hmono (g+1) (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [show a < L W ↔ W+step*(j+a) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]

theorem rectCapacity_total (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ)
    (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*A), rectCapacity A h s E U d W) + rectGain A h s E U d =
      area U * shapeSum s (fun q j => s.m*A+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*A), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*A), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [rectCapacity, rectGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact rectPosition_sum (s.m*A) (2*h) (q*(131071-h)) j ((q-j)/E) U d (hjq.trans hq) hh

end KoalaRect

end Merged_KoalaRectPosition

end Merged_KoalaRectPosition

-- merged module KoalaRectCutoff
section Merged_KoalaRectCutoff

-- merged module KoalaRectQuotient
section Merged_KoalaRectQuotient

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section

open Polynomial MvPolynomial
open K1_14 (FX Equation)
open Cardinal
open K1_14_4 (seedView seedView_coeff flatten)

/-- Degree in one seed coordinate with the ordinate kept in the coefficient ring. -/
def axisDegree (f : Equation) (z : Fin 2) : ℕ := (seedView f).degreeOf z

theorem axisDegree_le_iff (f : Equation) (z : Fin 2) (u : ℕ) :
    axisDegree f z ≤ u ↔ ∀ i : ℕ, (f.coeff i).degreeOf z ≤ u := by
  unfold axisDegree
  constructor
  · intro h i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hs : d ∈ (seedView f).support := by
      rw [MvPolynomial.mem_support_iff] at hd ⊢
      intro hz
      apply hd
      rw [← seedView_coeff, hz, Polynomial.coeff_zero]
    exact (MvPolynomial.degreeOf_le_iff.mp h) d hs
  · intro h
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
    apply (MvPolynomial.degreeOf_le_iff.mp (h i)) d
    rwa [MvPolynomial.mem_support_iff, ← seedView_coeff, ← Polynomial.mem_support_iff]

theorem axisDegree_mul {f g : Equation} (hf : f ≠ 0) (hg : g ≠ 0) (z : Fin 2) :
    axisDegree (f * g) z = axisDegree f z + axisDegree g z := by
  unfold axisDegree
  rw [map_mul, MvPolynomial.degreeOf_mul_eq (by simpa using hf) (by simpa using hg)]

theorem axisDegree_pow {f : Equation} (hf : f ≠ 0) (n : ℕ) (z : Fin 2) :
    axisDegree (f ^ n) z = n * axisDegree f z := by
  induction n with
  | zero => simp [axisDegree]
  | succ n ih => rw [pow_succ, axisDegree_mul (pow_ne_zero _ hf) hf, ih, Nat.succ_mul]

private abbrev QuotientSlots (a : ℕ) (u : Fin 2 → ℕ) := Fin a × (∀ z : Fin 2, Fin (u z))

private def quotientExponent {a : ℕ} {u : Fin 2 → ℕ} (k : QuotientSlots a u) :
    Option (Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => z.elim k.1.val (fun i => (k.2 i).val))

private def quotientSupport (a : ℕ) (u : Fin 2 → ℕ) : Finset (Option (Fin 2) →₀ ℕ) :=
  Finset.univ.image (quotientExponent (a := a) (u := u))

private theorem flatten_mem_quotientSupport {q : Equation} {a : ℕ} {u : Fin 2 → ℕ}
    (hy : q.natDegree < a) (hu : ∀ z, axisDegree q z < u z) :
    flatten q ∈ restrictSupport FX (↑(quotientSupport a u) : Set (Option (Fin 2) →₀ ℕ)) := by
  apply (MvPolynomial.mem_restrictSupport_iff FX).mpr
  intro m hm
  have hc : ((seedView q).coeff m.some).coeff (m none) ≠ 0 := by
    change ((optionEquivRight FX (Fin 2) (flatten q)).coeff m.some).coeff (m none) ≠ 0
    rw [optionEquivRight_coeff_coeff, Finsupp.optionElim_some]
    exact MvPolynomial.mem_support_iff.mp hm
  have hs : m.some ∈ (seedView q).support :=
    MvPolynomial.mem_support_iff.mpr (fun hz => hc (by rw [hz, Polynomial.coeff_zero]))
  have hq : (q.coeff (m none)).coeff m.some ≠ 0 := by rwa [← seedView_coeff]
  have hmY : m none < a := (Polynomial.le_natDegree_of_ne_zero (fun hz => hq (by simp [hz]))).trans_lt hy
  have hmU (z : Fin 2) : m (some z) < u z :=
    (MvPolynomial.le_degreeOf_of_mem_support z hs).trans_lt (hu z)
  let k : QuotientSlots a u := ⟨⟨m none, hmY⟩, fun z => ⟨m (some z), hmU z⟩⟩
  change m ∈ quotientSupport a u
  refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
  ext z
  cases z <;> simp [quotientExponent, k]

/-- Dividing by `g` spends the ordinate degree and the two seed degrees independently. -/
theorem rank_rect_multiples_le (C : Submodule FX Equation) {g : Equation} (hg : g ≠ 0)
    {a yspent : ℕ} {U spent : Fin 2 → ℕ} (hyspent : yspent ≤ g.natDegree)
    (hspent : ∀ z, spent z ≤ axisDegree g z)
    (hC : ∀ c ∈ C, c ≠ 0 → c.natDegree < a ∧
      (∀ i z, (c.coeff i).degreeOf z ≤ U z) ∧ g ∣ c) :
    Module.rank FX C ≤ (↑((a - yspent) * (U 0 + 1 - spent 0) * (U 1 + 1 - spent 1)) : Cardinal) := by
  classical
  let u (z : Fin 2) := U z + 1 - spent z
  let S := quotientSupport (a - yspent) u
  let B := restrictSupport FX (↑S : Set (Option (Fin 2) →₀ ℕ))
  let _ : Module.Finite FX B := restrictSupport_finite S.finite_toSet
  let m : B →ₗ[FX] Equation :=
    (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
  have hm : C ≤ LinearMap.range m := by
    intro c hc
    by_cases hn : c = 0
    · rw [hn]
      exact (LinearMap.range m).zero_mem
    · obtain ⟨hY, hU, q, rfl⟩ := hC c hc hn
      have hq : q ≠ 0 := right_ne_zero_of_mul hn
      have hqY : q.natDegree < a - yspent := by
        rw [Polynomial.natDegree_mul hg hq] at hY
        omega
      have hqU (z : Fin 2) : axisDegree q z < u z := by
        have hu := (axisDegree_le_iff (g * q) z (U z)).mpr (fun i => hU i z)
        rw [axisDegree_mul hg hq] at hu
        have hs := hspent z
        dsimp [u]
        omega
      refine ⟨⟨flatten q, flatten_mem_quotientSupport hqY hqU⟩, ?_⟩
      change g * flatten.symm (flatten q) = g * q
      rw [AlgEquiv.symm_apply_apply]
  have hB : Module.finrank FX B ≤ (a - yspent) * (U 0 + 1 - spent 0) * (U 1 + 1 - spent 1) := by
    rw [MvPolynomial.finrank_restrictSupport_finset]
    calc
      S.card ≤ Fintype.card (QuotientSlots (a - yspent) u) := by
        simpa only [S, quotientSupport, Finset.card_univ] using
          (Finset.card_image_le (s := (Finset.univ : Finset (QuotientSlots (a - yspent) u)))
            (f := quotientExponent))
      _ = _ := by
        simp only [QuotientSlots, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Fin.prod_univ_two, u]
        rw [Nat.mul_assoc]
  calc
    _ ≤ Module.rank FX (LinearMap.range m) := Submodule.rank_mono hm
    _ ≤ Module.rank FX B := rank_range_le m
    _ ≤ _ := by rw [← Module.finrank_eq_rank]; exact_mod_cast hB


end
end KoalaRect

end Merged_KoalaRectQuotient

-- merged module KoalaRectCutoff
section Merged_KoalaRectCutoff

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section
open Finset Polynomial
open K1_14 (FX Jet Equation Shape)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth)
open K1_14_4 (gradeMap mem_filtered finrank_le_grades)
open scoped BigOperators

/-- Grade capacity for an independently prescribed physical window and
residual contact order. These can both decrease after graph division. -/
theorem rectContact_finrank_le (step B J k E W : ℕ) (U d : Fin 2 → ℕ)
    (V : Submodule FX Jet) {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree)
    (hk : 0 < step)
    (hrow : ∀ {P : Jet}, P ∈ V → P ≠ 0 →
      P.leadingCoeff.natDegree + P.natDegree ≤ B ∧ P.natDegree ≤ J)
    (haxis : ∀ P ∈ V, ∀ j i z, ((P.coeff j).coeff i).degreeOf z ≤ U z)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree)*step ≤ W+P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (k-P.natDegree) ∣ P.leadingCoeff)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    Module.finrank FX V ≤ ∑ j∈range (J+1),
      (gradeWidth step B W j-(k-j)*E)*rectSlots U d (k-j) := by
  refine finrank_le_grades (F := FX) (A := Equation) V (fun j=>(gradeWidth step B W j - (k-j)*E)*rectSlots U d (k-j))
    (J+1) ?_ ?_
  · intro j
    let r := k-j
    have hmul := rank_rect_multiples_le (gradeMap (F := FX) (A := Equation) V j).range
      (g := f^r) (pow_ne_zero r hf)
      (a := gradeWidth step B W j) (yspent := r*E)
      (U := U) (spent := fun z => r*axisDegree f z)
      (by rw [Polynomial.natDegree_pow]; exact Nat.mul_le_mul_left _ hE)
      (fun z => by rw [axisDegree_pow hf]) ?_
    · apply hmul.trans
      rw [Nat.mul_assoc]
      change (↑((gradeWidth step B W j-r*E)*rectSlots U (axisDegree f) r) : Cardinal) ≤
        ↑((gradeWidth step B W j-r*E)*rectSlots U d r)
      exact_mod_cast Nat.mul_le_mul_left (gradeWidth step B W j-r*E) (hslots r)
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB, _⟩ := hrow hpV hn
      have hwidth := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ (∀ i z, ((P.coeff j).coeff i).degreeOf z ≤ U z) ∧
        f^r ∣ P.coeff j
      refine ⟨?_, haxis P hpV j, ?_⟩
      · rw [← hj, coeff_natDegree, hj]
        have hle := (Nat.le_div_iff_mul_le hk).2 hwidth
        unfold gradeWidth
        omega
      · rwa [← hj, coeff_natDegree]
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2)

theorem rectCutoff_finrank_le (A h : ℕ) (s : Shape) (E W : ℕ) (U d : Fin 2 → ℕ)
    (V : Submodule FX Jet) {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree)
    (hk : 0 < 131071-h) (he : 0 < E)
    (hsupport : ∀ P ∈ V, RowCaps P s)
    (haxis : ∀ P ∈ V, ∀ j i z, ((P.coeff j).coeff i).degreeOf z ≤ U z)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (rectPower A h s W-P.natDegree) ∣ P.leadingCoeff)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    Module.finrank FX V ≤ rectCapacity A h s E U d W := by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J := by
    have hn' : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    exact ⟨(hsupport P hP _ _ hn').1, (hsupport P hP _ _ hn').2.1⟩
  rw [← rectCapacity_eq _ _ _ _ _ _ _ hk he]
  exact rectContact_finrank_le _ _ _ _ _ _ U d V hf hE hk hrow haxis hlead hdvd hslots

end
end KoalaRect

end Merged_KoalaRectCutoff

end Merged_KoalaRectCutoff
