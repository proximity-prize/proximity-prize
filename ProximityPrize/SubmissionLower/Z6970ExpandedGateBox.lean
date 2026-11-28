import ProximityPrize.SubmissionLower.Z6970ExpandedAmbientCore
import ProximityPrize.SubmissionLower.Z6970ExpandedCappedArithmetic

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000

namespace ExpandedGateBox6970

open K1_13_6 (GenericField)
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open ExpandedColumns6970 (jetColumns jetExponents)
open MvPolynomial Finset
open ExpandedLayerBank6970 (ambient)

def fitsBox (b j t : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ b ∧ m.weight oldWeight ≤ j ∧ m 3 ≤ t

noncomputable instance (b j t : ℕ) (m : JetExp) : Decidable (fitsBox b j t m) := by
  unfold fitsBox; infer_instance

noncomputable def ambCount (b j t : ℕ) : ℕ := (jetColumns.filter (fitsBox b j t)).card




theorem ambCount_mono {b j t b' j' t' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ht : t ≤ t') :
    ambCount b j t ≤ ambCount b' j' t' := by
  unfold ambCount
  apply Finset.card_le_card
  intro m hm
  obtain ⟨hc, hf⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hc, ⟨hf.1.trans hb, hf.2.1.trans hj, hf.2.2.trans ht⟩⟩

end ExpandedGateBox6970

namespace ExpandedExactAmbient6970
open K1_13_2_2 (JetExp oldWeight gradeWeight mem_cumulativeColumns)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open ExpandedColumns6970 (jetColumns sumGrade sumOld gradeCap)
open Low6969GateCell (cappedN capped_eq sumUpTo sumUpTo_eq)
open scoped BigOperators

def bound (b : ℕ) : ℕ := min 4025 (b+1)
def index (j : ℕ) : ℕ := min 1679 j

def count (b j t : ℕ) : ℤ :=
  sumUpTo (fun q => cappedN (gradeCap q) (index j) (min 500 t)) (bound b)

private noncomputable def grid (b j t : ℕ) : Finset (Σ _ : ℕ, JetExp) :=
  (Finset.range (bound b)).sigma fun q => cappedColumns (gradeCap q) (index j) (min 500 t)

private noncomputable def pad (x : Σ _ : ℕ, JetExp) : JetExp :=
  x.2 + Finsupp.single 0 (x.1 - gradeCap x.1)

private theorem pad_spec {b j t : ℕ} {x : Σ _ : ℕ, JetExp} (hx : x ∈ grid b j t) :
    (pad x).weight gradeWeight = x.1 ∧
    (pad x).weight oldWeight = x.2.weight oldWeight ∧
    (∀ i : Fin 4, i ≠ 0 → pad x i = x.2 i) := by
  obtain ⟨q,m⟩ := x
  have hm := (mem_cappedColumns.mp (Finset.mem_sigma.mp hx).2).1
  have hg : m.weight gradeWeight = gradeCap q := by
    exact_mod_cast (mem_cumulativeColumns.mp hm).1
  have hq : gradeCap q ≤ q := min_le_left _ _
  have h0 : pad ⟨q,m⟩ 0 = m 0 + (q-gradeCap q) := by simp [pad]
  have hsucc (i : Fin 4) (hi : i ≠ 0) : pad ⟨q,m⟩ i = m i := by
    simp [pad,Finsupp.single_eq_of_ne hi]
  refine ⟨?_, ?_, hsucc⟩
  · change (pad ⟨q,m⟩).weight gradeWeight = q
    rw [sumGrade, h0, hsucc 1 (by decide), hsucc 2 (by decide), hsucc 3 (by decide)]
    rw [sumGrade] at hg
    omega
  · rw [sumOld,sumOld,hsucc 1 (by decide),hsucc 2 (by decide),hsucc 3 (by decide)]

private theorem map_mem {b j t : ℕ} {x : Σ _ : ℕ, JetExp} (hx : x ∈ grid b j t) :
    pad x ∈ jetColumns.filter (ExpandedGateBox6970.fitsBox b j t) := by
  obtain ⟨q,m⟩ := x
  have hq : q < bound b := Finset.mem_range.mp (Finset.mem_sigma.mp hx).1
  obtain ⟨hm,ht⟩ := mem_cappedColumns.mp (Finset.mem_sigma.mp hx).2
  obtain ⟨hg,hi⟩ := mem_cumulativeColumns.mp hm
  obtain ⟨eB,eJ,eOther⟩ := pad_spec hx
  dsimp only at eB eJ eOther
  have hgrade : m.weight gradeWeight = gradeCap q := by exact_mod_cast hg
  have hindex : m.weight oldWeight ≤ index j := by exact_mod_cast hi
  have htop : m 3 ≤ min 500 t := by exact_mod_cast ht
  have hD : gradeCap q ≤ ExpandedTaper6970.cap q := min_le_right _ _
  have hb : q ≤ 4024 ∧ q ≤ b := by unfold bound at hq; omega
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨eB.trans_le hb.2,eJ.trans_le (hindex.trans (min_le_right _ _)),?_⟩⟩
  · apply ExpandedColumns6970.jetExponents_finite.mem_toFinset.mpr
    change (pad ⟨q,m⟩).weight gradeWeight ≤ 4024 ∧
      (pad ⟨q,m⟩).weight oldWeight ≤ 1679 ∧ _
    refine ⟨eB.trans_le hb.1,eJ.trans_le (hindex.trans (min_le_left _ _)),?_,?_⟩
    · rw [eOther 3 (by decide)]
      exact htop.trans (min_le_left _ _)
    · rw [eB,eOther 1 (by decide),eOther 2 (by decide),eOther 3 (by decide)]
      rw [sumGrade] at hgrade
      omega
  · rw [eOther 3 (by decide)]
    exact htop.trans (min_le_right _ _)

private theorem pad_injective (b j t : ℕ) : Set.InjOn pad (grid b j t : Set (Σ _ : ℕ, JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨q,m⟩ := x
  obtain ⟨q',m'⟩ := y
  have eQ : q = q' := (pad_spec hx).1.symm.trans
    ((congrArg (fun e : JetExp => e.weight gradeWeight) hxy).trans (pad_spec hy).1)
  subst q'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q-gradeCap q))
    exact hxy
  subst m'
  rfl

private noncomputable def unpad (m : JetExp) : Σ _ : ℕ, JetExp :=
  let q := m.weight gradeWeight
  ⟨q,Finsupp.equivFunOnFinite.symm ![m 0-(q-gradeCap q),m 1,m 2,m 3]⟩

private theorem unpad_coeff_zero (m : JetExp) :
    (unpad m).2 0 = m 0-(m.weight gradeWeight-gradeCap (m.weight gradeWeight)) := rfl

private theorem unpad_coeff_succ (m : JetExp) (i : Fin 4) (hi : i ≠ 0) :
    (unpad m).2 i = m i := by
  fin_cases i <;> first | exact (hi rfl).elim | rfl

private theorem unpad_removed {m : JetExp} (hm : m ∈ ExpandedColumns6970.jetExponents) :
    m.weight gradeWeight-gradeCap (m.weight gradeWeight) ≤ m 0 := by
  let q := m.weight gradeWeight
  have hc : m 1 + m 2 + m 3 ≤ ExpandedTaper6970.cap q := hm.2.2.2
  have hg := sumGrade m
  have hq : q = m 0 + m 1 + m 2 + m 3 := hg
  show q-gradeCap q ≤ m 0
  unfold gradeCap
  omega

private theorem unpad_mem {b j t : ℕ} {m : JetExp}
    (hm : m ∈ jetColumns.filter (ExpandedGateBox6970.fitsBox b j t)) :
    unpad m ∈ grid b j t := by
  obtain ⟨hcol,hfit⟩ := Finset.mem_filter.mp hm
  have hm' := ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp hcol
  let q := m.weight gradeWeight
  have hq : q < bound b := by
    have h := hm'.1
    have h' := hfit.1
    unfold bound
    change q ≤ 4024 at h
    change q ≤ b at h'
    omega
  have hremove := unpad_removed hm'
  have hg : (unpad m).2.weight gradeWeight = gradeCap q := by
    rw [sumGrade,unpad_coeff_zero,unpad_coeff_succ m 1 (by decide),
      unpad_coeff_succ m 2 (by decide),unpad_coeff_succ m 3 (by decide)]
    have h := sumGrade m
    have hq' : gradeCap q ≤ q := min_le_left _ _
    change q = _ at h
    change m 0-(q-gradeCap q)+m 1+m 2+m 3 = _
    change q-gradeCap q ≤ m 0 at hremove
    omega
  have hi : (unpad m).2.weight oldWeight = m.weight oldWeight := by
    rw [sumOld,sumOld,unpad_coeff_succ m 1 (by decide),
      unpad_coeff_succ m 2 (by decide),unpad_coeff_succ m 3 (by decide)]
  have htop : (unpad m).2 3 ≤ min 500 t := by
    rw [unpad_coeff_succ m 3 (by decide)]
    exact le_min hm'.2.2.1 hfit.2.2
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_range.mpr hq, mem_cappedColumns.mpr ⟨mem_cumulativeColumns.mpr ⟨?_,?_⟩,?_⟩⟩
  · exact_mod_cast hg
  · rw [hi]
    exact_mod_cast (show m.weight oldWeight ≤ index j from le_min hm'.2.1 hfit.2.1)
  · exact_mod_cast htop

private theorem pad_unpad {m : JetExp} (hm : m ∈ ExpandedColumns6970.jetExponents) :
    pad (unpad m) = m := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [pad,Finsupp.add_apply,Finsupp.single_eq_same]
    change (unpad m).2 0 + (m.weight gradeWeight-gradeCap (m.weight gradeWeight)) = m 0
    rw [unpad_coeff_zero,Nat.sub_add_cancel (unpad_removed hm)]
  · simp [pad,Finsupp.single_eq_of_ne hi,unpad_coeff_succ m i hi]

theorem count_eq (b j t : ℕ) : count b j t = (ExpandedGateBox6970.ambCount b j t : ℤ) := by
  have size : ((grid b j t).card : ℤ) = count b j t := by
    unfold grid count
    rw [Finset.card_sigma,Nat.cast_sum,sumUpTo_eq]
    apply Finset.sum_congr rfl
    intro q _
    rw [capped_card K1_13_2_2_2.proof]
    have h : min (500 : ℤ) (t : ℤ) = ((min 500 t : ℕ) : ℤ) := by omega
    rw [h,capped_eq]
  rw [← size]
  unfold ExpandedGateBox6970.ambCount
  exact_mod_cast Finset.card_bij
    (s := grid b j t) (t := jetColumns.filter (ExpandedGateBox6970.fitsBox b j t))
    (fun x _ => pad x) (fun _ hx => map_mem hx)
    (fun _ hx _ hy h => pad_injective b j t hx hy h)
    (fun y hy => ⟨unpad y,unpad_mem hy,pad_unpad
      (ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp (Finset.mem_filter.mp hy).1)⟩)


end ExpandedExactAmbient6970
