import ProximityPrize.SubmissionLower.R6960Low6960VariableSelect
import ProximityPrize.SubmissionLower.R6960Low6960ShapeGate

-- merged module Gate61Box
section Merged_Gate61Box

set_option autoImplicit false
set_option Elab.async false

namespace Gate61Box

open K1_13_6 (GenericField)
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetColumns jetExponents)
open MvPolynomial Finset
open Low6960SharedShapeRank (ambient)

def fitsBox (b j t : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ b ∧ m.weight oldWeight ≤ j ∧ m 3 ≤ t

noncomputable instance (b j t : ℕ) (m : JetExp) : Decidable (fitsBox b j t m) := by
  unfold fitsBox; infer_instance

theorem fits_eq (r : ℕ) (m : JetExp) : Low6960ShapeGate.fits r m ↔ fitsBox (r*63) (r*26) (r*7) m :=
  Iff.rfl

noncomputable def ambCount (b j t : ℕ) : ℕ := (jetColumns.filter (fitsBox b j t)).card

noncomputable def boxSpace (b j t : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (fitsBox b j t)))).comap ambient.subtype

theorem boxSpace_dim (b j t : ℕ) : Module.finrank GenericField (boxSpace b j t) = ambCount b j t := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (fitsBox b j t))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact TaperColumns.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (fitsBox b j t)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, finrank_restrictSupport_finset]
  rfl

theorem cutoff_eq_box (r : ℕ) : Low6960SharedShapeRank.cutoff r = boxSpace (r*63) (r*26) (r*7) := rfl

theorem ambCount_cutoff (r : ℕ) : ambCount (r*63) (r*26) (r*7) = Low6960ShapeGate.width r := rfl

theorem boxSpace_mono {b j t b' j' t' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ht : t ≤ t') :
    boxSpace b j t ≤ boxSpace b' j' t' := by
  intro Q hQ m hm
  have hfin : fitsBox b j t m := (Finset.mem_filter.mp
    ((mem_restrictSupport_iff GenericField).mp hQ hm)).2
  have hcol := (Finset.mem_filter.mp
    ((mem_restrictSupport_iff GenericField).mp hQ hm)).1
  exact Finset.mem_filter.mpr ⟨hcol, ⟨hfin.1.trans hb, hfin.2.1.trans hj, hfin.2.2.trans ht⟩⟩

theorem ambCount_mono {b j t b' j' t' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ht : t ≤ t') :
    ambCount b j t ≤ ambCount b' j' t' := by
  unfold ambCount
  apply Finset.card_le_card
  intro m hm
  obtain ⟨hc, hf⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hc, ⟨hf.1.trans hb, hf.2.1.trans hj, hf.2.2.trans ht⟩⟩

end Gate61Box

end Merged_Gate61Box

-- merged module Gate61Amb
section Merged_Gate61Amb

set_option autoImplicit false

namespace Gate61Amb
open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open TaperColumns (jetColumns jetExponents)
open TaperMoments (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open TaperColumns (sumGrade sumOld)

def bound (b : ℕ) : ℕ := min 4013 (b + 1)
def start (k : ℕ) : ℕ := 16 * k
def stop (b k : ℕ) : ℕ := min (bound b) (start (k + 1))
def chunks (b : ℕ) : ℕ := (bound b + 15) / 16
def padGrade (b k : ℕ) : ℕ := min (gradeCap (start k)) (gradeCap (stop b k - 1))
def index (j : ℕ) : ℕ := min 1650 j

private theorem grade_le {b k q : ℕ} (hlo : start k ≤ q) (hhi : q < stop b k) :
    padGrade b k ≤ gradeCap q := by
  unfold padGrade gradeCap
  have hcap := TaperBudget.cap_antitone (show q ≤ stop b k-1 by omega)
  exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans hlo))
    ((min_le_right _ _).trans ((min_le_right _ _).trans hcap))

noncomputable def grid (b j t : ℕ) : Finset (Σ _ : ℕ, ℕ × JetExp) :=
  (range (chunks b)).sigma fun k => (Ico (start k) (stop b k)).product
    (cappedColumns (padGrade b k) (index j) t)

noncomputable def pad (b : ℕ) (x : Σ _ : ℕ, ℕ × JetExp) : JetExp :=
  x.2.2 + Finsupp.single 0 (x.2.1 - padGrade b x.1)

private theorem pad_spec {b j t : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid b j t) :
    (pad b x).weight gradeWeight = x.2.1 ∧
    (pad b x).weight oldWeight = x.2.2.weight oldWeight ∧
    (∀ i : Fin 4, i ≠ 0 → pad b x i = x.2.2 i) := by
  obtain ⟨k,q,m⟩ := x
  have hm := (mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2).1
  have hm' := (mem_cumulativeColumns.mp hm).1
  have hg : m.weight gradeWeight = padGrade b k := by exact_mod_cast hm'
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  change start k ≤ q at hl
  change q < stop b k at hh
  have hq := (grade_le hl hh).trans (min_le_left _ _ : gradeCap q ≤ q)
  have h0 : pad b ⟨k,q,m⟩ 0 = m 0 + (q-padGrade b k) := by simp [pad]
  have hsucc (i : Fin 4) (hi : i ≠ 0) : pad b ⟨k,q,m⟩ i = m i := by
    simp [pad,Finsupp.single_eq_of_ne hi]
  refine ⟨?_, ?_, hsucc⟩
  · change (pad b ⟨k,q,m⟩).weight gradeWeight = q
    rw [sumGrade, h0, hsucc 1 (by decide), hsucc 2 (by decide), hsucc 3 (by decide)]
    rw [sumGrade] at hg
    omega
  · rw [sumOld,sumOld,hsucc 1 (by decide),hsucc 2 (by decide),hsucc 3 (by decide)]

private theorem map_mem {b j t : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid b j t) :
    pad b x ∈ jetColumns.filter (Gate61Box.fitsBox b j t) := by
  obtain ⟨k,q,m⟩ := x
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hj,ht⟩ := mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2
  obtain ⟨hg,hi⟩ := mem_cumulativeColumns.mp hj
  obtain ⟨eB,eJ,eOther⟩ := pad_spec hx
  dsimp only at eB eJ eOther hl hh
  have hgrade : m.weight gradeWeight = padGrade b k := by exact_mod_cast hg
  have hindex : m.weight oldWeight ≤ index j := by exact_mod_cast hi
  have htop : m 3 ≤ t := by exact_mod_cast ht
  have hD := (grade_le hl hh).trans (min_le_right _ _ : gradeCap q ≤ TaperBudget.cap q)
  have hb : q ≤ 4012 ∧ q ≤ b := by
    unfold stop bound at hh
    omega
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨eB.trans_le hb.2,eJ.trans_le (hindex.trans (min_le_right _ _)),?_⟩⟩
  · apply TaperColumns.jetExponents_finite.mem_toFinset.mpr
    change (pad b ⟨k,q,m⟩).weight gradeWeight ≤ 4012 ∧
      (pad b ⟨k,q,m⟩).weight oldWeight ≤ 1650 ∧ _
    refine ⟨eB.trans_le hb.1,eJ.trans_le (hindex.trans (min_le_left _ _)),?_⟩
    rw [eB,eOther 1 (by decide),eOther 2 (by decide),eOther 3 (by decide)]
    rw [sumGrade] at hgrade
    omega
  · rwa [eOther 3 (by decide)]

private theorem pad_injective (b j t : ℕ) : Set.InjOn (pad b) (grid b j t : Set (Σ _ : ℕ, ℕ × JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨k,q,m⟩ := x
  obtain ⟨k',q',m'⟩ := y
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hlo',hhi'⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hy).2).1
  have eQ : q = q' := (pad_spec hx).1.symm.trans ((congrArg (fun e : JetExp => e.weight gradeWeight) hxy).trans (pad_spec hy).1)
  subst q'
  have eK : k = k' := by
    change q < stop b k at hhi
    change q < stop b k' at hhi'
    change start k ≤ q at hlo
    change start k' ≤ q at hlo'
    simp only [stop, start] at hhi hhi' hlo hlo'
    omega
  subst k'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q-padGrade b k))
    exact hxy
  subst m'
  rfl

def block (b j t k : ℕ) : ℤ :=
  ((stop b k-start k : ℕ) : ℤ) * cappedCount (padGrade b k) (index j) t

def compute (b j t : ℕ) : ℤ := ∑ k ∈ range (chunks b), block b j t k

private theorem grid_eq (b j t : ℕ) : ((grid b j t).card : ℤ) = compute b j t := by
  unfold grid compute
  rw [card_sigma,Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  change (((Ico (start k) (stop b k)).product
    (cappedColumns (padGrade b k) (index j) t)).card : ℤ) = block b j t k
  have hcard := Finset.card_product (Ico (start k) (stop b k))
    (cappedColumns (padGrade b k) (index j) t)
  change ((Ico (start k) (stop b k)).product
    (cappedColumns (padGrade b k) (index j) t)).card = _ at hcard
  rw [hcard, Nat.card_Ico, Nat.cast_mul, capped_card K1_13_2_2_2.proof]
  rfl

theorem amb_ge (b j t : ℕ) : compute b j t ≤ (Gate61Box.ambCount b j t : ℤ) := by
  rw [← grid_eq]
  unfold Gate61Box.ambCount
  exact_mod_cast Finset.card_le_card_of_injOn (pad b) (fun _ h => map_mem h) (pad_injective b j t)

theorem amb_full (b j t : ℕ) (hb : 4012 ≤ b) (hj : 1650 ≤ j) (htt : 550 ≤ t) :
    Gate61Box.ambCount b j t = Low6960Prices.symbolCount := by
  unfold Gate61Box.ambCount
  have jc : jetColumns.card = Low6960Prices.symbolCount := by
    exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq
  rw [filter_true_of_mem, jc]
  intro m hm
  have h : m ∈ jetExponents := TaperColumns.jetExponents_finite.mem_toFinset.mp hm
  unfold Gate61Box.fitsBox
  have ht : 3 * m 3 ≤ m.weight oldWeight := by rw [sumOld]; omega
  exact ⟨h.1.trans hb, h.2.1.trans hj, by have hJ := h.2.1; omega⟩

theorem amb_le (b j t : ℕ) : Gate61Box.ambCount b j t ≤ Low6960Prices.symbolCount := by
  unfold Gate61Box.ambCount
  have jc : jetColumns.card = Low6960Prices.symbolCount := by
    exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq
  rw [← jc]
  exact Finset.card_filter_le _ _

end Gate61Amb

end Merged_Gate61Amb
