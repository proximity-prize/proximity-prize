import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily

set_option Elab.async false
set_option autoImplicit false

namespace Low6960ShapeGate

open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open TaperColumns (jetColumns jetExponents)
open TaperMoments (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open TaperColumns (sumGrade sumOld)

def fits (r : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ r*62 ∧ m.weight oldWeight ≤ r*26 ∧ m 3 ≤ r*7

noncomputable instance (r : ℕ) (m : JetExp) : Decidable (fits r m) := by unfold fits; infer_instance

noncomputable def width (r : ℕ) : ℕ := (jetColumns.filter (fits r)).card

def bound (r : ℕ) : ℕ := min 4013 (r*62+1)
def start (k : ℕ) : ℕ := 16*k
def stop (r k : ℕ) : ℕ := min (bound r) (start (k+1))
def chunks (r : ℕ) : ℕ := (bound r + 15) / 16

def padGrade (r k : ℕ) : ℕ :=
  min (gradeCap (start k)) (gradeCap (stop r k-1))

def index (r : ℕ) : ℕ := min 1650 (r*26)

private theorem grade_le {r k q : ℕ} (hlo : start k ≤ q) (hhi : q < stop r k) :
    padGrade r k ≤ gradeCap q := by
  unfold padGrade gradeCap
  have hcap := TaperBudget.cap_antitone (show q ≤ stop r k-1 by omega)
  exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans hlo))
    ((min_le_right _ _).trans ((min_le_right _ _).trans hcap))

private noncomputable def grid (r : ℕ) : Finset (Σ _ : ℕ, ℕ × JetExp) :=
  (range (chunks r)).sigma fun k => (Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*7))

private noncomputable def pad (r : ℕ) (x : Σ _ : ℕ, ℕ × JetExp) : JetExp :=
  x.2.2 + Finsupp.single 0 (x.2.1 - padGrade r x.1)

private theorem pad_spec {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
    (pad r x).weight gradeWeight = x.2.1 ∧
    (pad r x).weight oldWeight = x.2.2.weight oldWeight ∧
    (∀ i : Fin 4, i ≠ 0 → pad r x i = x.2.2 i) := by
  obtain ⟨k,q,m⟩ := x
  have hm := (mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2).1
  have hm' := (mem_cumulativeColumns.mp hm).1
  have hg : m.weight gradeWeight = padGrade r k := by exact_mod_cast hm'
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  change start k ≤ q at hl
  change q < stop r k at hh
  have hq := (grade_le hl hh).trans (min_le_left _ _ : gradeCap q ≤ q)
  have h0 : pad r ⟨k,q,m⟩ 0 = m 0 + (q-padGrade r k) := by simp [pad]
  have hsucc (i : Fin 4) (hi : i ≠ 0) : pad r ⟨k,q,m⟩ i = m i := by
    simp [pad,Finsupp.single_eq_of_ne hi]
  refine ⟨?_, ?_, hsucc⟩
  · change (pad r ⟨k,q,m⟩).weight gradeWeight = q
    rw [sumGrade, h0, hsucc 1 (by decide), hsucc 2 (by decide), hsucc 3 (by decide)]
    rw [sumGrade] at hg
    omega
  · rw [sumOld,sumOld,hsucc 1 (by decide),hsucc 2 (by decide),hsucc 3 (by decide)]

private theorem map_mem {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
    pad r x ∈ jetColumns.filter (fits r) := by
  obtain ⟨k,q,m⟩ := x
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hj,ht⟩ := mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2
  obtain ⟨hg,hi⟩ := mem_cumulativeColumns.mp hj
  obtain ⟨eB,eJ,eOther⟩ := pad_spec hx
  dsimp only at eB eJ eOther hl hh
  have hgrade : m.weight gradeWeight = padGrade r k := by exact_mod_cast hg
  have hindex : m.weight oldWeight ≤ index r := by exact_mod_cast hi
  have htop : m 3 ≤ r*7 := by exact_mod_cast ht
  have hD := (grade_le hl hh).trans (min_le_right _ _ : gradeCap q ≤ TaperBudget.cap q)
  have hb : q ≤ 4012 ∧ q ≤ r*62 := by
    unfold stop bound at hh
    omega
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨eB.trans_le hb.2,eJ.trans_le (hindex.trans (min_le_right _ _)),?_⟩⟩
  · apply TaperColumns.jetExponents_finite.mem_toFinset.mpr
    change (pad r ⟨k,q,m⟩).weight gradeWeight ≤ 4012 ∧
      (pad r ⟨k,q,m⟩).weight oldWeight ≤ 1650 ∧ _
    refine ⟨eB.trans_le hb.1,eJ.trans_le (hindex.trans (min_le_left _ _)),?_⟩
    rw [eB,eOther 1 (by decide),eOther 2 (by decide),eOther 3 (by decide)]
    rw [sumGrade] at hgrade
    omega
  · rwa [eOther 3 (by decide)]

private theorem pad_injective (r : ℕ) : Set.InjOn (pad r) (grid r : Set (Σ _ : ℕ, ℕ × JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨k,q,m⟩ := x
  obtain ⟨k',q',m'⟩ := y
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hlo',hhi'⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hy).2).1
  have eQ : q = q' := (pad_spec hx).1.symm.trans ((congrArg (fun e : JetExp => e.weight gradeWeight) hxy).trans (pad_spec hy).1)
  subst q'
  have eK : k = k' := by
    change q < stop r k at hhi
    change q < stop r k' at hhi'
    change start k ≤ q at hlo
    change start k' ≤ q at hlo'
    simp only [stop, start] at hhi hhi' hlo hlo'
    omega
  subst k'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q-padGrade r k))
    exact hxy
  subst m'
  rfl

def block (r k : ℕ) : ℤ :=
  ((stop r k-start k : ℕ) : ℤ) * cappedCount (padGrade r k) (index r) (r*7)

def compute (r : ℕ) : ℤ := ∑ k ∈ range (chunks r), block r k

private theorem grid_eq (r : ℕ) : ((grid r).card : ℤ) = compute r := by
  unfold grid compute
  rw [card_sigma,Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  change (((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*7))).card : ℤ) = block r k
  have hcard := Finset.card_product (Ico (start k) (stop r k))
    (cappedColumns (padGrade r k) (index r) (r*7))
  change ((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*7))).card = _ at hcard
  rw [hcard, Nat.card_Ico, Nat.cast_mul, capped_card K1_13_2_2_2.proof]
  rfl

theorem width_ge (r : ℕ) : compute r ≤ (width r : ℤ) := by
  rw [← grid_eq]
  exact_mod_cast Finset.card_le_card_of_injOn (pad r) (fun _ h => map_mem h) (pad_injective r)

private theorem jet_count : jetColumns.card = Low6960Prices.symbolCount := by
  exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq

private theorem width_le (r : ℕ) : width r ≤ Low6960Prices.symbolCount := by
  rw [← jet_count]
  exact card_le_card (filter_subset _ _)

private theorem width_full (r : ℕ) (hr : 79 ≤ r) : width r = Low6960Prices.symbolCount := by
  unfold width
  rw [filter_true_of_mem, jet_count]
  intro m hm
  have h : m ∈ jetExponents := TaperColumns.jetExponents_finite.mem_toFinset.mp hm
  unfold fits
  have ht : 3*m 3 ≤ m.weight oldWeight := by rw [sumOld]; omega
  exact ⟨h.1.trans (by omega), h.2.1.trans (by omega), by have hJ := h.2.1; omega⟩

def intPrefix (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => intPrefix f n + f n

theorem intPrefix_eq (f : ℕ → ℤ) (n : ℕ) :
    intPrefix f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [intPrefix]
  | succ n ih => rw [intPrefix,sum_range_succ,ih]

def fastRow (r : ℕ) : ℤ := intPrefix (block r) (chunks r)

theorem fastRow_eq (r : ℕ) : fastRow r = compute r := intPrefix_eq _ _

def rowLoss (i : ℕ) : ℤ := (Low6960Prices.symbolCount : ℤ) - fastRow (i+1)

private theorem intPrefix_add (f : ℕ → ℤ) (a b : ℕ) :
    intPrefix f (a+b) = intPrefix f a + intPrefix (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [intPrefix]
  | succ b ih => rw [Nat.add_succ, intPrefix, ih, intPrefix, add_assoc]

private theorem part0 : intPrefix (fun k => rowLoss (0+k)) 7 = 2847535206290 := by decide +kernel

private theorem part7 : intPrefix (fun k => rowLoss (7+k)) 7 = 2844600842885 := by decide +kernel

private theorem part14 : intPrefix (fun k => rowLoss (14+k)) 7 = 2828214672008 := by decide +kernel

private theorem part21 : intPrefix (fun k => rowLoss (21+k)) 7 = 2778003636968 := by decide +kernel

private theorem part28 : intPrefix (fun k => rowLoss (28+k)) 7 = 2663805428571 := by decide +kernel

private theorem part35 : intPrefix (fun k => rowLoss (35+k)) 7 = 2445668485908 := by decide +kernel

private theorem part42 : intPrefix (fun k => rowLoss (42+k)) 7 = 2073852004051 := by decide +kernel

private theorem part49 : intPrefix (fun k => rowLoss (49+k)) 7 = 1488825924177 := by decide +kernel

private theorem part56 : intPrefix (fun k => rowLoss (56+k)) 7 = 622658340704 := by decide +kernel

private theorem part63 : intPrefix (fun k => rowLoss (63+k)) 7 = 22729886625 := by decide +kernel

private theorem part70 : intPrefix (fun k => rowLoss (70+k)) 7 = 8349761869 := by decide +kernel

private theorem part77 : intPrefix (fun k => rowLoss (77+k)) 1 = 1058415011 := by decide +kernel

set_option maxRecDepth 10000 in
theorem computed_loss : intPrefix rowLoss 78 = Low6960SharedPrice.slopeLoss := by
  have h0 : intPrefix rowLoss 0 = 0 := rfl
  have h7 : intPrefix rowLoss 7 = 2847535206290 := by
    rw [show (7 : ℕ) = 0+7 by decide,intPrefix_add,h0,part0]
    rfl
  have h14 : intPrefix rowLoss 14 = 5692136049175 := by
    rw [show (14 : ℕ) = 7+7 by decide,intPrefix_add,h7,part7]
    rfl
  have h21 : intPrefix rowLoss 21 = 8520350721183 := by
    rw [show (21 : ℕ) = 14+7 by decide,intPrefix_add,h14,part14]
    rfl
  have h28 : intPrefix rowLoss 28 = 11298354358151 := by
    rw [show (28 : ℕ) = 21+7 by decide,intPrefix_add,h21,part21]
    rfl
  have h35 : intPrefix rowLoss 35 = 13962159786722 := by
    rw [show (35 : ℕ) = 28+7 by decide,intPrefix_add,h28,part28]
    rfl
  have h42 : intPrefix rowLoss 42 = 16407828272630 := by
    rw [show (42 : ℕ) = 35+7 by decide,intPrefix_add,h35,part35]
    rfl
  have h49 : intPrefix rowLoss 49 = 18481680276681 := by
    rw [show (49 : ℕ) = 42+7 by decide,intPrefix_add,h42,part42]
    rfl
  have h56 : intPrefix rowLoss 56 = 19970506200858 := by
    rw [show (56 : ℕ) = 49+7 by decide,intPrefix_add,h49,part49]
    rfl
  have h63 : intPrefix rowLoss 63 = 20593164541562 := by
    rw [show (63 : ℕ) = 56+7 by decide,intPrefix_add,h56,part56]
    rfl
  have h70 : intPrefix rowLoss 70 = 20615894428187 := by
    rw [show (70 : ℕ) = 63+7 by decide,intPrefix_add,h63,part63]
    rfl
  have h77 : intPrefix rowLoss 77 = 20624244190056 := by
    rw [show (77 : ℕ) = 70+7 by decide,intPrefix_add,h70,part70]
    rfl
  have h78 : intPrefix rowLoss 78 = 20625302605067 := by
    rw [show (78 : ℕ) = 77+1 by decide,intPrefix_add,h77,part77]
    rfl
  exact h78

theorem loss_bound (N : ℕ) :
    (∑ i ∈ range N, (Low6960Prices.symbolCount - width (i+1))) ≤ Low6960SharedPrice.slopeLoss := by
  let f : ℕ → ℕ := fun i => Low6960Prices.symbolCount - width (i+1)
  change (∑ i ∈ range N, f i) ≤ _
  have hzero (i : ℕ) (hi : 78 ≤ i) : f i = 0 := by
    dsimp [f]
    rw [width_full (i+1) (by omega),Nat.sub_self]
  rw [K1_13_8.sum_range_min N 78 hzero]
  refine (sum_le_sum_of_subset (range_mono (min_le_right N 78))).trans ?_
  have row (i : ℕ) : (f i : ℤ) ≤ rowLoss i := by
    unfold f rowLoss
    rw [Int.ofNat_sub (width_le _),fastRow_eq]
    exact sub_le_sub_left (width_ge (i+1)) _
  apply Int.ofNat_le.mp
  rw [Nat.cast_sum, ← computed_loss, intPrefix_eq]
  exact sum_le_sum fun i _ => row i

#print axioms loss_bound

end Low6960ShapeGate
