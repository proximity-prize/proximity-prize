import ProximityPrize.SubmissionLower.Final50SharedPrice
import ProximityPrize.SubmissionLower.PrimaryTaperColumnData

set_option Elab.async false
set_option autoImplicit false

namespace Final50ShapeGate

open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open TaperColumns (jetColumns jetExponents)
open TaperMoments (gradeCap)
open scoped BigOperators
open Finset
open private K1_13_2_2_3.cappedColumns K1_13_2_2_3.mem_cappedColumns K1_13_2_2_3.capped_card
  from ProximityPrize.SubmissionLower.Fast068
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open private sumGrade sumOld from ProximityPrize.SubmissionLower.PrimaryTaperColumns

def fits (r : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ r*60 ∧ m.weight oldWeight ≤ r*25 ∧ m 3 ≤ r*6

noncomputable instance (r : ℕ) (m : JetExp) : Decidable (fits r m) := by unfold fits; infer_instance

noncomputable def width (r : ℕ) : ℕ := (jetColumns.filter (fits r)).card

def bound (r : ℕ) : ℕ := min 4013 (r*60+1)
def start (k : ℕ) : ℕ := 64*k
def stop (r k : ℕ) : ℕ := min (bound r) (start (k+1))
def chunks (r : ℕ) : ℕ := (bound r + 63) / 64

def padGrade (r k : ℕ) : ℕ :=
  min (gradeCap (start k)) (gradeCap (stop r k-1))

def index (r : ℕ) : ℕ := min 1650 (r*25)

private theorem grade_le {r k q : ℕ} (hlo : start k ≤ q) (hhi : q < stop r k) :
    padGrade r k ≤ gradeCap q := by
  unfold padGrade gradeCap
  have hcap := TaperBudget.cap_antitone (show q ≤ stop r k-1 by omega)
  exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans hlo))
    ((min_le_right _ _).trans ((min_le_right _ _).trans hcap))

private noncomputable def grid (r : ℕ) : Finset (Σ _ : ℕ, ℕ × JetExp) :=
  (range (chunks r)).sigma fun k => (Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*6))

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
  have htop : m 3 ≤ r*6 := by exact_mod_cast ht
  have hD := (grade_le hl hh).trans (min_le_right _ _ : gradeCap q ≤ TaperBudget.cap q)
  have hb : q ≤ 4012 ∧ q ≤ r*60 := by
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
  ((stop r k-start k : ℕ) : ℤ) * cappedCount (padGrade r k) (index r) (r*6)

def compute (r : ℕ) : ℤ := ∑ k ∈ range (chunks r), block r k

private theorem grid_eq (r : ℕ) : ((grid r).card : ℤ) = compute r := by
  unfold grid compute
  rw [card_sigma,Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  change (((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*6))).card : ℤ) = block r k
  have hcard := Finset.card_product (Ico (start k) (stop r k))
    (cappedColumns (padGrade r k) (index r) (r*6))
  change ((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (r*6))).card = _ at hcard
  rw [hcard, Nat.card_Ico, Nat.cast_mul, capped_card K1_13_2_2_2.proof]
  rfl

theorem width_ge (r : ℕ) : compute r ≤ (width r : ℤ) := by
  rw [← grid_eq]
  exact_mod_cast Finset.card_le_card_of_injOn (pad r) (fun _ h => map_mem h) (pad_injective r)

private theorem jet_count : jetColumns.card = Final50Price.symbolCount := by
  exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq

private theorem width_le (r : ℕ) : width r ≤ Final50Price.symbolCount := by
  rw [← jet_count]
  exact card_le_card (filter_subset _ _)

private theorem width_full (r : ℕ) (hr : 92 ≤ r) : width r = Final50Price.symbolCount := by
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

def rowLoss (i : ℕ) : ℤ := (Final50Price.symbolCount : ℤ) - fastRow (i+1)

private theorem intPrefix_add (f : ℕ → ℤ) (a b : ℕ) :
    intPrefix f (a+b) = intPrefix f a + intPrefix (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [intPrefix]
  | succ b ih => rw [Nat.add_succ, intPrefix, ih, intPrefix, add_assoc]

private theorem part0 : intPrefix (fun i => rowLoss (0+i)) 7 = 2847561416346 := by decide +kernel

private theorem part7 : intPrefix (fun i => rowLoss (7+i)) 7 = 2845169148870 := by decide +kernel

private theorem part14 : intPrefix (fun i => rowLoss (14+i)) 7 = 2831592953132 := by decide +kernel

private theorem part21 : intPrefix (fun i => rowLoss (21+i)) 7 = 2789695783148 := by decide +kernel

private theorem part28 : intPrefix (fun i => rowLoss (28+i)) 7 = 2694035513036 := by decide +kernel

private theorem part35 : intPrefix (fun i => rowLoss (35+i)) 7 = 2510867945576 := by decide +kernel

private theorem part42 : intPrefix (fun i => rowLoss (42+i)) 7 = 2198146136942 := by decide +kernel

private theorem part49 : intPrefix (fun i => rowLoss (49+i)) 7 = 1705518666002 := by decide +kernel

private theorem part56 : intPrefix (fun i => rowLoss (56+i)) 7 = 974496625064 := by decide +kernel

private theorem part63 : intPrefix (fun i => rowLoss (63+i)) 7 = 169003912251 := by decide +kernel

private theorem part70 : intPrefix (fun i => rowLoss (70+i)) 7 = 53197576283 := by decide +kernel

private theorem part77 : intPrefix (fun i => rowLoss (77+i)) 7 = 36300626368 := by decide +kernel

private theorem part84 : intPrefix (fun i => rowLoss (84+i)) 7 = 31448894158 := by decide +kernel

set_option maxRecDepth 10000 in
theorem computed_loss : intPrefix rowLoss 91 = Final50SharedPrice.slopeLoss := by
  have h0 : intPrefix rowLoss 0 = 0 := rfl
  have h7 : intPrefix rowLoss 7 = 2847561416346 := by
    rw [show (7 : ℕ) = 0+7 by decide,intPrefix_add,h0,part0]
    rfl
  have h14 : intPrefix rowLoss 14 = 5692730565216 := by
    rw [show (14 : ℕ) = 7+7 by decide,intPrefix_add,h7,part7]
    rfl
  have h21 : intPrefix rowLoss 21 = 8524323518348 := by
    rw [show (21 : ℕ) = 14+7 by decide,intPrefix_add,h14,part14]
    rfl
  have h28 : intPrefix rowLoss 28 = 11314019301496 := by
    rw [show (28 : ℕ) = 21+7 by decide,intPrefix_add,h21,part21]
    rfl
  have h35 : intPrefix rowLoss 35 = 14008054814532 := by
    rw [show (35 : ℕ) = 28+7 by decide,intPrefix_add,h28,part28]
    rfl
  have h42 : intPrefix rowLoss 42 = 16518922760108 := by
    rw [show (42 : ℕ) = 35+7 by decide,intPrefix_add,h35,part35]
    rfl
  have h49 : intPrefix rowLoss 49 = 18717068897050 := by
    rw [show (49 : ℕ) = 42+7 by decide,intPrefix_add,h42,part42]
    rfl
  have h56 : intPrefix rowLoss 56 = 20422587563052 := by
    rw [show (56 : ℕ) = 49+7 by decide,intPrefix_add,h49,part49]
    rfl
  have h63 : intPrefix rowLoss 63 = 21397084188116 := by
    rw [show (63 : ℕ) = 56+7 by decide,intPrefix_add,h56,part56]
    rfl
  have h70 : intPrefix rowLoss 70 = 21566088100367 := by
    rw [show (70 : ℕ) = 63+7 by decide,intPrefix_add,h63,part63]
    rfl
  have h77 : intPrefix rowLoss 77 = 21619285676650 := by
    rw [show (77 : ℕ) = 70+7 by decide,intPrefix_add,h70,part70]
    rfl
  have h84 : intPrefix rowLoss 84 = 21655586303018 := by
    rw [show (84 : ℕ) = 77+7 by decide,intPrefix_add,h77,part77]
    rfl
  have h91 : intPrefix rowLoss 91 = 21687035197176 := by
    rw [show (91 : ℕ) = 84+7 by decide,intPrefix_add,h84,part84]
    rfl
  exact h91


theorem loss_bound (N : ℕ) :
    (∑ i ∈ range N, (Final50Price.symbolCount - width (i+1))) ≤ Final50SharedPrice.slopeLoss := by
  let f : ℕ → ℕ := fun i => Final50Price.symbolCount - width (i+1)
  change (∑ i ∈ range N, f i) ≤ _
  have hzero (i : ℕ) (hi : 91 ≤ i) : f i = 0 := by
    dsimp [f]
    rw [width_full (i+1) (by omega),Nat.sub_self]
  rw [K1_13_8.sum_range_min N 91 hzero]
  refine (sum_le_sum_of_subset (range_mono (min_le_right N 91))).trans ?_
  have row (i : ℕ) : (f i : ℤ) ≤ rowLoss i := by
    unfold f rowLoss
    rw [Int.ofNat_sub (width_le _),fastRow_eq]
    exact sub_le_sub_left (width_ge (i+1)) _
  apply Int.ofNat_le.mp
  rw [Nat.cast_sum, ← computed_loss, intPrefix_eq]
  exact sum_le_sum fun i _ => row i

#print axioms loss_bound

end Final50ShapeGate
