import ProximityPrize.SubmissionLower.Final50SharedPrice
import ProximityPrize.SubmissionLower.PrimaryTaperColumnData
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase -- serialize candidate build

set_option autoImplicit false

namespace Final50ShapeGate

open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open TaperColumns (jetColumns jetExponents)
open TaperMoments (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open private sumGrade sumOld from ProximityPrize.SubmissionLower.PrimaryTaperColumns

def fits (r : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ r*61 ∧ m.weight oldWeight ≤ r*24 ∧ m 3 ≤ r*7

noncomputable instance (r : ℕ) (m : JetExp) : Decidable (fits r m) := by unfold fits; infer_instance

noncomputable def width (r : ℕ) : ℕ := (jetColumns.filter (fits r)).card

def bound (r : ℕ) : ℕ := min 4013 (r*61+1)
def start (k : ℕ) : ℕ := 4*k
def stop (r k : ℕ) : ℕ := min (bound r) (start (k+1))
def chunks (r : ℕ) : ℕ := (bound r + 3) / 4

def padGrade (r k : ℕ) : ℕ :=
  min (gradeCap (start k)) (gradeCap (stop r k-1))

def index (r : ℕ) : ℕ := min 1650 (r*24)

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

theorem pad_spec {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
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

theorem map_mem {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
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
  have hb : q ≤ 4012 ∧ q ≤ r*61 := by
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

theorem grid_eq (r : ℕ) : ((grid r).card : ℤ) = compute r := by
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

private theorem jet_count : jetColumns.card = Final50Price.symbolCount := by
  exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq

theorem width_le (r : ℕ) : width r ≤ Final50Price.symbolCount := by
  rw [← jet_count]
  exact card_le_card (filter_subset _ _)

theorem width_full (r : ℕ) (hr : 79 ≤ r) : width r = Final50Price.symbolCount := by
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

theorem intPrefix_add (f : ℕ → ℤ) (a b : ℕ) :
    intPrefix f (a+b) = intPrefix f a + intPrefix (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [intPrefix]
  | succ b ih => rw [Nat.add_succ, intPrefix, ih, intPrefix, add_assoc]

private theorem part0 : intPrefix (fun i => rowLoss (0+i)) 3 = 1220420898039 := by decide +kernel

private theorem part3 : intPrefix (fun i => rowLoss (3+i)) 3 = 1220377992214 := by decide +kernel

private theorem part6 : intPrefix (fun i => rowLoss (6+i)) 3 = 1220159780418 := by decide +kernel

theorem part9 : intPrefix (fun i => rowLoss (9+i)) 3 = 1219520189847 := by decide +kernel

theorem part12 : intPrefix (fun i => rowLoss (12+i)) 3 = 1218101403920 := by decide +kernel

theorem part15 : intPrefix (fun i => rowLoss (15+i)) 3 = 1215433861274 := by decide +kernel

theorem part18 : intPrefix (fun i => rowLoss (18+i)) 3 = 1210936257027 := by decide +kernel

theorem part21 : intPrefix (fun i => rowLoss (21+i)) 3 = 1203915541221 := by decide +kernel

theorem part24 : intPrefix (fun i => rowLoss (24+i)) 3 = 1193566920717 := by decide +kernel

theorem part27 : intPrefix (fun i => rowLoss (27+i)) 3 = 1178973856930 := by decide +kernel

theorem part30 : intPrefix (fun i => rowLoss (30+i)) 3 = 1159108068468 := by decide +kernel

theorem part33 : intPrefix (fun i => rowLoss (33+i)) 3 = 1132829528151 := by decide +kernel

theorem part36 : intPrefix (fun i => rowLoss (36+i)) 3 = 1098886466282 := by decide +kernel

theorem part39 : intPrefix (fun i => rowLoss (39+i)) 3 = 1055915367122 := by decide +kernel

theorem part42 : intPrefix (fun i => rowLoss (42+i)) 3 = 1002440972673 := by decide +kernel

theorem part45 : intPrefix (fun i => rowLoss (45+i)) 3 = 936876278601 := by decide +kernel

private theorem part48 : intPrefix (fun i => rowLoss (48+i)) 3 = 857522538651 := by decide +kernel

theorem part51 : intPrefix (fun i => rowLoss (51+i)) 3 = 762569259862 := by decide +kernel

theorem part54 : intPrefix (fun i => rowLoss (54+i)) 3 = 650094207726 := by decide +kernel

theorem part57 : intPrefix (fun i => rowLoss (57+i)) 3 = 518063400687 := by decide +kernel

theorem part60 : intPrefix (fun i => rowLoss (60+i)) 3 = 364442005867 := by decide +kernel

theorem part63 : intPrefix (fun i => rowLoss (63+i)) 3 = 190538249674 := by decide +kernel

theorem part66 : intPrefix (fun i => rowLoss (66+i)) 3 = 42516881189 := by decide +kernel

theorem part69 : intPrefix (fun i => rowLoss (69+i)) 3 = 1838782459 := by decide +kernel

theorem part72 : intPrefix (fun i => rowLoss (72+i)) 3 = 917601919 := by decide +kernel

theorem part75 : intPrefix (fun i => rowLoss (75+i)) 3 = 654282687 := by decide +kernel

set_option maxRecDepth 10000 in
theorem computed_loss : intPrefix rowLoss 78 = Final50SharedPrice.slopeLoss := by
  have h0 : intPrefix rowLoss 0 = 0 := rfl
  have h3 : intPrefix rowLoss 3 = 1220420898039 := by
    rw [show (3 : ℕ) = 0+3 by decide,intPrefix_add,h0,part0]
    rfl
  have h6 : intPrefix rowLoss 6 = 2440798890253 := by
    rw [show (6 : ℕ) = 3+3 by decide,intPrefix_add,h3,part3]
    rfl
  have h9 : intPrefix rowLoss 9 = 3660958670671 := by
    rw [show (9 : ℕ) = 6+3 by decide,intPrefix_add,h6,part6]
    rfl
  have h12 : intPrefix rowLoss 12 = 4880478860518 := by
    rw [show (12 : ℕ) = 9+3 by decide,intPrefix_add,h9,part9]
    rfl
  have h15 : intPrefix rowLoss 15 = 6098580264438 := by
    rw [show (15 : ℕ) = 12+3 by decide,intPrefix_add,h12,part12]
    rfl
  have h18 : intPrefix rowLoss 18 = 7314014125712 := by
    rw [show (18 : ℕ) = 15+3 by decide,intPrefix_add,h15,part15]
    rfl
  have h21 : intPrefix rowLoss 21 = 8524950382739 := by
    rw [show (21 : ℕ) = 18+3 by decide,intPrefix_add,h18,part18]
    rfl
  have h24 : intPrefix rowLoss 24 = 9728865923960 := by
    rw [show (24 : ℕ) = 21+3 by decide,intPrefix_add,h21,part21]
    rfl
  have h27 : intPrefix rowLoss 27 = 10922432844677 := by
    rw [show (27 : ℕ) = 24+3 by decide,intPrefix_add,h24,part24]
    rfl
  have h30 : intPrefix rowLoss 30 = 12101406701607 := by
    rw [show (30 : ℕ) = 27+3 by decide,intPrefix_add,h27,part27]
    rfl
  have h33 : intPrefix rowLoss 33 = 13260514770075 := by
    rw [show (33 : ℕ) = 30+3 by decide,intPrefix_add,h30,part30]
    rfl
  have h36 : intPrefix rowLoss 36 = 14393344298226 := by
    rw [show (36 : ℕ) = 33+3 by decide,intPrefix_add,h33,part33]
    rfl
  have h39 : intPrefix rowLoss 39 = 15492230764508 := by
    rw [show (39 : ℕ) = 36+3 by decide,intPrefix_add,h36,part36]
    rfl
  have h42 : intPrefix rowLoss 42 = 16548146131630 := by
    rw [show (42 : ℕ) = 39+3 by decide,intPrefix_add,h39,part39]
    rfl
  have h45 : intPrefix rowLoss 45 = 17550587104303 := by
    rw [show (45 : ℕ) = 42+3 by decide,intPrefix_add,h42,part42]
    rfl
  have h48 : intPrefix rowLoss 48 = 18487463382904 := by
    rw [show (48 : ℕ) = 45+3 by decide,intPrefix_add,h45,part45]
    rfl
  have h51 : intPrefix rowLoss 51 = 19344985921555 := by
    rw [show (51 : ℕ) = 48+3 by decide,intPrefix_add,h48,part48]
    rfl
  have h54 : intPrefix rowLoss 54 = 20107555181417 := by
    rw [show (54 : ℕ) = 51+3 by decide,intPrefix_add,h51,part51]
    rfl
  have h57 : intPrefix rowLoss 57 = 20757649389143 := by
    rw [show (57 : ℕ) = 54+3 by decide,intPrefix_add,h54,part54]
    rfl
  have h60 : intPrefix rowLoss 60 = 21275712789830 := by
    rw [show (60 : ℕ) = 57+3 by decide,intPrefix_add,h57,part57]
    rfl
  have h63 : intPrefix rowLoss 63 = 21640154795697 := by
    rw [show (63 : ℕ) = 60+3 by decide,intPrefix_add,h60,part60]
    rfl
  have h66 : intPrefix rowLoss 66 = 21830693045371 := by
    rw [show (66 : ℕ) = 63+3 by decide,intPrefix_add,h63,part63]
    rfl
  have h69 : intPrefix rowLoss 69 = 21873209926560 := by
    rw [show (69 : ℕ) = 66+3 by decide,intPrefix_add,h66,part66]
    rfl
  have h72 : intPrefix rowLoss 72 = 21875048709019 := by
    rw [show (72 : ℕ) = 69+3 by decide,intPrefix_add,h69,part69]
    rfl
  have h75 : intPrefix rowLoss 75 = 21875966310938 := by
    rw [show (75 : ℕ) = 72+3 by decide,intPrefix_add,h72,part72]
    rfl
  have h78 : intPrefix rowLoss 78 = 21876620593625 := by
    rw [show (78 : ℕ) = 75+3 by decide,intPrefix_add,h75,part75]
    rfl
  exact h78

theorem loss_bound (N : ℕ) :
    (∑ i ∈ range N, (Final50Price.symbolCount - width (i+1))) ≤ Final50SharedPrice.slopeLoss := by
  let f : ℕ → ℕ := fun i => Final50Price.symbolCount - width (i+1)
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


end Final50ShapeGate
