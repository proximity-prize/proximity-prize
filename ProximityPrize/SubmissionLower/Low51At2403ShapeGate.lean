import ProximityPrize.SubmissionLower.PrimaryTaperColumnData

set_option Elab.async false
set_option autoImplicit false

namespace Low51At2403ShapeGate

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

abbrev symbolCount : ℕ := 406807694511
abbrev slopeLoss : ℕ := 21489377150447

def fits (r : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ r*61 ∧ m.weight oldWeight ≤ r*25 ∧ m 3 ≤ r*6

noncomputable instance (r : ℕ) (m : JetExp) : Decidable (fits r m) := by unfold fits; infer_instance

noncomputable def width (r : ℕ) : ℕ := (jetColumns.filter (fits r)).card

def bound (r : ℕ) : ℕ := min 4013 (r*61+1)
def start (k : ℕ) : ℕ := 32*k
def stop (r k : ℕ) : ℕ := min (bound r) (start (k+1))
def chunks (r : ℕ) : ℕ := (bound r + 31) / 32

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

private theorem jet_count : jetColumns.card = symbolCount := by
  exact_mod_cast TaperColumns.jet_card_eq.trans TaperColumns.sourceCount_eq

private theorem width_le (r : ℕ) : width r ≤ symbolCount := by
  rw [← jet_count]
  exact card_le_card (filter_subset _ _)

private theorem width_full (r : ℕ) (hr : 92 ≤ r) : width r = symbolCount := by
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

def rowLoss (i : ℕ) : ℤ := (symbolCount : ℤ) - fastRow (i+1)

private theorem intPrefix_add (f : ℕ → ℤ) (a b : ℕ) :
    intPrefix f (a+b) = intPrefix f a + intPrefix (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [intPrefix]
  | succ b ih => rw [Nat.add_succ, intPrefix, ih, intPrefix, add_assoc]

private theorem part0 : intPrefix (fun i => rowLoss (0+i)) 4 = 1627223115000 := by decide +kernel

private theorem part4 : intPrefix (fun i => rowLoss (4+i)) 4 = 1627050917408 := by decide +kernel

private theorem part8 : intPrefix (fun i => rowLoss (8+i)) 4 = 1626127242104 := by decide +kernel

private theorem part12 : intPrefix (fun i => rowLoss (12+i)) 4 = 1623350691360 := by decide +kernel

private theorem part16 : intPrefix (fun i => rowLoss (16+i)) 4 = 1617103621816 := by decide +kernel

private theorem part20 : intPrefix (fun i => rowLoss (20+i)) 4 = 1605252027456 := by decide +kernel

private theorem part24 : intPrefix (fun i => rowLoss (24+i)) 4 = 1585145597368 := by decide +kernel

private theorem part28 : intPrefix (fun i => rowLoss (28+i)) 4 = 1553617727104 := by decide +kernel

private theorem part32 : intPrefix (fun i => rowLoss (32+i)) 4 = 1506985453240 := by decide +kernel

private theorem part36 : intPrefix (fun i => rowLoss (36+i)) 4 = 1441049552640 := by decide +kernel

private theorem part40 : intPrefix (fun i => rowLoss (40+i)) 4 = 1351094399768 := by decide +kernel

private theorem part44 : intPrefix (fun i => rowLoss (44+i)) 4 = 1231888138240 := by decide +kernel

private theorem part48 : intPrefix (fun i => rowLoss (48+i)) 4 = 1077682536248 := by decide +kernel

private theorem part52 : intPrefix (fun i => rowLoss (52+i)) 4 = 882213091072 := by decide +kernel

private theorem part56 : intPrefix (fun i => rowLoss (56+i)) 4 = 638699339454 := by decide +kernel

private theorem part60 : intPrefix (fun i => rowLoss (60+i)) 4 = 340848405424 := by decide +kernel

private theorem part64 : intPrefix (fun i => rowLoss (64+i)) 4 = 63905616051 := by decide +kernel

private theorem part68 : intPrefix (fun i => rowLoss (68+i)) 4 = 29888568126 := by decide +kernel

private theorem part72 : intPrefix (fun i => rowLoss (72+i)) 4 = 20110189742 := by decide +kernel

private theorem part76 : intPrefix (fun i => rowLoss (76+i)) 4 = 13935857438 := by decide +kernel

private theorem part80 : intPrefix (fun i => rowLoss (80+i)) 4 = 10541721678 := by decide +kernel

private theorem part84 : intPrefix (fun i => rowLoss (84+i)) 4 = 9094822398 := by decide +kernel

private theorem part88 : intPrefix (fun i => rowLoss (88+i)) 3 = 6568519312 := by decide +kernel

theorem computed_loss : intPrefix rowLoss 91 = slopeLoss := by
  have h0 : intPrefix rowLoss 0 = 0 := rfl
  have h4 : intPrefix rowLoss 4 = 1627223115000 := by
    rw [show (4 : ℕ) = 0+4 by decide,intPrefix_add,h0,part0]
    rfl
  have h8 : intPrefix rowLoss 8 = 3254274032408 := by
    rw [show (8 : ℕ) = 4+4 by decide,intPrefix_add,h4,part4]
    rfl
  have h12 : intPrefix rowLoss 12 = 4880401274512 := by
    rw [show (12 : ℕ) = 8+4 by decide,intPrefix_add,h8,part8]
    rfl
  have h16 : intPrefix rowLoss 16 = 6503751965872 := by
    rw [show (16 : ℕ) = 12+4 by decide,intPrefix_add,h12,part12]
    rfl
  have h20 : intPrefix rowLoss 20 = 8120855587688 := by
    rw [show (20 : ℕ) = 16+4 by decide,intPrefix_add,h16,part16]
    rfl
  have h24 : intPrefix rowLoss 24 = 9726107615144 := by
    rw [show (24 : ℕ) = 20+4 by decide,intPrefix_add,h20,part20]
    rfl
  have h28 : intPrefix rowLoss 28 = 11311253212512 := by
    rw [show (28 : ℕ) = 24+4 by decide,intPrefix_add,h24,part24]
    rfl
  have h32 : intPrefix rowLoss 32 = 12864870939616 := by
    rw [show (32 : ℕ) = 28+4 by decide,intPrefix_add,h28,part28]
    rfl
  have h36 : intPrefix rowLoss 36 = 14371856392856 := by
    rw [show (36 : ℕ) = 32+4 by decide,intPrefix_add,h32,part32]
    rfl
  have h40 : intPrefix rowLoss 40 = 15812905945496 := by
    rw [show (40 : ℕ) = 36+4 by decide,intPrefix_add,h36,part36]
    rfl
  have h44 : intPrefix rowLoss 44 = 17164000345264 := by
    rw [show (44 : ℕ) = 40+4 by decide,intPrefix_add,h40,part40]
    rfl
  have h48 : intPrefix rowLoss 48 = 18395888483504 := by
    rw [show (48 : ℕ) = 44+4 by decide,intPrefix_add,h44,part44]
    rfl
  have h52 : intPrefix rowLoss 52 = 19473571019752 := by
    rw [show (52 : ℕ) = 48+4 by decide,intPrefix_add,h48,part48]
    rfl
  have h56 : intPrefix rowLoss 56 = 20355784110824 := by
    rw [show (56 : ℕ) = 52+4 by decide,intPrefix_add,h52,part52]
    rfl
  have h60 : intPrefix rowLoss 60 = 20994483450278 := by
    rw [show (60 : ℕ) = 56+4 by decide,intPrefix_add,h56,part56]
    rfl
  have h64 : intPrefix rowLoss 64 = 21335331855702 := by
    rw [show (64 : ℕ) = 60+4 by decide,intPrefix_add,h60,part60]
    rfl
  have h68 : intPrefix rowLoss 68 = 21399237471753 := by
    rw [show (68 : ℕ) = 64+4 by decide,intPrefix_add,h64,part64]
    rfl
  have h72 : intPrefix rowLoss 72 = 21429126039879 := by
    rw [show (72 : ℕ) = 68+4 by decide,intPrefix_add,h68,part68]
    rfl
  have h76 : intPrefix rowLoss 76 = 21449236229621 := by
    rw [show (76 : ℕ) = 72+4 by decide,intPrefix_add,h72,part72]
    rfl
  have h80 : intPrefix rowLoss 80 = 21463172087059 := by
    rw [show (80 : ℕ) = 76+4 by decide,intPrefix_add,h76,part76]
    rfl
  have h84 : intPrefix rowLoss 84 = 21473713808737 := by
    rw [show (84 : ℕ) = 80+4 by decide,intPrefix_add,h80,part80]
    rfl
  have h88 : intPrefix rowLoss 88 = 21482808631135 := by
    rw [show (88 : ℕ) = 84+4 by decide,intPrefix_add,h84,part84]
    rfl
  have h91 : intPrefix rowLoss 91 = 21489377150447 := by
    rw [show (91 : ℕ) = 88+3 by decide,intPrefix_add,h88,part88]
    rfl
  exact h91

theorem loss_bound (N : ℕ) :
    (∑ i ∈ range N, (symbolCount - width (i+1))) ≤ slopeLoss := by
  let f : ℕ → ℕ := fun i => symbolCount - width (i+1)
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

theorem loss_lt_layer (N : ℕ) :
    (∑ i ∈ range N, (symbolCount - width (i+1))) < 21490487750071 :=
  (loss_bound N).trans_lt (by decide)

#print axioms loss_lt_layer

end Low51At2403ShapeGate
