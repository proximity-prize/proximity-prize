import ProximityPrize.SubmissionLower.R6966ProofHelperWindowPrefix

set_option Elab.async false

-- merged module R6966ProofHelperWindowGrouping
section Merged_R6966ProofHelperWindowGrouping

namespace Research6966.HelperWindowGrouping
open Finset
open K1_14 (Shape)
open HelperAvoidance (power debitAt rectSlots triSlots)
open HelperBankRank (cells)
open HelperWindowPrefix (volume)
open PadeFiltered (physicalWindow)
set_option maxHeartbeats 850000

def sumCount (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumCount f n + f n

theorem sumCount_eq (f : ℕ → ℕ) (n : ℕ) :
    sumCount f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih => rw [sumCount, ih, sum_range_succ]

/-- One physical layer for the divisor power `k+1`. The start and stop are
exclusive prefixes in the residual window after paying the divisor. -/
def layer (s : Shape) (h N k a b wt : ℕ) : ℕ :=
  if (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J then
    let hi := N-2*h*k-(k+1)*wt
    let lo := hi-2*h
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    volume hi B J (131071-h) - volume lo B J (131071-h)
  else 0

def grouped (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ) : ℕ :=
  sumCount (fun k => layer s h N k a b wt * slots (k+1)) limit

private theorem power_eq_window {N h W k : ℕ} (hp : 0 < h) (mem : W < N) :
    power N h W = k+1 ↔ N-2*h*(k+1) ≤ W ∧ W < N-2*h*k := by
  have hs : 0 < 2*h := by omega
  have lo := K1_14_4.power_threshold N (2*h) W 0 k mem hs
  have hi := K1_14_4.power_threshold N (2*h) W 0 (k+1) mem hs
  simp only [Nat.zero_add, Nat.sub_zero] at lo hi
  change k < power N h W ↔ W+2*h*k < N at lo
  change k+1 < power N h W ↔ W+2*h*(k+1) < N at hi
  omega

private theorem shifted_prefix (f : ℕ → ℕ) (stop paid : ℕ) :
    (∑ W ∈ range stop, if paid ≤ W then f (W-paid) else 0) =
      ∑ W ∈ range (stop-paid), f W := by
  classical
  by_cases live : paid ≤ stop
  · rw [← sum_range_add_sum_Ico (fun W => if paid ≤ W then f (W-paid) else 0) live]
    have early : (∑ W ∈ range paid, if paid ≤ W then f (W-paid) else 0) = 0 := by
      apply sum_eq_zero
      intro W hw
      rw [ite_eq_right (Nat.not_le.mpr (mem_range.mp hw))]
    rw [early, Nat.zero_add]
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro W _
    simp only [Nat.le_add_right paid W, ite_true, Nat.add_sub_cancel_left]
  · rw [Nat.sub_eq_zero_of_le (by omega), range_zero, sum_empty]
    apply sum_eq_zero
    intro W hw
    have := mem_range.mp hw
    rw [ite_eq_right (by omega)]

private theorem shifted_interval (f : ℕ → ℕ) (lo hi paid : ℕ) (range_ok : lo ≤ hi) :
    (∑ W ∈ Ico lo hi, if paid ≤ W then f (W-paid) else 0) =
      (∑ W ∈ range (hi-paid), f W)-(∑ W ∈ range (lo-paid), f W) := by
  have eq := sum_range_add_sum_Ico (fun W => if paid ≤ W then f (W-paid) else 0) range_ok
  rw [shifted_prefix, shifted_prefix] at eq
  omega

theorem layer_eq (s : Shape) (h N k a b wt : ℕ) (hp : 0 < h) (narrow : s.J < 131071-h) :
    layer s h N k a b wt =
      ∑ W ∈ range N, if power N h W = k+1 then (cells s h W (k+1) a b wt).card else 0 := by
  classical
  unfold layer
  by_cases room : (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J
  · rw [ite_eq_left room]
    dsimp only
    let endW := N-2*h*k
    let startW := N-2*h*(k+1)
    let paid := (k+1)*wt
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    let f (W : ℕ) := (physicalWindow B J (131071-h) W).card
    have filter_eq : (range N).filter (fun W => power N h W = k+1) = Ico startW endW := by
      ext W
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨mem,eq⟩
        exact (power_eq_window hp mem).mp eq
      · intro interval
        have mem : W < N := interval.2.trans_le (Nat.sub_le _ _)
        exact ⟨mem,(power_eq_window hp mem).mpr interval⟩
    have order : startW ≤ endW := by
      dsimp only [startW,endW]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have lo : endW-paid-2*h = startW-paid := by
      dsimp only [startW,endW,paid]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    change volume (endW-paid) B J (131071-h)-volume (endW-paid-2*h) B J (131071-h) = _
    have nJ : J < 131071-h := (Nat.sub_le _ _).trans_lt narrow
    rw [lo, HelperWindowPrefix.volume_eq_sum _ _ _ _ nJ, HelperWindowPrefix.volume_eq_sum _ _ _ _ nJ,
      ← sum_filter, filter_eq, ← shifted_interval f startW endW paid order]
    apply sum_congr rfl
    intro W _
    by_cases full : paid ≤ W
    · rw [ite_eq_left full, cells, ite_eq_left ⟨room.1,room.2,full⟩]
    · rw [ite_eq_right full, cells, ite_eq_right (fun all => full all.2.2), card_empty]
  · rw [ite_eq_right room]
    symm
    apply sum_eq_zero
    intro W _
    have no : ¬ ((k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J ∧ (k+1)*wt ≤ W) :=
      fun all => room ⟨all.1,all.2.1⟩
    rw [cells, ite_eq_right no, card_empty]
    split <;> rfl

/-- Group the raw-weight debit into disjoint divisor powers. The caller may
cut off any powers that have zero slot count or cannot fit the degree box. -/
theorem grouped_eq_debit_of_cutoff (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (narrow : s.J < 131071-h)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b ∨ N ≤ 2*h*(k-1)+k*wt) :
    grouped s h N a b wt limit slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  classical
  rw [grouped, sumCount_eq]
  calc
    _ = ∑ k ∈ range limit, ∑ W ∈ range N,
        if power N h W = k+1 then (cells s h W (k+1) a b wt).card*slots (k+1) else 0 := by
      apply sum_congr rfl
      intro k _
      rw [layer_eq s h N k a b wt hp narrow, sum_mul]
      apply sum_congr rfl
      intro W _
      split <;> simp_all
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro W hW
      let t := power N h W
      have pos : 0 < t := (show 0 < 1 by decide).trans_le (Nat.le_add_right _ _)
      change (∑ k ∈ range limit, if t = k+1 then (cells s h W (k+1) a b wt).card*slots (k+1) else 0) =
        (cells s h W t a b wt).card*slots t
      by_cases active : t ≤ limit
      · have live : t-1 ∈ range limit := mem_range.mpr (by omega)
        rw [sum_eq_single_of_mem (t-1) live]
        · rw [Nat.sub_add_cancel pos, ite_eq_left rfl]
        · intro k _ ne
          rw [ite_eq_right (by omega)]
      · have zero : (cells s h W t a b wt).card*slots t = 0 := by
          rcases tail t (by omega) with fee | aLarge | bLarge | closed
          · rw [fee, Nat.mul_zero]
          · rw [cells, ite_eq_right (fun live => (Nat.not_le.mpr aLarge) live.1), card_empty, Nat.zero_mul]
          · rw [cells, ite_eq_right (fun live => (Nat.not_le.mpr bLarge) live.2.1), card_empty, Nat.zero_mul]
          · have inWindow := (@power_eq_window N h W (t-1) hp (mem_range.mp hW)).mp
                (show power N h W = t-1+1 from (Nat.sub_add_cancel pos).symm)
            have stale : ¬ t*wt ≤ W := by omega
            rw [cells, ite_eq_right (fun live => stale live.2.2), card_empty, Nat.zero_mul]
        rw [zero]
        apply sum_eq_zero
        intro k hk
        have kin := mem_range.mp hk
        rw [ite_eq_right (by omega)]

theorem grouped_eq_debit (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (narrow : s.J < 131071-h)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b) :
    grouped s h N a b wt limit slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  apply grouped_eq_debit_of_cutoff s h N a b wt limit slots hp narrow
  intro k large
  rcases tail k large with fee | width | slope
  · exact Or.inl fee
  · exact Or.inr (Or.inl width)
  · exact Or.inr (Or.inr (Or.inl slope))


end Research6966.HelperWindowGrouping

end Merged_R6966ProofHelperWindowGrouping

-- merged module R6966ProofHelperWindowIntervals
section Merged_R6966ProofHelperWindowIntervals

namespace Research6966.HelperWindowIntervals
open Finset
open K1_14 (Shape shapeSum triangle)
open HelperAvoidance (debitAt rectSlots triSlots)
open HelperWindowGrouping (sumCount sumCount_eq grouped layer)
open HelperWindowPrefix (volume volume_eq_shapeSum)
set_option maxHeartbeats 850000

private theorem shape_mono (s : Shape) (f g : ℕ → ℕ → ℕ)
    (cap : ∀ q ≤ s.B, ∀ j ≤ min q s.J, f q j ≤ g q j) : shapeSum s f ≤ shapeSum s g := by
  unfold shapeSum
  exact sum_le_sum (fun q hq => sum_le_sum (fun j hj =>
    cap q (Nat.lt_succ_iff.mp (mem_range.mp hq)) j (Nat.lt_succ_iff.mp (mem_range.mp hj))))

theorem volume_mono (s : Shape) {lo hi wLo wHi : ℕ}
    (stop : lo ≤ hi) (step : wLo ≤ wHi) (narrow : s.J < wLo) :
    volume lo s.B s.J wHi ≤ volume hi s.B s.J wLo := by
  rw [volume_eq_shapeSum s _ _ (narrow.trans_le step), volume_eq_shapeSum s _ _ narrow]
  exact shape_mono s _ _ (fun q _ j _ =>
    (Nat.sub_le_sub_right (Nat.add_le_add_right stop j) _).trans
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right q step) _))

private theorem slice_eq (s : Shape) (stop w span : ℕ) (narrow : s.J < w) :
    volume stop s.B s.J w-volume (stop-span) s.B s.J w =
      shapeSum s (fun q j => min span (stop+j-w*q)) := by
  have pieces : volume stop s.B s.J w =
      shapeSum s (fun q j => min span (stop+j-w*q))+volume (stop-span) s.B s.J w := by
    rw [volume_eq_shapeSum s _ _ narrow, volume_eq_shapeSum s _ _ narrow]
    unfold shapeSum
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro j hj
    have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_left q s.J)
    have qw := Nat.mul_le_mul_right q (show 1 ≤ w by omega)
    omega
  omega

theorem slice_mono (B J : ℕ) {lo hi wLo wHi spanLo spanHi : ℕ}
    (stop : lo ≤ hi) (step : wLo ≤ wHi) (span : spanLo ≤ spanHi) (narrow : J < wLo) :
    volume lo B J wHi-volume (lo-spanLo) B J wHi ≤
      volume hi B J wLo-volume (hi-spanHi) B J wLo := by
  let s : Shape := ⟨0,B,J,0⟩
  change volume lo s.B s.J wHi-volume (lo-spanLo) s.B s.J wHi ≤
    volume hi s.B s.J wLo-volume (hi-spanHi) s.B s.J wLo
  rw [slice_eq s _ _ _ (narrow.trans_le step), slice_eq s _ _ _ narrow]
  exact shape_mono s _ _ (fun q _ j _ => min_le_min span
    ((Nat.sub_le_sub_right (Nat.add_le_add_right stop j) _).trans
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right q step) _)))

def cutoff (s : Shape) (agreement h reserve : ℕ) : ℕ := s.m*agreement-2*h*reserve

def layerBound (s : Shape) (agreement reserve lo hi k a b wt : ℕ) : ℕ :=
  if (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J then
    let stop := cutoff s agreement lo reserve-2*lo*k-(k+1)*wt
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    volume stop B J (131071-hi)-volume (stop-2*hi) B J (131071-hi)
  else 0

def bound (s : Shape) (agreement reserve lo hi a b wt limit : ℕ) (slots : ℕ → ℕ) : ℕ :=
  sumCount (fun k => layerBound s agreement reserve lo hi k a b wt * slots (k+1)) limit

theorem debit_le (s : Shape) (agreement reserve lo hi h a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (hl : lo ≤ h) (hh : h ≤ hi) (narrow : s.J < 131071-hi)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b) :
    (∑ W ∈ range (cutoff s agreement h reserve), debitAt s h (cutoff s agreement h reserve) W a b wt slots) ≤
      bound s agreement reserve lo hi a b wt limit slots := by
  have narrow' : s.J < 131071-h := narrow.trans_le (Nat.sub_le_sub_left hh _)
  rw [← HelperWindowGrouping.grouped_eq_debit s h _ a b wt limit slots hp narrow' tail]
  unfold grouped bound
  rw [sumCount_eq, sumCount_eq]
  apply sum_le_sum
  intro k hk
  apply Nat.mul_le_mul_right
  unfold layer layerBound
  split
  · dsimp only
    have cut : cutoff s agreement h reserve ≤ cutoff s agreement lo reserve :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_right reserve (Nat.mul_le_mul_left 2 hl)) _
    have stop : cutoff s agreement h reserve-2*h*k-(k+1)*wt ≤
        cutoff s agreement lo reserve-2*lo*k-(k+1)*wt :=
      Nat.sub_le_sub_right ((Nat.sub_le_sub_right cut _).trans
        (Nat.sub_le_sub_left (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 hl)) _)) _
    exact slice_mono _ _ stop (Nat.sub_le_sub_left hh _) (Nat.mul_le_mul_left 2 hh)
      ((Nat.sub_le _ _).trans_lt narrow)
  · exact le_rfl

/-- A bank inequality certified at the two ends of an interval applies at
each integer height in it. The residual debit is bounded as a single
clipped window, preserving the cancellation between its two prefixes. -/
theorem positive (s : Shape) (agreement reserve lo hi h a b wt limit width rate nodes moment : ℕ)
    (slots : ℕ → ℕ) (hp : 0 < h) (hl : lo ≤ h) (hh : h ≤ hi) (narrow : s.J < 131071-hi)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b)
    (cert : width*nodes+hi*rate*moment+bound s agreement reserve lo hi a b wt limit slots <
      width*volume (cutoff s agreement hi reserve) s.B s.J (131071-lo)) :
    width*nodes+h*rate*moment+
        (∑ W ∈ range (cutoff s agreement h reserve), debitAt s h (cutoff s agreement h reserve) W a b wt slots) <
      width*shapeSum s (fun q j => cutoff s agreement h reserve+j-q*(131071-h)) := by
  have pay := debit_le s agreement reserve lo hi h a b wt limit slots hp hl hh narrow tail
  have pole := Nat.mul_le_mul_right moment (Nat.mul_le_mul_right rate hh)
  have cut : cutoff s agreement hi reserve ≤ cutoff s agreement h reserve :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_right reserve (Nat.mul_le_mul_left 2 hh)) _
  have n := narrow.trans_le (Nat.sub_le_sub_left hh 131071)
  have src := volume_mono s cut (Nat.sub_le_sub_left hl _) n
  rw [volume_eq_shapeSum s (cutoff s agreement h reserve) (131071-h) n] at src
  have agree : shapeSum s (fun q j => cutoff s agreement h reserve+j-(131071-h)*q) =
      shapeSum s (fun q j => cutoff s agreement h reserve+j-q*(131071-h)) := by
    simp only [Nat.mul_comm (131071-h)]
  exact ((Nat.add_le_add (Nat.add_le_add_left pole _) pay).trans_lt cert).trans_le
    (Nat.mul_le_mul_left _ (src.trans_eq agree))

def slotLimit (s : Shape) (U u : ℕ) : ℕ := if u = 0 then s.J else min s.J (U/u)

private theorem slot_limit {s : Shape} {U u k : ℕ} (large : slotLimit s U u < k) :
    U < k*u ∨ s.J < k := by
  unfold slotLimit at large
  split at large
  · exact Or.inr large
  · rename_i nz
    by_cases h : s.J < k
    · exact Or.inr h
    · exact Or.inl ((Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero nz)).mp (by omega))

theorem triangle_tail (s : Shape) (a U u : ℕ) :
    ∀ k > slotLimit s U u, triSlots U u k = 0 ∨ s.B < k*a ∨ s.J < k*1 := by
  intro k large
  rcases slot_limit large with cap | slope
  · exact Or.inl (ite_eq_right (Nat.not_le.mpr cap))
  · exact Or.inr (Or.inr (by simpa only [Nat.mul_one] using slope))

def box (CAP v : ℕ) : Fin 2 → ℕ := ![CAP-v,v]
def axis (u : ℕ) : Fin 2 → ℕ := ![0,u]

theorem rectangle_tail (s : Shape) (a CAP v u : ℕ) :
    ∀ k > slotLimit s v u, rectSlots (box CAP v) (axis u) k = 0 ∨ s.B < k*a ∨ s.J < k*1 := by
  intro k large
  rcases slot_limit large with cap | slope
  · apply Or.inl
    apply ite_eq_right
    intro room
    exact (Nat.not_le.mpr cap) (room 1)
  · exact Or.inr (Or.inr (by simpa only [Nat.mul_one] using slope))

end Research6966.HelperWindowIntervals

end Merged_R6966ProofHelperWindowIntervals

-- merged module R6966ProofHelperWindowCertificate
section Merged_R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCertificate
open Finset
open K1_14 (Shape shapeSum triangle)
open HelperAvoidance (debitAt rectSlots triSlots)
open HelperWindowIntervals (cutoff bound slotLimit triangle_tail rectangle_tail box axis)
open HelperWindowPrefix (volume)
set_option maxHeartbeats 850000

structure Witness where
  degree : ℕ
  rect : Bool
  lower : ℕ
  reserve : ℕ
  m : ℕ
  B : ℕ
  J : ℕ
  v : ℕ
  nodes : ℕ
  pole : ℕ

def agreement : ℕ := 179769
def firstHeight : ℕ := 2330
def lastHeight : ℕ := 2499
def seedCap : ℕ := 510000

def Witness.shape (b : Witness) : Shape :=
  ⟨b.m,b.B,b.J,if b.rect then seedCap else b.v⟩

def Witness.bank (b : Witness) : P1_7.Bank := ⟨b.shape,b.nodes,b.pole⟩

def Witness.weight (b : Witness) : ℕ := b.degree*(131071-lastHeight)-1

def Witness.width (b : Witness) : ℕ :=
  if b.rect then KoalaRect.area (box seedCap b.v) else triangle b.v

def Witness.rate (b : Witness) : ℕ :=
  if b.rect then box seedCap b.v 0+box seedCap b.v 1+2 else 2*(b.v+1)

def Witness.slots (b : Witness) (k : ℕ) : ℕ :=
  if b.rect then rectSlots (box seedCap b.v) (axis b.lower) k else triSlots b.v b.lower k

def Witness.top (b : Witness) (h : ℕ) : ℕ := cutoff b.shape agreement h b.reserve

def Witness.loop (b : Witness) (lo hi : ℕ) : ℕ :=
  bound b.shape agreement b.reserve lo hi b.degree 1 b.weight
    (slotLimit b.shape b.v b.lower) b.slots

def Positive (b : Witness) (lo hi : ℕ) : Prop :=
  b.width*b.nodes+hi*b.rate*b.pole+b.loop lo hi <
    b.width*volume (b.top hi) b.B b.J (131071-lo)

instance (b : Witness) (lo hi : ℕ) : Decidable (Positive b lo hi) := by
  unfold Positive
  infer_instance

def Cover (b : Witness) (lo : ℕ) : List ℕ → Prop
  | [] => lo = lastHeight+1
  | hi :: rest => lo ≤ hi ∧ hi ≤ lastHeight ∧ Positive b lo hi ∧ Cover b (hi+1) rest

theorem cover_height {b : Witness} {endpoints : List ℕ} {lo h : ℕ}
    (cover : Cover b lo endpoints) (low : lo ≤ h) (high : h ≤ lastHeight) :
    ∃ lo hi, lo ≤ h ∧ h ≤ hi ∧ hi ≤ lastHeight ∧ Positive b lo hi := by
  induction endpoints generalizing lo with
  | nil =>
    change lo=lastHeight+1 at cover
    omega
  | cons hi ends ih =>
    obtain ⟨_, hh, pos, tail⟩ := cover
    by_cases first : h ≤ hi
    · exact ⟨lo, hi, low, first, hh, pos⟩
    · exact ih tail (by omega)


theorem weight_room (b : Witness) {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight)
    (hs : 2*b.reserve ≤ b.B) (hw : b.B*(131071-firstHeight) ≤ b.top firstHeight) :
    b.B*(131071-h) ≤ b.top h := by
  have delta : 131071-firstHeight = (131071-h)+(h-firstHeight) := by
    have last : lastHeight ≤ 131071 := by decide
    omega
  have res : 2*h*b.reserve = 2*firstHeight*b.reserve+(h-firstHeight)*(2*b.reserve) := by
    conv_lhs => rw [show h = firstHeight+(h-firstHeight) by omega]
    ring
  have more := Nat.mul_le_mul_left (h-firstHeight) hs
  have pre : b.B*(131071-firstHeight)+2*firstHeight*b.reserve ≤ b.m*agreement := by
    change b.B*(131071-firstHeight) ≤ b.m*agreement-2*firstHeight*b.reserve at hw
    by_cases nz : b.B*(131071-firstHeight) = 0
    · have bp : 0 < 131071-firstHeight := by decide
      have bz : b.B = 0 := (Nat.mul_eq_zero.mp nz).resolve_right bp.ne'
      have : b.reserve=0 := by omega
      rw [this, Nat.mul_zero, Nat.add_zero, nz]
      exact Nat.zero_le _
    · omega
  change b.B*(131071-h) ≤ b.m*agreement-2*h*b.reserve
  rw [res]
  rw [delta, Nat.mul_add] at pre
  rw [Nat.mul_comm (h-firstHeight) b.B] at more
  omega

theorem cutoff_order (b : Witness) {h : ℕ} (pos : 0 < b.top h) :
    b.top h-1+2*h*b.reserve < b.shape.m*agreement := by
  change 0 < b.m*agreement-2*h*b.reserve at pos
  change b.m*agreement-2*h*b.reserve-1+2*h*b.reserve < b.m*agreement
  omega

structure Verified (b : Witness) : Prop where
  node_eq : P1_7_1.nodeRows b.shape = b.nodes
  pole_ge : P1_7_1.groupedPoleMoment b.B b.J ≤ b.pole
  caps : b.B ≤ 5585 ∧ b.J ≤ 1200 ∧ b.v ≤ seedCap ∧ 0 < b.m ∧ 2*b.reserve ≤ b.B
  width_at_first : b.B*(131071-firstHeight) ≤ b.top firstHeight
  endpoints : ∃ endpoints : List ℕ, Cover b firstHeight endpoints

theorem Verified.raw_positive {b : Witness} (checked : Verified b) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    b.width*b.nodes+h*b.rate*b.pole+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight b.slots) <
      b.width*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  obtain ⟨ends, cover⟩ := checked.endpoints
  obtain ⟨bot, top, hb, ht, htop, cert⟩ := cover_height cover lo hi
  have tail : ∀ k > slotLimit b.shape b.v b.lower,
      b.slots k = 0 ∨ b.shape.B < k*b.degree ∨ b.shape.J < k*1 := by
    intro k big
    cases tag : b.rect
    · simpa only [Witness.slots,tag,Bool.false_eq_true,ite_false] using
        triangle_tail b.shape b.degree b.v b.lower k big
    · simpa only [Witness.slots,tag,ite_true] using
        rectangle_tail b.shape b.degree seedCap b.v b.lower k big
  have pos : 0 < h := (show 0 < firstHeight by decide).trans_le lo
  have narrow : b.shape.J < 131071-top := by
    change b.J < 131071-top
    have small := checked.caps.2.1
    have last : lastHeight = 2499 := rfl
    omega
  exact HelperWindowIntervals.positive b.shape agreement b.reserve bot top h b.degree 1 b.weight _
    b.width b.rate b.nodes b.pole b.slots pos hb ht narrow tail cert

theorem Verified.rectangle {b : Witness} (checked : Verified b) (rect : b.rect = true) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    KoalaRect.rectDebit h b.nodes b.pole (box seedCap b.v)+
        (∑ W ∈ range (b.top h),
          debitAt b.shape h (b.top h) W b.degree 1 b.weight (rectSlots (box seedCap b.v) (axis b.lower))) <
      KoalaRect.area (box seedCap b.v)*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  have slots : b.slots = rectSlots (box seedCap b.v) (axis b.lower) := by
    funext k
    simp only [Witness.slots,rect,ite_true]
  simpa only [Witness.width,Witness.rate,slots,rect,ite_true,KoalaRect.rectDebit]
    using checked.raw_positive lo hi

theorem Verified.triangle {b : Witness} (checked : Verified b) (tri : b.rect = false) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    P1_7.debit h b.bank+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight (triSlots b.v b.lower)) <
      triangle b.v*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  have pos := checked.raw_positive lo hi
  have slots : b.slots = triSlots b.v b.lower := by
    funext k
    simp only [Witness.slots,tri,Bool.false_eq_true,ite_false]
  simpa only [Witness.width,Witness.rate,slots,tri,Bool.false_eq_true,ite_false,Nat.mul_left_comm h 2,
    Nat.mul_assoc,P1_7.debit,Witness.bank,Witness.shape] using pos

end Research6966.HelperWindowCertificate

end Merged_R6966ProofHelperWindowCertificate
