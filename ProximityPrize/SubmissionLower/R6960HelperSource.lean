import ProximityPrize.SubmissionLower.R6960PowerLayers
import ProximityPrize.SubmissionLower.UpperBranch5

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.HelperSource
open Finset Polynomial
open K1_14 (Shape Jet FX L Banks shapeSum triangle slots seedHasse jetAt)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open K1_14_3 (RowCaps)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open P1_7 (Bank debit)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_5 (kept)
open PowerLayers (eligiblePositions layerCost)
open private position_sum from ProximityPrize.SubmissionLower.UpperBranch5
open private pole_bound from ProximityPrize.SubmissionLower.UpperBranch1
open private slots_anti rise_of_convex from ProximityPrize.SubmissionLower.UpperBranch6

/-- The last nonzero power permitted by the slope and total jet caps. -/
def orderCap (s : Shape) (d c q j : ℕ) : ℕ :=
  if c = 0 then j/d else min (j/d) ((s.B-q)/c)

theorem le_orderCap (s : Shape) {d c q j k : ℕ} (hd : 0 < d) (hq : q ≤ s.B) :
    k ≤ orderCap s d c q j ↔ k*d ≤ j ∧ q+k*c ≤ s.B := by
  unfold orderCap
  split
  · rename_i hc
    rw [hc, Nat.mul_zero, Nat.add_zero, Nat.le_div_iff_mul_le hd]
    simp [hq]
  · rename_i hc
    rw [le_min_iff, Nat.le_div_iff_mul_le hd, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc)]
    omega

/-- The gain is the drop in the allowed seed count at each successive Hasse layer,
times the number of cutoffs at which that drop has occurred. -/
def coordinateGain (s : Shape) (A h r d c v q j : ℕ) : ℕ :=
  let C := kept s.U v (orderCap s d c q j)
  ∑ i ∈ range (orderCap s d c q j + 1),
    (C i - C (i+1)) * (s.m*A+j-q*(131071-h)-2*h*(r+i))

def gain (s : Shape) (A h r d c v : ℕ) : ℕ :=
  shapeSum s (coordinateGain s A h r d c v)

def cutoffCount (s : Shape) (A h r : ℕ) : ℕ := s.m*A-2*h*r

private theorem layerCost_eq (s : Shape) (h N W d c v : ℕ) (hd : 0 < d) :
    layerCost s h N W d c v =
      shapeSum s fun q j =>
        if q*(131071-h) ≤ W+j then
          kept s.U v (orderCap s d c q j) (1+(N-1-W)/(2*h))
        else 0 := by
  classical
  let k := 1+(N-1-W)/(2*h)
  unfold layerCost eligiblePositions
  change (((range (s.B+1)).product (range (s.J+1))).filter (fun a =>
    a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2)).card *
    slots s.U (k*v) = _
  rw [← Nat.nsmul_eq_mul, ← sum_const, sum_filter]
  change (∑ a ∈ range (s.B+1) ×ˢ range (s.J+1),
    if a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2 then slots s.U (k*v) else 0) = _
  rw [sum_product (range (s.B+1)) (range (s.J+1)) (fun a : ℕ×ℕ =>
    if a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2 then slots s.U (k*v) else 0)]
  unfold shapeSum
  apply sum_congr rfl
  intro q hq
  have hqb : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hq)
  rw [← sum_subset (s₁ := range (min q s.J+1)) (s₂ := range (s.J+1))
    (range_mono (Nat.succ_le_succ (min_le_right _ _)))]
  · apply sum_congr rfl
    intro j hj
    have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
    change (if j≤q ∧ k*d≤j ∧ q+k*c≤s.B ∧ q*(131071-h)≤W+j then slots s.U (k*v) else 0) =
      if q*(131071-h)≤W+j then kept s.U v (orderCap s d c q j) k else 0
    simp only [kept, le_orderCap s hd hqb]
    by_cases hw : q*(131071-h) ≤ W+j
    · simp only [hjq, hw, true_and, and_true, ite_true]
    · simp only [hw, and_false, ite_false]
  · intro j hj hn
    have hq' : ¬ j≤q := by
      simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hn
      omega
    simp [hq']

private theorem coordinate_total (s : Shape) (A h r d c v q j : ℕ) (hh : 0<h)
    (hk : 1≤131071-h) (hj : j≤q) :
    let N := cutoffCount s A h r
    (∑ W ∈ range N, if q*(131071-h) ≤ W+j then
      kept s.U v (orderCap s d c q j) (1+(N-1-W)/(2*h)) else 0) +
    coordinateGain s A h r d c v q j = triangle s.U*(N+j-q*(131071-h)) := by
  dsimp only
  let N := cutoffCount s A h r
  let t := q*(131071-h)
  let g := orderCap s d c q j
  have hq : q ≤ t := by simpa [t] using Nat.mul_le_mul_left q hk
  have hjt : j ≤ t := hj.trans hq
  have he (i : ℕ) : N+0-(t-j)-2*h*(0+i) = s.m*A+j-t-2*h*(r+i) := by
    simp only [Nat.add_zero, Nat.zero_add]
    unfold N cutoffCount
    rw [Nat.mul_add]
    omega
  have eq := position_sum N (2*h) (t-j) 0 s.U v g (Nat.zero_le _) (by omega)
  simp only [Nat.add_zero, Nat.sub_zero, Nat.zero_add] at eq
  have hwidth : N-(t-j) = N+j-t := by omega
  have he' (i : ℕ) : N-(t-j)-2*h*i = s.m*A+j-t-2*h*(r+i) := by simpa using he i
  simp_rw [he'] at eq
  rw [hwidth] at eq
  have hsplit :
      coordinateGain s A h r d c v q j =
      (∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
         (s.m*A+j-t-2*h*(r+a))) +
      slots s.U (g*v) * (s.m*A+j-t-2*h*(r+g)) := by
    unfold coordinateGain
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro i hi
      have h := mem_range.mp hi
      simp only [kept, ite_eq_left h.le, ite_eq_left (Nat.succ_le_of_lt h)]
      rfl
    · simp [kept, g, t]
  rw [hsplit]
  have hguard (W : ℕ) : t-j ≤ W ↔ t ≤ W+j := by omega
  simpa only [hguard] using eq

/-- The integrated upper rank bound and the explicit gain exactly partition the
unpenalized source volume. -/
theorem cutoff_total (s : Shape) (A h r d c v : ℕ) (hh : 0 < h) (hk : 1 ≤ 131071-h)
    (hd : 0 < d) :
    let N := cutoffCount s A h r
    (∑ W ∈ range N, layerCost s h N W d c v) + gain s A h r d c v =
      triangle s.U * shapeSum s (fun q j => N+j-q*(131071-h)) := by
  dsimp only
  let N := cutoffCount s A h r
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range N, shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range N, F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp_rw [layerCost_eq s h (cutoffCount s A h r) _ d c v hd]
  rw [hswap]
  simp only [gain, shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  exact coordinate_total s A h r d c v q j hh hk
    ((Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _))

/-- Native CRT ranks at any cutoff. The physical and grouped-pole debits
are independent of the agreement used to choose that cutoff. -/
theorem crt_rank_floor {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (hh : 0<h) (hk : h≤131070)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (W : ℕ)
    (hW : K1_14_1.rawWidthCond h t.shape W) :
    K1_14_1.rawVolumeAt h t.shape W ≤ debit h t +
      ∑ w ∈ range (W+1), Module.finrank FX (evaluated Crt word t.shape w) := by
  have hlocal := P1_7_1_1.of_children P1_7_1_1_1.proof P1_7_1_1_2.proof
  have hvol := P0_10_1.ambient_bound (by omega : h ≤ 131071) t.shape W hW
  have hcontact := P0_10_1.physical_bound h word t.shape W
  have hpole := pole_bound hlocal hh (hk.trans_lt (by decide)) Crt word t.shape small W
  have hsum := P1_7_1.telescope hk Crt word t.shape W
  have hphys : K1_14_1.physicalDebit t.shape = triangle t.shape.U * t.nodeRows := by
    rw [← hnodes]
    unfold K1_14_1.physicalDebit nodeRows
    rw [Nat.mul_assoc]
  rw [hphys] at hcontact
  have hextra := Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hmoment
  unfold debit
  omega

def WidthGuard (t : Bank) (A h r : ℕ) : Prop :=
  t.shape.B * (131071-h) < cutoffCount t.shape A h r

/-- A positive factor-sensitive surplus gives the strict rank comparison
required by the forced-power argument. -/
theorem crt_supply {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r d c v : ℕ) (hh : 0<h) (hk : h≤131070) (hd : 0<d)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (width : WidthGuard t A h r)
    (surplus : debit h t < gain t.shape A h r d c v) :
    let N := cutoffCount t.shape A h r
    (∑ W ∈ range N, layerCost t.shape h N W d c v) <
      ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W) := by
  dsimp only
  let N := cutoffCount t.shape A h r
  have hw : t.shape.B*(131071-h)<N := width
  have hcomplete : N-1+1=N := by omega
  have hf := crt_rank_floor Crt word t hh hk hnodes hmoment small (N-1) (by
    intro q hq j _
    rw [hcomplete]
    exact (Nat.mul_le_mul_right _ hq).trans (hw.le.trans (Nat.le_add_right N j)))
  unfold K1_14_1.rawVolumeAt at hf
  rw [hcomplete] at hf
  have ht := cutoff_total t.shape A h r d c v hh (by omega) hd
  dsimp only at ht
  change (∑ W ∈ range N, layerCost t.shape h N W d c v) + gain t.shape A h r d c v =
    triangle t.shape.U * shapeSum t.shape (fun q j => N+j-q*(131071-h)) at ht
  change (∑ W ∈ range N, layerCost t.shape h N W d c v) <
    ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W)
  omega

theorem nonzero_of_supply {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (s : Shape) (N : ℕ) (supply : 0 < ∑ W ∈ range N, Module.finrank FX (evaluated Crt word s W)) :
    ∃ P ∈ evaluated Crt word s (N-1), P ≠ 0 := by
  by_contra! hz
  have hall : (∑ W ∈ range N, Module.finrank FX (evaluated Crt word s W)) = 0 := by
    apply sum_eq_zero
    intro W hW
    have hW' : W ≤ N-1 := by have := mem_range.mp hW; omega
    have hb : evaluated Crt word s W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (evaluated_mono Crt word rfl rfl rfl le_rfl hW' hP))
    rw [hb, finrank_bot]
  omega

/-- Avoid a prime in the actual evaluated CRT bank using its degree lower bounds
and the positive arithmetic receipt. -/
theorem crt_avoiding_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r d c v : ℕ) (hh : 0<h) (hk : h≤131070) (hd : 0<d)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (smallSeed : t.shape.U<K1.p) (width : WidthGuard t A h r)
    (surplus : debit h t < gain t.shape A h r d c v)
    {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : d≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (cutoffCount t.shape A h r-1), ¬ G∣Q := by
  by_contra! shared
  let N := cutoffCount t.shape A h r
  have supply := crt_supply Crt word t A r d c v hh hk hd hnodes hmoment small width surplus
  obtain ⟨P, hP, hnP⟩ := nonzero_of_supply Crt word t.shape N (lt_of_le_of_lt (Nat.zero_le _) supply)
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ t.shape.U := by
    by_cases hz : ((P.coeff j).coeff i)=0
    · simp [hz]
    · exact (evaluated_shape Crt word hP j i hz).2.2
  obtain ⟨Q, hQ, hAvoid⟩ := PowerLayers.avoiding_row t.shape h N d c v hh
    (evaluated Crt word t.shape) G P irr (hd.trans_le slope) seeded hnP (shared P hP)
    smallSeed hpc slope seed excess
    (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound hh hk Crt word t.shape W R hR hnR)
    (fun _ _ _ hR i a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR i a))
    supply
  exact hAvoid (shared Q hQ)

#print axioms cutoff_total
#print axioms crt_rank_floor
#print axioms crt_avoiding_row

/-- A clipped affine width before converting back to natural-number slots. -/
def signedWidth (s : Shape) (A h r q j i : ℕ) : ℤ :=
  (s.m : ℤ)*A+j-(131071-(h : ℤ))*q-2*(h : ℤ)*(r+i)

theorem width_cast (s : Shape) (A h r q j i : ℕ) (hk : h≤131071) :
    ((s.m*A+j-q*(131071-h)-2*h*(r+i) : ℕ) : ℤ) =
      max 0 (signedWidth s A h r q j i) := by
  rw [Nat.sub_sub]
  have he : (↑(s.m*A+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*(r+i) : ℕ) : ℤ) =
      signedWidth s A h r q j i := by
    simp only [signedWidth, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]
    ring
  generalize s.m*A+j = x at *
  generalize q*(131071-h)+2*h*(r+i) = y at *
  by_cases hxy : y≤x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y=0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]

private theorem weighted_convex (s : Shape) (A h r q j i c : ℕ) (hk : h+2≤131071) :
    let f := fun h => ((c*(s.m*A+j-q*(131071-h)-2*h*(r+i)) : ℕ) : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  dsimp only
  simp only [Nat.cast_mul, width_cast s A h r q j i (by omega),
    width_cast s A (h+1) r q j i (by omega), width_cast s A (h+2) r q j i hk, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg c)
  by_cases hn : signedWidth s A (h+1) r q j i ≤ 0
  · rw [max_eq_left hn, zero_add]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hn)]
    have hlin : signedWidth s A (h+1) r q j i + signedWidth s A (h+1) r q j i =
        signedWidth s A h r q j i + signedWidth s A (h+2) r q j i := by
      simp only [signedWidth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hlin]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)

def surplus (t : Bank) (A h r d c v : ℕ) : ℤ :=
  (gain t.shape A h r d c v : ℤ)-(debit h t : ℤ)

theorem surplus_convex (t : Bank) (A h r d c v : ℕ) (hk : h+2≤131071) :
    surplus t A (h+1) r d c v + surplus t A (h+1) r d c v ≤
      surplus t A h r d c v + surplus t A (h+2) r d c v := by
  have hg : (gain t.shape A (h+1) r d c v : ℤ) + gain t.shape A (h+1) r d c v ≤
      (gain t.shape A h r d c v : ℤ) + gain t.shape A (h+2) r d c v := by
    simp only [gain, shapeSum, coordinateGain, Nat.cast_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro q _
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro i _
    exact weighted_convex t.shape A h r q j i _ hk
  have hd : (debit (h+1) t : ℤ) + debit (h+1) t = (debit h t : ℤ) + debit (h+2) t := by
    simp only [debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  unfold surplus
  omega

theorem surplus_positive (t : Bank) (A lo h r d c v : ℕ) (hl : lo≤h) (hk : h≤131070)
    (positive : 0<surplus t A lo r d c v)
    (increasing : surplus t A lo r d c v ≤ surplus t A (lo+1) r d c v) :
    debit h t < gain t.shape A h r d c v := by
  have inc := rise_of_convex (f := fun n => surplus t A n r d c v)
    (fun n hn => surplus_convex t A n r d c v (by omega)) hl increasing
  have hp := positive.trans_le inc.1
  unfold surplus at hp
  omega

theorem width_at_height (t : Bank) (A lo h r : ℕ) (hl : lo≤h) (hk : h≤131071)
    (hs : 2*r≤t.shape.B) (hw : WidthGuard t A lo r) :
    WidthGuard t A h r := by
  unfold WidthGuard cutoffCount at *
  have hl' : lo ≤ 131071 := hl.trans hk
  have z := Nat.mul_le_mul_left (h-lo) hs
  have hlip : t.shape.B*(131071-h) + 2*h*r ≤
      t.shape.B*(131071-lo) + 2*lo*r := by
    have h₁ : 131071-h+(h-lo)=131071-lo := by omega
    have h₂ : lo+(h-lo)=h := by omega
    have h₁' := congrArg (t.shape.B * ·) h₁
    have h₂' := congrArg (fun n : ℕ => 2*n*r) h₂
    simp only [Nat.mul_add, Nat.add_mul] at h₁' h₂'
    rw [Nat.mul_comm t.shape.B (h-lo)] at h₁'
    rw [Nat.mul_comm (2*(h-lo)) r, ←Nat.mul_assoc r 2 (h-lo),
      Nat.mul_comm r 2, Nat.mul_comm (2*r) (h-lo)] at h₂'
    omega
  omega

#print axioms surplus_positive
#print axioms width_at_height
end Lower6960.HelperSource
