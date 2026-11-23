import ProximityPrize.SubmissionLower.KoalaGateChunkSums

set_option autoImplicit false
set_option Elab.async false

namespace FadicGate
open Finset
open FadicClipping (skip skip_le skip_spec)
open private FadicGate.prefix_eq_sum from ProximityPrize.SubmissionLower.FadicDenomProgression
open FadicGate (prefix_eq_sum)

/-- Add the rising part in one progression and visit only the remaining tiles. -/
def rRisePrefix (f : ℕ → ℕ) (J T theta base step total shift offset : ℕ) : ℕ :=
  let first := skip total (51*base+shift) (theta+1) (51*step)
  if first < 4 then rPrefix f total
  else rCappedProg first (base+offset) step J T +
    rPrefix (fun i => f (first+i)) (total-first)

theorem rRisePrefix_eq (f : ℕ → ℕ) (J T theta base step total shift offset : ℕ)
    (h : ∀ i < total, 51 * (base+step*i) + shift ≤ theta →
      f i = rCapped (base+offset+step*i) J T) :
    rRisePrefix f J T theta base step total shift offset = rPrefix f total := by
  let first := skip total (51*base+shift) (theta+1) (51*step)
  have hfirst : first ≤ total := skip_le _ _ _ _
  change (if first < 4 then rPrefix f total else
    rCappedProg first (base+offset) step J T +
      rPrefix (fun i => f (first+i)) (total-first)) = rPrefix f total
  by_cases hs : first < 4
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs, rCappedProg_eq, prefix_eq_sum, prefix_eq_sum f total]
    conv_rhs => rw [← Nat.add_sub_of_le hfirst, sum_range_add]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have ht := hi'.trans_le hfirst
    have hk : ¬ theta+1 ≤ 51*base+shift+(51*step)*i := by
      intro ha
      exact (not_le_of_gt hi') ((skip_spec ht).mpr ha)
    have hlin : 51*(base+step*i)+shift = 51*base+shift+(51*step)*i := by ring
    symm
    exact h i ht (by rw [hlin]; omega)

private theorem rSegHi_full {base h m i : ℕ} (hi : i < m/h) :
    rSegHi base h m i = base+h*i+(h-1) := by
  have hh : 0 < h := by by_contra! hn; simp [Nat.eq_zero_of_le_zero hn] at hi
  have hmul := (Nat.le_div_iff_mul_le hh).mp (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul, Nat.mul_comm i h] at hmul
  unfold rSegHi
  rw [rMin_eq]
  change base + min (h*i+h-1) (m-1) = base+h*i+(h-1)
  rw [min_eq_left (show h*i+h-1 ≤ m-1 by omega)]
  omega

private theorem rLowSeg_rising {J T theta base h m i : ℕ} (hi : i < m/h)
    (hr : 51*(base+h*i)+26*(h-1) ≤ theta) :
    rLowSeg J T theta base h m i = rCapped (base+0+h*i) J T := by
  rw [rLowSeg, rSegHi_full hi, rLowSegAux, cond_ble, rMin_eq]
  change (if 26*(base+h*i+(h-1)) ≤ theta then
    rCapped (min (base+h*i) ((theta-26*(base+h*i+(h-1)))/25)) J T
    else 0) = _
  have hz : 26*(base+h*i+(h-1)) ≤ theta := by omega
  have hd : base+h*i ≤ (theta-26*(base+h*i+(h-1)))/25 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).2
    omega
  rw [ite_eq_left hz, min_eq_left hd, add_zero]

private theorem rHighSeg_rising {J T theta base h m i : ℕ} (hi : i < m/h)
    (hr : 51*(base+h*i)+25*(h-1) ≤ theta) :
    rHighSeg J T theta base h m i = rCapped (base+(h-1)+h*i) J T := by
  rw [rHighSeg, rSegHi_full hi, rHighSegAux, cond_ble, rMin_eq]
  change (if 26*(base+h*i) ≤ theta then
    rCapped (min (base+h*i+(h-1)) ((theta-26*(base+h*i))/25)) J T
    else 0) = _
  have hz : 26*(base+h*i) ≤ theta := by omega
  have hd : base+h*i+(h-1) ≤ (theta-26*(base+h*i))/25 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).2
    omega
  rw [ite_eq_left hz, min_eq_left hd, show base+h*i+(h-1) = base+(h-1)+h*i by omega]

private def rSegSumLowRising (J T Θ base h m : ℕ) : ℕ :=
  h * rRisePrefix (rLowSeg J T Θ base h m) J T Θ base h (m/h) (26*(h-1)) 0
    + m%h * rLowSeg J T Θ base h m (m/h)

private def rSegSumHighRising (J T Θ base h m : ℕ) : ℕ :=
  h * rRisePrefix (rHighSeg J T Θ base h m) J T Θ base h (m/h) (25*(h-1)) (h-1)
    + m%h * rHighSeg J T Θ base h m (m/h)

private theorem rSegSumLowRising_eq (J T Θ base h m : ℕ) :
    rSegSumLowRising J T Θ base h m = rSegSumLow J T Θ base h m := by
  unfold rSegSumLowRising rSegSumLow
  rw [rRisePrefix_eq (h := fun _ hi hr => rLowSeg_rising hi hr)] <;> rfl

private theorem rSegSumHighRising_eq (J T Θ base h m : ℕ) :
    rSegSumHighRising J T Θ base h m = rSegSumHigh J T Θ base h m := by
  unfold rSegSumHighRising rSegSumHigh
  rw [rRisePrefix_eq (h := fun _ hi hr => rHighSeg_rising hi hr)] <;> rfl


private def rFastLowRising (B J T theta step : ℕ) : ℕ :=
  if step = 1 then rExactBox B J T theta else
    let lo := rFlatLo B J
    let hi := rFlatHi B J theta
    rSegSumLowRising J T theta 0 step lo + (hi-lo) * rCapped J J T +
      rSegSumLowRising J T theta hi step (B+1-hi)

private def rFastHighRising (B J T theta step : ℕ) : ℕ :=
  if step = 1 then rExactBox B J T theta else
    let lo := rFlatLo B J
    let hi := rFlatHi B J theta
    rSegSumHighRising J T theta 0 step lo + (hi-lo) * rCapped J J T +
      rSegSumHighRising J T theta hi step (B+1-hi)

private theorem rFastLowRising_eq (B J T theta step : ℕ) :
    rFastLowRising B J T theta step = rFastLow B J T theta step := by
  simp only [rFastLowRising, rFastLow, rFastLowAux, rSegSumLowRising_eq] <;> rfl

private theorem rFastHighRising_eq (B J T theta step : ℕ) :
    rFastHighRising B J T theta step = rFastHigh B J T theta step := by
  simp only [rFastHighRising, rFastHigh, rFastHighAux, rSegSumHighRising_eq] <;> rfl

private def risingDepth (h bl bh jl jh tl L H a : ℕ) : Entry → ℕ
  | none => 0
  | some (B, J, T) =>
    cond (rBoxOK bh jh H a B J)
      (let theta := 131312 - a*H
       rFastLowRising B J T theta h -
        cond (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L theta)
          (rFastHighRising (B-bl) (J-jl) (T-tl) (theta-L) h) 0) 0

private theorem risingDepth_eq (h bl bh jl jh tl L H a : ℕ) (e : Entry) :
    risingDepth h bl bh jl jh tl L H a e = rVarDepthLow h bl bh jl jh tl L H a e := by
  cases e with
  | none => rfl
  | some v =>
    obtain ⟨B,J,T⟩ := v
    simp only [risingDepth, rVarDepthLow, rVarDepthAux, rVarMultHigh,
      rFastLowRising_eq, rFastHighRising_eq] <;> rfl

private def risingList (h bl bh jl jh tl L H : ℕ) : ℕ → List Entry → ℕ
  | _, [] => 0
  | k, e :: es => risingDepth h bl bh jl jh tl L H k e + risingList h bl bh jl jh tl L H (k+1) es

private theorem risingList_eq (h bl bh jl jh tl L H k : ℕ) (es : List Entry) :
    risingList h bl bh jl jh tl L H k es = rVarList h bl bh jl jh tl L H k es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [risingList, rVarList, risingDepth_eq, ih] <;> rfl

private def risingLevelLoss (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) : ℕ :=
  S - rMax (rFastLowRising (rMin pB 4012) (rMin pJ 1650) pT 131312 h)
    (risingList h bl bh jl jh tl L H 0 es)

private theorem risingLevelLoss_eq (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) :
    risingLevelLoss S h bl bh jl jh tl L H pB pJ pT es =
      rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es := by
  simp only [risingLevelLoss, rVarLevelLoss, rVarPlainLow, rFastLowRising_eq, risingList_eq] <;> rfl

end FadicGate

namespace KoalaGateCheck

open FadicGate
open KoalaWeightedRate (Envelope)

/-- The same fixed loss certificate, with each rising part summed as a progression. -/
def lossChunkRising (h : ℕ) (p : Envelope) (plain : ℕ → ℕ × ℕ × ℕ)
    (boxes : ℕ → List Entry) (i n : ℕ) : ℕ :=
  rPrefix (fun j =>
    let r := i+j+1
    FadicGate.risingLevelLoss 406807694511 h p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow
      p.taperHigh (plain r).1 (plain r).2.1 (plain r).2.2 (boxes r)) n

theorem lossChunkRising_eq (h : ℕ) (p : Envelope) (plain : ℕ → ℕ × ℕ × ℕ)
    (boxes : ℕ → List Entry) (i n : ℕ) :
    lossChunkRising h p plain boxes i n = lossChunk h p plain boxes i n := by
  simp only [lossChunkRising, lossChunk, FadicGate.risingLevelLoss_eq]

end KoalaGateCheck
