import ProximityPrize.SubmissionLower.FadicDegree
import ProximityPrize.SubmissionLower.FadicChunk

-- merged module FadicNat
section Merged_FadicNat
set_option autoImplicit false
namespace FadicGate
open K1_13_2 (cappedCount cumulative denominator)
open scoped BigOperators
open Finset
def denomQR (q r : ℕ) : ℕ :=
  1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
def denomN (n : ℕ) : ℕ := denomQR (n / 6) (n % 6)
def denomSub (v k : ℕ) : ℕ := if k ≤ v then denomN (v - k) else 0
def cumAux (d v : ℕ) : ℕ :=
  (denomN v + denomSub v (2 * d + 3) + denomSub v (2 * d + 4) + denomSub v (2 * d + 5)) -
    (denomSub v (d + 1) + denomSub v (d + 2) + denomSub v (d + 3) + denomSub v (3 * d + 6))
def cumulativeN (d u : ℕ) : ℕ := cumAux d (min u (3 * d))
def cappedCountN (d u t : ℕ) : ℕ :=
  cumulativeN d u -
    (if 3 * (t + 1) ≤ u then (if t + 1 ≤ d then cumulativeN (d - (t + 1)) (u - 3 * (t + 1))
      else 0) else 0)
end FadicGate

end Merged_FadicNat

-- merged module FadicRaw
section Merged_FadicRaw
set_option autoImplicit false
namespace FadicGate
def rMin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b
def rMax (a b : ℕ) : ℕ := cond (Nat.ble a b) b a
def rDenomQR (q r : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add 1 (Nat.div (Nat.mul r (Nat.add r 1)) 2))
      (Nat.mul q (Nat.add (Nat.add 22 (Nat.mul 7 r)) (Nat.div (Nat.mul r (Nat.sub r 1)) 2))))
    (Nat.mul (Nat.add 57 (Nat.mul 6 r)) (Nat.div (Nat.mul q (Nat.sub q 1)) 2)))
    (Nat.mul (Nat.mul (Nat.mul 6 q) (Nat.sub q 1)) (Nat.sub q 2))
def rDenom (n : ℕ) : ℕ := rDenomQR (Nat.div n 6) (Nat.mod n 6)
def rDenomSub (v k : ℕ) : ℕ := cond (Nat.ble k v) (rDenom (Nat.sub v k)) 0
def rCumAux (d v : ℕ) : ℕ :=
  Nat.sub
    (Nat.add (Nat.add (Nat.add (rDenom v) (rDenomSub v (Nat.add (Nat.mul 2 d) 3)))
      (rDenomSub v (Nat.add (Nat.mul 2 d) 4))) (rDenomSub v (Nat.add (Nat.mul 2 d) 5)))
    (Nat.add (Nat.add (Nat.add (rDenomSub v (Nat.add d 1)) (rDenomSub v (Nat.add d 2)))
      (rDenomSub v (Nat.add d 3))) (rDenomSub v (Nat.add (Nat.mul 3 d) 6)))
def rCumulative (d u : ℕ) : ℕ := rCumAux d (rMin u (Nat.mul 3 d))
def rCapped (d u t : ℕ) : ℕ :=
  Nat.sub (rCumulative d u)
    (cond (Nat.ble (Nat.mul 3 (Nat.add t 1)) u)
      (cond (Nat.ble (Nat.add t 1) d)
        (rCumulative (Nat.sub d (Nat.add t 1)) (Nat.sub u (Nat.mul 3 (Nat.add t 1)))) 0) 0)
def rPrefix (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (rPrefix f n) (f n)
def rFlatLo (B J : ℕ) : ℕ := rMin J (Nat.add B 1)
def rFlatHi (B J Θ : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 25 J) Θ)
    (rMax (rFlatLo B J) (rMin (Nat.add B 1) (Nat.add (Nat.div (Nat.sub Θ (Nat.mul 25 J)) 26) 1)))
    (rFlatLo B J)
end FadicGate

end Merged_FadicRaw

-- merged module FadicChunkRaw
section Merged_FadicChunkRaw

/-!
# Kernel-raw evaluator of the chunked certificate
-/

set_option autoImplicit false

namespace FadicGate

def rSegLo (base h k : ℕ) : ℕ := Nat.add base (Nat.mul h k)
def rSegHi (base h m k : ℕ) : ℕ :=
  Nat.add base (rMin (Nat.sub (Nat.add (Nat.mul h k) h) 1) (Nat.sub m 1))

def rLowSegAux (J T Θ lo hi : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 26 hi) Θ)
    (rCapped (rMin lo (Nat.div (Nat.sub Θ (Nat.mul 26 hi)) 25)) J T) 0

def rHighSegAux (J T Θ lo hi : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 26 lo) Θ)
    (rCapped (rMin hi (Nat.div (Nat.sub Θ (Nat.mul 26 lo)) 25)) J T) 0

def rLowSeg (J T Θ base h m k : ℕ) : ℕ := rLowSegAux J T Θ (rSegLo base h k) (rSegHi base h m k)
def rHighSeg (J T Θ base h m k : ℕ) : ℕ := rHighSegAux J T Θ (rSegLo base h k) (rSegHi base h m k)

def rSegSumLow (J T Θ base h m : ℕ) : ℕ :=
  Nat.add (Nat.mul h (rPrefix (rLowSeg J T Θ base h m) (Nat.div m h)))
    (Nat.mul (Nat.mod m h) (rLowSeg J T Θ base h m (Nat.div m h)))

def rSegSumHigh (J T Θ base h m : ℕ) : ℕ :=
  Nat.add (Nat.mul h (rPrefix (rHighSeg J T Θ base h m) (Nat.div m h)))
    (Nat.mul (Nat.mod m h) (rHighSeg J T Θ base h m (Nat.div m h)))

def rFastLowAux (B J T Θ h lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rSegSumLow J T Θ 0 h lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rSegSumLow J T Θ hi h (Nat.sub (Nat.add B 1) hi))

def rFastHighAux (B J T Θ h lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rSegSumHigh J T Θ 0 h lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rSegSumHigh J T Θ hi h (Nat.sub (Nat.add B 1) hi))

def rFastLow (B J T Θ h : ℕ) : ℕ := rFastLowAux B J T Θ h (rFlatLo B J) (rFlatHi B J Θ)
def rFastHigh (B J T Θ h : ℕ) : ℕ := rFastHighAux B J T Θ h (rFlatLo B J) (rFlatHi B J Θ)







end FadicGate

end Merged_FadicChunkRaw

-- merged module FadicCast
section Merged_FadicCast
set_option autoImplicit false
namespace FadicGate
open K1_13_2 (cappedCount cumulative denominator)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
theorem cond_ble {α : Type*} (a b : ℕ) (x y : α) :
    cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · have hb : Nat.ble a b = true := Nat.ble_eq.mpr h
    rw [hb, if_pos h]
    rfl
  · have hb : Nat.ble a b = false := by
      cases hc : Nat.ble a b
      · rfl
      · exact absurd (Nat.ble_eq.mp hc) h
    rw [hb, if_neg h]
    rfl
theorem rMin_eq (a b : ℕ) : rMin a b = min a b := by
  unfold rMin
  rw [cond_ble]
  rfl
theorem rMax_eq (a b : ℕ) : rMax a b = max a b := by
  unfold rMax
  rw [cond_ble]
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right h]
  · rw [if_neg h, max_eq_left (by omega)]
theorem rDenomSub_eq (v k : ℕ) : rDenomSub v k = denomSub v k := by
  unfold rDenomSub denomSub
  rw [cond_ble]
  rfl
theorem rCumAux_eq (d v : ℕ) : rCumAux d v = cumAux d v := by
  unfold rCumAux cumAux
  simp only [rDenomSub_eq]
  rfl
theorem rCumulative_eq (d u : ℕ) : rCumulative d u = cumulativeN d u := by
  unfold rCumulative cumulativeN
  rw [rMin_eq, rCumAux_eq]
  rfl
theorem rCapped_eq (d u t : ℕ) : rCapped d u t = cappedCountN d u t := by
  unfold rCapped cappedCountN
  rw [cond_ble, cond_ble]
  simp only [rCumulative_eq]
  rfl
theorem denominator_neg {x : ℤ} (hx : x < 0) : denominator x = 0 := by
  unfold denominator
  simp [hx]
private theorem half_succ (r : ℕ) : ((r * (r + 1) / 2 : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) + 1) / 2 := by
  push_cast
  rfl
private theorem half_pred (r : ℕ) : ((r * (r - 1) / 2 : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) / 2 := by
  rcases r with _ | r
  · simp
  · have : r + 1 - 1 = r := by omega
    rw [this]
    push_cast
    ring_nf
private theorem cube_term (q : ℕ) :
    ((6 * q * (q - 1) * (q - 2) : ℕ) : ℤ) = 6 * (q : ℤ) * ((q : ℤ) - 1) * ((q : ℤ) - 2) := by
  rcases q with _ | _ | q
  · simp
  · simp
  · have h1 : q + 2 - 1 = q + 1 := by omega
    have h2 : q + 2 - 2 = q := by omega
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 ⊢
    rw [h1, h2]
    push_cast
    ring
theorem denomQR_cast (q r : ℕ) :
    ((denomQR q r : ℕ) : ℤ) =
      1 + (r : ℤ) * ((r : ℤ) + 1) / 2 +
        (q : ℤ) * (22 + 7 * (r : ℤ) + (r : ℤ) * ((r : ℤ) - 1) / 2) +
        (57 + 6 * (r : ℤ)) * ((q : ℤ) * ((q : ℤ) - 1) / 2) +
        6 * (q : ℤ) * ((q : ℤ) - 1) * ((q : ℤ) - 2) := by
  rw [← half_succ, ← half_pred, ← half_pred, ← cube_term]
  unfold denomQR
  push_cast
  ring
theorem denomN_cast (n : ℕ) : ((denomN n : ℕ) : ℤ) = denominator n := by
  unfold denomN denominator
  have h0 : ¬ ((n : ℤ) < 0) := by omega
  rw [if_neg h0]
  have hq : (n : ℤ) / 6 = ((n / 6 : ℕ) : ℤ) := by push_cast; rfl
  have hr : (n : ℤ) % 6 = ((n % 6 : ℕ) : ℤ) := by push_cast; rfl
  simp only [hq, hr]
  exact denomQR_cast (n / 6) (n % 6)
theorem denomSub_cast (v k : ℕ) : ((denomSub v k : ℕ) : ℤ) = denominator ((v : ℤ) - (k : ℤ)) := by
  unfold denomSub
  split
  · rename_i h
    rw [denomN_cast, Nat.cast_sub h]
  · rename_i h
    rw [denominator_neg (by omega)]
    rfl
private theorem cumulative_split (d u : ℕ) :
    cumulative d u =
      ((denomN (min u (3 * d)) + denomSub (min u (3 * d)) (2 * d + 3) +
          denomSub (min u (3 * d)) (2 * d + 4) + denomSub (min u (3 * d)) (2 * d + 5) : ℕ) : ℤ) -
      ((denomSub (min u (3 * d)) (d + 1) + denomSub (min u (3 * d)) (d + 2) +
          denomSub (min u (3 * d)) (d + 3) + denomSub (min u (3 * d)) (3 * d + 6) : ℕ) : ℤ) := by
  unfold cumulative
  have h1 : ¬ ((d : ℤ) < 0) := by omega
  have h2 : ¬ ((u : ℤ) < 0) := by omega
  have hv : min (u : ℤ) (3 * (d : ℤ)) = ((min u (3 * d) : ℕ) : ℤ) := by push_cast; rfl
  simp only [h1, h2, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hv]
  set V := min u (3 * d)
  push_cast
  rw [denomN_cast, denomSub_cast, denomSub_cast, denomSub_cast, denomSub_cast, denomSub_cast,
    denomSub_cast, denomSub_cast]
  push_cast
  ring_nf
theorem cumulative_nonneg (d u : ℤ) : 0 ≤ cumulative d u := by
  rw [← K1_13_2_2_2.proof d u]
  positivity
theorem cumulativeN_cast (d u : ℕ) : ((cumulativeN d u : ℕ) : ℤ) = cumulative d u := by
  have hs := cumulative_split d u
  have hn := cumulative_nonneg d u
  unfold cumulativeN cumAux
  rw [hs] at hn
  rw [hs, Nat.cast_sub (by exact_mod_cast (sub_nonneg.mp hn))]
theorem cumulative_of_neg {d u : ℤ} (h : d < 0 ∨ u < 0) : cumulative d u = 0 := by
  unfold cumulative
  rcases h with h | h <;> simp [h]
theorem cappedCountN_cast (d u t : ℕ) : ((cappedCountN d u t : ℕ) : ℤ) = cappedCount d u t := by
  have hcc : cappedCount d u t = cumulative d u -
      cumulative ((d : ℤ) - (t : ℤ) - 1) ((u : ℤ) - 3 * ((t : ℤ) + 1)) := by
    unfold cappedCount
    have ht : ¬ ((t : ℤ) < 0) := by omega
    rw [if_neg ht]
  have hsub : ((if 3 * (t + 1) ≤ u then (if t + 1 ≤ d then cumulativeN (d - (t + 1)) (u - 3 * (t + 1))
      else 0) else 0 : ℕ) : ℤ) = cumulative ((d : ℤ) - (t : ℤ) - 1) ((u : ℤ) - 3 * ((t : ℤ) + 1)) := by
    split
    · rename_i hu
      split
      · rename_i hd
        rw [cumulativeN_cast, Nat.cast_sub hd, Nat.cast_sub hu]
        push_cast
        ring_nf
      · rename_i hd
        rw [cumulative_of_neg (Or.inl (by omega))]
        rfl
    · rename_i hu
      rw [cumulative_of_neg (Or.inr (by omega))]
      rfl
  have hn := cappedCount_nonneg d u t
  unfold cappedCountN
  rw [hcc, ← cumulativeN_cast, ← hsub] at hn
  rw [Nat.cast_sub (by exact_mod_cast (sub_nonneg.mp hn)), cumulativeN_cast, hsub, hcc]
theorem rCapped_cast (d u t : ℕ) : ((rCapped d u t : ℕ) : ℤ) = cappedCount d u t := by
  rw [rCapped_eq, cappedCountN_cast]
theorem rPrefix_cast (f : ℕ → ℕ) (n : ℕ) : ((rPrefix f n : ℕ) : ℤ) = ∑ k ∈ range n, (f k : ℤ) := by
  induction n with
  | zero => simp [rPrefix]
  | succ n ih =>
    rw [rPrefix, sum_range_succ, ← ih]
    rfl
theorem rSegHi_eq (base h m k : ℕ) : rSegHi base h m k = segHi base h m k := by
  unfold rSegHi segHi
  rw [rMin_eq]
  rfl
theorem rLowSeg_cast (J T Θ base h m k : ℕ) :
    ((rLowSeg J T Θ base h m k : ℕ) : ℤ) = lowSeg J T Θ base h m k := by
  unfold rLowSeg rLowSegAux lowSeg lowDeg
  rw [cond_ble, rSegHi_eq, rMin_eq]
  show ((if 26 * segHi base h m k ≤ Θ then rCapped (min (segLo base h k) ((Θ - 26 * segHi base h m k) / 25)) J T else 0 : ℕ) : ℤ) = _
  by_cases hc : 26 * segHi base h m k ≤ Θ
  · rw [if_pos hc, if_pos hc, rCapped_cast]
  · rw [if_neg hc, if_neg hc]
    rfl
theorem rHighSeg_cast (J T Θ base h m k : ℕ) :
    ((rHighSeg J T Θ base h m k : ℕ) : ℤ) = highSeg J T Θ base h m k := by
  unfold rHighSeg rHighSegAux highSeg highDeg
  rw [cond_ble, rSegHi_eq, rMin_eq]
  show ((if 26 * segLo base h k ≤ Θ then rCapped (min (segHi base h m k) ((Θ - 26 * segLo base h k) / 25)) J T else 0 : ℕ) : ℤ) = _
  by_cases hc : 26 * segLo base h k ≤ Θ
  · rw [if_pos hc, if_pos hc, rCapped_cast]
  · rw [if_neg hc, if_neg hc]
    rfl
theorem rSegSumLow_cast (J T Θ base h m : ℕ) :
    ((rSegSumLow J T Θ base h m : ℕ) : ℤ) = segSumLow J T Θ base h m := by
  unfold rSegSumLow segSumLow
  show ((h * rPrefix (rLowSeg J T Θ base h m) (m / h) + (m % h) * rLowSeg J T Θ base h m (m / h) : ℕ)
    : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, rPrefix_cast, rLowSeg_cast]
  simp only [rLowSeg_cast]
theorem rSegSumHigh_cast (J T Θ base h m : ℕ) :
    ((rSegSumHigh J T Θ base h m : ℕ) : ℤ) = segSumHigh J T Θ base h m := by
  unfold rSegSumHigh segSumHigh
  show ((h * rPrefix (rHighSeg J T Θ base h m) (m / h) + (m % h) * rHighSeg J T Θ base h m (m / h) : ℕ)
    : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, rPrefix_cast, rHighSeg_cast]
  simp only [rHighSeg_cast]
theorem rFlatLo_eq (B J : ℕ) : rFlatLo B J = flatLo B J := by
  unfold rFlatLo flatLo
  rw [rMin_eq]
theorem rFlatHi_eq (B J Θ : ℕ) : rFlatHi B J Θ = flatHi B J Θ := by
  unfold rFlatHi flatHi
  rw [cond_ble, rMax_eq, rMin_eq, rFlatLo_eq]
  rfl
theorem rFastLow_cast (B J T Θ h : ℕ) : ((rFastLow B J T Θ h : ℕ) : ℤ) = fastLow B J T Θ h := by
  unfold rFastLow rFastLowAux fastLow
  rw [rFlatLo_eq, rFlatHi_eq]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  push_cast
  rw [rSegSumLow_cast, rSegSumLow_cast, rCapped_cast]
theorem rFastHigh_cast (B J T Θ h : ℕ) : ((rFastHigh B J T Θ h : ℕ) : ℤ) = fastHigh B J T Θ h := by
  unfold rFastHigh rFastHighAux fastHigh
  rw [rFlatLo_eq, rFlatHi_eq]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  push_cast
  rw [rSegSumHigh_cast, rSegSumHigh_cast, rCapped_cast]
theorem ble_true (a b : ℕ) : Nat.ble a b = true ↔ a ≤ b := by
  rw [Nat.ble_eq]
theorem natSub_cast (a b : ℕ) : ((a - b : ℕ) : ℤ) = max 0 ((a : ℤ) - (b : ℤ)) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_right (by omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega), max_eq_left (by omega)]
    rfl
end FadicGate
#print axioms FadicGate.rCapped_cast

end Merged_FadicCast

-- merged module FadicVarCert
section Merged_FadicVarCert
set_option autoImplicit false
namespace FadicGate
open K1_13_2 (cappedCount)
open scoped BigOperators
open Finset
def varMultHigh (h bl jl tl L B J T Θ : ℕ) : ℤ :=
  if bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ then fastHigh (B - bl) (J - jl) (T - tl) (Θ - L) h else 0
def varDepthLow (h bl bh jl jh tl L H a : ℕ) : Entry → ℤ
  | none => 0
  | some (B, J, T) =>
    if BoxOK bh jh H a B J then
      max 0 (fastLow B J T (varΘ H a) h - varMultHigh h bl jl tl L B J T (varΘ H a))
    else 0
theorem varMult_le (h bl jl tl L B J T Θ : ℕ) (hh : 0 < h) :
    varMult bl jl tl L B J T Θ ≤ varMultHigh h bl jl tl L B J T Θ := by
  unfold varMult varMultHigh
  split
  · exact le_fastHigh _ _ _ _ hh
  · exact le_rfl
theorem varDepthLow_le (h bl bh jl jh tl L H a : ℕ) (e : Entry) (hh : 0 < h) :
    varDepthLow h bl bh jl jh tl L H a e ≤ varDepthDim bl bh jl jh tl L H a e := by
  rcases e with _ | ⟨B, J, T⟩
  · exact le_rfl
  · simp only [varDepthLow, varDepthDim]
    split
    · apply max_le_max le_rfl
      have h1 := fastLow_le B J T (varΘ H a) hh
      have h2 := varMult_le h bl jl tl L B J T (varΘ H a) hh
      linarith
    · exact le_rfl
def varPlainLow (h B J T : ℕ) : ℤ := fastLow (min B 4012) (min J 1650) T 131312 h
theorem varPlainLow_le (h B J T : ℕ) (hh : 0 < h) : varPlainLow h B J T ≤ varPlainDim B J T :=
  fastLow_le _ _ _ _ hh
def varLevelLoss (S : ℤ) (h bl bh jl jh tl L H : ℕ) (plain : ℕ × ℕ × ℕ) (es : List Entry) : ℤ :=
  max 0 (S - max (varPlainLow h plain.1 plain.2.1 plain.2.2)
    (∑ a ∈ range es.length, varDepthLow h bl bh jl jh tl L H a (es.getD a none)))
def varCertLoss (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) : ℤ :=
  if Rt ≤ i + 1 then 0 else varLevelLoss S h bl bh jl jh tl L H (plain (i + 1)) (table (i + 1))
theorem gateLoss_le_varCertLoss (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) (hh : 0 < h) :
    max 0 (S - varGateDim S bl bh jl jh tl L H Rt plain (fun r => (table r).length)
      (fun r a => (table r).getD a none) (i + 1)) ≤
      varCertLoss S h bl bh jl jh tl L H Rt plain table i := by
  unfold varCertLoss varGateDim
  split
  · simp
  · unfold varLevelLoss
    apply max_le_max le_rfl
    have h1 := varPlainLow_le h (plain (i + 1)).1 (plain (i + 1)).2.1 (plain (i + 1)).2.2 hh
    have h2 : (∑ a ∈ range (table (i + 1)).length,
        varDepthLow h bl bh jl jh tl L H a ((table (i + 1)).getD a none)) ≤
        varFadicDim bl bh jl jh tl L H (table (i + 1)).length (fun a => (table (i + 1)).getD a none) :=
      sum_le_sum fun a _ => varDepthLow_le h bl bh jl jh tl L H a _ hh
    have h3 := max_le_max h1 h2
    linarith
theorem loss_of_varCert (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (Ltot : ℤ) (hh : 0 < h)
    (hsum : ∑ i ∈ range Rt, varCertLoss S h bl bh jl jh tl L H Rt plain table i = Ltot) (N : ℕ) :
    ∑ i ∈ range N, max 0 (S - varGateDim S bl bh jl jh tl L H Rt plain
      (fun r => (table r).length) (fun r a => (table r).getD a none) (i + 1)) ≤ Ltot := by
  have hzero (i : ℕ) (hi : Rt ≤ i) : varCertLoss S h bl bh jl jh tl L H Rt plain table i = 0 := by
    unfold varCertLoss
    exact if_pos (by omega)
  have hnonneg (i : ℕ) : 0 ≤ varCertLoss S h bl bh jl jh tl L H Rt plain table i := by
    unfold varCertLoss
    split
    · exact le_rfl
    · exact le_max_left _ _
  refine (sum_le_sum fun i _ =>
    gateLoss_le_varCertLoss S h bl bh jl jh tl L H Rt plain table i hh).trans ?_
  rw [← hsum]
  rcases le_total N Rt with hN | hN
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun i _ _ => hnonneg i)
  · rw [← sum_range_add_sum_Ico _ hN]
    have : ∑ i ∈ Ico Rt N, varCertLoss S h bl bh jl jh tl L H Rt plain table i = 0 :=
      sum_eq_zero fun i hi => hzero i (mem_Ico.mp hi).1
    rw [this, add_zero]
def rBoxOK (bh jh H a B J : ℕ) : Bool :=
  Nat.ble (Nat.add B (Nat.mul a bh)) 4012 && Nat.ble (Nat.add J (Nat.mul a jh)) 1650 &&
    Nat.ble (Nat.mul a H) 131312
def rVarMultHigh (h bl jl tl L B J T Θ : ℕ) : ℕ :=
  cond (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ)
    (rFastHigh (Nat.sub B bl) (Nat.sub J jl) (Nat.sub T tl) (Nat.sub Θ L) h) 0
def rVarDepthAux (h bl jl tl L B J T Θ : ℕ) : ℕ :=
  Nat.sub (rFastLow B J T Θ h) (rVarMultHigh h bl jl tl L B J T Θ)
def rVarDepthLow (h bl bh jl jh tl L H a : ℕ) : Entry → ℕ
  | none => 0
  | some (B, J, T) =>
    cond (rBoxOK bh jh H a B J)
      (rVarDepthAux h bl jl tl L B J T (Nat.sub 131312 (Nat.mul a H))) 0
def rVarList (h bl bh jl jh tl L H : ℕ) : ℕ → List Entry → ℕ
  | _, [] => 0
  | k, e :: es => Nat.add (rVarDepthLow h bl bh jl jh tl L H k e) (rVarList h bl bh jl jh tl L H (k + 1) es)
def rVarPlainLow (h B J T : ℕ) : ℕ := rFastLow (rMin B 4012) (rMin J 1650) T 131312 h
def rVarLevelLoss (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) : ℕ :=
  Nat.sub S (rMax (rVarPlainLow h pB pJ pT) (rVarList h bl bh jl jh tl L H 0 es))
theorem rBoxOK_iff (bh jh H a B J : ℕ) : rBoxOK bh jh H a B J = true ↔ BoxOK bh jh H a B J := by
  unfold rBoxOK BoxOK
  simp only [Bool.and_eq_true, ble_true, Nat.mul_eq, Nat.add_eq]
  tauto
theorem rVarMultHigh_cast (h bl jl tl L B J T Θ : ℕ) :
    ((rVarMultHigh h bl jl tl L B J T Θ : ℕ) : ℤ) = varMultHigh h bl jl tl L B J T Θ := by
  unfold rVarMultHigh varMultHigh
  by_cases hg : bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ
  · have hb : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ) = true := by
      simp only [Bool.and_eq_true, ble_true]
      exact ⟨⟨⟨hg.1, hg.2.1⟩, hg.2.2.1⟩, hg.2.2.2⟩
    rw [hb, if_pos hg]
    exact rFastHigh_cast _ _ _ _ _
  · have hb : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ) = false := by
      cases hc : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ)
      · rfl
      · simp only [Bool.and_eq_true, ble_true] at hc
        exact absurd ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩ hg
    rw [hb, if_neg hg]
    rfl
theorem rVarDepthLow_cast (h bl bh jl jh tl L H a : ℕ) (e : Entry) :
    ((rVarDepthLow h bl bh jl jh tl L H a e : ℕ) : ℤ) = varDepthLow h bl bh jl jh tl L H a e := by
  rcases e with _ | ⟨B, J, T⟩
  · rfl
  · simp only [rVarDepthLow, varDepthLow]
    by_cases hok : BoxOK bh jh H a B J
    · rw [(rBoxOK_iff bh jh H a B J).mpr hok, if_pos hok]
      show ((Nat.sub (rFastLow B J T (Nat.sub 131312 (Nat.mul a H)) h)
        (rVarMultHigh h bl jl tl L B J T (Nat.sub 131312 (Nat.mul a H))) : ℕ) : ℤ) = _
      rw [Nat.sub_eq, natSub_cast, rFastLow_cast, rVarMultHigh_cast]
      rfl
    · have hb : rBoxOK bh jh H a B J = false := by
        cases hc : rBoxOK bh jh H a B J
        · rfl
        · exact absurd ((rBoxOK_iff bh jh H a B J).mp hc) hok
      rw [hb, if_neg hok]
      rfl
theorem rVarList_cast (h bl bh jl jh tl L H : ℕ) (es : List Entry) (k : ℕ) :
    ((rVarList h bl bh jl jh tl L H k es : ℕ) : ℤ) =
      ∑ a ∈ range es.length, varDepthLow h bl bh jl jh tl L H (k + a) (es.getD a none) := by
  induction es generalizing k with
  | nil => simp [rVarList]
  | cons e es ih =>
    rw [rVarList, Nat.add_eq, Nat.cast_add, ih (k + 1), rVarDepthLow_cast, List.length_cons,
      sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    congr 1
    omega
theorem rVarPlainLow_cast (h B J T : ℕ) :
    ((rVarPlainLow h B J T : ℕ) : ℤ) = varPlainLow h B J T := by
  unfold rVarPlainLow varPlainLow
  rw [rMin_eq, rMin_eq, rFastLow_cast]
theorem rVarLevelLoss_cast (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) :
    ((rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es : ℕ) : ℤ) =
      varLevelLoss S h bl bh jl jh tl L H (pB, pJ, pT) es := by
  unfold rVarLevelLoss varLevelLoss
  rw [Nat.sub_eq, natSub_cast, rMax_eq, Nat.cast_max, rVarPlainLow_cast, rVarList_cast]
  simp only [zero_add]
theorem varCertLoss_row (S h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i pB pJ pT : ℕ) (es : List Entry) (v : ℕ)
    (hi : ¬ Rt ≤ i + 1) (hp : plain (i + 1) = (pB, pJ, pT)) (ht : table (i + 1) = es)
    (hv : rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es = v) :
    varCertLoss (S : ℤ) h bl bh jl jh tl L H Rt plain table i = (v : ℤ) := by
  unfold varCertLoss
  rw [if_neg hi, hp, ht, ← rVarLevelLoss_cast, hv]
theorem varCertLoss_terminal (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) (hi : Rt ≤ i + 1) :
    varCertLoss S h bl bh jl jh tl L H Rt plain table i = ((0 : ℕ) : ℤ) := by
  unfold varCertLoss
  rw [if_pos hi]
  rfl
end FadicGate
#print axioms FadicGate.loss_of_varCert
#print axioms FadicGate.rVarLevelLoss_cast

end Merged_FadicVarCert
