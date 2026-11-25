import ProximityPrize.SubmissionLower.FadicChunk

set_option Elab.async false

-- merged module FadicVarCert
section Merged_FadicVarCert
set_option Elab.async false

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

end Merged_FadicVarCert

-- merged module Final54W0
section Merged_Final54W0
set_option Elab.async false

set_option autoImplicit false
set_option maxRecDepth 100000

namespace FadicGate.Final54W0

open FadicGate

def lvl1 : List Entry := [some (68, 24, 6)]
def lvl2 : List Entry := [some (127, 50, 11), some (11, 2, 0)]
def lvl3 : List Entry := [some (199, 73, 18), some (99, 34, 8), some (11, 2, 0)]
def lvl4 : List Entry := [some (255, 99, 25), some (166, 64, 16), some (17, 5, 1), some (11, 2, 0)]
def lvl5 : List Entry := [some (322, 123, 32), some (245, 92, 23), some (145, 53, 13), some (17, 5, 1), some (11, 2, 0)]
def lvl6 : List Entry := [some (390, 147, 38), some (318, 118, 30), some (191, 72, 18), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl7 : List Entry := [some (457, 171, 45), some (378, 143, 38), some (281, 110, 27), some (151, 61, 14), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl8 : List Entry := [some (517, 196, 53), some (463, 167, 44), some (341, 129, 34), some (237, 91, 23), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl9 : List Entry := [some (596, 218, 59), some (507, 195, 52), some (418, 161, 43), some (293, 106, 27), some (168, 62, 15), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl10 : List Entry := [some (652, 244, 66), some (579, 218, 59), some (486, 184, 49), some (393, 150, 39), some (293, 106, 27), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl11 : List Entry := [some (712, 269, 74), some (652, 244, 66), some (557, 213, 58), some (455, 172, 45), some (331, 126, 31), some (174, 65, 15), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl12 : List Entry := [some (779, 293, 81), some (712, 269, 74), some (629, 236, 65), some (509, 195, 53), some (374, 145, 38), some (302, 117, 30), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl13 : List Entry := [some (839, 318, 89), some (779, 293, 81), some (702, 262, 72), some (621, 226, 61), some (494, 186, 50), some (374, 145, 38), some (179, 68, 17), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl14 : List Entry := [some (907, 342, 95), some (839, 318, 89), some (762, 287, 80), some (669, 253, 70), some (571, 217, 59), some (432, 162, 42), some (315, 119, 30), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl15 : List Entry := [some (974, 366, 102), some (907, 342, 95), some (835, 313, 87), some (731, 275, 76), some (627, 237, 65), some (482, 180, 48), some (432, 162, 42), some (187, 71, 17), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl16 : List Entry := [some (1034, 391, 110), some (974, 366, 102), some (895, 338, 95), some (808, 306, 85), some (696, 258, 70), some (584, 222, 60), some (482, 180, 48), some (327, 121, 31), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl17 : List Entry := [some (1113, 413, 116), some (1034, 391, 110), some (968, 364, 102), some (880, 329, 92), some (787, 295, 82), some (696, 258, 70), some (526, 197, 53), some (455, 173, 46), some (199, 73, 18), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl18 : List Entry := [some (1173, 438, 124), some (1113, 413, 116), some (1030, 386, 108), some (947, 353, 99), some (866, 317, 88), some (740, 280, 77), some (568, 216, 58), some (526, 197, 53), some (327, 125, 33), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl19 : List Entry := [some (1248, 461, 129), some (1173, 438, 124), some (1115, 410, 114), some (1026, 381, 106), some (910, 345, 96), some (806, 301, 84), some (688, 257, 70), some (568, 216, 58), some (461, 176, 46), some (195, 78, 19), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl20 : List Entry := [some (1296, 488, 138), some (1248, 461, 129), some (1163, 437, 123), some (1086, 406, 114), some (976, 366, 103), some (856, 325, 91), some (796, 300, 83), some (630, 232, 63), some (568, 216, 58), some (338, 127, 33), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl21 : List Entry := [some (1368, 511, 145), some (1296, 488, 138), some (1248, 461, 129), some (1136, 430, 121), some (1069, 400, 113), some (958, 361, 99), some (856, 325, 91), some (669, 252, 69), some (630, 232, 63), some (466, 179, 48), some (210, 79, 20), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl22 : List Entry := [some (1431, 536, 151), some (1368, 511, 145), some (1296, 488, 138), some (1219, 457, 129), some (1138, 421, 118), some (1038, 388, 109), some (912, 345, 97), some (777, 295, 82), some (669, 252, 69), some (606, 229, 62), some (346, 130, 33), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl23 : List Entry := [some (1495, 560, 160), some (1431, 536, 151), some (1368, 511, 145), some (1279, 482, 137), some (1186, 448, 127), some (1105, 412, 116), some (974, 367, 103), some (891, 335, 93), some (719, 270, 75), some (669, 252, 69), some (478, 181, 49), some (218, 82, 20), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl24 : List Entry := [some (1551, 586, 167), some (1495, 560, 160), some (1431, 536, 151), some (1358, 504, 143), some (1273, 469, 131), some (1155, 436, 123), some (1030, 387, 109), some (974, 367, 103), some (763, 287, 80), some (719, 270, 75), some (618, 231, 63), some (346, 134, 35), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl25 : List Entry := [some (1618, 610, 174), some (1551, 586, 167), some (1495, 560, 160), some (1412, 533, 152), some (1335, 502, 143), some (1217, 458, 129), some (1134, 425, 120), some (1030, 387, 109), some (875, 329, 91), some (763, 287, 80), some (719, 270, 75), some (486, 184, 49), some (223, 85, 22), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl26 : List Entry := [some (1690, 633, 181), some (1618, 610, 174), some (1551, 586, 167), some (1491, 555, 158), some (1400, 524, 147), some (1329, 489, 137), some (1217, 458, 129), some (1099, 408, 114), some (983, 372, 104), some (805, 306, 85), some (763, 287, 80), some (618, 235, 65), some (370, 134, 35), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl27 : List Entry := [some (1769, 655, 187), some (1690, 633, 181), some (1618, 610, 174), some (1547, 581, 165), some (1464, 548, 156), some (1375, 519, 148), some (1283, 479, 136), some (1153, 431, 122), some (1099, 408, 114), some (863, 323, 89), some (805, 306, 85), some (768, 283, 78), some (498, 186, 50), some (231, 88, 22), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl28 : List Entry := [some (1813, 683, 195), some (1769, 655, 187), some (1690, 633, 181), some (1636, 604, 172), some (1524, 573, 164), some (1449, 539, 153), some (1350, 503, 143), some (1205, 452, 127), some (1153, 431, 122), some (983, 364, 101), some (863, 323, 89), some (805, 306, 85), some (629, 237, 65), some (371, 138, 36), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl29 : List Entry := [some (1900, 704, 199), some (1813, 683, 195), some (1769, 655, 187), some (1680, 632, 180), some (1603, 601, 171), some (1516, 563, 160), some (1400, 527, 150), some (1321, 488, 137), some (1205, 452, 127), some (1091, 407, 114), some (925, 339, 94), some (863, 323, 89), some (769, 287, 79), some (497, 190, 51), some (243, 90, 23), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl30 : List Entry := [some (1952, 730, 209), some (1900, 704, 199), some (1813, 683, 195), some (1771, 652, 185), some (1678, 624, 176), some (1564, 590, 169), some (1462, 549, 156), some (1400, 527, 150), some (1259, 475, 135), some (1198, 448, 126), some (952, 361, 101), some (925, 339, 94), some (863, 323, 89), some (637, 240, 65), some (377, 141, 36), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl31 : List Entry := [some (2012, 755, 217), some (1952, 730, 209), some (1900, 704, 199), some (1813, 683, 195), some (1730, 650, 186), some (1659, 621, 177), some (1572, 583, 166), some (1462, 549, 156), some (1315, 495, 141), some (1259, 475, 135), some (1070, 400, 113), some (952, 361, 101), some (925, 339, 94), some (769, 291, 81), some (505, 193, 51), some (242, 94, 24), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1), some (11, 2, 0)]
def lvl32 : List Entry := [some (2083, 779, 221), some (2012, 755, 217), some (1952, 730, 209), some (1900, 704, 199), some (1802, 673, 193), some (1709, 645, 184), some (1626, 612, 175), some (1541, 571, 162), some (1377, 517, 147), some (1315, 495, 141), some (1170, 444, 125), some (996, 378, 106), some (952, 361, 101), some (909, 341, 95), some (649, 242, 66), some (382, 144, 38), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2), some (17, 5, 1)]
def lvl33 : List Entry := [some (2135, 805, 231), some (2083, 779, 221), some (2012, 755, 217), some (1952, 730, 209), some (1869, 703, 201), some (1788, 667, 190), some (1701, 635, 180), some (1591, 595, 169), some (1481, 555, 158), some (1377, 517, 147), some (1290, 485, 137), some (1054, 394, 111), some (996, 378, 106), some (952, 361, 101), some (777, 294, 81), some (510, 196, 53), some (250, 97, 24), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2), some (24, 8, 2)]
def lvl34 : List Entry := [some (2207, 828, 238), some (2135, 805, 231), some (2083, 779, 221), some (2012, 755, 217), some (1956, 724, 205), some (1848, 692, 198), some (1755, 658, 188), some (1645, 618, 177), some (1599, 588, 166), some (1442, 539, 151), some (1377, 517, 147), some (1162, 437, 124), some (1054, 394, 111), some (996, 378, 106), some (921, 343, 96), some (650, 246, 67), some (390, 147, 38), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3), some (32, 11, 2)]
def lvl35 : List Entry := [some (2286, 850, 244), some (2207, 828, 238), some (2135, 805, 231), some (2083, 779, 221), some (2010, 747, 213), some (1939, 712, 203), some (1815, 683, 196), some (1707, 640, 183), some (1645, 618, 177), some (1498, 559, 157), some (1442, 539, 151), some (1278, 479, 135), some (1100, 413, 116), some (1054, 394, 111), some (996, 378, 106), some (801, 294, 81), some (522, 198, 54), some (262, 99, 25), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4), some (44, 13, 3)]
def lvl36 : List Entry := [some (2334, 877, 253), some (2286, 850, 244), some (2207, 828, 238), some (2135, 805, 231), some (2058, 774, 222), some (2012, 744, 211), some (1890, 706, 201), some (1813, 675, 192), some (1707, 640, 183), some (1556, 581, 166), some (1498, 559, 157), some (1386, 522, 148), some (1162, 429, 121), some (1100, 413, 116), some (1054, 394, 111), some (920, 347, 97), some (662, 248, 68), some (402, 149, 39), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (55, 19, 5), some (43, 17, 4)]
def lvl37 : List Entry := [some (2421, 898, 257), some (2334, 877, 253), some (2286, 850, 244), some (2207, 828, 238), some (2141, 801, 230), some (2050, 770, 219), some (1977, 738, 211), some (1890, 706, 201), some (1786, 662, 189), some (1643, 619, 177), some (1556, 581, 166), some (1498, 559, 157), some (1262, 474, 132), some (1162, 429, 121), some (1100, 413, 116), some (1054, 394, 111), some (788, 300, 83), some (530, 201, 54), some (263, 103, 26), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (63, 22, 5), some (51, 20, 4)]
def lvl38 : List Entry := [some (2469, 925, 266), some (2421, 898, 257), some (2334, 877, 253), some (2286, 850, 244), some (2201, 826, 238), some (2114, 794, 228), some (2037, 763, 219), some (1944, 729, 209), some (1836, 686, 196), some (1747, 657, 188), some (1608, 602, 171), some (1556, 581, 166), some (1365, 515, 147), some (1201, 449, 127), some (1162, 429, 121), some (1100, 413, 116), some (932, 349, 98), some (680, 249, 67), some (410, 152, 39), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (69, 25, 6), some (52, 24, 5)]
def lvl39 : List Entry := [some (2529, 950, 274), some (2469, 925, 266), some (2421, 898, 257), some (2334, 877, 253), some (2288, 847, 242), some (2201, 815, 232), some (2108, 787, 223), some (2000, 755, 216), some (1886, 710, 203), some (1836, 686, 196), some (1662, 625, 179), some (1608, 602, 171), some (1477, 557, 158), some (1245, 466, 132), some (1201, 449, 127), some (1162, 429, 121), some (1060, 401, 113), some (812, 300, 83), some (541, 203, 54), some (275, 105, 27), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (76, 28, 7), some (52, 28, 7)]
def lvl40 : List Entry := [some (2604, 973, 279), some (2529, 950, 274), some (2469, 925, 266), some (2421, 898, 257), some (2324, 876, 252), some (2253, 841, 242), some (2164, 812, 234), some (2066, 776, 223), some (1952, 732, 210), some (1886, 710, 203), some (1724, 647, 185), some (1662, 625, 179), some (1616, 595, 168), some (1349, 509, 145), some (1245, 466, 132), some (1201, 449, 127), some (1162, 429, 121), some (940, 352, 98), some (673, 254, 70), some (413, 155, 41), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (87, 30, 7), some (52, 32, 9)]
def lvl41 : List Entry := [some (2656, 999, 289), some (2604, 973, 279), some (2529, 950, 274), some (2469, 925, 266), some (2421, 898, 257), some (2328, 870, 248), some (2232, 836, 240), some (2129, 801, 229), some (2058, 766, 219), some (1952, 732, 210), some (1834, 681, 195), some (1724, 647, 185), some (1662, 625, 179), some (1469, 550, 157), some (1287, 485, 137), some (1245, 466, 132), some (1201, 449, 127), some (1068, 404, 113), some (813, 304, 84), some (541, 207, 56), some (286, 107, 27), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (87, 34, 9), some (52, 36, 9)]
def lvl42 : List Entry := [some (2755, 1018, 292), some (2656, 999, 289), some (2604, 973, 279), some (2529, 950, 274), some (2469, 925, 266), some (2380, 896, 258), some (2297, 858, 244), some (2193, 825, 238), some (2129, 801, 229), some (2031, 753, 216), some (1915, 723, 207), some (1780, 667, 191), some (1724, 647, 185), some (1573, 594, 169), some (1337, 503, 143), some (1287, 485, 137), some (1245, 466, 132), some (1201, 449, 127), some (941, 356, 99), some (681, 257, 70), some (421, 158, 41), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (95, 37, 9), some (52, 40, 11)]
def lvl43 : List Entry := [some (2791, 1047, 302), some (2755, 1018, 292), some (2656, 999, 289), some (2604, 973, 279), some (2529, 950, 274), some (2448, 920, 264), some (2384, 890, 254), some (2288, 856, 246), some (2193, 825, 238), some (2081, 777, 223), some (2031, 753, 216), some (1861, 686, 195), some (1780, 667, 191), some (1693, 635, 181), some (1457, 544, 155), some (1337, 503, 143), some (1287, 485, 137), some (1245, 466, 132), some (1085, 405, 114), some (813, 308, 86), some (549, 210, 56), some (286, 111, 29), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (107, 39, 10), some (52, 44, 13)]
def lvl44 : List Entry := [some (2875, 1068, 308), some (2791, 1047, 302), some (2755, 1018, 292), some (2656, 999, 289), some (2604, 973, 279), some (2531, 941, 271), some (2436, 916, 264), some (2349, 884, 254), some (2286, 842, 241), some (2131, 801, 230), some (2081, 777, 223), some (1917, 706, 201), some (1861, 686, 195), some (1780, 667, 191), some (1565, 587, 168), some (1395, 520, 147), some (1337, 503, 143), some (1287, 485, 137), some (1211, 457, 129), some (953, 358, 100), some (693, 259, 71), some (426, 161, 43), some (158, 63, 16), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (108, 43, 11), some (52, 49, 11)]
def lvl45 : List Entry := [some (2942, 1092, 315), some (2875, 1068, 308), some (2791, 1047, 302), some (2755, 1018, 292), some (2656, 999, 289), some (2575, 969, 279), some (2498, 938, 270), some (2421, 907, 261), some (2318, 872, 250), some (2218, 822, 234), some (2131, 801, 230), some (1990, 749, 215), some (1917, 706, 201), some (1861, 686, 195), some (1691, 625, 178), some (1457, 536, 152), some (1395, 520, 147), some (1337, 503, 143), some (1287, 485, 137), some (1091, 408, 114), some (821, 311, 86), some (566, 211, 57), some (294, 114, 29), some (158, 63, 16), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (114, 46, 11), some (52, 52, 16)]
def lvl46 : List Entry := [some (2986, 1120, 323), some (2942, 1092, 315), some (2875, 1068, 308), some (2791, 1047, 302), some (2755, 1018, 292), some (2664, 992, 286), some (2589, 958, 275), some (2500, 929, 267), some (2384, 893, 257), some (2303, 857, 246), some (2218, 822, 234), some (2106, 785, 225), some (1955, 732, 209), some (1917, 706, 201), some (1795, 668, 191), some (1540, 581, 166), some (1457, 536, 152), some (1395, 520, 147), some (1337, 503, 143), some (1223, 459, 130), some (952, 362, 101), some (694, 263, 72), some (434, 164, 43), some (171, 65, 16), some (158, 63, 16), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (127, 48, 11), some (52, 52, 17)]
def lvl47 : List Entry := [some (3073, 1141, 327), some (2986, 1120, 323), some (2942, 1092, 315), some (2875, 1068, 308), some (2791, 1047, 302), some (2708, 1020, 294), some (2625, 987, 285), some (2550, 953, 274), some (2471, 914, 261), some (2384, 893, 257), some (2272, 845, 242), some (2197, 822, 237), some (2009, 755, 217), some (1955, 732, 209), some (1917, 706, 201), some (1656, 622, 178), some (1478, 557, 158), some (1457, 536, 152), some (1395, 520, 147), some (1337, 503, 143), some (1115, 408, 114), some (836, 312, 87), some (566, 215, 59), some (306, 116, 30), some (171, 65, 16), some (158, 63, 16), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (139, 50, 12), some (52, 52, 17)]
def lvl48 : List Entry := [some (3125, 1167, 337), some (3073, 1141, 327), some (2986, 1120, 323), some (2942, 1092, 315), some (2875, 1068, 308), some (2795, 1041, 298), some (2697, 1010, 292), some (2610, 978, 282), some (2523, 940, 271), some (2471, 914, 261), some (2310, 871, 250), some (2272, 845, 242), some (2065, 775, 223), some (2009, 755, 217), some (1955, 732, 209), some (1776, 663, 190), some (1524, 575, 164), some (1478, 557, 158), some (1457, 536, 152), some (1395, 520, 147), some (1243, 460, 129), some (964, 364, 102), some (704, 265, 73), some (446, 166, 44), some (179, 68, 16), some (171, 65, 16), some (158, 63, 16), some (158, 59, 14), some (147, 57, 14), some (139, 54, 14), some (52, 52, 17)]
def lvl49 : List Entry := [some (3185, 1192, 345), some (3125, 1167, 337), some (3073, 1141, 327), some (2986, 1120, 323), some (2942, 1092, 315), some (2847, 1067, 308), some (2774, 1041, 301), some (2689, 1000, 288), some (2594, 975, 281), some (2523, 940, 271), some (2376, 892, 257), some (2310, 871, 250), some (2173, 813, 231), some (2065, 775, 223), some (2009, 755, 217), some (1880, 707, 202), some (1644, 616, 176), some (1524, 575, 164), some (1478, 557, 158), some (1457, 536, 152), some (1340, 517, 147), some (1104, 414, 116), some (832, 317, 88), some (577, 217, 59), some (307, 120, 31), some (179, 68, 16), some (171, 65, 16), some (158, 63, 16), some (158, 59, 14), some (147, 57, 14), some (52, 52, 17)]
def lvl50 : List Entry := [some (3256, 1216, 349), some (3185, 1192, 345), some (3125, 1167, 337), some (3073, 1141, 327), some (2986, 1120, 323), some (2907, 1092, 316), some (2849, 1064, 306), some (2772, 1033, 297), some (2689, 1000, 288), some (2573, 964, 278), some (2463, 913, 261), some (2376, 892, 257), some (2268, 849, 244), some (2127, 797, 229), some (2061, 776, 222), some (1960, 755, 216), some (1752, 659, 189), some (1570, 594, 169), some (1524, 575, 164), some (1466, 559, 159), some (1366, 552, 156), some (1220, 468, 132), some (976, 366, 103), some (724, 266, 72), some (445, 170, 45), some (191, 70, 17), some (179, 68, 16), some (171, 65, 16), some (158, 63, 16), some (158, 59, 14), some (52, 52, 17)]
def lvl51 : List Entry := [some (3308, 1242, 359), some (3256, 1216, 349), some (3185, 1192, 345), some (3125, 1167, 337), some (3073, 1141, 327), some (2986, 1120, 323), some (2897, 1091, 315), some (2820, 1060, 306), some (2737, 1027, 297), some (2633, 989, 286), some (2548, 948, 273), some (2432, 918, 264), some (2325, 895, 258), some (2171, 819, 236), some (2079, 806, 229), some (1974, 791, 227), some (1844, 705, 202), some (1632, 610, 174), some (1570, 594, 169), some (1473, 584, 166), some (1363, 577, 164), some (1240, 537, 159), some (1088, 421, 118), some (852, 318, 87), some (585, 220, 59), some (317, 122, 32), some (191, 70, 17), some (179, 68, 16), some (171, 65, 16), some (158, 63, 16), some (52, 52, 17)]
def lvl52 : List Entry := [some (3411, 1260, 363), some (3308, 1242, 359), some (3256, 1216, 349), some (3185, 1192, 345), some (3125, 1167, 337), some (3073, 1141, 327), some (2963, 1112, 322), some (2911, 1080, 311), some (2787, 1051, 304), some (2679, 1014, 292), some (2597, 990, 284), some (2446, 948, 274), some (2345, 933, 269), some (2205, 846, 243), some (2092, 833, 239), some (1977, 823, 237), some (1848, 764, 219), some (1717, 657, 188), some (1597, 616, 176), some (1483, 609, 174), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (973, 371, 103), some (717, 271, 75), some (457, 172, 46), some (190, 74, 18), some (191, 70, 17), some (179, 68, 16), some (171, 65, 16), some (52, 52, 17)]
def lvl53 : List Entry := [some (3443, 1290, 372), some (3411, 1260, 363), some (3308, 1242, 359), some (3256, 1216, 349), some (3185, 1192, 345), some (3125, 1167, 337), some (3034, 1136, 326), some (2943, 1110, 320), some (2815, 1082, 312), some (2699, 1046, 302), some (2592, 1029, 297), some (2464, 978, 281), some (2343, 966, 279), some (2230, 898, 257), some (2102, 864, 248), some (1977, 853, 245), some (1900, 802, 267), some (1728, 715, 204), some (1603, 642, 183), some (1482, 636, 182), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (841, 324, 89), some (585, 224, 61), some (337, 123, 31), some (190, 74, 18), some (191, 70, 17), some (179, 68, 16), some (52, 52, 17)]
def lvl54 : List Entry := [some (3507, 1314, 381), some (3443, 1290, 372), some (3411, 1260, 363), some (3308, 1242, 359), some (3256, 1216, 349), some (3157, 1197, 346), some (3070, 1165, 336), some (2946, 1142, 330), some (2835, 1114, 322), some (2707, 1080, 313), some (2596, 1064, 307), some (2476, 1012, 289), some (2342, 999, 288), some (2222, 952, 275), some (2093, 898, 259), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1600, 667, 191), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (709, 277, 75), some (465, 175, 46), some (202, 76, 19), some (190, 74, 18), some (179, 72, 18), some (52, 52, 17)]
def lvl55 : List Entry := [some (3594, 1335, 385), some (3507, 1314, 381), some (3443, 1290, 372), some (3380, 1265, 366), some (3288, 1246, 358), some (3189, 1227, 355), some (3074, 1206, 347), some (2954, 1176, 341), some (2851, 1147, 331), some (2715, 1126, 326), some (2600, 1099, 317), some (2471, 1045, 301), some (2428, 1014, 316), some (2296, 961, 320), some (2164, 908, 293), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (578, 229, 64), some (338, 127, 32), some (202, 76, 19), some (183, 75, 19), some (52, 52, 17)]
def lvl56 : List Entry := [some (3642, 1362, 394), some (3594, 1335, 385), some (3507, 1314, 381), some (3412, 1295, 375), some (3320, 1276, 367), some (3201, 1261, 363), some (3079, 1240, 360), some (2966, 1210, 349), some (2836, 1185, 343), some (2717, 1170, 339), some (2659, 1120, 329), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (446, 182, 50), some (210, 79, 19), some (184, 79, 20), some (52, 52, 17)]
def lvl57 : List Entry := [some (3702, 1387, 402), some (3626, 1365, 394), some (3539, 1344, 390), some (3428, 1328, 384), some (3325, 1310, 380), some (3206, 1295, 376), some (3083, 1275, 370), some (2968, 1254, 362), some (2854, 1226, 356), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (315, 135, 35), some (182, 84, 20), some (52, 52, 17)]
def lvl58 : List Entry := [some (3777, 1410, 407), some (3658, 1395, 403), some (3555, 1377, 399), some (3448, 1360, 394), some (3329, 1345, 390), some (3210, 1330, 386), some (3083, 1311, 379), some (3024, 1279, 373), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (183, 88, 21), some (52, 52, 17)]
def lvl59 : List Entry := [some (3809, 1440, 416), some (3690, 1425, 412), some (3571, 1410, 408), some (3448, 1396, 403), some (3329, 1381, 399), some (3210, 1366, 395), some (3159, 1332, 391), some (3088, 1279, 426), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (184, 113, 37), some (52, 52, 17)]
def lvl60 : List Entry := [some (3821, 1474, 424), some (3718, 1456, 420), some (3579, 1445, 415), some (3460, 1430, 411), some (3342, 1414, 410), some (3298, 1385, 406), some (3220, 1332, 444), some (3088, 1279, 426), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (184, 113, 37), some (52, 52, 17)]
def lvl61 : List Entry := [some (3814, 1510, 438), some (3695, 1495, 434), some (3576, 1480, 430), some (3457, 1465, 426), some (3402, 1438, 422), some (3352, 1385, 461), some (3220, 1332, 444), some (3088, 1279, 426), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (184, 113, 37), some (52, 52, 17)]
def lvl62 : List Entry := [some (3818, 1545, 448), some (3699, 1530, 444), some (3576, 1516, 439), some (3509, 1491, 436), some (3484, 1438, 479), some (3352, 1385, 461), some (3220, 1332, 444), some (3088, 1279, 426), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (184, 113, 37), some (52, 52, 17)]
def lvl63 : List Entry := [some (3830, 1579, 456), some (3707, 1565, 451), some (3620, 1544, 447), some (3616, 1491, 497), some (3484, 1438, 479), some (3352, 1385, 461), some (3220, 1332, 444), some (3088, 1279, 426), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (184, 113, 37), some (52, 52, 17)]
def lvl64 : List Entry := [some (3831, 1614, 468), some (3720, 1597, 466), some (3748, 1544, 503), some (3616, 1491, 497), some (3484, 1438, 479), some (3352, 1385, 461), some (3220, 1332, 444), some (3088, 1279, 426), some (2956, 1226, 408), some (2824, 1173, 391), some (2692, 1120, 373), some (2560, 1067, 355), some (2428, 1014, 338), some (2296, 961, 320), some (2164, 908, 302), some (2032, 855, 285), some (1900, 802, 267), some (1768, 749, 249), some (1636, 696, 232), some (1504, 643, 214), some (1372, 590, 196), some (1240, 537, 179), some (1108, 484, 161), some (976, 431, 143), some (844, 378, 126), some (712, 325, 108), some (580, 272, 90), some (448, 219, 73), some (316, 166, 55), some (184, 113, 37), some (52, 52, 17)]
def lvl65 : List Entry := []
def lvl66 : List Entry := []

def boxes : ℕ → List Entry
  | 1 => lvl1
  | 2 => lvl2
  | 3 => lvl3
  | 4 => lvl4
  | 5 => lvl5
  | 6 => lvl6
  | 7 => lvl7
  | 8 => lvl8
  | 9 => lvl9
  | 10 => lvl10
  | 11 => lvl11
  | 12 => lvl12
  | 13 => lvl13
  | 14 => lvl14
  | 15 => lvl15
  | 16 => lvl16
  | 17 => lvl17
  | 18 => lvl18
  | 19 => lvl19
  | 20 => lvl20
  | 21 => lvl21
  | 22 => lvl22
  | 23 => lvl23
  | 24 => lvl24
  | 25 => lvl25
  | 26 => lvl26
  | 27 => lvl27
  | 28 => lvl28
  | 29 => lvl29
  | 30 => lvl30
  | 31 => lvl31
  | 32 => lvl32
  | 33 => lvl33
  | 34 => lvl34
  | 35 => lvl35
  | 36 => lvl36
  | 37 => lvl37
  | 38 => lvl38
  | 39 => lvl39
  | 40 => lvl40
  | 41 => lvl41
  | 42 => lvl42
  | 43 => lvl43
  | 44 => lvl44
  | 45 => lvl45
  | 46 => lvl46
  | 47 => lvl47
  | 48 => lvl48
  | 49 => lvl49
  | 50 => lvl50
  | 51 => lvl51
  | 52 => lvl52
  | 53 => lvl53
  | 54 => lvl54
  | 55 => lvl55
  | 56 => lvl56
  | 57 => lvl57
  | 58 => lvl58
  | 59 => lvl59
  | 60 => lvl60
  | 61 => lvl61
  | 62 => lvl62
  | 63 => lvl63
  | 64 => lvl64
  | 65 => lvl65
  | 66 => lvl66
  | _ => []

def plainT : ℕ → ℕ × ℕ × ℕ
  | 65 => (3926, 1640, 446)
  | 66 => (4012, 1629, 543)
  | _ => (0, 0, 0)

def terminal : ℕ := 67

private abbrev lossAt := varCertLoss ((((406807694511 : ℕ)) : ℤ)) 8 106 132 48 53 4 2756 4257 67 plainT boxes
private abbrev verifyLevel := varCertLoss_row 406807694511 8 106 132 48 53 4 2756 4257 67 plainT boxes

theorem row0 : lossAt 0 = ((406807663671 : ℕ) : ℤ) :=
  verifyLevel 0 0 0 0 lvl1 406807663671
    (by decide) rfl rfl (by decide +kernel)
theorem row1 : lossAt 1 = ((406807278985 : ℕ) : ℤ) :=
  verifyLevel 1 0 0 0 lvl2 406807278985
    (by decide) rfl rfl (by decide +kernel)
theorem row2 : lossAt 2 = ((406805643603 : ℕ) : ℤ) :=
  verifyLevel 2 0 0 0 lvl3 406805643603
    (by decide) rfl rfl (by decide +kernel)
theorem row3 : lossAt 3 = ((406801060085 : ℕ) : ℤ) :=
  verifyLevel 3 0 0 0 lvl4 406801060085
    (by decide) rfl rfl (by decide +kernel)
theorem row4 : lossAt 4 = ((406790582836 : ℕ) : ℤ) :=
  verifyLevel 4 0 0 0 lvl5 406790582836
    (by decide) rfl rfl (by decide +kernel)
theorem row5 : lossAt 5 = ((406772417670 : ℕ) : ℤ) :=
  verifyLevel 5 0 0 0 lvl6 406772417670
    (by decide) rfl rfl (by decide +kernel)
theorem row6 : lossAt 6 = ((406740115449 : ℕ) : ℤ) :=
  verifyLevel 6 0 0 0 lvl7 406740115449
    (by decide) rfl rfl (by decide +kernel)
theorem row7 : lossAt 7 = ((406692979018 : ℕ) : ℤ) :=
  verifyLevel 7 0 0 0 lvl8 406692979018
    (by decide) rfl rfl (by decide +kernel)
theorem row8 : lossAt 8 = ((406623806237 : ℕ) : ℤ) :=
  verifyLevel 8 0 0 0 lvl9 406623806237
    (by decide) rfl rfl (by decide +kernel)
theorem row9 : lossAt 9 = ((406519760478 : ℕ) : ℤ) :=
  verifyLevel 9 0 0 0 lvl10 406519760478
    (by decide) rfl rfl (by decide +kernel)
theorem row10 : lossAt 10 = ((406386581021 : ℕ) : ℤ) :=
  verifyLevel 10 0 0 0 lvl11 406386581021
    (by decide) rfl rfl (by decide +kernel)
theorem row11 : lossAt 11 = ((406218923425 : ℕ) : ℤ) :=
  verifyLevel 11 0 0 0 lvl12 406218923425
    (by decide) rfl rfl (by decide +kernel)
theorem row12 : lossAt 12 = ((405972298907 : ℕ) : ℤ) :=
  verifyLevel 12 0 0 0 lvl13 405972298907
    (by decide) rfl rfl (by decide +kernel)
theorem row13 : lossAt 13 = ((405689133043 : ℕ) : ℤ) :=
  verifyLevel 13 0 0 0 lvl14 405689133043
    (by decide) rfl rfl (by decide +kernel)
theorem row14 : lossAt 14 = ((405349316399 : ℕ) : ℤ) :=
  verifyLevel 14 0 0 0 lvl15 405349316399
    (by decide) rfl rfl (by decide +kernel)
theorem row15 : lossAt 15 = ((404907477751 : ℕ) : ℤ) :=
  verifyLevel 15 0 0 0 lvl16 404907477751
    (by decide) rfl rfl (by decide +kernel)
theorem row16 : lossAt 16 = ((404342094980 : ℕ) : ℤ) :=
  verifyLevel 16 0 0 0 lvl17 404342094980
    (by decide) rfl rfl (by decide +kernel)
theorem row17 : lossAt 17 = ((403760362568 : ℕ) : ℤ) :=
  verifyLevel 17 0 0 0 lvl18 403760362568
    (by decide) rfl rfl (by decide +kernel)
theorem row18 : lossAt 18 = ((403000180456 : ℕ) : ℤ) :=
  verifyLevel 18 0 0 0 lvl19 403000180456
    (by decide) rfl rfl (by decide +kernel)
theorem row19 : lossAt 19 = ((402133717899 : ℕ) : ℤ) :=
  verifyLevel 19 0 0 0 lvl20 402133717899
    (by decide) rfl rfl (by decide +kernel)
theorem row20 : lossAt 20 = ((401087944559 : ℕ) : ℤ) :=
  verifyLevel 20 0 0 0 lvl21 401087944559
    (by decide) rfl rfl (by decide +kernel)
theorem row21 : lossAt 21 = ((399894008550 : ℕ) : ℤ) :=
  verifyLevel 21 0 0 0 lvl22 399894008550
    (by decide) rfl rfl (by decide +kernel)
theorem row22 : lossAt 22 = ((398574101583 : ℕ) : ℤ) :=
  verifyLevel 22 0 0 0 lvl23 398574101583
    (by decide) rfl rfl (by decide +kernel)
theorem row23 : lossAt 23 = ((397118034995 : ℕ) : ℤ) :=
  verifyLevel 23 0 0 0 lvl24 397118034995
    (by decide) rfl rfl (by decide +kernel)
theorem row24 : lossAt 24 = ((395306266911 : ℕ) : ℤ) :=
  verifyLevel 24 0 0 0 lvl25 395306266911
    (by decide) rfl rfl (by decide +kernel)
theorem row25 : lossAt 25 = ((393289289504 : ℕ) : ℤ) :=
  verifyLevel 25 0 0 0 lvl26 393289289504
    (by decide) rfl rfl (by decide +kernel)
theorem row26 : lossAt 26 = ((391112278165 : ℕ) : ℤ) :=
  verifyLevel 26 0 0 0 lvl27 391112278165
    (by decide) rfl rfl (by decide +kernel)
theorem row27 : lossAt 27 = ((388741554242 : ℕ) : ℤ) :=
  verifyLevel 27 0 0 0 lvl28 388741554242
    (by decide) rfl rfl (by decide +kernel)
theorem row28 : lossAt 28 = ((385945623339 : ℕ) : ℤ) :=
  verifyLevel 28 0 0 0 lvl29 385945623339
    (by decide) rfl rfl (by decide +kernel)
theorem row29 : lossAt 29 = ((382889877330 : ℕ) : ℤ) :=
  verifyLevel 29 0 0 0 lvl30 382889877330
    (by decide) rfl rfl (by decide +kernel)
theorem row30 : lossAt 30 = ((379409591517 : ℕ) : ℤ) :=
  verifyLevel 30 0 0 0 lvl31 379409591517
    (by decide) rfl rfl (by decide +kernel)
theorem row31 : lossAt 31 = ((375791878635 : ℕ) : ℤ) :=
  verifyLevel 31 0 0 0 lvl32 375791878635
    (by decide) rfl rfl (by decide +kernel)
theorem row32 : lossAt 32 = ((371688899405 : ℕ) : ℤ) :=
  verifyLevel 32 0 0 0 lvl33 371688899405
    (by decide) rfl rfl (by decide +kernel)
theorem row33 : lossAt 33 = ((367204033193 : ℕ) : ℤ) :=
  verifyLevel 33 0 0 0 lvl34 367204033193
    (by decide) rfl rfl (by decide +kernel)
theorem row34 : lossAt 34 = ((362527785133 : ℕ) : ℤ) :=
  verifyLevel 34 0 0 0 lvl35 362527785133
    (by decide) rfl rfl (by decide +kernel)
theorem row35 : lossAt 35 = ((357178721331 : ℕ) : ℤ) :=
  verifyLevel 35 0 0 0 lvl36 357178721331
    (by decide) rfl rfl (by decide +kernel)
theorem row36 : lossAt 36 = ((351005825524 : ℕ) : ℤ) :=
  verifyLevel 36 0 0 0 lvl37 351005825524
    (by decide) rfl rfl (by decide +kernel)
theorem row37 : lossAt 37 = ((344877215295 : ℕ) : ℤ) :=
  verifyLevel 37 0 0 0 lvl38 344877215295
    (by decide) rfl rfl (by decide +kernel)
theorem row38 : lossAt 38 = ((338262711775 : ℕ) : ℤ) :=
  verifyLevel 38 0 0 0 lvl39 338262711775
    (by decide) rfl rfl (by decide +kernel)
theorem row39 : lossAt 39 = ((331109622415 : ℕ) : ℤ) :=
  verifyLevel 39 0 0 0 lvl40 331109622415
    (by decide) rfl rfl (by decide +kernel)
theorem row40 : lossAt 40 = ((322971720421 : ℕ) : ℤ) :=
  verifyLevel 40 0 0 0 lvl41 322971720421
    (by decide) rfl rfl (by decide +kernel)
theorem row41 : lossAt 41 = ((314429541941 : ℕ) : ℤ) :=
  verifyLevel 41 0 0 0 lvl42 314429541941
    (by decide) rfl rfl (by decide +kernel)
theorem row42 : lossAt 42 = ((304971693166 : ℕ) : ℤ) :=
  verifyLevel 42 0 0 0 lvl43 304971693166
    (by decide) rfl rfl (by decide +kernel)
theorem row43 : lossAt 43 = ((295459530041 : ℕ) : ℤ) :=
  verifyLevel 43 0 0 0 lvl44 295459530041
    (by decide) rfl rfl (by decide +kernel)
theorem row44 : lossAt 44 = ((285264882421 : ℕ) : ℤ) :=
  verifyLevel 44 0 0 0 lvl45 285264882421
    (by decide) rfl rfl (by decide +kernel)
theorem row45 : lossAt 45 = ((273781479782 : ℕ) : ℤ) :=
  verifyLevel 45 0 0 0 lvl46 273781479782
    (by decide) rfl rfl (by decide +kernel)
theorem row46 : lossAt 46 = ((261586274143 : ℕ) : ℤ) :=
  verifyLevel 46 0 0 0 lvl47 261586274143
    (by decide) rfl rfl (by decide +kernel)
theorem row47 : lossAt 47 = ((249459922345 : ℕ) : ℤ) :=
  verifyLevel 47 0 0 0 lvl48 249459922345
    (by decide) rfl rfl (by decide +kernel)
theorem row48 : lossAt 48 = ((235512426022 : ℕ) : ℤ) :=
  verifyLevel 48 0 0 0 lvl49 235512426022
    (by decide) rfl rfl (by decide +kernel)
theorem row49 : lossAt 49 = ((220853347186 : ℕ) : ℤ) :=
  verifyLevel 49 0 0 0 lvl50 220853347186
    (by decide) rfl rfl (by decide +kernel)
theorem row50 : lossAt 50 = ((205405587461 : ℕ) : ℤ) :=
  verifyLevel 50 0 0 0 lvl51 205405587461
    (by decide) rfl rfl (by decide +kernel)
theorem row51 : lossAt 51 = ((189949959150 : ℕ) : ℤ) :=
  verifyLevel 51 0 0 0 lvl52 189949959150
    (by decide) rfl rfl (by decide +kernel)
theorem row52 : lossAt 52 = ((174092564460 : ℕ) : ℤ) :=
  verifyLevel 52 0 0 0 lvl53 174092564460
    (by decide) rfl rfl (by decide +kernel)
theorem row53 : lossAt 53 = ((158951961528 : ℕ) : ℤ) :=
  verifyLevel 53 0 0 0 lvl54 158951961528
    (by decide) rfl rfl (by decide +kernel)
theorem row54 : lossAt 54 = ((144124734478 : ℕ) : ℤ) :=
  verifyLevel 54 0 0 0 lvl55 144124734478
    (by decide) rfl rfl (by decide +kernel)
theorem row55 : lossAt 55 = ((130797780671 : ℕ) : ℤ) :=
  verifyLevel 55 0 0 0 lvl56 130797780671
    (by decide) rfl rfl (by decide +kernel)
theorem row56 : lossAt 56 = ((118538078623 : ℕ) : ℤ) :=
  verifyLevel 56 0 0 0 lvl57 118538078623
    (by decide) rfl rfl (by decide +kernel)
theorem row57 : lossAt 57 = ((107720548141 : ℕ) : ℤ) :=
  verifyLevel 57 0 0 0 lvl58 107720548141
    (by decide) rfl rfl (by decide +kernel)
theorem row58 : lossAt 58 = ((97885617934 : ℕ) : ℤ) :=
  verifyLevel 58 0 0 0 lvl59 97885617934
    (by decide) rfl rfl (by decide +kernel)
theorem row59 : lossAt 59 = ((89013060835 : ℕ) : ℤ) :=
  verifyLevel 59 0 0 0 lvl60 89013060835
    (by decide) rfl rfl (by decide +kernel)
theorem row60 : lossAt 60 = ((81196602173 : ℕ) : ℤ) :=
  verifyLevel 60 0 0 0 lvl61 81196602173
    (by decide) rfl rfl (by decide +kernel)
theorem row61 : lossAt 61 = ((74370949404 : ℕ) : ℤ) :=
  verifyLevel 61 0 0 0 lvl62 74370949404
    (by decide) rfl rfl (by decide +kernel)
theorem row62 : lossAt 62 = ((68644384832 : ℕ) : ℤ) :=
  verifyLevel 62 0 0 0 lvl63 68644384832
    (by decide) rfl rfl (by decide +kernel)
theorem row63 : lossAt 63 = ((64120844253 : ℕ) : ℤ) :=
  verifyLevel 63 0 0 0 lvl64 64120844253
    (by decide) rfl rfl (by decide +kernel)
theorem row64 : lossAt 64 = ((19296523259 : ℕ) : ℤ) :=
  verifyLevel 64 3926 1640 446 lvl65 19296523259
    (by decide) rfl rfl (by decide +kernel)
theorem row65 : lossAt 65 = ((14395312325 : ℕ) : ℤ) :=
  verifyLevel 65 4012 1629 543 lvl66 14395312325
    (by decide) rfl rfl (by decide +kernel)
theorem row66 : lossAt 66 = ((0 : ℕ) : ℤ) :=
  varCertLoss_terminal _ 8 106 132 48 53 4 2756 4257 67 plainT boxes 66 (by decide)

theorem total : ∑ i ∈ Finset.range 67, lossAt i = ((20130931984877 : ℕ) : ℤ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66]
  norm_num

/-- Variable gate loss for tilted group 0: grade [106, 132], index [48, 53], top >= 4, taper [2756, 4257], terminal level 67, blocks of 8 grades. -/
theorem loss (N : ℕ) :
    ∑ i ∈ Finset.range N, max 0 ((((406807694511 : ℕ)) : ℤ) - varGateDim ((((406807694511 : ℕ)) : ℤ)) 106 132 48 53 4 2756 4257 67 plainT
      (fun r => (boxes r).length) (fun r a => (boxes r).getD a none) (i + 1)) ≤ ((20130931984877 : ℕ) : ℤ) :=
  loss_of_varCert ((((406807694511 : ℕ)) : ℤ)) 8 106 132 48 53 4 2756 4257 67 plainT boxes ((20130931984877 : ℕ) : ℤ) (by norm_num) total N

end FadicGate.Final54W0

#print axioms FadicGate.Final54W0.loss

end Merged_Final54W0
