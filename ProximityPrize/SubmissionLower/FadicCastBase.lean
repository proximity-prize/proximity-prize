import ProximityPrize.SubmissionLower.FadicChunk
import ProximityPrize.SubmissionLower.FadicRaw

/-!
# The raw evaluator computes the checked bounds

`rCertLoss_cast : ((rCertLoss S h σb σj σt bl bh jl jh i : ℕ) : ℤ) = certLoss S h … i`.

The accepted `denominator`, `cumulative` and `cappedCount` are evaluated in `ℕ`.  The two
subtractions of the accepted formulas never truncate because both sides are cardinalities
(`K1_13_2_2_2.proof` and `capped_card`).
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount cumulative denominator)
open scoped BigOperators
open Finset
open private K1_13_2_2_3.cappedColumns K1_13_2_2_3.mem_cappedColumns K1_13_2_2_3.capped_card
  from ProximityPrize.SubmissionLower.Fast068
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)

/-! ### Raw forms are the plain forms -/

theorem cond_ble {α : Type*} (a b : ℕ) (x y : α) :
    cond (Nat.ble a b) x y=if a≤b then x else y:=by
  by_cases h:a≤b
  · have hb : Nat.ble a b = true := Nat.ble_eq.mpr h
    rw [hb,if_pos h]
    rfl
  · have hb : Nat.ble a b = false := by
      cases hc:Nat.ble a b
      · rfl
      · exact absurd (Nat.ble_eq.mp hc) h
    rw [hb,if_neg h]
    rfl

theorem rMin_eq (a b : ℕ) : rMin a b = min a b := by
  unfold rMin
  rw [cond_ble]
  rfl

theorem rMax_eq (a b : ℕ) : rMax a b = max a b := by
  unfold rMax
  rw [cond_ble]
  by_cases h:a≤b
  · rw [if_pos h,max_eq_right h]
  · rw [if_neg h,max_eq_left (by omega)]

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
  rw [rMin_eq,rCumAux_eq]
  rfl

theorem rCapped_eq (d u t : ℕ) : rCapped d u t = cappedCountN d u t := by
  unfold rCapped cappedCountN
  rw [cond_ble,cond_ble]
  simp only [rCumulative_eq]
  rfl

/-! ### The plain forms compute the accepted counts -/

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
    ((6*q*(q - 1)*(q - 2):ℕ):ℤ)=6*(q:ℤ)*((q:ℤ) - 1)*((q:ℤ) - 2):=by
  rcases q with _ | _ | q
  · simp
  · simp
  · have h1 : q + 2 - 1 = q + 1 := by omega
    have h2:q+2 - 2=q:=by omega
    simp only [Nat.add_assoc,Nat.reduceAdd] at h1 h2 ⊢
    rw [h1,h2]
    push_cast
    ring

theorem denomQR_cast (q r : ℕ) :
    ((denomQR q r : ℕ) : ℤ) =
      1 + (r : ℤ) * ((r : ℤ) + 1) / 2 +
        (q:ℤ)*(22+7*(r:ℤ)+(r:ℤ)*((r:ℤ) - 1) / 2) +
        (57+6*(r:ℤ))*((q:ℤ)*((q:ℤ) - 1) / 2) +
        6*(q:ℤ)*((q:ℤ) - 1)*((q:ℤ) - 2):=by
  rw [← half_succ, ← half_pred, ← half_pred, ← cube_term]
  unfold denomQR
  push_cast
  ring

theorem denomN_cast (n : ℕ) : ((denomN n : ℕ) : ℤ) = denominator n := by
  unfold denomN denominator
  have h0 : ¬ ((n:ℤ) < 0):=by omega
  rw [if_neg h0]
  have hq:(n:ℤ) / 6=((n / 6:ℕ):ℤ):=by push_cast; rfl
  have hr:(n:ℤ) % 6=((n % 6:ℕ):ℤ):=by push_cast; rfl
  simp only [hq,hr]
  exact denomQR_cast (n / 6) (n % 6)

theorem denomSub_cast (v k : ℕ) : ((denomSub v k : ℕ) : ℤ) = denominator ((v : ℤ) - (k : ℤ)) := by
  unfold denomSub
  split
  · rename_i h
    rw [denomN_cast,Nat.cast_sub h]
  · rename_i h
    rw [denominator_neg (by omega)]
    rfl

/-- The accepted formula for `cumulative` with the negative terms collected. -/
private theorem cumulative_split (d u : ℕ) :
    cumulative d u =
      ((denomN (min u (3 * d)) + denomSub (min u (3 * d)) (2 * d + 3) +
          denomSub (min u (3*d)) (2*d+4)+denomSub (min u (3*d)) (2*d+5):ℕ):ℤ) -
      ((denomSub (min u (3 * d)) (d + 1) + denomSub (min u (3 * d)) (d + 2) +
          denomSub (min u (3*d)) (d+3)+denomSub (min u (3*d)) (3*d+6):ℕ):ℤ):=by
  unfold cumulative
  have h1 : ¬ ((d:ℤ) < 0):=by omega
  have h2 : ¬ ((u:ℤ) < 0):=by omega
  have hv:min (u:ℤ) (3*(d:ℤ))=((min u (3*d):ℕ):ℤ):=by push_cast; rfl
  simp only [h1,h2,decide_false,Bool.or_self,Bool.false_eq_true, ↓reduceIte,hv]
  set V:=min u (3*d)
  push_cast
  rw [denomN_cast, denomSub_cast, denomSub_cast, denomSub_cast, denomSub_cast, denomSub_cast,
    denomSub_cast,denomSub_cast]
  push_cast
  ring_nf

theorem cumulative_nonneg (d u : ℤ) : 0 ≤ cumulative d u := by
  rw [← K1_13_2_2_2.proof d u]
  positivity

theorem cumulativeN_cast (d u : ℕ) : ((cumulativeN d u : ℕ) : ℤ) = cumulative d u := by
  have hs:=cumulative_split d u
  have hn:=cumulative_nonneg d u
  unfold cumulativeN cumAux
  rw [hs] at hn
  rw [hs,Nat.cast_sub (by exact_mod_cast (sub_nonneg.mp hn))]

theorem cumulative_of_neg {d u : ℤ} (h : d < 0 ∨ u < 0) : cumulative d u = 0 := by
  unfold cumulative
  rcases h with h | h <;> simp [h]

theorem cappedCountN_cast (d u t : ℕ) : ((cappedCountN d u t : ℕ) : ℤ) = cappedCount d u t := by
  have hcc : cappedCount d u t = cumulative d u -
      cumulative ((d:ℤ) - (t:ℤ) - 1) ((u:ℤ) - 3*((t:ℤ)+1)):=by
    unfold cappedCount
    have ht : ¬ ((t:ℤ) < 0):=by omega
    rw [if_neg ht]
  have hsub : ((if 3 * (t + 1) ≤ u then (if t + 1 ≤ d then cumulativeN (d - (t + 1)) (u - 3 * (t + 1))
      else 0) else 0:ℕ):ℤ)=cumulative ((d:ℤ) - (t:ℤ) - 1) ((u:ℤ) - 3*((t:ℤ)+1)):=by
    split
    · rename_i hu
      split
      · rename_i hd
        rw [cumulativeN_cast,Nat.cast_sub hd,Nat.cast_sub hu]
        push_cast
        ring_nf
      · rename_i hd
        rw [cumulative_of_neg (Or.inl (by omega))]
        rfl
    · rename_i hu
      rw [cumulative_of_neg (Or.inr (by omega))]
      rfl
  have hn:=cappedCount_nonneg d u t
  unfold cappedCountN
  rw [hcc, ← cumulativeN_cast, ← hsub] at hn
  rw [Nat.cast_sub (by exact_mod_cast (sub_nonneg.mp hn)),cumulativeN_cast,hsub,hcc]

theorem rCapped_cast (d u t : ℕ) : ((rCapped d u t : ℕ) : ℤ) = cappedCount d u t := by
  rw [rCapped_eq,cappedCountN_cast]

end FadicGate
