/- Apache-2.0. 68.36 degree-interval receipts by Bome2017 over the BitWonka and Lucieno physical bounds. -/
import ProximityPrize.SubmissionLower.Night6836OfferPlan
import ProximityPrize.SubmissionLower.Night6836OfferData
import ProximityPrize.SubmissionLower.Night6836RawMono
import ProximityPrize.SubmissionLower.Night6836GridData
import ProximityPrize.SubmissionLower.Night6836Room
set_option Elab.async false
namespace Koala6836.Offers
open Koala6835.Offers (check price valid)
open ProximityPrize.SubmissionLower.Raw6836
open Koala6836.Tables
open Koala6836.Room
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def binOK (r e k : ℕ) : Bool :=
  check bank rowRaw r e (min 9352 (r+e+100*k+99)) (oneUnits r e k*10000000000000)
    5 (r+e+100*k) (binPlan r e k)
def singleOK (r e : ℕ) : Bool :=
  if maxTotal r e=0 then true else
    (if r+e<split r e then check bank rowRaw r e (split r e-1) (lowBudget r e) 12 (r+e) (bottomPlan r e) else true) &&
    check bank rowRaw r e (maxTotal r e) (highBudget r e) 12 (split r e) (topPlan r e)
def rowOK (r e : ℕ) : Bool := singleOK r e && (List.range 94).all fun k =>
  if r+e+100*k≤9352 then binOK r e k else true
theorem one_price_of_row {r e t cost : ℕ} (row : rowOK r e = true) (left : r+e ≤ t)
    (top : t ≤ 9352)
    (hraw : cost ≤ rowRaw r e (t-(r+e)))
    (hwin : ∀i, valid (bank i) r e t t → cost ≤ (bank i).fee) :
    cost ≤ oneUnits r e ((t-(r+e))/100)*10000000000000 := by
  let k := (t-(r+e))/100
  have hk : k < 94 := by dsimp [k]; omega
  simp only [rowOK,Bool.and_eq_true] at row
  have h := List.all_eq_true.mp row.2 k (List.mem_range.mpr hk)
  have h0 : r+e+100*k ≤ t := by dsimp [k]; omega
  simp only [if_pos (h0.trans top)] at h
  apply price bank rowRaw (fun rr ee a b hab => raw_mono_z rr ee hab) r e t cost hraw hwin _ _ 5 _ _ h
  · exact h0
  · dsimp only [k]; omega
theorem singleton_price_of_row {r e t cost : ℕ} (row : rowOK r e = true)
    (left : r+e ≤ t) (top : t ≤ maxTotal r e) (pos : 0<r)
    (hraw : cost ≤ rowRaw r e (t-(r+e)))
    (hwin : ∀i, valid (bank i) r e t t → cost ≤ (bank i).fee) :
    cost ≤ budget r e t := by
  simp only [rowOK,Bool.and_eq_true] at row
  have h := row.1
  have ne : maxTotal r e≠0 := by omega
  simp only [singleOK, if_neg ne, Bool.and_eq_true] at h
  by_cases hh : t<split r e
  · have hstart : r+e < split r e := by omega
    rw [Room.budget,if_pos hh]
    have hl := h.1
    simp only [if_pos hstart] at hl
    exact price bank rowRaw (fun rr ee a b hab => raw_mono_z rr ee hab) r e t cost hraw hwin _ _ 12 _ _ hl left (by omega)
  · rw [Room.budget,if_neg hh]
    exact price bank rowRaw (fun rr ee a b hab => raw_mono_z rr ee hab) r e t cost hraw hwin _ _ 12 _ _ h.2 (by omega) top
end Koala6836.Offers
