/- Apache-2.0. Bome2017. Soundness for every bitmap-checked, quantized additive
   terminal certificate, independent of its score and row counts. -/
import ProximityPrize.SubmissionLower.Slice
import ProximityPrize.SubmissionLower.PhysicalDP
namespace KoalaNight.Grid
open Koala6835.Packed Koala6835.Partition
set_option autoImplicit false
set_option maxHeartbeats 1000000
structure Table where
  bits : ℕ
  n : ℕ
  guard : ℕ
  one : ℕ → ℕ → ℕ
  all : ℕ → ℕ → ℕ
  comp : ℕ → ℕ → ℕ
def single (T:Table) (r e k:ℕ) := digit T.bits (T.one r e) k
def overall (T:Table) (r e k:ℕ) := digit T.bits (T.all r e) k
def multiple (T:Table) (r e k:ℕ) := T.guard-digit T.bits (T.comp r e) k
def dat (T:Table) (M r e:ℕ) : Bool :=
  (T.all r e < (2^T.bits)^T.n && T.comp r e < (2^T.bits)^T.n) &&
  (List.range T.n).all fun k=>decide (
     single T r e k≤M ∧ overall T r e k≤M ∧ digit T.bits (T.comp r e) k≤T.guard ∧
     single T r e k≤overall T r e k ∧ multiple T r e k≤overall T r e k)
def check (T:Table) (r e a m:ℕ) := passes T.bits T.n T.guard (T.one a m) (T.all (r-a) (e-m)) (T.comp r e)
def checks (T:Table) (r e:ℕ) :=
  (List.range (r/2)).all fun i=>(List.range (e+1)).all fun m=>check T r e (i+1) m
private theorem fields (T:Table) (M r e k:ℕ) (d:dat T M r e=true) (hk:k<T.n) :
  single T r e k≤M ∧ overall T r e k≤M ∧ digit T.bits (T.comp r e) k≤T.guard ∧
  single T r e k≤overall T r e k ∧ multiple T r e k≤overall T r e k :=
  of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp d).2 k (List.mem_range.mpr hk))

theorem certificate (T:Table) (M quantum R Y Z width:ℕ)
    (guard:M+M+T.guard<2^T.bits)
    (height:∀r e k:ℕ,1≤r → r+e+k*width≤Z → k<T.n)
    (valid:∀r e:ℕ,1≤r → r≤R → r+e≤Y → dat T M r e=true ∧ checks T r e=true) :
    Certificate (fun r e k=>single T r e k*quantum) (fun r e k=>overall T r e k*quantum)
       (fun r e k=>multiple T r e k*quantum) R Y Z width := by
  constructor
  · intro r e k hr hm hY hZ
    exact Nat.mul_le_mul_right _ (fields T M r e k (valid r e hr hm hY).1 (height _ _ _ hr hZ)).2.2.2.1
  · intro r e k hr hm hY hZ
    exact Nat.mul_le_mul_right _ (fields T M r e k (valid r e hr hm hY).1 (height _ _ _ hr hZ)).2.2.2.2
  · intro r e k a m h ha ha2 hm hk hR hY hZ
    have hr : 1≤r := by omega
    have hn := height r e k hr hZ
    obtain ⟨dt,c⟩ := valid r e hr hR hY
    have da := (valid a m ha (by omega) (by omega)).1
    have db := (valid (r-a) (e-m) (by omega) (by omega) (by omega)).1
    have c1 := List.all_eq_true.mp c (a-1) (List.mem_range.mpr (by omega))
    have c2 := List.all_eq_true.mp c1 m (List.mem_range.mpr (by omega))
    rw [show a-1+1=a by omega] at c2
    have byn : T.all (r-a) (e-m)<(2^T.bits)^T.n :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp db).1).1
    have cn : T.comp r e<(2^T.bits)^T.n :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp dt).1).2
    have good (j:ℕ) (lo:j<T.n) : digit T.bits (T.one a m) j≤M ∧ digit T.bits (T.all (r-a) (e-m)) j≤M :=
      ⟨(fields _ _ _ _ _ da lo).1,(fields _ _ _ _ _ db lo).2.1⟩
    have comp (j:ℕ) : digit T.bits (T.comp r e) j≤T.guard := by
      by_cases inside:j<T.n
      · exact (fields _ _ _ _ _ dt inside).2.2.1
      have small : T.comp r e < (2^T.bits)^j :=
        cn.trans_le (Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega))
      rw [digit_div,Nat.div_eq_of_lt small,Nat.zero_mod];omega
    have inequality := pass_sound T.bits T.n M T.guard _ _ _ byn cn good comp guard c2 h (k-h) (by omega) (by omega)
    rw [show h+(k-h)=k by omega] at inequality
    have fee : single T a m h+overall T (r-a) (e-m) (k-h) ≤ multiple T r e k := by
      unfold single overall multiple
      omega
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right quantum fee
#print axioms certificate
end KoalaNight.Grid
