/- Adapted from PR657 HighCore82258TerminalArithmetic. The saved rectangle
checks use the original agreement. The width and Parts proofs are shared here
independently of the active 69.55 model. -/
import ProximityPrize.SubmissionLower.UpperBranch6

set_option Elab.async false
set_option autoImplicit true

namespace Pr657RectStockTerminalArithmetic
open Finset
open K1_14 (Shape)
open P0_10_5 (Row scan joinRows)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open P1_7_6 (linearEnd lt_linearEnd)

abbrev stockAgreement:ℕ:=179886

def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m*stockAgreement:ℕ)+(j:ℤ) - (131071 - (h:ℤ))*q - 2*(h:ℤ)*t
def colEnd (s : Shape) (h t : ℕ) : ℕ :=
  linearEnd (2*h*t) (131071-h) (s.m*stockAgreement) (s.B+1)
def edgeShift (s : Shape) (h t : ℕ) : ℕ :=
  2*h*t+(131071-h)*colEnd s h t+1 - s.m*stockAgreement
private theorem width_eq_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    width s h q j t = (↑(s.m*stockAgreement+j : ℕ) : ℤ) -
      (↑(2*h*t+(131071-h)*q:ℕ):ℤ):=by
  simp only [width,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hh,Nat.cast_ofNat]
  ring
theorem width_sum (s : Shape) (h t j l : ℕ) (hh : h ≤ 131071) (hj : j ≤ 131071-h) :
    (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
      (∑ q ∈ Ico l (colEnd s h t), width s h q j t) +
        if colEnd s h t < s.B+1 ∧ l ≤ colEnd s h t ∧ edgeShift s h t ≤ j then
          width s h (colEnd s h t) j t else 0:=by
  let k:=colEnd s h t
  let D:=131071-h
  have hk (q : ℕ) : q < k ↔ q < s.B+1 ∧ 2*h*t + D*q < s.m*stockAgreement :=
    lt_linearEnd _ _ _ _ _
  have hkB : k ≤ s.B+1 := by
    by_contra! h
    exact (Nat.lt_irrefl _) ((hk (s.B+1)).mp h).1
  have hpos (q : ℕ) (hq : q < k) : 0 ≤ width s h q j t := by
    have hp:=((hk q).mp hq).2
    rw [width_eq_cast s h q j t hh]
    change 2*h*t+D*q < s.m*stockAgreement at hp
    change 0≤(↑(s.m*stockAgreement+j:ℕ):ℤ) - (↑(2*h*t+D*q:ℕ):ℤ)
    omega
  have hsum : (∑ q ∈ Ico l k, max 0 (width s h q j t)) = ∑ q ∈ Ico l k, width s h q j t := by
    apply sum_congr rfl
    intro q hq
    exact max_eq_right (hpos q (mem_Ico.mp hq).2)
  by_cases hb:k < s.B+1
  · have hbase : s.m*stockAgreement ≤ 2*h*t + D*k := by
      by_contra! he
      exact (Nat.lt_irrefl _) ((hk k).mpr ⟨hb,he⟩)
    have hzero (q : ℕ) (hq : k < q) : max 0 (width s h q j t) = 0 := by
      have hm:D*(k+1)≤D*q:=Nat.mul_le_mul_left D (by omega)
      rw [Nat.mul_add,Nat.mul_one] at hm
      apply max_eq_left
      rw [width_eq_cast s h q j t hh]
      change j≤D at hj
      change (↑(s.m*stockAgreement+j:ℕ):ℤ) - (↑(2*h*t+D*q:ℕ):ℤ)≤0
      omega
    have hrestrict :
        (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
          ∑ q ∈ Ico l (k+1),max 0 (width s h q j t):=by
      symm
      apply sum_subset
      · intro q hq
        obtain ⟨ha,he⟩:=mem_Ico.mp hq
        exact mem_Ico.mpr ⟨ha,by omega⟩
      · intro q hq hn
        obtain ⟨ha,he⟩:=mem_Ico.mp hq
        exact hzero q (by
          by_contra! hle
          exact hn (mem_Ico.mpr ⟨ha,by omega⟩))
    change _=(∑ q ∈ Ico l k,_)+if k < s.B+1 ∧ l≤k ∧ edgeShift s h t≤j then _ else _
    rw [hrestrict]
    by_cases hl:l≤k
    · rw [sum_Ico_succ_top hl, hsum]
      simp only [hb,hl,true_and]
      congr 1
      have hsign : 0 < width s h k j t ↔ edgeShift s h t ≤ j := by
        rw [width_eq_cast s h k j t hh]
        change (0 : ℤ) < (↑(s.m*stockAgreement+j : ℕ) : ℤ) - (↑(2*h*t+D*k : ℕ) : ℤ) ↔
          2*h*t+D*k+1-s.m*stockAgreement≤j
        omega
      by_cases hw:edgeShift s h t≤j
      · rw [ite_eq_left hw,max_eq_right ((hsign.mpr hw).le)]
      · rw [ite_eq_right hw,max_eq_left (by have:=mt hsign.mp hw; omega)]
    · have he : Ico l (k+1) = ∅ := Ico_eq_empty_of_le (by omega)
      have hf:Ico l k = ∅ := Ico_eq_empty_of_le (by omega)
      simp [he,hf,hl]
  · have he : k = s.B+1 := by omega
    change _=(∑ q ∈ Ico l k,_)+if k < s.B+1 ∧ l≤k ∧ edgeShift s h t≤j then _ else _
    rw [← he,hsum]
    simp
theorem twice_width_interval (s : Shape) (h t j l k : ℕ) (hh : h ≤ 131071)
    (hl:l≤k) :
    2 * (∑ q ∈ Ico l k, width s h q j t) =
      ((k : ℤ)-l) * (2*((s.m*stockAgreement : ℕ)+(j : ℤ)-2*(h : ℤ)*t) -
        ((131071-h:ℕ):ℤ)*((l:ℤ)+k-1)):=by
  rw [sum_Ico_eq_sum_range]
  have hf (a : ℕ) : width s h (l+a) j t =
      width s h l j t+(-((131071-h:ℕ):ℤ))*(a:ℤ):=by
    simp only [width,Nat.cast_add,Nat.cast_sub hh,Nat.cast_ofNat]
    ring
  simp_rw [hf]
  rw [twice_sum_linear]
  simp only [Nat.cast_sub hl,width,Nat.cast_sub hh,Nat.cast_ofNat]
  ring

inductive Parts (f : ℕ → Row) (last : ℕ) : ℕ → ℕ → ℤ → ℤ → Prop
  | final {a : ℕ} {gain next : ℤ} :
      scan f a last=⟨true,gain,next⟩→Parts f last a last gain next
  | more {a count : ℕ} {gain next restGain restNext : ℤ} :
      scan f a 16=⟨true,gain,next⟩→Parts f last (a+16) count restGain restNext →
      Parts f last a (16+count) (gain+restGain) (next+restNext)
theorem Parts.scan_eq {f : ℕ → Row} {last a count : ℕ} {gain next : ℤ}
    (parts:Parts f last a count gain next):scan f a count=⟨true,gain,next⟩:=by
  induction parts with
  | final h => exact h
  | @more a count gain next restGain restNext h _ ih =>
    exact joinRows a 16 count _ _ h ih rfl

end Pr657RectStockTerminalArithmetic
