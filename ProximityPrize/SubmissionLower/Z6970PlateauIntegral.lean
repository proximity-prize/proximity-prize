import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinParity

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ExpandedPlateauIntegral6970
open Finset KoalaPiecewiseTriangle KoalaLinearWindow
open scoped BigOperators

def poly (a d : ℤ) (n : ℕ) : ℤ :=
  let k : ℤ := n
  6*k*a*(a+1) + 3*d*(2*a+1)*k*(k-1) + d*d*k*(k-1)*(2*k-1)

theorem poly_eq (a d : ℤ) (n : ℕ) :
    6 * (∑ i ∈ range n, (a+d*(i:ℤ))*(a+d*(i:ℤ)+1)) = poly a d n := by
  induction n with
  | zero => simp [poly]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [poly, Nat.cast_succ]
    ring

def clipped (s : Span) (l : Line) : ℤ :=
  let pos := s.keep l
  poly (l.at pos.lo) l.d pos.size / 6

theorem clipped_eq (s : Span) (l : Line) :
    clipped s l = ∑ x ∈ s.finset, Low48PrimaryPivot.twiceTri (l.at x) := by
  rw [split_sum s l (fun x => Low48PrimaryPivot.twiceTri (l.at x))]
  have hn : (∑ x ∈ (s.split l).2.finset, Low48PrimaryPivot.twiceTri (l.at x)) = 0 := by
    apply sum_eq_zero
    intro x hx
    have ht := ((mem_keep _ _ _).mp hx).2
    change 0 ≤ -l.a-1 + (-l.d)*x at ht
    simp only [neg_mul] at ht
    simp [Low48PrimaryPivot.twiceTri, max_eq_left (show l.at x ≤ 0 by unfold Line.at; omega)]
  rw [hn,add_zero]
  change _ = ∑ x ∈ (s.keep l).finset, _
  rw [sum_congr rfl (g := fun x => l.at x * (l.at x + 1)) (by
    intro x hx
    exact congrArg (fun z : ℤ => z*(z+1)) (max_eq_right ((mem_keep _ _ _).mp hx).2))]
  rw [Span.sum_eq_range]
  let pos := s.keep l
  have hv (i : ℕ) : l.at (pos.lo + (i:ℤ)) = l.at pos.lo + l.d*(i:ℤ) := by
    simp [Line.at,mul_add,add_assoc]
  change poly (l.at pos.lo) l.d pos.size / 6 = ∑ i ∈ range pos.size, l.at (pos.lo+(i:ℤ))*(l.at (pos.lo+(i:ℤ))+1)
  simp_rw [hv]
  have h := poly_eq (l.at pos.lo) l.d pos.size
  omega

def delta (z : ℤ) : ℤ :=
  Low48PrimaryPivot.twiceTri z - Low48PrimaryPivot.twiceTri (z-1835)

def bill (s : Span) (l : Line) : ℤ :=
  clipped s l - clipped s ⟨l.a-1835,l.d⟩

theorem bill_eq (s : Span) (l : Line) :
    bill s l = ∑ x ∈ s.finset, delta (l.at x) := by
  unfold bill delta
  rw [clipped_eq,clipped_eq,sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro x _
  congr 1
  simp [Line.at]
  ring

def value (v x : ℤ) : List Line → ℤ
  | [] => v
  | k :: ks => value (max v (k.at x)) x ks

def receipt (s : Span) (l : Line) : List Line → ℤ
  | [] => bill s l
  | k :: ks =>
    if s.hi ≤ s.lo then 0 else
      let cut := s.split (l.sub k)
      receipt cut.1 l ks + receipt cut.2 k ks

theorem receipt_eq (s : Span) (l : Line) (ls : List Line) :
    receipt s l ls = ∑ x ∈ s.finset, delta (value (l.at x) x ls) := by
  induction ls generalizing s l with
  | nil => exact bill_eq s l
  | cons k ks ih =>
    by_cases he : s.hi ≤ s.lo
    · have hz : s.finset = ∅ := Finset.Ico_eq_empty_of_le he
      simp [receipt,he,hz]
    simp only [receipt,if_neg he]
    rw [ih,ih,split_sum s (l.sub k) (fun x => delta (value (l.at x) x (k::ks)))]
    congr 1
    · apply sum_congr rfl
      intro x hx
      have ht := ((mem_keep _ _ _).mp hx).2
      change 0 ≤ (l.a-k.a)+(l.d-k.d)*x at ht
      rw [sub_mul] at ht
      have hk : k.at x ≤ l.at x := by unfold Line.at; omega
      simp [value,max_eq_left hk]
    · apply sum_congr rfl
      intro x hx
      have ht := ((mem_keep _ _ _).mp hx).2
      change 0 ≤ -(l.a-k.a)-1 + (-(l.d-k.d))*x at ht
      rw [neg_mul,sub_mul] at ht
      have hk : l.at x ≤ k.at x := by unfold Line.at; omega
      simp [value,max_eq_right hk]

end ExpandedPlateauIntegral6970
