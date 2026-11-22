import ProximityPrize.SubmissionLower.UpperBranch1
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

namespace HighChamberDraft

open P1_7_1 (columnCount pivotCount)
open P1_7_1_3 (triangularCut edge width low high)

private theorem mul_succ_le_iff (m k : ℕ) :
    m*(m+1) ≤ k*(k+1) ↔ m ≤ k := by
  constructor
  · intro h
    by_contra! hk
    have hm : 0 < m := by omega
    have hlt : k+1 < m+1 := by omega
    exact (not_lt_of_ge h) ((Nat.mul_le_mul_right (k+1) hk.le).trans_lt
      (Nat.mul_lt_mul_of_pos_left hlt hm))
  · intro h
    exact Nat.mul_le_mul h (Nat.add_le_add_right h 1)

/-- The upper search endpoint is excluded. A width of at most 2^fuel suffices. -/
theorem cut_eq_of_mul_succ (omitted k fuel lo hi : ℕ)
    (htri : 2*omitted = k*(k+1))
    (hlo : lo ≤ k) (hhi : k < hi) (hwidth : hi ≤ lo+2^fuel) :
    triangularCut omitted fuel lo hi = k := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [triangularCut, pow_zero] at hwidth ⊢
    omega
  | succ fuel ih =>
    by_cases hg : lo+1 < hi
    · simp only [triangularCut, if_pos hg]
      let m := (lo+hi)/2
      change (if m*(m+1) ≤ 2*omitted then triangularCut omitted fuel m hi
        else triangularCut omitted fuel lo m) = k
      have hw : hi ≤ lo+2*2^fuel := by
        simpa only [pow_succ, Nat.mul_comm (2^fuel)] using hwidth
      have hl : m ≤ lo+2^fuel := by dsimp [m]; omega
      have hr : hi ≤ m+2^fuel := by dsimp [m]; omega
      by_cases hm : m ≤ k
      · have htest : m*(m+1) ≤ 2*omitted := by
          rw [htri]
          exact (mul_succ_le_iff m k).mpr hm
        rw [if_pos htest]
        exact ih m hi hm hhi hr
      · have htest : ¬ m*(m+1) ≤ 2*omitted := by
          rw [htri]
          exact fun h => hm ((mul_succ_le_iff m k).mp h)
        rw [if_neg htest]
        exact ih lo m hlo (by omega) hl
    · rw [triangularCut, if_neg hg]
      omega

/-- In the high chamber the pivot deficit is one right-hand ramp. -/
theorem column_and_deficit (B J t q : ℕ)
    (hBJ : 2*J+1 ≤ B) (ht : J ≤ t) (he : B+1 < edge B J t)
    (hq : q ≤ B) :
    columnCount B J t q = min (J+1) (q+1) ∧
    pivotCount B J t q + (q+1-(edge B J t-J)) = columnCount B J t q := by
  have hhigh : high B J t = J := by
    unfold edge at he
    unfold high
    omega
  have hlow : low J t = 0 := Nat.sub_eq_zero_of_le ht
  have hc : columnCount B J t q = min (J+1) (q+1) := by
    change min q (high B J t) + 1 - low J t = _
    rw [hhigh, hlow]
    omega
  refine ⟨hc, ?_⟩
  unfold pivotCount
  rw [hc]
  change min (min (J+1) (q+1)) (B+2*J-(t+q)) + (q+1-(edge B J t-J)) = _
  unfold edge at he ⊢
  omega

theorem high_cut (B J t omitted : ℕ)
    (hBJ : 2*J+1 ≤ B) (ht : J ≤ t) (he : B+1 < edge B J t)
    (hwidth : J+2 ≤ 2^16)
    (htri : 2*omitted = (t-J+1)*(t-J+2)) :
    min B (low J t + triangularCut omitted 16 0 (width B J t+1)) = t-J+1 := by
  have hhigh : high B J t = J := by
    unfold edge at he
    unfold high
    omega
  have hlow : low J t = 0 := Nat.sub_eq_zero_of_le ht
  have hw : width B J t = J+1 := by simp [width, hhigh, hlow]
  have hk : t-J+1 ≤ B := by unfold edge at he; omega
  have hk' : t-J+1 < J+1+1 := by unfold edge at he; omega
  rw [hlow, zero_add, hw, cut_eq_of_mul_succ omitted (t-J+1) 16 0 (J+1+1)
    (by simpa only [Nat.add_assoc] using htri) (Nat.zero_le _) hk'
    (by simpa only [zero_add, Nat.add_assoc] using hwidth), min_eq_right hk]


open Finset P1_7_1_3
open scoped BigOperators
open private column_volume ramp_count sum_after
  from ProximityPrize.SubmissionLower.UpperBranch1

private def tri (k : ℕ) : ℕ := ∑ i ∈ range k, (i+1)

private theorem twice_tri (k : ℕ) : 2*tri k = k*(k+1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih =>
    simp only [tri, sum_range_succ] at ih ⊢
    rw [Nat.mul_add, ih]
    ring

private theorem tri_choose (k : ℕ) : tri k = (k+1).choose 2 := by
  rw [Nat.choose_two_right, show k+1-1 = k by omega,
    Nat.mul_comm (k+1) k, ← twice_tri]
  exact (Nat.mul_div_cancel_left _ (by decide)).symm

private theorem split_range (f : ℕ → ℕ) {a N : ℕ} (ha : a ≤ N) :
    (∑ q ∈ range N, f q) =
      (∑ q ∈ range a, f q) + ∑ i ∈ range (N-a), f (a+i) := by
  rw [← sum_range_add, Nat.add_sub_of_le ha]

private theorem ramp_tail (f : ℕ → ℕ) (a k : ℕ) :
    (∑ q ∈ range (a+k), f q*ramp a q) =
      ∑ i ∈ range k, f (a+i)*(i+1) := by
  rw [sum_after _ (a+k) a (fun q hq => by
    rw [show ramp a q = 0 by unfold ramp; omega, mul_zero]),
    show a+k-a = k by omega]
  apply sum_congr rfl
  intro i _
  rw [show ramp a (a+i) = i+1 by unfold ramp; omega]

private theorem column_rank6 (B J t : ℕ) :
    6*(∑ q ∈ range (B+1), columnCount B J t q) =
      columnVolume6 B J t (rampCount6 (B+1)) := by
  simpa only [one_mul] using
    column_volume B J t (fun _ => 1) (rampCount6 (B+1))
      (fun a => by simpa only [one_mul] using (ramp_count (B+1) a).symm)

/-- Exact high-edge receipt for the frozen estimator, not just its upper bound. -/
theorem offset_of_high (B J t : ℕ)
    (hBJ : 2*J+1 ≤ B) (ht : J ≤ t) (he : B+1 < edge B J t)
    (hwidth : J+2 ≤ 2^16) :
    offsetEstimate B J t = (B+J-t)*tri (t-J+1) := by
  let C := J+1
  let a := edge B J t-J
  let k := t-J+1
  let c := columnCount B J t
  let p := pivotCount B J t
  let N := ∑ q ∈ range (B+1), c q
  let R := ∑ q ∈ range (B+1), p q
  let V := ∑ q ∈ range (B+1), q*c q
  let W := ∑ q ∈ range (B+1), q*p q
  let E := ∑ q ∈ range (B+1), (q-k)*c q
  let L := ∑ i ∈ range k, i*(i+1)
  have ha : a = B+J-t := by dsimp [a, edge] at *; omega
  have hsplit : a+k = B+1 := by dsimp [a,k,edge] at *; omega
  have hk : k < J := by dsimp [k,edge] at *; omega
  have hkB : k ≤ B+1 := by omega
  have hcol (q : ℕ) (hq : q ≤ B) : c q = min C (q+1) :=
    (column_and_deficit B J t q hBJ ht he hq).1
  have hdef (q : ℕ) (hq : q ≤ B) :
      p q+ramp a q = c q :=
    (column_and_deficit B J t q hBJ ht he hq).2
  have hN : N = tri J + C*(B+1-J) := by
    unfold N
    rw [split_range c (show J ≤ B+1 by omega)]
    congr 1
    · exact sum_congr rfl fun q hq => by
        rw [hcol q (by have := mem_range.mp hq; omega),
          min_eq_right (by dsimp [C]; have := mem_range.mp hq; omega)]
    · calc
        _ = ∑ i ∈ range (B+1-J), C := by
          apply sum_congr rfl
          intro i hi
          rw [hcol (J+i) (by have := mem_range.mp hi; omega),
            min_eq_left (by dsimp [C]; omega)]
        _ = _ := by simp [Nat.mul_comm]
  have htail (f : ℕ → ℕ) :
      (∑ q ∈ range (B+1), f q*ramp a q) =
        ∑ i ∈ range k, f (a+i)*(i+1) := by
    rw [← hsplit]
    exact ramp_tail f a k
  have hRank : R+tri k = N := by
    have hd := htail (fun _ => 1)
    simp only [one_mul] at hd
    unfold R N tri
    rw [← hd, ← sum_add_distrib]
    exact sum_congr rfl fun q hq => hdef q (by have := mem_range.mp hq; omega)
  have htri : tri k < tri J := by
    have h := (Nat.mul_lt_mul_of_pos_left (show k+1 < J+1 by omega)
      (show 0 < J by omega))
    have h' := (Nat.mul_le_mul_right (k+1) hk.le).trans_lt h
    rw [← twice_tri k, ← twice_tri J] at h'
    omega
  have hRstrict : C*(B+1-J) < R := by omega
  have hR6 : 6*R = pivotRank6 B J t := pivot_rank B J t
  have hN6 : 6*N = columnVolume6 B J t (rampCount6 (B+1)) := column_rank6 B J t
  have hRdiv : pivotRank6 B J t/6 = R := by
    rw [← hR6, Nat.mul_div_cancel_left _ (by decide)]
  have hNdiv : columnVolume6 B J t (rampCount6 (B+1))/6 = N := by
    rw [← hN6, Nat.mul_div_cancel_left _ (by decide)]
  have hhigh : high B J t = J := by
    unfold edge at he
    unfold high
    omega
  have hlow : low J t = 0 := Nat.sub_eq_zero_of_le ht
  have hwide : width B J t = C := by simp [width, hhigh, hlow, C]
  have htest : ¬R ≤ width B J t*(B+1-high B J t) := by
    rw [hwide,hhigh]
    exact not_le_of_gt hRstrict
  have hThreshold : threshold B J t = k := by
    unfold threshold
    rw [hRdiv, if_neg htest, hNdiv, show N-R = tri k by omega]
    exact high_cut B J t (tri k) hBJ ht he hwidth
      (by simpa only [k, Nat.add_assoc] using twice_tri k)
  have hhead : (∑ q ∈ range k, c q) = tri k := by
    apply sum_congr rfl
    intro q hq
    rw [hcol q (by have := mem_range.mp hq; omega),
      min_eq_right (by dsimp [C]; have := mem_range.mp hq; omega)]
  have htop : R = ∑ i ∈ range (B+1-k), c (k+i) := by
    have h := split_range c hkB
    change N = _ at h
    rw [hhead] at h
    omega
  have hExcess : E = ∑ i ∈ range (B+1-k), i*c (k+i) := by
    unfold E
    rw [split_range _ hkB, sum_eq_zero (fun q hq => by
      rw [show q-k = 0 by have := mem_range.mp hq; omega, zero_mul]), zero_add]
    exact sum_congr rfl fun i _ => by rw [show k+i-k = i by omega]
  have hObj : R*k+E = ∑ i ∈ range (B+1-k), (k+i)*c (k+i) := by
    rw [htop, hExcess, sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hlowW : (∑ q ∈ range k, q*c q) = L := by
    apply sum_congr rfl
    intro q hq
    rw [hcol q (by have := mem_range.mp hq; omega),
      min_eq_right (by dsimp [C]; have := mem_range.mp hq; omega)]
  have hV : L+(R*k+E) = V := by
    unfold V
    rw [split_range _ hkB, hlowW, hObj]
  have hW : W+(L+a*tri k) = V := by
    have hd := htail id
    change (∑ q ∈ range (B+1), q*ramp a q) =
      ∑ i ∈ range k, (a+i)*(i+1) at hd
    have htailW : (∑ i ∈ range k, (a+i)*(i+1)) = L+a*tri k := by
      simp only [Nat.add_mul, sum_add_distrib, ← mul_sum, L, tri, Nat.add_comm]
    unfold W V
    rw [← htailW, ← hd, ← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    rw [← Nat.mul_add, hdef q (by have := mem_range.mp hq; omega)]
  have hE6 : 6*E = excess6 B J t k := column_excess B J t k
  have hW6 : 6*W = pivotWeight6 B J t := pivot_weight B J t
  unfold offsetEstimate
  rw [hThreshold]
  change (pivotRank6 B J t*k+excess6 B J t k-pivotWeight6 B J t)/6 = _
  rw [← hR6, ← hE6, ← hW6]
  change (6*R*k+6*E-6*W)/6 = _
  rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_sub_left_distrib,
    Nat.mul_div_cancel_left _ (by decide), ← ha]
  change R*k+E-W = a*tri k
  omega

theorem offset_receipt (B J t : ℕ)
    (hBJ : 2*J+1 ≤ B) (ht : J ≤ t) (he : B+1 < edge B J t)
    (hwidth : J+2 ≤ 2^16) :
    offsetEstimate B J t = (B+J-t)*((t-J+1)*(t-J+2)/2) := by
  rw [offset_of_high B J t hBJ ht he hwidth]
  have htri : 2*tri (t-J+1) = (t-J+1)*(t-J+2) := by
    simpa only [Nat.add_assoc] using twice_tri (t-J+1)
  rw [← htri, Nat.mul_div_cancel_left _ (by decide)]

/-- Polynomial prefix for the high-edge receipts, with one division. -/
def highPrefix (B v : ℕ) : ℕ :=
  (v*(v+1)*(v+2)*(4*B-3*(v-1)))/24

private theorem choose_step (n k : ℕ) :
    (k+1)*(n+1).choose (k+1) = (n+1-k)*(n+1).choose k := by
  calc
    _ = (n+1).choose (k+1)*(k+1) := Nat.mul_comm _ _
    _ = (n+1)*n.choose k := (Nat.add_one_mul_choose_eq n k).symm
    _ = n.choose k*(n+1) := Nat.mul_comm _ _
    _ = (n+1).choose k*(n+1-k) := Nat.choose_mul_succ_eq n k
    _ = _ := Nat.mul_comm _ _

private theorem high_sum_choose (B v : ℕ) (hv : v ≤ B+1) :
    (∑ i ∈ range v, (B-i)*(i+2).choose 2) + 3*(v+2).choose 4 =
      B*(v+2).choose 3 := by
  induction v with
  | zero => simp [Nat.choose_eq_zero_of_lt (by decide : 2 < 4)]
  | succ v ih =>
    have hprev := ih (by omega)
    have hs : 3*(v+2).choose 3 = v*(v+2).choose 2 := by
      simpa only [show v+1+1 = v+2 by omega, show v+2-2 = v by omega]
        using choose_step (v+1) 2
    have hterm : (B-v)*(v+2).choose 2 + 3*(v+2).choose 3 =
        B*(v+2).choose 2 := by
      rw [hs, ← Nat.add_mul, Nat.sub_add_cancel (by omega : v ≤ B)]
    rw [sum_range_succ, show v+1+2 = (v+2)+1 by omega,
      Nat.choose_succ_succ' (v+2) 3, Nat.choose_succ_succ' (v+2) 2]
    simp only [show (2 : ℕ)+1 = 3 by rfl, show (3 : ℕ)+1 = 4 by rfl]
    rw [Nat.mul_add, Nat.mul_add]
    omega

private theorem high_prefix_sum (B v : ℕ) (hv : v ≤ B+1) :
    (∑ i ∈ range v, (B-i)*tri (i+1)) = highPrefix B v := by
  let P := v*(v+1)*(v+2)
  have h2 : 2*(v+2).choose 2 = (v+1)*(v+2) := by
    have h := twice_tri (v+1)
    rw [tri_choose] at h
    simpa only [Nat.add_assoc] using h
  have h3s : 3*(v+2).choose 3 = v*(v+2).choose 2 := by
    simpa only [show v+1+1 = v+2 by omega, show v+2-2 = v by omega]
      using choose_step (v+1) 2
  have h4s : 4*(v+2).choose 4 = (v-1)*(v+2).choose 3 := by
    simpa only [show v+1+1 = v+2 by omega, show v+2-3 = v-1 by omega]
      using choose_step (v+1) 3
  have h3 : 6*(v+2).choose 3 = P := by
    calc
      _ = 2*(3*(v+2).choose 3) := by ring
      _ = v*(2*(v+2).choose 2) := by rw [h3s]; ring
      _ = P := by rw [h2]; unfold P; ring
  have h4 : 24*(v+2).choose 4 = (v-1)*P := by
    calc
      _ = 6*(4*(v+2).choose 4) := by ring
      _ = (v-1)*(6*(v+2).choose 3) := by rw [h4s]; ring
      _ = _ := by rw [h3]
  have h3' : 24*(v+2).choose 3 = 4*P := by
    rw [← h3]
    ring
  have h := high_sum_choose B v hv
  simp only [tri_choose]
  have hf : (∑ i ∈ range v, (B-i)*(i+2).choose 2) =
      B*(v+2).choose 3-3*(v+2).choose 4 := by omega
  rw [hf]
  unfold highPrefix
  have hk : 24*(B*(v+2).choose 3-3*(v+2).choose 4) =
      P*(4*B-3*(v-1)) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    calc
      _ = B*(24*(v+2).choose 3)-3*(24*(v+2).choose 4) := by
        congr 1 <;> ring
      _ = _ := by
        rw [h3',h4]
        congr 1 <;> ring
  change _ = (P*(4*B-3*(v-1)))/24
  rw [← hk, Nat.mul_div_cancel_left _ (by decide)]

/-- The block is wholly inside the high-edge chamber. The end is exclusive. -/
theorem block_of_high_endpoints (B J start len : ℕ)
    (hBJ : 2*J+1 ≤ B) (hstart : J ≤ start) (hend : start+len ≤ 2*J-1)
    (hwidth : J+2 ≤ 2^16) :
    blockEstimate B J start len =
      highPrefix B (start-J+len)-highPrefix B (start-J) := by
  let l := start-J
  have hl : start = J+l := by dsimp [l]; omega
  have hcap : l+len ≤ B+1 := by dsimp [l]; omega
  have hcap₀ : l ≤ B+1 := by omega
  have hblock :
      blockEstimate B J start len = ∑ i ∈ range len, (B-(l+i))*tri (l+i+1) := by
    rw [blockEstimate, evaluate_eq]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hEdge : B+1 < edge B J (start+i) := by unfold edge; omega
    rw [offset_of_high B J _ hBJ (by omega) hEdge hwidth,
      show B+J-(start+i)=B-(l+i) by omega,
      show start+i-J+1=l+i+1 by omega]
  rw [hblock, ← high_prefix_sum B (l+len) hcap, ← high_prefix_sum B l hcap₀,
    sum_range_add, Nat.add_sub_cancel_left]

end HighChamberDraft
