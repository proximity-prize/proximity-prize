import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.UpperBranch6

set_option Elab.async false

-- merged module HighCore82258TerminalArithmetic
section Merged_HighCore82258TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open HighCore82258 (Bank debit jointGain)
export P1_7_6 (orderEnd linearEnd Quad prefixProduct intervalProduct seedEnd yStart seedQuad scaledDebit)
def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m * agreement : ℕ) + (j : ℤ) - (131071 - (h : ℤ)) * q - 2 * (h : ℤ) * t
def surplus (h : ℕ) (b : Bank) (E v : ℕ) : ℤ :=
  (jointGain h b.shape E v : ℤ) - (debit h b : ℤ)
def colEnd (s : Shape) (h t : ℕ) : ℕ :=
  linearEnd (2*h*t) (131071-h) (s.m*agreement) (s.B+1)
def edgeShift (s : Shape) (h t : ℕ) : ℕ :=
  2*h*t + (131071-h)*colEnd s h t + 1 - s.m*agreement
def innerEnd (s : Shape) (h E v d t R : ℕ) : ℕ :=
  linearEnd (yStart E d t) (E-1) (colEnd s h t) (seedEnd s v d R)
def outerEnd (s : Shape) (h E v d t R : ℕ) : ℕ :=
  min (t+1-edgeShift s h t)
    (linearEnd (yStart E d t) (E-1) (colEnd s h t+1) (seedEnd s v d R))
def widthOrigin (s : Shape) (h t : ℕ) : ℤ :=
  (s.m*agreement : ℕ) + (t : ℤ) - 2*(h : ℤ)*t
def innerQuad (s : Shape) (h E d t : ℕ) : Quad :=
  let D : ℤ := (131071-h : ℕ)
  let k : ℤ := colEnd s h t
  let l : ℤ := yStart E d t
  let p : ℤ := (E-1 : ℕ)
  P1_7_6.Quad.ofLines (k-l) (-p) (2*widthOrigin s h t-D*(l+k-1)) (-2-D*p)
def outerQuad (s : Shape) (h t : ℕ) : Quad :=
  ⟨2*(widthOrigin s h t-((131071-h : ℕ) : ℤ)*colEnd s h t), -2, 0⟩
def phaseBlock (s : Shape) (h E v d t : ℕ) : ℤ :=
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let c := seedQuad s v d
  intervalProduct c (innerQuad s h E d t) L (innerEnd s h E v d t R) +
    if colEnd s h t < s.B+1 then
      intervalProduct c (outerQuad s h t) L (outerEnd s h E v d t R)
    else 0
def blockSurplus (s : Shape) (N P h E v : ℕ) : ℤ :=
  (∑ t ∈ range (s.J+orderEnd s E v), (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) -
    scaledDebit s N P h
def BlockChecks (s : Shape) (N P h E v : ℕ) : Prop :=
  0 < blockSurplus s N P h E v ∧ blockSurplus s N P h E v ≤ blockSurplus s N P (h+1) E v
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape shapeSum slots)
open HighCore82258 (agreement)
open HighCore82258 (Bank debit jointGain)
open P1_7_6 (rise_of_convex)
theorem width_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    (↑(s.m * agreement + j - q * (131071-h) - 2*h*t : ℕ) : ℤ) =
      max 0 (width s h q j t) := by
  rw [Nat.sub_sub]
  have hd : (↑(131071-h : ℕ) : ℤ) = 131071 - h := Nat.cast_sub hh
  have he : (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*t : ℕ) : ℤ) =
      width s h q j t := by
    simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hd]
    ring
  generalize s.m*agreement+j = x at *
  generalize q*(131071-h)+2*h*t = y at *
  by_cases hxy : y ≤ x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]
private theorem width_convex (s : Shape) (h q j t : ℕ) :
    max 0 (width s (h+1) q j t) + max 0 (width s (h+1) q j t) ≤
      max 0 (width s h q j t) + max 0 (width s (h+2) q j t) := by
  have hlin : width s (h+1) q j t + width s (h+1) q j t =
      width s h q j t + width s (h+2) q j t := by
    simp only [width, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases hn : width s (h+1) q j t ≤ 0
  · rw [max_eq_left hn, zero_add]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hn), hlin]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
private theorem weighted_convex (s : Shape) (h q j t c : ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (↑(c * (s.m * agreement + j - q*(131071-h) - 2*h*t) : ℕ) : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  dsimp only
  simp only [Nat.cast_mul, width_cast s h q j t (by omega),
    width_cast s (h+1) q j t (by omega), width_cast s (h+2) q j t hh, ← mul_add]
  exact mul_le_mul_of_nonneg_left (width_convex s h q j t) (Int.natCast_nonneg c)
private theorem gain_convex (s : Shape) (h E v : ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (jointGain h s E v : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  simp only [jointGain, shapeSum, Nat.cast_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  let g := (q-j)/E
  let raw := fun k a => s.m*agreement+j-q*(131071-k)-2*k*(j+a)
  let A := fun k => (↑(∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v))*raw k a : ℕ) : ℤ)
  let B := fun k => (↑(slots s.U (g*v)*raw k g : ℕ) : ℤ)
  simp only [Nat.cast_add]
  change A (h+1) + B (h+1) + (A (h+1) + B (h+1)) ≤ A h + B h + (A (h+2) + B (h+2))
  rw [add_add_add_comm (A (h+1)), add_add_add_comm (A h)]
  apply add_le_add
  · simp only [A, Nat.cast_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro a _
    exact weighted_convex s h q j (j+a) (slots s.U (a*v) - slots s.U ((a+1)*v)) hh
  · exact weighted_convex s h q j (j+(q-j)/E) (slots s.U (((q-j)/E)*v)) hh
private theorem debit_affine (h : ℕ) (b : Bank) :
    (debit (h+1) b : ℤ) + (debit (h+1) b : ℤ) =
      (debit h b : ℤ) + (debit (h+2) b : ℤ) := by
  simp only [debit, P1_7.debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring
private theorem surplus_convex (h : ℕ) (b : Bank) (E v : ℕ) (hh : h+2 ≤ 131071) :
    surplus (h+1) b E v + surplus (h+1) b E v ≤
      surplus h b E v + surplus (h+2) b E v := by
  have hg := gain_convex b.shape h E v hh
  have hd := debit_affine h b
  dsimp only at hg
  unfold surplus
  omega
theorem strict_of_first_difference {lo h : ℕ} {b : Bank} {E v : ℕ}
    (hl : lo ≤ h) (hh : h < 131071)
    (hpos : 0 < surplus lo b E v) (hrise : surplus lo b E v ≤ surplus (lo+1) b E v) :
    debit h b < jointGain h b.shape E v := by
  have hmon := rise_of_convex (f := fun h => surplus h b E v)
    (fun n hn => surplus_convex n b E v (by omega)) hl hrise
  have hsur := hpos.trans_le hmon.1
  unfold surplus at hsur
  omega
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape shapeSum slots triangle)
open HighCore82258 (agreement)
open HighCore82258 (jointGain)
open P1_7_6 (slots_anti sum_range_guard diagonal)
def phase (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ t ∈ range (s.J + orderEnd s E v), ∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
    (slots s.U ((a+d)*v) : ℤ) *
      ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)
private theorem position_phases (s : Shape) (h E v q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => slots s.U (a*v)
    let x := s.m*agreement+j-q*(131071-h)
    let g := (q-j)/E
    let f := fun d a => (c (a+d) : ℤ)*max 0 (width s h q j (j+a))
    (↑((∑ a ∈ range g, (c a - c (a+1))*(x-2*h*(j+a))) + c g*(x-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+0) ≤ q then f 0 a else 0) -
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+1) ≤ q then f 1 a else 0) := by
  dsimp only
  let g := (q-j)/E
  let f := fun d a => (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a))
  have step (a : ℕ) : slots s.U ((a+1)*v) ≤ slots s.U (a*v) :=
    slots_anti _ (Nat.mul_le_mul_right v (by omega))
  have hdiff :
      (↑((∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
          (s.m*agreement+j-q*(131071-h)-2*h*(j+a))) +
        slots s.U (g*v)*(s.m*agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (g+1), f 0 a) - ∑ a ∈ range g, f 1 a := by
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sum]
    rw [show (∑ a ∈ range g, f 0 a) + f 0 g - (∑ a ∈ range g, f 1 a) =
        ((∑ a ∈ range g, f 0 a) - (∑ a ∈ range g, f 1 a)) + f 0 g by ring,
      ← sum_sub_distrib]
    simp only [Nat.cast_mul, width_cast s h _ _ _ hh, f, Nat.add_zero]
    have hs (a : ℕ) :
        (↑(slots s.U (a*v) - slots s.U ((a+1)*v) : ℕ) : ℤ) =
          (slots s.U (a*v) : ℤ) - slots s.U ((a+1)*v) := Int.ofNat_sub (step a)
    simp only [hs, sub_mul]
  rw [hdiff]
  have hz (d a : ℕ) (ha : orderEnd s E v ≤ a) (hg : a+d ≤ g) : f d a = 0 := by
    have hcap : g ≤ s.B/E := Nat.div_le_div_right (by omega)
    have hab : a < s.B/E+1 := by omega
    unfold orderEnd at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge : s.U/v < a+d := by omega
      have hout : s.U < (a+d)*v := by
        by_contra! hm
        exact (Nat.not_le_of_lt hlarge) ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)).2 hm)
      simp [f, slots, Nat.not_le_of_lt hout]
  have hdiv (a d : ℕ) : j+E*(a+d) ≤ q ↔ a+d ≤ g := by
    rw [Nat.le_div_iff_mul_le he, Nat.mul_comm (a+d) E]
    omega
  rw [sum_range_guard (g+1) _ (fun a ha hb => hz 0 a ha (by omega)),
    sum_range_guard g _ (fun a ha hb => hz 1 a ha (by omega))]
  have hzero (a : ℕ) : j+E*a ≤ q ↔ a ≤ g := by simpa using hdiv a 0
  simp only [hzero, Nat.add_zero, Nat.lt_succ_iff, Nat.add_one_le_iff, f]
private def phaseQ (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
    if j + E*(a+d) ≤ q then
      (slots s.U ((a+d)*v) : ℤ) * max 0 (width s h q j (j+a)) else 0
private theorem phaseQ_expand (s : Shape) (h E v d q : ℕ) :
    (∑ j ∈ range (min q s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0) =
    ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0 := by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
private theorem gain_eq_phaseQ (s : Shape) (h E v : ℕ) (hh : h ≤ 131071) (he : 0 < E) :
    (jointGain h s E v : ℤ) = phaseQ s h E v 0 - phaseQ s h E v 1 := by
  unfold jointGain shapeSum phaseQ
  push_cast only [Nat.cast_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← phaseQ_expand s h E v 0 q, ← phaseQ_expand s h E v 1 q, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range, Nat.lt_succ_iff] at hq hj
  exact position_phases s h E v q j hh he hq (hj.trans (min_le_left _ _))
private theorem phaseQ_eq (s : Shape) (h E v d : ℕ) : phaseQ s h E v d = phase s h E v d := by
  have hR : orderEnd s E v-1+1 = orderEnd s E v := by
    apply Nat.sub_add_cancel
    unfold orderEnd
    split
    · exact Nat.succ_pos _
    · exact le_min (Nat.succ_pos _) (Nat.succ_pos _)
  unfold phaseQ phase
  rw [sum_comm]
  conv_lhs =>
    enter [2, j]
    rw [sum_comm]
  conv_lhs =>
    rw [← hR]
    rw [diagonal]
  rw [Nat.add_assoc, hR]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro a ha
  have hta : t-a+a = t := Nat.sub_add_cancel (by have := (mem_Ico.mp ha).2; omega)
  rw [mul_sum, ← sum_filter]
  have hf : (range (s.B+1)).filter (fun q => t-a+E*(a+d) ≤ q) =
      Ico (t-a+E*(a+d)) (s.B+1) := by
    ext q
    simp only [mem_range, mem_filter, mem_Ico]
    tauto
  rw [hf, hta]
theorem gain_eq_phases (s : Shape) (h E v : ℕ) (hh : h ≤ 131071) (he : 0 < E) :
    (jointGain h s E v : ℤ) = phase s h E v 0 - phase s h E v 1 := by
  rw [gain_eq_phaseQ s h E v hh he, phaseQ_eq, phaseQ_eq]
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open HighCore82258 (agreement)
open K1_14 (Shape)
open K1_14_2_1 (twice_sum_linear)
export P1_7_6 (lt_linearEnd)
private theorem width_eq_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    width s h q j t = (↑(s.m*agreement+j : ℕ) : ℤ) -
      (↑(2*h*t+(131071-h)*q : ℕ) : ℤ) := by
  simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hh, Nat.cast_ofNat]
  ring
theorem width_sum (s : Shape) (h t j l : ℕ) (hh : h ≤ 131071) (hj : j ≤ 131071-h) :
    (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
      (∑ q ∈ Ico l (colEnd s h t), width s h q j t) +
        if colEnd s h t < s.B+1 ∧ l ≤ colEnd s h t ∧ edgeShift s h t ≤ j then
          width s h (colEnd s h t) j t else 0 := by
  let k := colEnd s h t
  let D := 131071-h
  have hk (q : ℕ) : q < k ↔ q < s.B+1 ∧ 2*h*t + D*q < s.m*agreement :=
    lt_linearEnd _ _ _ _ _
  have hkB : k ≤ s.B+1 := by
    by_contra! h
    exact (Nat.lt_irrefl _) ((hk (s.B+1)).mp h).1
  have hpos (q : ℕ) (hq : q < k) : 0 ≤ width s h q j t := by
    have hp := ((hk q).mp hq).2
    rw [width_eq_cast s h q j t hh]
    change 2*h*t+D*q < s.m*agreement at hp
    change 0 ≤ (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*q : ℕ) : ℤ)
    omega
  have hsum : (∑ q ∈ Ico l k, max 0 (width s h q j t)) = ∑ q ∈ Ico l k, width s h q j t := by
    apply sum_congr rfl
    intro q hq
    exact max_eq_right (hpos q (mem_Ico.mp hq).2)
  by_cases hb : k < s.B+1
  · have hbase : s.m*agreement ≤ 2*h*t + D*k := by
      by_contra! he
      exact (Nat.lt_irrefl _) ((hk k).mpr ⟨hb,he⟩)
    have hzero (q : ℕ) (hq : k < q) : max 0 (width s h q j t) = 0 := by
      have hm : D*(k+1) ≤ D*q := Nat.mul_le_mul_left D (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      apply max_eq_left
      rw [width_eq_cast s h q j t hh]
      change j ≤ D at hj
      change (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*q : ℕ) : ℤ) ≤ 0
      omega
    have hrestrict :
        (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
          ∑ q ∈ Ico l (k+1), max 0 (width s h q j t) := by
      symm
      apply sum_subset
      · intro q hq
        obtain ⟨ha,he⟩ := mem_Ico.mp hq
        exact mem_Ico.mpr ⟨ha,by omega⟩
      · intro q hq hn
        obtain ⟨ha,he⟩ := mem_Ico.mp hq
        exact hzero q (by
          by_contra! hle
          exact hn (mem_Ico.mpr ⟨ha,by omega⟩))
    change _ = (∑ q ∈ Ico l k, _) + if k < s.B+1 ∧ l ≤ k ∧ edgeShift s h t ≤ j then _ else _
    rw [hrestrict]
    by_cases hl : l ≤ k
    · rw [sum_Ico_succ_top hl, hsum]
      simp only [hb, hl, true_and]
      congr 1
      have hsign : 0 < width s h k j t ↔ edgeShift s h t ≤ j := by
        rw [width_eq_cast s h k j t hh]
        change (0 : ℤ) < (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*k : ℕ) : ℤ) ↔
          2*h*t+D*k+1-s.m*agreement ≤ j
        omega
      by_cases hw : edgeShift s h t ≤ j
      · rw [ite_eq_left hw, max_eq_right ((hsign.mpr hw).le)]
      · rw [ite_eq_right hw, max_eq_left (by have := mt hsign.mp hw; omega)]
    · have he : Ico l (k+1) = ∅ := Ico_eq_empty_of_le (by omega)
      have hf : Ico l k = ∅ := Ico_eq_empty_of_le (by omega)
      simp [he,hf,hl]
  · have he : k = s.B+1 := by omega
    change _ = (∑ q ∈ Ico l k, _) + if k < s.B+1 ∧ l ≤ k ∧ edgeShift s h t ≤ j then _ else _
    rw [← he, hsum]
    simp
theorem twice_width_interval (s : Shape) (h t j l k : ℕ) (hh : h ≤ 131071)
    (hl : l ≤ k) :
    2 * (∑ q ∈ Ico l k, width s h q j t) =
      ((k : ℤ)-l) * (2*((s.m*agreement : ℕ)+(j : ℤ)-2*(h : ℤ)*t) -
        ((131071-h : ℕ) : ℤ)*((l : ℤ)+k-1)) := by
  rw [sum_Ico_eq_sum_range]
  have hf (a : ℕ) : width s h (l+a) j t =
      width s h l j t + (-((131071-h : ℕ) : ℤ))*(a : ℤ) := by
    simp only [width, Nat.cast_add, Nat.cast_sub hh, Nat.cast_ofNat]
    ring
  simp_rw [hf]
  rw [twice_sum_linear]
  simp only [Nat.cast_sub hl, width, Nat.cast_sub hh, Nat.cast_ofNat]
  ring
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open HighCore82258 (agreement)
open K1_14 (Shape slots triangle)
open HighCore82258 (debit)
open P1_7_6 (intervalProduct_eq)
open P1_7_6 (lt_seedEnd yStart_eq seedQuad_eq sum_clipped)
private theorem widthOrigin_eq (s : Shape) (h t a q : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    width s h q (t-a) t = widthOrigin s h t - a - ((131071-h : ℕ) : ℤ)*q := by
  simp only [width, widthOrigin, Nat.cast_sub hh, Nat.cast_sub ha, Nat.cast_ofNat]
  ring
private theorem innerQuad_eq (s : Shape) (h E d t a : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (ha : a ≤ t) (hl : t-a+E*(a+d) ≤ colEnd s h t) :
    2*(∑ q ∈ Ico (t-a+E*(a+d)) (colEnd s h t), width s h q (t-a) t) =
      (innerQuad s h E d t).eval a := by
  rw [twice_width_interval s h t (t-a) _ _ hh hl, innerQuad, P1_7_6.Quad.eval_ofLines,
    yStart_eq E d t a he ha]
  simp only [widthOrigin, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  ring
private theorem outerQuad_eq (s : Shape) (h t a : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    2*width s h (colEnd s h t) (t-a) t = (outerQuad s h t).eval a := by
  rw [widthOrigin_eq s h t a _ hh ha]
  simp only [outerQuad, P1_7_6.Quad.eval]
  ring
theorem phaseBlock_eq (s : Shape) (h E v d t : ℕ)
    (hh : h ≤ 131071) (hj : s.J ≤ 131071-h) (he : 0 < E) :
    240*(∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
      (slots s.U ((a+d)*v) : ℤ) *
        ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)) =
      phaseBlock s h E v d t := by
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let k := colEnd s h t
  let l := fun a => t-a+E*(a+d)
  let c := fun a => (slots s.U ((a+d)*v) : ℤ)
  let inner := fun a => ∑ q ∈ Ico (l a) k, width s h q (t-a) t
  let outer := fun a =>
    if k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a then width s h k (t-a) t else 0
  let R₁ := innerEnd s h E v d t R
  let R₂ := outerEnd s h E v d t R
  have ht (a : ℕ) (ha : a < R) : a ≤ t :=
    (Nat.le_of_lt_succ ha).trans (min_le_left _ _)
  have hcore (a : ℕ) : a < R₁ ↔ a < R ∧ (a+d)*v ≤ s.U ∧ l a < k := by
    simp only [R₁, innerEnd, lt_linearEnd, lt_seedEnd]
    constructor
    · rintro ⟨⟨ha,hv⟩,hk⟩
      exact ⟨ha,hv,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
    · rintro ⟨ha,hv,hk⟩
      exact ⟨⟨ha,hv⟩,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
  have hedge (a : ℕ) :
      a < R₂ ↔ a < R ∧ (a+d)*v ≤ s.U ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a := by
    simp only [R₂, outerEnd, lt_min_iff, lt_linearEnd, lt_seedEnd]
    constructor
    · rintro ⟨hs,⟨ha,hv⟩,hk⟩
      refine ⟨ha,hv,?_,by omega⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
    · rintro ⟨ha,hv,hk,hs⟩
      refine ⟨by have := ht a ha; omega,⟨ha,hv⟩,?_⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
  have hw (a : ℕ) (ha : a ∈ Ico L R) :
      (∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) = inner a + outer a := by
    obtain ⟨ha₀,_⟩ := mem_Ico.mp ha
    exact width_sum s h t (t-a) (l a) hh ((by dsimp [L] at ha₀; omega : t-a ≤ s.J).trans hj)
  have hsplit :
      (∑ a ∈ Ico L R, c a * ∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) =
        (∑ a ∈ Ico L R, c a * inner a) + (∑ a ∈ Ico L R, c a * outer a) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a ha => by rw [hw a ha, mul_add])
  have normalize (x y : ℤ) : 4*(x*y) = (2*x)*(2*y) := by ring
  have hi :
      4*(∑ a ∈ Ico L R, c a * inner a) =
        ∑ a ∈ Ico L R₁, (seedQuad s v d).eval a * (innerQuad s h E d t).eval a := by
    rw [mul_sum]
    apply sum_clipped (fun a ha => ((hcore a).mp ha).1)
    · intro a ha hn
      have haR := (mem_Ico.mp ha).2
      by_cases hv : (a+d)*v ≤ s.U
      · have hl : k ≤ l a := by
          by_contra! hl
          exact (Nat.not_lt_of_ge hn) ((hcore a).mpr ⟨haR,hv,hl⟩)
        simp [inner, Ico_eq_empty_of_le hl]
      · simp [c, slots, hv]
    · intro a ha
      obtain ⟨haR,hv,hl⟩ := (hcore a).mp (mem_Ico.mp ha).2
      rw [normalize, seedQuad_eq s v d a hv, ← innerQuad_eq s h E d t a hh he (ht a haR) hl.le]
  have ho :
      240*(∑ a ∈ Ico L R, c a * outer a) =
        if k < s.B+1 then intervalProduct (seedQuad s v d) (outerQuad s h t) L R₂ else 0 := by
    by_cases hk : k < s.B+1
    · rw [ite_eq_left hk, ← intervalProduct_eq, show (240 : ℤ) = 60*4 by decide, mul_assoc, mul_sum]
      congr 1
      apply sum_clipped (fun a ha => ((hedge a).mp ha).1)
      · intro a ha hn
        have haR := (mem_Ico.mp ha).2
        by_cases hv : (a+d)*v ≤ s.U
        · have hbound : ¬(k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a) :=
            fun ⟨_,hl,hs⟩ => (Nat.not_lt_of_ge hn) ((hedge a).mpr ⟨haR,hv,hl,hs⟩)
          simp only [outer, ite_eq_right hbound, mul_zero]
        · simp [c, slots, hv]
      · intro a ha
        obtain ⟨haR,hv,hl,hs⟩ := (hedge a).mp (mem_Ico.mp ha).2
        rw [normalize, seedQuad_eq s v d a hv, ← outerQuad_eq s h t a hh (ht a haR)]
        simp only [outer, hk, hl, hs, and_self, ite_true]
        rfl
    · simp [outer, hk]
  change _ = intervalProduct _ _ L R₁ + if k < s.B+1 then intervalProduct _ _ L R₂ else 0
  rw [hsplit, mul_add, ho, ← intervalProduct_eq (seedQuad s v d) (innerQuad s h E d t), ← hi]
  ring
theorem blockSurplus_eq (b : HighCore82258.Bank) (h E v : ℕ)
    (hh : h ≤ 131071) (hj : b.shape.J ≤ 131071-h) (he : 0 < E) :
    blockSurplus b.shape b.nodeRows b.poleMoment h E v = 240*surplus h b E v := by
  unfold blockSurplus scaledDebit surplus debit P1_7.debit
  rw [gain_eq_phases b.shape h E v hh he, mul_sub]
  push_cast
  congr 1
  unfold phase
  rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [phaseBlock_eq _ _ _ _ _ _ hh hj he, phaseBlock_eq _ _ _ _ _ _ hh hj he]
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open P1_7_6 (intervalProduct_eq)
open P1_7_6_4 (Core corePrefix diagonalCore)
open P1_7_6 (lt_seedEnd)
def bankCore (s : Shape) (h E v d k : ℕ) : Core :=
  let D : ℤ := (131071-h : ℕ)
  let p : ℤ := (E-1 : ℕ)
  let w : ℤ := (E*d : ℕ)
  ⟨k,E*d,E-1,seedEnd s v d (orderEnd s E v),seedQuad s v d,
    ⟨(k : ℤ)-w,-p⟩, ⟨2*(s.m*agreement : ℕ)-D*(w+k-1),-2-D*p⟩,
    2-4*(h : ℤ)-D⟩
def outerPart (s : Shape) (h E v d t : ℕ) : ℤ :=
  if colEnd s h t < s.B+1 then
    intervalProduct (seedQuad s v d) (outerQuad s h t) (t-s.J)
      (outerEnd s h E v d t (min t (orderEnd s E v-1)+1))
  else 0
private theorem diagonal_eq (s : Shape) (h E v d t k : ℕ) (hk : colEnd s h t = k) :
    phaseBlock s h E v d t = 60*diagonalCore (bankCore s h E v d k) s.J t + outerPart s h E v d t := by
  let C := bankCore s h E v d k
  let R := min t (orderEnd s E v-1)+1
  change intervalProduct (seedQuad s v d) (innerQuad s h E d t) (t-s.J)
      (innerEnd s h E v d t R) + outerPart s h E v d t =
    60*diagonalCore C s.J t + outerPart s h E v d t
  rw [← intervalProduct_eq, diagonalCore, ← sum_filter]
  congr 2
  have hmem : Ico (t-s.J) (innerEnd s h E v d t R) =
      (range C.cap).filter (fun a => a ≤ t ∧ t < a+(s.J+1) ∧ t+(C.offset+C.step*a) < C.column) := by
    have hend : 0 < orderEnd s E v := by
      unfold orderEnd
      split
      · exact Nat.succ_pos _
      · exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)
    ext a
    simp only [mem_Ico, mem_filter, mem_range, C, bankCore, innerEnd, lt_linearEnd, lt_seedEnd,
      hk, yStart, R]
    omega
  apply sum_congr hmem
  intro a _
  have ht : (innerQuad s h E d t).eval a = C.term a t := by
    simp only [C, bankCore, Core.term, P1_7_6_4.Line.at, innerQuad, hk, P1_7_6.Quad.eval_ofLines,
      widthOrigin, yStart, Nat.cast_add]
    ring
  rw [ht]
  rfl
private theorem colEnd_lt (s : Shape) (h t q : ℕ) :
    q < colEnd s h t ↔ q < s.B+1 ∧ 2*h*t+(131071-h)*q < s.m*agreement :=
  lt_linearEnd _ _ _ _ _
private theorem outer_sum (s : Shape) (h E v d l r k : ℕ) (hJ : s.J < 2*h)
    (hk : ∀ t ∈ Ico l r, colEnd s h t = k) :
    (∑ t ∈ Ico l r, outerPart s h E v d t) = if l < r then outerPart s h E v d l else 0 := by
  by_cases hl : l < r
  · rw [ite_eq_left hl]
    have hkl := hk l (mem_Ico.mpr ⟨le_rfl,hl⟩)
    apply sum_eq_single l
    · intro t ht hne
      have hat : l+1 ≤ t := by have := (mem_Ico.mp ht).1; omega
      have hkt := hk t ht
      unfold outerPart
      rw [hkt]
      split
      next hb =>
        have htop : s.m*agreement ≤ 2*h*l+(131071-h)*k := by
          by_contra! hpos
          exact (Nat.lt_irrefl _) (hkl ▸ (colEnd_lt s h l k).mpr ⟨hb,hpos⟩)
        have hstep := Nat.mul_le_mul_left (2*h) hat
        rw [Nat.mul_add, Nat.mul_one] at hstep
        have he : s.J < edgeShift s h t := by unfold edgeShift; rw [hkt]; omega
        have hz : outerEnd s h E v d t (min t (orderEnd s E v-1)+1) ≤ t-s.J :=
          (min_le_left _ _).trans (by omega)
        exact ite_eq_right (not_lt_of_ge hz)
      next => rfl
    · exact fun h => (h (mem_Ico.mpr ⟨le_rfl,hl⟩)).elim
  · simp [hl, Ico_eq_empty_of_le (Nat.le_of_not_gt hl)]
def groupValue (s : Shape) (h E v d l r k : ℕ) : ℤ :=
  if l < r then
    let C := bankCore s h E v d k
    corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l
  else 0
theorem groupValue_eq (s : Shape) (h E v d l r k : ℕ) (hJ : s.J < 2*h)
    (hk : ∀ t ∈ Ico l r, colEnd s h t = k) :
    groupValue s h E v d l r k = 6*(∑ t ∈ Ico l r, phaseBlock s h E v d t) := by
  unfold groupValue
  by_cases hl : l < r
  · rw [ite_eq_left hl]
    let C := bankCore s h E v d k
    change corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l = _
    have hs : (∑ t ∈ Ico l r, phaseBlock s h E v d t) =
        ∑ t ∈ Ico l r, (60*diagonalCore C s.J t + outerPart s h E v d t) :=
      sum_congr rfl fun t ht => diagonal_eq s h E v d t k (hk t ht)
    rw [hs, sum_add_distrib, ← mul_sum, outer_sum s h E v d l r k hJ hk, ite_eq_left hl]
    simp only [corePrefix, Core.prefix_eq, diagonalCore]
    rw [sum_Ico_eq_sub _ hl.le]
    ring
  · simp [hl, Ico_eq_empty_of_le (Nat.le_of_not_gt hl)]
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open P0_10_5 (Row scan)
open P0_10_5 (scan_sum)
def boundary (s : Shape) (h n i : ℕ) : ℕ :=
  if i = 0 then 0
  else linearEnd ((131071-h)*(s.B+1-i)) (2*h) (s.m*agreement) n
private theorem lt_boundary (s : Shape) (h n i t : ℕ) (hi : 0 < i) (hB : i ≤ s.B+1) :
    t < boundary s h n i ↔ t < n ∧ s.B+1-i < colEnd s h t := by
  have hb : s.B+1-i < s.B+1 := by omega
  simp only [boundary, ite_eq_right (Nat.ne_of_gt hi), colEnd, lt_linearEnd, hb, true_and, add_comm]
private theorem boundary_step (s : Shape) (h n i : ℕ) (hi : i+1 ≤ s.B+1) :
    boundary s h n i ≤ boundary s h n (i+1) := by
  by_cases hz : i = 0
  · simp [hz,boundary]
  by_contra! hn
  let t := boundary s h n (i+1)
  obtain ⟨ht,hk⟩ := (lt_boundary s h n i t (by omega) (by omega)).mp hn
  exact (Nat.lt_irrefl _) ((lt_boundary s h n (i+1) t (by omega) hi).mpr ⟨ht,by omega⟩)
private theorem group_column (s : Shape) (h n i t : ℕ) (hi : i+1 ≤ s.B+1)
    (ht : t ∈ Ico (boundary s h n i) (boundary s h n (i+1))) :
    colEnd s h t = s.B+1-i := by
  obtain ⟨hl,hr⟩ := mem_Ico.mp ht
  obtain ⟨htn,hq⟩ := (lt_boundary s h n (i+1) t (by omega) hi).mp hr
  have hu : colEnd s h t ≤ s.B+1-i := by
    by_contra! hh
    by_cases hz : i = 0
    · subst i
      have he : s.B+1 < colEnd s h t := by simpa using hh
      exact (Nat.lt_irrefl _) ((lt_linearEnd _ _ _ _ _).mp he).1
    · exact (not_lt_of_ge hl) ((lt_boundary s h n i t (by omega) (by omega)).mpr ⟨htn,hh⟩)
  omega
private theorem sum_groups (s : Shape) (h n count : ℕ) (hc : count ≤ s.B+1) (f : ℕ → ℤ) :
    (∑ i ∈ range count, ∑ t ∈ Ico (boundary s h n i) (boundary s h n (i+1)), f t) =
      ∑ t ∈ range (boundary s h n count), f t := by
  induction count with
  | zero => simp [boundary]
  | succ i ih =>
    rw [sum_range_succ, ih (by omega : i ≤ s.B+1), sum_range_add_sum_Ico f (boundary_step s h n i hc)]
def runValue (s : Shape) (h E v n i : ℕ) : ℤ :=
  let l := boundary s h n i
  let r := boundary s h n (i+1)
  let k := s.B+1-i
  groupValue s h E v 0 l r k - groupValue s h E v 1 l r k
def runRow (s : Shape) (h E v n i : ℕ) : Row :=
  ⟨true,runValue s h E v n i,runValue s (h+1) E v n i⟩
private theorem run_sum (s : Shape) (h E v n count : ℕ) (hc : count ≤ s.B+1)
    (hJ : s.J < 2*h) (hb : boundary s h n count = n) :
    (∑ i ∈ range count, runValue s h E v n i) =
      6*(∑ t ∈ range n, (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) := by
  conv_rhs => rw [← hb, ← sum_groups s h n count hc, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hc' : i+1 ≤ s.B+1 := Nat.le_trans (mem_range.mp hi) hc
  have hk := fun t ht => group_column s h n i t hc' ht
  rw [runValue, groupValue_eq _ _ _ _ _ _ _ _ hJ hk,
    groupValue_eq _ _ _ _ _ _ _ _ hJ hk, sum_sub_distrib]
  ring
theorem checks_of_runs (s : Shape) (N P h E v n count : ℕ) (left next cost costNext : ℤ)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hs : scan (runRow s h E v n) 0 count = ⟨true,left,next⟩)
    (hl : 6*scaledDebit s N P h = cost) (hr : 6*scaledDebit s N P (h+1) = costNext)
    (hp : cost < left) (hd : left+costNext ≤ next+cost) :
    BlockChecks s N P h E v := by
  have hbase := scan_sum (runRow s h E v n) 0 count false
  have hnext := scan_sum (runRow s h E v n) 0 count true
  rw [hs] at hbase hnext
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, runRow] at hbase hnext
  rw [run_sum s h E v n count hc hJ hb] at hbase
  rw [run_sum s (h+1) E v n count hc (by omega) hbNext] at hnext
  unfold BlockChecks blockSurplus
  rw [hn]
  omega
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open K1_14 (Shape)
open P0_10_5 (Row scan joinRows)
inductive Parts (f : ℕ → Row) (last : ℕ) : ℕ → ℕ → ℤ → ℤ → Prop
  | final {a : ℕ} {gain next : ℤ} :
      scan f a last = ⟨true, gain, next⟩ → Parts f last a last gain next
  | more {a count : ℕ} {gain next restGain restNext : ℤ} :
      scan f a 16 = ⟨true, gain, next⟩ → Parts f last (a+16) count restGain restNext →
      Parts f last a (16+count) (gain+restGain) (next+restNext)
theorem Parts.scan_eq {f : ℕ → Row} {last a count : ℕ} {gain next : ℤ}
    (parts : Parts f last a count gain next) : scan f a count = ⟨true, gain, next⟩ := by
  induction parts with
  | final h => exact h
  | @more a count gain next restGain restNext h _ ih =>
    exact joinRows a 16 count _ _ h ih rfl
theorem certify {s : Shape} {N P h E v n last count : ℕ}
    {gain next cost costNext : ℤ}
    (parts : Parts (runRow s h E v n) last 0 count gain next)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hl : 6*scaledDebit s N P h = cost) (hr : 6*scaledDebit s N P (h+1) = costNext)
    (hp : cost < gain) (hd : gain+costNext ≤ next+cost) :
    BlockChecks s N P h E v :=
  checks_of_runs s N P h E v n count gain next cost costNext
    hn hc hJ hb hbNext parts.scan_eq hl hr hp hd
end HighCore82258TerminalArithmetic
end

end Merged_HighCore82258TerminalArithmetic

-- merged module HighCore82258Terminal
section Merged_HighCore82258Terminal

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258Terminal

open HighCore82258
open HighCore82258TerminalArithmetic
open K1_14 (Shape)

private def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs =>
    BlockChecks ({t.shape with U := g.slots}) t.nodeRows t.poleMoment h e (g.seedCap+1) ∧
      GradeChecks t h (e+1) gs

private theorem grade_at (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
    (hc : GradeChecks t h e gs) (i : Fin gs.length) :
    BlockChecks {t.shape with U := (gs.get i).slots} t.nodeRows t.poleMoment h (i.val+e) ((gs.get i).seedCap+1) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · simpa [GradeChecks] using hc.1
    · have h' := ih (e+1) hc.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h'

set_option quotPrecheck false
local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

namespace h2395
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 : BlockChecks (S 180000) N P 2536 27 0 :=
  block! 2608,12,0x3bc0bd135a821094f82045800,0x3bc0bf52a131d269f4439bf00,(more! 0x32aa532a25b41e6fd81f3dae0,0x32b052fea7d109e80717fc900,(more! 0x860bf7ce67370c53504dc5a0,0x85d697777d266dac22e40fc0,(last! 0xb5b0c05effeda7f253290c0,0xb31c31071b0f2e9946f8e40)))
private theorem r1 : BlockChecks (S 172349) N P 2536 1 339 :=
  block! 2727,1,0x36c8e62f2113c445e214b5000,0x36c8e855f3f9e7c3fbffd0200,(more! 0x2d3d4346c8cda08a5eb03cc20,0x2d42c56164964bc01333f0760,(more! 0x7de571ec27b1e6635b8ac1a0,0x7dc205d888f6b8a770fb3560,(more! 0x1ad4b539d8cf3c8b04204d40,0x1aa13bb300d07937f6b5a4a0,(last! 0x75fc8c8fca550176340,0x49a5106669ec5a6c500))))
private theorem r2 : BlockChecks (S 173304) N P 2536 2 334 :=
  block! 2737,1,0x3764a2c9e149d49830b5e9800,0x3764a4f3c1892d4f8b810e700,(more! 0x2dc6bc78609897232cde1da00,0x2dcc4e7abaab8fdaf472622a0,(more! 0x7f286d5ac159c540f434d480,0x7f03e53cc3e97c6df3727560,(more! 0x1ab593c576a7bc8eac0a2780,0x1a8248a691eb5b49e7638fe0,(last! 0x63fbd0ffa1d82efb6ac0,0x53a6087148188bc8f500))))
private theorem r3 : BlockChecks (S 179574) N P 2536 3 328 :=
  block! 2766,2,0x3b78790cf33d2be596ee7e800,0x3b787b4add63063d0c3eea900,(more! 0x311253b5b651c5cd511d65800,0x311850c7152d740a6e1c0f080,(more! 0x88b5261c0c29b5a315a88d00,0x888de3bfd77bfb252b22c780,(more! 0x1da72b88f463f991fea3ad80,0x1d7052c494f643d6f10a4880,(last! 0x603cf5ccfe3cfc8b83680,0x5a06ff47f4328dc60cd00))))
private theorem r4 : BlockChecks (S 177387) N P 2536 4 323 :=
  block! 2768,2,0x3a082b3dd649e3390e55d2000,0x3a082d74c31b8ab75a4e99400,(more! 0x2ffe0ae7d226b1390bec45a00,0x3003e212b0099eb56868ce2a0,(more! 0x85105d1a989629e4eee61480,0x84e8e2413d48a5b03ed56f00,(more! 0x1b8c1c3a2be2b0048cd1be40,0x1b57c8193a39cc50dd8eb940,(last! 0x58c12eb72defd49ab0c20,0x53331329c32b0655677c0))))
private theorem r5 : BlockChecks (S 175478) N P 2536 5 318 :=
  block! 2770,2,0x38ca5e388fbb01cbe5967e800,0x38ca606962abb22a4f5fea900,(more! 0x2f10819d6e9b860b69a4eb480,0x2f163813f4cd65415b825d700,(more! 0x81e77af28432e29e6f395ac0,0x81bfbe9907d7d7b85c93eda0,(more! 0x19b0ffa70e3f1c5514dbf940,0x197ee9f2e69e3891232b3900,(last! 0x54f22959740e37c5e33c0,0x4fde4fbfa3aaa52b58b40))))
private theorem r6 : BlockChecks (S 176977) N P 2536 6 312 :=
  block! 2786,3,0x39c39fd94e6e80bfbaf563000,0x39c3a20eebcd75ea7926c6e00,(more! 0x2fe7ec148d7532f9cc6202b40,0x2fedbc05d0f440705df2f3de0,(more! 0x840603a519b2f67193f89e40,0x83dceee6f1fe060ffce1abc0,(more! 0x19abdd8f42ca39c06fa2bf40,0x1979ac7b50c8e9a22aa2aaa0,(last! 0x95b27ebcaa2e24c9fb8c0,0x8eb43b17e39e12c0fd620))))
private theorem r7 : BlockChecks (S 177384) N P 2536 7 306 :=
  block! 2798,4,0x3a07aab2d9f19395ee5c91800,0x3a07ace9c44ee11c5ba32f700,(more! 0x302f0fb7e300271b9a737ddc0,0x3034e68a1f9f5dfc8964799a0,(more! 0x8474fc4999624509681ac9c0,0x844aea6df194acbf2725a620,(more! 0x19088be514ee06512ccee0a0,0x18d6f872b431bb64eae0d120,(last! 0xc2784dca6c56ef53ae8e0,0xbaa7b1c0ea81d0fbef200))))
private theorem r8 : BlockChecks (S 176903) N P 2536 8 300 :=
  block! 2808,4,0x39b74514b7870839b6612c000,0x39b7474a185aa78254bd3f800,(more! 0x2fff1aae1ffb57e23d0e8d340,0x3004e92540101c85987a07ec0,(more! 0x838444e962a51dcc4237b080,0x83598971eb4839175e3f8940,(more! 0x17f14d83ab6fac80c7a9bac0,0x17c0e53c3571489bb1fe46c0,(last! 0xd13ff0ed55c3bd7f57440,0xc9964d8c09eee6788ffc0))))
private theorem r9 : BlockChecks (S 178309) N P 2536 9 293 :=
  block! 2827,5,0x3aa2e3b09ac5b8a55e2141000,0x3aa2e5ea79f0b7b659524ba00,(more! 0x30ce35c5132a7adc405338f00,0x30d41c49dbb2b80d357d4bac0,(more! 0x85809f057829ad6a2777b100,0x85548c2fd9bc36fef2e30d60,(more! 0x17b9a094ea188258210c9b80,0x17891fea16abe2f879479660,(last! 0x109f1f9ab14be9e81e2880,0x1018626f376a3f55730980))))
private theorem r10 : BlockChecks (S 178543) N P 2536 10 286 :=
  block! 2843,5,0x3aca48ce2325d0c4d862e8000,0x3aca4b08c1c4395baddc89000,(more! 0x30ff8fe0930cfbe330e38f000,0x31057a4f7c1d04d2cac568000,(more! 0x85ac72404b8828da250bb540,0x857f783c0df68eb6bc643060,(more! 0x16ee3aabf366b63a359e3200,0x16be5bc6819b1bf94fbc6100,(last! 0x10e1f16409e58fd13f5140,0x1062ce61d837d4241a4ea0))))
private theorem r11 : BlockChecks (S 179864) N P 2536 11 278 :=
  block! 2865,6,0x3ba9a6345a4e00436abcd9800,0x3ba9a87331b87e33a1fe34700,(more! 0x31c6a42ac974c9435a25cfbc0,0x31cca55ec696bc049a2a1ea20,(more! 0x878af186f3ebb222c42dc680,0x875ca581abb1c589f01eeee0,(more! 0x16940902cde1efc42d111a60,0x16640e96e30609e7557bd460,(last! 0x11261affcf05b424a225c0,0x10ace102e711d3b3630300))))
private theorem r12 : BlockChecks (S 179838) N P 2536 12 270 :=
  block! 2885,7,0x3ba53cb17fb1429ca0dcaa800,0x3ba53ef041d60a28a36b4a100,(more! 0x31d529a42fc8cc35ac1b6f540,0x31db2a3d3b352eda027bd7260,(more! 0x87507539f5c485a062be5cc0,0x872164200520d1846e3ee420,(more! 0x15a33fd2c81518b4d82056e0,0x1573fcf334469dde1f5a57a0,(last! 0xd7bdfb510b49272bb50c0,0xd19c342183215e475d1c0))))
private theorem r13 : BlockChecks (S 178760) N P 2536 13 262 :=
  block! 2901,8,0x3aeedd0d67cc19a33bf021800,0x3aeedf48b7f54343531619700,(more! 0x315218500ab4979b201e73340,0x3158060c6d5613e2e9d4852a0,(more! 0x8574b7dca63b43ebabe69880,0x85455a1e526271bf22971940,(more! 0x144f7c38e909f18e21f97520,0x1421911d41a5442d2e2a7fa0,(last! 0x817d4dac31b4c11812bc0,0x7d489b0bdb87492deb640))))
private theorem r14 : BlockChecks (S 179370) N P 2536 14 252 :=
  block! 2930,9,0x3b55ed64e68ef3619bd95c800,0x3b55efa229cce7e1e9d6cf500,(more! 0x31b7ac81cf277587be9428c40,0x31bda49e59129a9d19779fcc0,(more! 0x863a80bdd05c00b845291600,0x860a2e2255276940ef194280,(more! 0x13a5930ada9dd3455be01bc0,0x1377e0276aef0e4c65a32800,(last! 0x3fa8f4b04c5472cea9500,0x3d00f9389119d757a46c0))))
private theorem r15 : BlockChecks (S 179648) N P 2536 15 241 :=
  block! 2919,8,0x3b850386bea4500106e2b5800,0x3b8505c4e555803a9c0871f00,(more! 0x31ef050350d4130606e0562e0,0x31f501bb31ff98fe51f5a3a40,(more! 0x867ea9617502ee22ad2b6880,0x864d91614b40251ca56dc200,(more! 0x12e032b5559cbc151233f940,0x12b2e40da91164c866c12280,(last! 0x10c44c6c01091221c3080,0xfa337981f0aba4923960))))
private theorem r16 : BlockChecks (S 179554) N P 2536 16 229 :=
  block! 2875,7,0x3b751594d19c683d3b50d0800,0x3b7517d2ab6540203952d3d00,(more! 0x31f1cdf27076794b016c49500,0x31f7c8cb8bff9414e16095ea0,(more! 0x8631d43c208f94b3fc4398c0,0x86002dfe2e18dea951f7c560,(more! 0x12029cfda3266852143f4660,0x11d5e9fbc9224cec163d9fc0,(last! 0x90c6d728b261b6efc00,0x726cf10147678557840))))
private theorem r17 : BlockChecks (S 179916) N P 2536 17 215 :=
  block! 2837,5,0x3bb279b75f5a0fe4113d37800,0x3bb27bf6614ffa9cb1e409300,(more! 0x32334c9c0b40215ea2b66a320,0x32394d7d8f663ebbdea849360,(more! 0x869dcb14119e96e3b24d6f80,0x866b731461ec1ecefaf18380,(more! 0x115506d0eade86c78cfaf6e0,0x1128a46cef9fffb3cf498420,(last! 0x0,0x0))))
private theorem r18 : BlockChecks (S 179883) N P 2536 18 200 :=
  block! 2802,4,0x3bacdfb83d10572fc26772000,0x3bace1f724066441d1667d400,(more! 0x323cb89f980e6c0f0aa52dd00,0x3242b8abc6ba44f23de953e40,(more! 0x86702ff047949c297df5fc40,0x863d603a83f56ed2e4a9ee00,(more! 0x109241d6910c80e9d2ee9cc0,0x1066645d736b4ec75dcc15c0,(last! 0x0,0x0))))
private theorem r19 : BlockChecks (S 179596) N P 2536 19 184 :=
  block! 2771,3,0x3b7c3360d78e143f576257800,0x3b7c359ed3b3d7b083229d300,(more! 0x32219e84ab31f5d4945facc80,0x322799532b9cd5752b551dae0,(more! 0x85e13d4bcafd50c12ce60f40,0x85ae1fa2865bba6e216bd1a0,(more! 0xfc81093626a5800ee8d11e0,0xf9cd3e0318a48a4c463d940,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 179633) N P 2536 20 166 :=
  block! 2744,1,0x3b8278a5bdbf006f65f473000,0x3b827ae3d82a6ed1a19f60e00,(more! 0x323308a57e80b161051be1ba0,0x323903d5c7f62999d7ac9c640,(more! 0x85d6a402df42b7ec617cc6a0,0x85a320d48264e56cbf9837a0,(more! 0xf205c4e17fe6a95e04fee00,0xef57f234a81fb725faebba0,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 179890) N P 2536 21 146 :=
  block! 2719,16,0x3bae0fe0fa30ef5b3add08800,0x3bae121fe6e123afa6d11ed00,(more! 0x326299ce2235d3591eae2be00,0x32689931c9eb77d44c926bc60,(more! 0x8627000a775589b133d0bd60,0x85f30a57cf893699d2e77760,(last! 0xe90613e5bad6aef7a09a940,0xe65b44b10597f2a54dbaa80)))
private theorem r22 : BlockChecks (S 179925) N P 2536 22 125 :=
  block! 2696,16,0x3bb400da166403740418f9000,0x3bb403191fb6fc1440d646a00,(more! 0x32724bdb85e541c160a3aef40,0x32784b9a121af1c089da3c680,(more! 0x8622651ebc0c4e95cce098e0,0x85ee1fb1980830e4a7fb7b40,(last! 0xdf8eb0c1413338d43daca40,0xdce88436986bb3a546480c0)))
private theorem r23 : BlockChecks (S 179808) N P 2536 23 103 :=
  block! 2675,15,0x3ba0259d2fdefd13cbd025800,0x3ba027dbd97840f11b6927f00,(more! 0x326be9425d2e130dea29db9a0,0x3271e6ba7fa5289c6e58fece0,(more! 0x85e46b96b24e463e79f6e800,0x85aff02de78a0051cb47bca0,(last! 0xd5f5a3de293cd4241bbd020,0xd35516affcd27b76ba85b40)))
private theorem r24 : BlockChecks (S 179897) N P 2536 24 79 :=
  block! 2656,14,0x3baf400cbe6c340265629f000,0x3baf424bb0d68f992e4bc0600,(more! 0x3281f1f74938d959f99a7f6c0,0x3287f0bd3a45df93a2d779920,(more! 0x85fb748f8fa8222eccf75fa0,0x85c6b470481f22148cd19b60,(last! 0xcd96d154625cc8854dffa20,0xcaf946c07517b52a91ee380)))
private theorem r25 : BlockChecks (S 179864) N P 2536 25 54 :=
  block! 2639,13,0x3ba9a6345a4e00436abcd9800,0x3ba9a87331b87e33a1fe34700,(more! 0x328637752ae2b0a45fc6b75a0,0x328c356d41e64fe5231ffb6c0,(more! 0x85e4b42b0ca4291a83e2baa0,0x85afc375c3d5037a6d23dfa0,(last! 0xc52383eb03909f4c808ebe0,0xc289ce9b12266d50ce52aa0)))
private theorem r26 : BlockChecks (S 180000) N P 2536 26 27 :=
  block! 2623,13,0x3bc0bd135a821094f82045800,0x3bc0bf52a131d269f4439bf00,(more! 0x32a1db7a4843f931689bacaa0,0x32a7db946a242ca9c12cd66e0,(more! 0x86140b405ae227fc14091040,0x85dedd78c2b3610c41b5a7e0,(last! 0xbda0ec69bd9321766644e40,0xbb08ede85a2e27e939813e0)))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 900) N P 7773 8 0 :=
  block! 54,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b44034829a1c5c40,0x1b440b0132a3efce0)
private theorem r1 : BlockChecks (S 821) N P 7773 1 27 :=
  block! 63,1,0x16b4691bfccae8780,0x16b46c2e9238bb500,(last! 0x16b469e60cf39a680,0x16b47065d051b2120)
private theorem r2 : BlockChecks (S 771) N P 7773 2 26 :=
  block! 62,1,0x140c8975326695d00,0x140c8c57ef5305e00,(last! 0x140c907ab565f9380,0x140c96636d8c3b740)
private theorem r3 : BlockChecks (S 796) N P 7773 3 24 :=
  block! 66,2,0x155b30a8b220bf240,0x155b33a35b4de0980,(last! 0x155b34cc89b45ea60,0x155b3afff981a4da0)
private theorem r4 : BlockChecks (S 855) N P 7773 4 21 :=
  block! 73,3,0x189ade77390253e00,0x189ae1aa576bf9400,(last! 0x189ae1c092142b7e0,0x189ae8aae50a3f6c0)
private theorem r5 : BlockChecks (S 879) N P 7773 5 17 :=
  block! 67,2,0x19fe04ee09e5aec00,0x19fe08381f97ac800,(last! 0x19fe0de212de406c0,0x19fe1519ad30c4f80)
private theorem r6 : BlockChecks (S 900) N P 7773 6 11 :=
  block! 61,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b3cccb63cd44c040,0x1b3cd43274f8314e0)
private theorem r7 : BlockChecks (S 899) N P 7773 7 4 :=
  block! 57,1,0x1b2d6acfe1cdcfd00,0x1b2d6e2d1ae6c1e00,(last! 0x1b2d770f87d996c00,0x1b2d7e8890a242a40)
theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,trivial⟩
end h7773

set_option maxHeartbeats 800000

private theorem checks (b : Band) (hb : b ≠ .h2367) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.none
    | h7773 => exact h7773.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.all
    | h7773 => exact h7773.all
  cases x with
  | none => exact hn
  | some i => exact grade_at _ _ _ _ hc i


end HighCore82258Terminal

end Merged_HighCore82258Terminal
