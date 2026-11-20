import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.UpperBranch6
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (HighBand agreement)
open P3_7 (Bank Test debit jointGain tested threshold seedThreshold)
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
def TestChecks (b : HighBand) (x : Test b) : Prop :=
  let t := tested b x
  BlockChecks t.shape t.nodeRows t.poleMoment b.row.lo (threshold b x) (seedThreshold b x)
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape shapeSum slots)
open P3 (agreement)
open P3_7 (Bank debit jointGain)
open private rise_of_convex from ProximityPrize.SubmissionLower.UpperBranch6
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
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P3 (agreement)
open P3_7 (jointGain)
open private slots_anti sum_range_guard diagonal from ProximityPrize.SubmissionLower.UpperBranch6
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
end P3_7_4
end
section
namespace P3_7_4
open Finset
open P3 (agreement)
open K1_14 (Shape)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
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
end P3_7_4
end
section
namespace P3_7_4
open Finset
open P3 (agreement)
open K1_14 (Shape slots triangle)
open P3_7 (debit)
open P1_7_6 (intervalProduct_eq)
open private lt_seedEnd yStart_eq seedQuad_eq sum_clipped from ProximityPrize.SubmissionLower.UpperBranch6
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
theorem blockSurplus_eq (b : P3_7.Bank) (h E v : ℕ)
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
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (agreement)
open P1_7_6 (intervalProduct_eq)
open P1_7_6_4 (Core corePrefix diagonalCore)
open private lt_seedEnd from ProximityPrize.SubmissionLower.UpperBranch6
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
end P3_7_4
end
section
namespace P3_7_4
open P3 (HighBand)
open P3_7 (Bank Grade Test grades terminal)
def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs => BlockChecks {t.shape with U := g.slots} t.nodeRows t.poleMoment h e (g.seedCap+1)
      ∧ GradeChecks t h (e+1) gs
private theorem checks_at_grade (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
    (hc : GradeChecks t h e gs) (i : Fin gs.length) :
    BlockChecks {t.shape with U := (gs.get i).slots} t.nodeRows t.poleMoment h
      (i.val+e) ((gs.get i).seedCap+1) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · change BlockChecks {t.shape with U := g.slots} t.nodeRows t.poleMoment h (0+e) (g.seedCap+1)
      simpa only [Nat.zero_add] using hc.1
    · have h := ih (e+1) hc.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h
theorem tests_of_gradeChecks (b : HighBand)
    (hz : TestChecks b none) (hs : GradeChecks (terminal b) b.row.lo 1 (grades b)) (x : Test b) :
    TestChecks b x := by
  cases x with
  | none => exact hz
  | some i => exact checks_at_grade _ _ _ _ hs i
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (agreement)
open P0_10_5 (Row scan)
open private scan_sum from ProximityPrize.SubmissionLower.PortHighBase
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
end P3_7_4
end
section
namespace P3_7_4
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
end P3_7_4
end
section
namespace P3_7_4
open P3_7 (Test)
open P0_10_5 (Row)
local notation "S" u => (⟨124,173,32,u⟩ : K1_14.Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 22832869
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
private theorem r0 : BlockChecks (S 946) N P 7773 7 0 :=
  r! 57,1;0x1e110619562db71c0,0x1e1109a388df00e80; (z! 0x1e170bd72aee0e480,0x1e1713d446d33f5c0)
private theorem r1 : BlockChecks (S 886) N P 7773 1 26 :=
  r! 67,2;0x1a6770724bb553ec0,0x1a6773c31431c0c80; (z! 0x1a6c14eaf40e08420,0x1a6c1c1d901a4af00)
private theorem r2 : BlockChecks (S 913) N P 7773 2 24 :=
  r! 71,2;0x1c05d1e372dd1a280,0x1c05d54e118aea700; (z! 0x1c09805f614986ba0,0x1c0987deabfc71960)
private theorem r3 : BlockChecks (S 946) N P 7773 3 22 :=
  r! 76,3;0x1e110619562db71c0,0x1e1109a388df00e80; (z! 0x1e15edfeeac865a80,0x1e15f5f27d5a52500)
private theorem r4 : BlockChecks (S 946) N P 7773 4 19 :=
  r! 76,3;0x1e110619562db71c0,0x1e1109a388df00e80; (z! 0x1e164d1f9c2cf9420,0x1e1655163799283a0)
private theorem r5 : BlockChecks (S 946) N P 7773 5 14 :=
  r! 67,2;0x1e110619562db71c0,0x1e1109a388df00e80; (z! 0x1e15565b8c4b42100,0x1e155e4a3faae98c0)
private theorem r6 : BlockChecks (S 946) N P 7773 6 8 :=
  r! 61,1;0x1e110619562db71c0,0x1e1109a388df00e80; (z! 0x1e16bd15d1e123400,0x1e16c51055c53dac0)
theorem checks_7773 : ∀ x : Test .h7773, TestChecks .h7773 x :=
  tests_of_gradeChecks .h7773 r0 ⟨r1, r2, r3, r4, r5, r6, trivial⟩
end P3_7_4
end
section
namespace P3_7_4
open P3 (HighBand)
open P3_7 (Test debit jointGain tested threshold seedThreshold terminal)
def c1 : Prop := ∀ x : Test .h2274, TestChecks .h2274 x
def c2 : Prop := ∀ x : Test .h2294, TestChecks .h2294 x
private theorem window (b : HighBand) :
    (terminal b).shape.J ≤ 2218 := by
  cases b <;> decide
private theorem checked_interval (b : HighBand) (h : ℕ) (hl : b.row.lo ≤ h) (hu : h ≤ b.row.hi)
    (x : Test b) (hc : TestChecks b x) :
    debit h (tested b x) < jointGain h (tested b x).shape (threshold b x) (seedThreshold b x) := by
  let t := tested b x
  let E := threshold b x
  let v := seedThreshold b x
  have hj : t.shape.J = (terminal b).shape.J := by cases x <;> rfl
  have he : 0 < E := by cases x <;> exact Nat.succ_pos _
  have hJ := window b
  have hu' := (P3_7.terminal_guards b).2.1
  have hw : b.row.lo+1 ≤ 131071 := by omega
  have hJ' : t.shape.J ≤ 131071-b.row.lo := by omega
  have hJ'' : t.shape.J ≤ 131071-(b.row.lo+1) := by omega
  change BlockChecks t.shape t.nodeRows t.poleMoment b.row.lo E v at hc
  unfold BlockChecks at hc
  rw [blockSurplus_eq t b.row.lo E v (by omega) hJ' he,
    blockSurplus_eq t (b.row.lo+1) E v hw hJ'' he] at hc
  obtain ⟨hp, hr⟩ := hc
  change debit h t < jointGain h t.shape E v
  exact strict_of_first_difference hl (by omega) (by omega) (by omega)
theorem of_children (h1 : c1) (h2 : c2) : P3_7.c4 := by
  intro b h hl hu x
  apply checked_interval b h hl hu x
  cases b with
  | h2274 => exact h1 x
  | h2294 => exact h2 x
  | h7773 => exact checks_7773 x
end P3_7_4
end
section
namespace P3_7_4_1
open P3_7 (Test)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks TestChecks Parts certify tests_of_gradeChecks)
local notation "S" u => (⟨6600,9172,1952,u⟩ : K1_14.Shape)
local notation "N" => 0x1e372113d00000
local notation "P" => 0xae27f29bc6cc
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
private theorem r0 : BlockChecks (S 211000) N P 2274 23 0 :=
  r! 2351,2;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x32d28e9ee7391a7eed47a2d20,0x32d88d87de97a27b7ed816560; p! 0x44a20da3aa6955c42e1b99c0,0x444351676213c090d0de1660; z! 0,0)
private theorem r1 : BlockChecks (S 162873) N P 2274 1 359 :=
  r! 2406,3;0x20d8c3ac1b073a9e789752c00,0x20d8c4dc6f2da339acd4c2200; (p! 0x1dc09a84692f1941609ff13c0,0x1dc42a52f762c93aff79d3500; p! 0x31533cdd2c0e13a2edfc8420,0x311ca40e992ae0e150f4ebc0; z! 0x2f603d33c7d1d85794b960,0x2db69faf21fc0c60e0cdc0)
private theorem r2 : BlockChecks (S 164297) N P 2274 2 354 :=
  r! 2417,4;0x216c59316c087c8d9bcd30c00,0x216c5a646954a2c8934fff200; (p! 0x1e4b0f08306648b71825a66e0,0x1e4eaf11ac4970f03c35a3de0; p! 0x31daea9971de84d400ee43c0,0x31a37b65796e30ca7107f580; z! 0x39dc6d2604690b39c6cc20,0x3808a4039331c526145120)
private theorem r3 : BlockChecks (S 166033) N P 2274 3 349 :=
  r! 2428,4;0x2222014655ee7e9abfab9fc00,0x2222027c919dddfbb7eedda00; (p! 0x1ef46f7f4c08a64a909cb0080,0x1ef823813e4b373472e6e0f60; p! 0x3293a62a920fcc858ca427e0,0x325b2553e0fa74bfbe11dd00; z! 0x45d095b2b0ba3da2d71140,0x43d2bff318b713020f8940)
private theorem r4 : BlockChecks (S 167408) N P 2274 4 343 :=
  r! 2441,5;0x22b33d8a45ccb5a08abcc2e00,0x22b33ec313319a4ea74833500; (p! 0x1f7d79ecd5fac288454759be0,0x1f813df26a4f840cbcff731e0; p! 0x330b0f3dc1cb294308ae6a00,0x32d1b1297e0d9102693004a0; z! 0x515ae2a220938792083140,0x4f3d18f1a413eeda6d5a20)
private theorem r5 : BlockChecks (S 169216) N P 2274 5 337 :=
  r! 2455,5;0x2374089b0793dbefaa4bf0e00,0x237409d735cca01dd5c7e8500; (p! 0x20319e973312ba8285fe9c200,0x203577d9c429e4752de7b5280; p! 0x33c8a543b511dcd3aa6cc260,0x338e170baa16a6152f297400; z! 0x5e241e575038799436c980,0x5be6b49bb830563c51c3a0)
private theorem r6 : BlockChecks (S 171591) N P 2274 6 331 :=
  r! 2471,6;0x24746edda94f255eb4daff000,0x2474701e4792e7121f0236800; (p! 0x211f6d8626f6656af881c01c0,0x2123630341c70c90515b03b40; p! 0x34e40f90ce5b855b107d3600,0x34a7e347f260795420419040; z! 0x6c548edc39b8b49ac8ace0,0x69f6f39997169fe082d360)
private theorem r7 : BlockChecks (S 173880) N P 2274 7 324 :=
  r! 2489,6;0x256eed8bd5a5c0b3969361e00,0x256eeed0bad1805603c8d9d00; (p! 0x220864d70fcb55cf40fb10f20,0x220c75f5ff25c51bb8754d300; p! 0x35ef51561768d6e992c5c700,0x35b1872f8b63bbe4a2e76600; z! 0x7959fc10d1d50f877a6700,0x76e55d23c18f573a610fc0)
private theorem r8 : BlockChecks (S 177154) N P 2274 8 317 :=
  r! 2511,7;0x26dafb393fd87be866aa32a00,0x26dafc844314e45f2e5c48f00; (p! 0x2358372dda46dcbda865b8e80,0x235c706cccd79a5fdd2ca21c0; p! 0x37a4aa912f61b17ecb2bb700,0x37648119b7f2c793bc28a5c0; z! 0x87cbfd590e9f3a2c4b8fc0,0x853c5331bdfac5382f5ec0)
private theorem r9 : BlockChecks (S 180959) N P 2274 9 309 :=
  r! 2538,8;0x288a9b4fa3c12f0015e884000,0x288a9ca1c30d0b2360b9e6000; (p! 0x24e58598708c19d8186516dc0,0x24e9ee77f3177e463a61f5a20; p! 0x39bc71a041e93bb2deebbcc0,0x39796f1a6fb73390269fe140; z! 0x94fcfb37f416a858e399c0,0x92555c43f1dfa1fe3d7940)
private theorem r10 : BlockChecks (S 187112) N P 2274 10 301 :=
  r! 2574,9;0x2b57fa517058f8d709039be00,0x2b57fbaf0ed507ca504d80d00; (p! 0x27754d343240cfc79b56a39c0,0x277a05304eb145b29b55f7c00; p! 0x3d860f9065b2a851dbfc5160,0x3d3e55390134d75fa6b226a0; z! 0xa53bda6022de435dc505e0,0xa2694f97766293c8228800)
private theorem r11 : BlockChecks (S 195637) N P 2274 11 291 :=
  r! 2625,11;0x2f6182d0afc4de7a16610f400,0x2f61843e3c0cc17ed83760e00; (p! 0x2b2299d6266b2b5baebc29c20,0x2b27c3f99dc2699d7d9d28540; p! 0x433971020f308bfb0c89fe00,0x42eae8577a8ee3fffb22db60; z! 0xb591a3da6898c1a4bd61e0,0xb2808891932c7faa66a940)
private theorem r12 : BlockChecks (S 211000) N P 2274 12 278 :=
  r! 2711,14;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x32239f191ff250da45f4b5c40,0x3229a40d74e22de5baf925540; p! 0x4eb97ca41032e6d230df71e0,0x4e5e00a627b0f943528a9840; z! 0xd054441370d1dc1fe95560,0xccb291cdc1181501083260)
private theorem r13 : BlockChecks (S 211000) N P 2274 13 263 :=
  r! 2658,12;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x3239831888f165c999ccb3800,0x323f8791953b8a29009fd0080; p! 0x4d94d87cdc9ad4ac758779e0,0x4d38c721659503a1fd5f7420; z! 0x96ff6192ace31e5d645000,0x93fac65f05770eb4bfa060)
private theorem r14 : BlockChecks (S 211000) N P 2274 14 245 :=
  r! 2608,11;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x324d061ca490221a721e66140,0x32530a2c8275ecde5f733ef60; p! 0x4c8d7e68f168a8a3e404ffa0,0x4c30da93b810a54418afcac0; z! 0x65e14d0261809f9a9621e0,0x6375b36f850f0e17f269c0)
private theorem r15 : BlockChecks (S 211000) N P 2274 15 226 :=
  r! 2564,9;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x32607053aef28b0bffac74e60,0x326673ccc7e47df2ddd6998e0; p! 0x4b800a8ef03dd6a1e5a29540,0x4b22d450cfdaaa4af4307740; z! 0x3d52c40ee3904a326818e0,0x3b830f84991d110e556d60)
private theorem r16 : BlockChecks (S 211000) N P 2274 16 203 :=
  r! 2526,8;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x3270d02341e84e79f7056c680,0x3276d335cca9c39e2fb939da0; p! 0x4a96f855ae163bdddb0252e0,0x4a3936d506fbc1d03a1fd0c0; z! 0x1ff889298ac232d8658d80,0x1eba711cd3034de65aafc0)
private theorem r17 : BlockChecks (S 211000) N P 2274 17 178 :=
  r! 2492,7;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x328048aabb3f18d27fc79ff60,0x32864b4bf4799cc6592b790e0; p! 0x49b260fd0fb95a236fa151c0,0x4954207893686586dc70e0e0; z! 0xcdbadb0bd8fc9782605e0,0xc23a7a4ea71190b8255e0)
private theorem r18 : BlockChecks (S 211000) N P 2274 18 151 :=
  r! 2462,5;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x328edb2f0942e368d9b0222c0,0x3294dd58879e71f2010689600; p! 0x48d30cd3ef4d0a04b9931100,0x4874668e7726e3bc7419a000; z! 0x3107097ad4f4cadd15440,0x2c5a6898504e8fc0e0300)
private theorem r19 : BlockChecks (S 211000) N P 2274 19 122 :=
  r! 2435,5;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x329c8d5c0e411f77f7e8bbe20,0x32a28f0adca6e4aec35240ba0; p! 0x47fb093ae06d3005a13ce0a0,0x479c28e23230cd2ee46bbfc0; z! 0x20caf44eee6ce6916ca0,0x17c30893569ecbadb100)
private theorem r20 : BlockChecks (S 211000) N P 2274 20 90 :=
  r! 2411,4;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x32a8c34b8e71e4c3c9035e420,0x32aec493c14c6513d5b1a5220; p! 0x47379c74ba2d2fa6301084c0,0x46d8b9773ba40034ab3c8f60; z! 0,0)
private theorem r21 : BlockChecks (S 211000) N P 2274 21 56 :=
  r! 2389,3;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x32b4433f982a9379efea582a0,0x32ba4420206bd41d0748677a0; p! 0x467f8d7b3528c6ad40c00220,0x4620b0f574e4630e2e4c58a0; z! 0,0)
private theorem r22 : BlockChecks (S 211000) N P 2274 22 20 :=
  r! 2369,2;0x371c3bf7415ff2e6c1a241e00,0x371c3d81824c7d3b16ce29d00; (p! 0x32bf14afbf849b319698c21a0,0x32c515295622a3f93644a4760; p! 0x45d27c03e576605c8c1a2c40,0x4573a5ecd60430ba3e24d8e0; z! 0,0)
theorem proof : P3_7_4.c1 :=
  tests_of_gradeChecks .h2274 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, trivial⟩
end P3_7_4_1
end
section
namespace P3_7_4_2
open P3_7 (grades terminal)
open P3_7_4 (TestChecks)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks GradeChecks Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
private theorem r0 : BlockChecks (S 234728) N P 2294 22 0 :=
  r! 2696,3;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4d463ec84376f01a0731fffe0,0x4d5ba78802b2e35ad61970880; p! 0x11b694283fc23343bd6bfe800,0x11b46663e2b18a509266ecfc0; p! 0x695127cee3fe54cfc177d7a0,0x681fabb9f84d05fc86a01660; z! 0,0)
private theorem r1 : BlockChecks (S 179424) N P 2294 1 331 :=
  r! 2761,6;0x3b5cf34f1895ff896a1267a00,0x3b5cf58c880247776096c2100; (p! 0x2c3453c9b6e60b5650ffc2700,0x2c40c4098b7f993c508c31040; p! 0xa4c0fa73e87a5755876730c0,0xa4ad1e0ff6814f1f99e22840; p! 0x4cb9d2520119b76c67f5f0c0,0x4c13137513f821369b72de40; z! 0x10f5764ab3d859a212236c0,0x1043fb9019d7ee476c18ce0)
private theorem r2 : BlockChecks (S 180915) N P 2294 2 326 :=
  r! 2773,6;0x3c5a668c1c1ccdf433232c800,0x3c5a68ce4f6bc0198189bb400; (p! 0x2cfa0137d291bb4a798fe5b00,0x2d06a7848295e188bf5e5b680; p! 0xa78d4c2b779d80b625ad39a0,0xa77918660bc3b887d79ffe80; p! 0x4d4ae32db5429eaab55a3e40,0x4ca18bc4b3b9e0320401e4c0; z! 0x12e5696c53947cef4e704c0,0x122d35cffd300712ec5f280)
private theorem r3 : BlockChecks (S 182775) N P 2294 3 321 :=
  r! 2788,7;0x3d99839f403e2917326663000,0x3d9985e76556ff8bd848ff800; (p! 0x2df083eaa11107ab12d76e6a0,0x2dfd6e3789173c89a02331c40; p! 0xab1277134de14a0178f6a000,0xaafdd586017a23c526386500; p! 0x4e2dce4946f1b5a999eb54a0,0x4d81179a0a0940629c9e84a0; z! 0x150237c5654806ec9e2e060,0x14434057c0a646f14e0cbc0)
private theorem r4 : BlockChecks (S 185099) N P 2294 4 316 :=
  r! 2804,7;0x3f2cd18a8f5012ee5ebdab800,0x3f2cd3da21d3d373926aa0c00; (p! 0x2f25a6e75920864b97b6a9340,0x2f32e719f01d62208947d3680; p! 0xaf84c3ba066c3d4022e4dd00,0xaf6f97a5f956b6bb7b9c6680; p! 0x4f79a136080b902de0310040,0x4ec88f633bdff219952e6500; z! 0x175354d795e912334cd0f00,0x168d5a8ec2a6f5cb7d8b300)
private theorem r5 : BlockChecks (S 187083) N P 2294 5 310 :=
  r! 2822,8;0x4089262419526063fd6bc3800,0x4089287a0313e13dd2ae1cc00; (p! 0x303316b179fc3c3f7064bc600,0x3040a151ca47bd206b868c880; p! 0xb35f178eeebe8d615ed80a00,0xb34972f2450ecacaead49a00; p! 0x506d2fa0cd25a379274065e0,0x4fb838d3e203dd9b5d5d13a0; z! 0x195642a5dfba4c10898f200,0x188c271e097a4d2cf528fa0)
theorem ordinary : TestChecks .h2294 none := r0
theorem grades1 (tail : GradeChecks (terminal .h2294) 2294 6 ((grades .h2294).drop 5))
    : GradeChecks (terminal .h2294) 2294 1 (grades .h2294) :=
  ⟨r1, r2, r3, r4, r5, tail⟩
end P3_7_4_2
end
section
namespace P3_7_4_2
open P3_7 (grades terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks GradeChecks Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
private theorem r6 : BlockChecks (S 189769) N P 2294 6 304 :=
  r! 2843,9;0x4266a4919cb2f469c3045c400,0x4266a6f01c0c7229c8b5dca00; (p! 0x31a0719df9affcca80ee1c5e0,0x31ae622764a2f0f0aee638940; p! 0xb8a58ece9fdc73c62cc60040,0xb88f457a8e27d81beb2eac00; p! 0x5205822401091a99e3e83560,0x514b2ada886e898941045a00; z! 0x1b8f4741b7b6bfa26262820,0x1ac03606a766d9df76b3240)
private theorem r7 : BlockChecks (S 192397) N P 2294 7 297 :=
  r! 2866,9;0x444068d6fa4343043dfa72c00,0x44406b3ddfc09cf24d5150e00; (p! 0x330bcd1c33eafc7d747db7a40,0x331a2304c91f649a14f0524c0; p! 0xbde4dc2cd3a9c15367f6aa40,0xbdcdee81ea90e3d00282d9c0; p! 0x538e1013b5b2901df69a5c60,0x52ce3fa180b42b0aec116800; z! 0x1d71ba66da1a4cf9f0034e0,0x1c9fbf88a44e11ee532b300)
private theorem r8 : BlockChecks (S 196316) N P 2294 8 290 :=
  r! 2895,10;0x470f0248484c911b8d3eb9200,0x470f04bbb42e58e2550d11d00; (p! 0x352cb2d3b0b811fdfed920100,0x353ba244b788fd2f18540b3c0; p! 0xc5d74c7e72724169ba1bd700,0xc5bf6688c5cdb6aaca4db640; p! 0x565343c90475003ec4e9be60,0x558b39acb19f72228a9b3de0; z! 0x1fabf8ef25ebe0ace282a20,0x1ed48545d6079f705b00080)
private theorem r9 : BlockChecks (S 201102) N P 2294 9 282 :=
  r! 2932,12;0x4a9039803382dd03d3aa6e600,0x4a903c02eb22a375bb10e4f00; (p! 0x37d239a1b40f1fc5962881500,0x37e1e900873133cb9c4454a60; p! 0xcfc671a3939b2f2cfa16a360,0xcfad54f96441aa1e7b967520; p! 0x59fcfcd3fdf884ef485124a0,0x592aa38ea7734fda9bd80ea0; z! 0x21c8fcf16967f480effc4e0,0x20eb24527d1dc95e6a23000)
private theorem r10 : BlockChecks (S 209391) N P 2294 10 274 :=
  r! 2983,14;0x50d53a92fd0c246d31b986000,0x50d53d303272f11fa603df000; (p! 0x3c8352c89c6f41de7c7d13be0,0x3c94593060a3dda25008ae380; p! 0xe187bc540664fd14ae7814a0,0xe16c755cb8445d52d8921a80; p! 0x6146169b393fd9ce1d19b440,0x60619d9501c667d845728700; z! 0x2519f9c2ad2692a43158e80,0x242bd1f0cc4457326e25920)
theorem grades2 (tail : GradeChecks (terminal .h2294) 2294 11 ((grades .h2294).drop 10))
    : GradeChecks (terminal .h2294) 2294 6 ((grades .h2294).drop 5) :=
  ⟨r6, r7, r8, r9, r10, tail⟩
end P3_7_4_2
end
section
namespace P3_7_4_2
open P3_7 (grades terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks GradeChecks Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
private theorem r11 : BlockChecks (S 221352) N P 2294 11 263 :=
  r! 3060,16;0x5a536dd25592197a347bdca00,0x5a537095c50e158df97f9e900; (p! 0x439337f3693405235fdcbf5a0,0x43a6471607a6aa0e2888c6620; p! 0xfc7b4082a8ee0d17db798420,0xfc5cae3d60f1b54945aaa060; p! 0x6cf221ff77f00bbd22f492e0,0x6bf264cb6cbb17317135ec40; z! 0x2960ca68b3314f9ff4f6ce0,0x28560622097a5d2789320e0)
private theorem r12 : BlockChecks (S 234728) N P 2294 12 250 :=
  r! 3094,2;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4bf8a3eee2f1335f03f779980,0x4c0e1b43fc9041523b5133660; p! 0x11c5c98be74ab90acedc46280,0x11c3a199df302c4fc1607a9a0; p! 0x7a82aa94c2c8425539b0bf60,0x7962087e7eb8a18190ac5a60; p! 0x2a5d0b33b766ca1f1abefe0,0x293aec39ff575bc319ef060; z! 0,0)
private theorem r13 : BlockChecks (S 234728) N P 2294 13 234 :=
  r! 3027,15;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4c2418a6f67a84f7400041e80,0x4c398f2e922cbbb950274e0e0; p! 0x11c4bc9d2133989bfa8f84b00,0x11c293c2f2f91566d47727900; p! 0x787ee07c0472e3e17d51eb00,0x775bd7ca2756c18ea5475ac0; z! 0x20367bea3d50108b35ef400,0x1f3c7c39c6f4e3d8588e440)
private theorem r14 : BlockChecks (S 234728) N P 2294 14 215 :=
  r! 2969,13;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4c4ab702cbc865e2046177aa0,0x4c602cf373bfd32e62272d380; p! 0x11c3dff278852bbd0817e29c0,0x11c1b630f86c7c236036f80c0; p! 0x76afe15269e41de562f289c0,0x758a7b488d3d29a755263b80; z! 0x175a5d710cd7c5bfd7205e0,0x1687afca464a251fadd01c0)
private theorem r15 : BlockChecks (S 234728) N P 2294 15 194 :=
  r! 2919,11;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4c6f744ac13f266bf592cf040,0x4c84e951a13333fb25a92ef20; p! 0x11c2c1c83ddc32e18a4f035a0,0x11c097379b785ebf3ea1db260; p! 0x74eee8af2d76827f425e5220,0x73c71cfcd7af01ae09cf7ee0; z! 0xfca5fb3b22b847b94d49e0,0xf1fc4f285e597003749f00)
theorem grades3 (tail : GradeChecks (terminal .h2294) 2294 16 ((grades .h2294).drop 15))
    : GradeChecks (terminal .h2294) 2294 11 ((grades .h2294).drop 10) :=
  ⟨r11, r12, r13, r14, r15, tail⟩
end P3_7_4_2
end
section
namespace P3_7_4_2
open P3_7 (grades terminal)
open P0_10_5 (Row)
open P3_7_4 (BlockChecks GradeChecks Parts certify)
local notation "S" u => (⟨7550,10506,2218,u⟩ : K1_14.Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
local notation "z!" l "," r => Parts.final (gain := l) (next := r) (Row.eq_of_check rfl)
local notation "p!" l "," r ";" p => Parts.more (gain := l) (next := r) (Row.eq_of_check rfl) p
local notation "r!" nn "," d ";" l "," r ";" p => certify
  (n := nn) (last := d) (cost := l) (costNext := r)
  p rfl (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide)
private theorem r16 : BlockChecks (S 234728) N P 2294 16 171 :=
  r! 2875,10;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4c9238c223d92265fef275ee0,0x4ca7aca1801ceba7008accae0; p! 0x11c1753132a586050565d6f00,0x11bf49e963345aa934faa3240; p! 0x7338e03c42daea1da6893c00,0x720eafe5f9b6722885764bc0; z! 0x9bac520fc9adc6ea71e080,0x93853bebe490fa41401360)
private theorem r17 : BlockChecks (S 234728) N P 2294 17 145 :=
  r! 2837,8;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4cb10ec47a4c6f45c1bf1cac0,0x4cc681baa4d59b4ce1b6b55a0; p! 0x11c062db708319e09f7147220,0x11be36e32398b86afdb7d84e0; p! 0x71a3b9c07b15220df52d1500,0x70773990f1845786c3914be0; z! 0x5452b19170487343bee160,0x4e9501653c8802c91bf640)
private theorem r18 : BlockChecks (S 234728) N P 2294 18 117 :=
  r! 2802,7;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4cce38d245d00aa7fc43aaae0,0x4ce3aab6e39d07454a5a633e0; p! 0x11bf341c3e8a61b585c40d200,0x11bd0787fc497899e6e2434c0; p! 0x7013999b31a370b3ecf2a640,0x6ee4f736872850409029bc40; z! 0x24e20601a37559cbc57140,0x21616185e06ab054b51bc0)
private theorem r19 : BlockChecks (S 234728) N P 2294 19 86 :=
  r! 2771,6;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4ce813d1b20e9e966a5b5d360,0x4cfd84e5d109d5f9485e41b80; p! 0x11be412ae1b0414d7ebfd6700,0x11bc13fec6f7527f67d6207c0; p! 0x6e9e8f00903690e13f493080,0x6d6e236c1d4a7b39e300c880; z! 0xadafff0fb064bce62c360,0x939fb281047c7d3ba2f80)
private theorem r20 : BlockChecks (S 234728) N P 2294 20 53 :=
  r! 2744,5;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4d008a525aeb13e7e11a82700,0x4d15fa7c7ae75ca2f7ee36200; p! 0x11bd3d9211a9fde2652ddc1a0,0x11bb0fde7d35d737339d8c800; p! 0x6d30dfd49a7cf1976c62b7e0,0x6bff4595fb9a7d5e9b9a25a0; z! 0x11c25988f5a8a73b0eba0,0xc0d6c2a900a17b544e00)
private theorem r21 : BlockChecks (S 234728) N P 2294 21 18 :=
  r! 2719,4;0x6590e50f38b8b871c5c744a00,0x6590e7fd67fe5196d46fe2900; (p! 0x4d17a0ee8e76c37e46661ba20,0x4d2d101fe7aac9de8299ace80; p! 0x11bc31e61188deea2097757a0,0x11ba03b8ced11f3d04f8209a0; p! 0x6bd146c0dc978ce37ce22de0,0x6a9f6855f04e9cec9e4c5e80; z! 0,0)
theorem grades4 : GradeChecks (terminal .h2294) 2294 16 ((grades .h2294).drop 15) :=
  ⟨r16, r17, r18, r19, r20, r21, trivial⟩
end P3_7_4_2
end
section
namespace P3_7_4_2
theorem proof : P3_7_4.c2 :=
  P3_7_4.tests_of_gradeChecks .h2294 ordinary (grades1 (grades2 (grades3 grades4)))
end P3_7_4_2
end
