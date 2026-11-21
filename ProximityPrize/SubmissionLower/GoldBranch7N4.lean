import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.UpperBranch6
import ProximityPrize.SubmissionLower.HighCore82219Source
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
end P3_7_4_2
end
