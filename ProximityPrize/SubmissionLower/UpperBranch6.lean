import ProximityPrize.SubmissionLower.UpperBranch7
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_6
open Finset
open K1_14 (Shape triangle)
open P1 (HighBand agreement)
open P1_7 (Bank Test debit jointGain tested threshold seedThreshold)
def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m * agreement : ℕ) + (j : ℤ) - (131071 - (h : ℤ)) * q - 2 * (h : ℤ) * t
def surplus (h : ℕ) (b : Bank) (E v : ℕ) : ℤ :=
  (jointGain h b.shape E v : ℤ) - (debit h b : ℤ)
def orderEnd (s : Shape) (E v : ℕ) : ℕ :=
  if v = 0 then s.B/E+1 else min (s.B/E+1) (s.U/v+1)
def linearEnd (base step bound cap : ℕ) : ℕ :=
  if base < bound then
    if step = 0 then cap else min cap ((bound - 1 - base)/step + 1)
  else 0
def colEnd (s : Shape) (h t : ℕ) : ℕ :=
  linearEnd (2*h*t) (131071-h) (s.m*agreement) (s.B+1)
def edgeShift (s : Shape) (h t : ℕ) : ℕ :=
  2*h*t + (131071-h)*colEnd s h t + 1 - s.m*agreement
structure Quad where
  constant : ℤ
  linear : ℤ
  square : ℤ
def Quad.eval (p : Quad) (a : ℤ) : ℤ :=
  p.constant + p.linear*a + p.square*a*a
def Quad.ofLines (x y z w : ℤ) : Quad :=
  ⟨x*z, x*w+y*z, y*w⟩
def prefixProduct (p q : Quad) (n : ℕ) : ℤ :=
  let x : ℤ := n
  let t := x*(x-1)
  let u := t*(2*x-1)
  60*x*(p.constant*q.constant) +
    30*t*(p.constant*q.linear+p.linear*q.constant) +
    10*u*(p.constant*q.square+p.linear*q.linear+p.square*q.constant) +
    15*t*t*(p.linear*q.square+p.square*q.linear) +
    2*u*(3*t-1)*(p.square*q.square)
def intervalProduct (p q : Quad) (L R : ℕ) : ℤ :=
  if L < R then prefixProduct p q R - prefixProduct p q L else 0
def seedEnd (s : Shape) (v d R : ℕ) : ℕ :=
  if v = 0 then R else min R (s.U/v+1-d)
def yStart (E d t : ℕ) := t+E*d
def seedQuad (s : Shape) (v d : ℕ) : Quad :=
  let u : ℤ := (s.U : ℤ) - (v : ℤ)*d
  Quad.ofLines (u+1) (-(v : ℤ)) (u+2) (-(v : ℤ))
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
  Quad.ofLines (k-l) (-p) (2*widthOrigin s h t-D*(l+k-1)) (-2-D*p)
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
def scaledDebit (s : Shape) (N P h : ℕ) : ℤ :=
  240*((triangle s.U : ℤ)*N + 2*(h : ℤ)*(s.U+1)*P)
def blockSurplus (s : Shape) (N P h E v : ℕ) : ℤ :=
  (∑ t ∈ range (s.J+orderEnd s E v), (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) -
    scaledDebit s N P h
def BlockChecks (s : Shape) (N P h E v : ℕ) : Prop :=
  0 < blockSurplus s N P h E v ∧ blockSurplus s N P h E v ≤ blockSurplus s N P (h+1) E v
def TestChecks (b : HighBand) (x : Test b) : Prop :=
  let t := tested b x
  BlockChecks t.shape t.nodeRows t.poleMoment b.row.lo (threshold b x) (seedThreshold b x)
end P1_7_6
end
section
namespace P1_7_6
open Finset
open K1_14 (Shape shapeSum slots)
open P1 (agreement)
open P1_7 (Bank debit jointGain)
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
  simp only [debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring
private theorem surplus_convex (h : ℕ) (b : Bank) (E v : ℕ) (hh : h+2 ≤ 131071) :
    surplus (h+1) b E v + surplus (h+1) b E v ≤
      surplus h b E v + surplus (h+2) b E v := by
  have hg := gain_convex b.shape h E v hh
  have hd := debit_affine h b
  dsimp only at hg
  unfold surplus
  omega
private theorem rise_of_convex {f : ℕ → ℤ} {lo h : ℕ}
    (hc : ∀ n < h, f (n+1) + f (n+1) ≤ f n + f (n+2))
    (hl : lo ≤ h) (hf : f lo ≤ f (lo+1)) :
    f lo ≤ f h ∧ f h ≤ f (h+1) := by
  induction h with
  | zero =>
    have he : lo = 0 := by omega
    subst lo
    exact ⟨le_rfl, hf⟩
  | succ h ih =>
    rcases Nat.lt_or_eq_of_le hl with hlt | he
    · obtain ⟨hh, hs⟩ := ih (fun n hn => hc n (by omega)) (by omega)
      have ht := hc h (by omega)
      exact ⟨hh.trans hs, by rw [show h+1+1 = h+2 by omega]; omega⟩
    · subst lo
      exact ⟨le_rfl, hf⟩
theorem strict_of_first_difference {lo h : ℕ} {b : Bank} {E v : ℕ}
    (hl : lo ≤ h) (hh : h < 131071)
    (hpos : 0 < surplus lo b E v) (hrise : surplus lo b E v ≤ surplus (lo+1) b E v) :
    debit h b < jointGain h b.shape E v := by
  have hmon := rise_of_convex (f := fun h => surplus h b E v)
    (fun n hn => surplus_convex n b E v (by omega)) hl hrise
  have hsur := hpos.trans_le hmon.1
  unfold surplus at hsur
  omega
end P1_7_6
end
section
namespace P1_7_6
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P1_7 (jointGain)
def phase (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ t ∈ range (s.J + orderEnd s E v), ∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
    (slots s.U ((a+d)*v) : ℤ) *
      ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)
private theorem slots_anti (U : ℕ) : Antitone (slots U) := by
  intro a b hab
  unfold slots
  split_ifs with ha hb hb
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul (by omega) (by omega)
  all_goals omega
private theorem sum_range_guard {f : ℕ → ℤ} (L R : ℕ)
    (hz : ∀ a, R ≤ a → a < L → f a = 0) :
    ∑ a ∈ range L, f a = ∑ a ∈ range R, if a < L then f a else 0 := by
  have hf : (range R).filter (· < L) = range (min L R) := by
    ext a
    simp only [mem_range, mem_filter, lt_min_iff]
    tauto
  rw [← sum_filter, hf]
  symm
  apply sum_subset (range_mono (min_le_left _ _))
  intro a ha hnot
  simp only [mem_range, lt_min_iff] at ha hnot
  exact hz a (by omega) ha
private theorem position_phases (s : Shape) (h E v q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => slots s.U (a*v)
    let x := s.m*P1.agreement+j-q*(131071-h)
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
          (s.m*P1.agreement+j-q*(131071-h)-2*h*(j+a))) +
        slots s.U (g*v)*(s.m*P1.agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
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
private theorem diagonal (J R : ℕ) (f : ℕ → ℕ → ℤ) :
    (∑ j ∈ range (J+1), ∑ a ∈ range (R+1), f j a) =
      ∑ t ∈ range (J+R+1), ∑ a ∈ Ico (t-J) (min t R+1), f (t-a) a := by
  calc
    _ = ∑ a ∈ range (R+1), ∑ j ∈ range (J+1), f j a := sum_comm
    _ = ∑ a ∈ range (R+1), ∑ t ∈ Ico a (a+(J+1)), f (t-a) a := by
      apply sum_congr rfl
      intro a _
      rw [sum_Ico_eq_sum_range]
      simp
    _ = ∑ a ∈ range (R+1), ∑ t ∈ range (J+R+1),
        if a ≤ t ∧ t-a ≤ J then f (t-a) a else 0 := by
      apply sum_congr rfl
      intro a ha
      have ha' := mem_range.mp ha
      rw [← sum_filter]
      congr 1
      ext t
      simp only [mem_Ico, mem_filter, mem_range]
      omega
    _ = ∑ t ∈ range (J+R+1), ∑ a ∈ range (R+1),
        if a ≤ t ∧ t-a ≤ J then f (t-a) a else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [← sum_filter]
      congr 1
      ext a
      simp only [mem_Ico, mem_filter, mem_range, Nat.lt_succ_iff, le_min_iff]
      omega
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
end P1_7_6
end
section
namespace P1_7_6
open Finset
open P1 (agreement)
open K1_14 (Shape)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
theorem lt_linearEnd (base step bound cap i : ℕ) :
    i < linearEnd base step bound cap ↔ i < cap ∧ base + step*i < bound := by
  unfold linearEnd
  by_cases hb : base < bound
  · rw [ite_eq_left hb]
    by_cases hs : step = 0
    · simp [hs, hb]
    · rw [ite_eq_right hs, lt_min_iff, Nat.lt_succ_iff,
        Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hs), Nat.mul_comm i step]
      omega
  · rw [ite_eq_right hb]
    omega
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
end P1_7_6
end
section
namespace P1_7_6
open Finset
theorem Quad.eval_ofLines (x y z w a : ℤ) :
    (Quad.ofLines x y z w).eval a = (x+y*a)*(z+w*a) := by
  unfold Quad.ofLines Quad.eval
  dsimp only
  ring
private theorem prefix_eq (p q : Quad) (n : ℕ) :
    60 * (∑ a ∈ range n, p.eval a * q.eval a) = prefixProduct p q n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [prefixProduct, Quad.eval, Nat.cast_succ]
    ring
theorem intervalProduct_eq (p q : Quad) (L R : ℕ) :
    60 * (∑ a ∈ Ico L R, p.eval a * q.eval a) = intervalProduct p q L R := by
  unfold intervalProduct
  by_cases h : L < R
  · rw [ite_eq_left h, sum_Ico_eq_sub _ h.le, mul_sub, prefix_eq, prefix_eq]
  · rw [ite_eq_right h, Ico_eq_empty_of_le (Nat.le_of_not_gt h), sum_empty, mul_zero]
end P1_7_6
end
section
namespace P1_7_6_4
open Finset
open P1_7_6 (Quad)
structure Line where
  base : ℤ
  slope : ℤ
def Line.at (l : Line) (a : ℤ) : ℤ := l.base+l.slope*a
def Line.sub (l r : Line) : Line := ⟨l.base-r.base,l.slope-r.slope⟩
def Line.addConst (l : Line) (c : ℤ) : Line := ⟨l.base+c,l.slope⟩
def Line.scale (l : Line) (c : ℤ) : Line := ⟨c*l.base,c*l.slope⟩
def Line.shift (l r : Line) (c : ℤ) : Line := ⟨l.base+c*r.base,l.slope+c*r.slope⟩
structure Cubic where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
def Cubic.at (p : Cubic) (a : ℤ) : ℤ := p.c0+p.c1*a+p.c2*a^2+p.c3*a^3
def Cubic.lines (x y z : Line) : Cubic :=
  let q := Quad.ofLines x.base x.slope y.base y.slope
  ⟨q.constant*z.base, q.constant*z.slope+q.linear*z.base,
    q.linear*z.slope+q.square*z.base, q.square*z.slope⟩
theorem Cubic.lines_at (x y z : Line) (a : ℤ) :
    (Cubic.lines x y z).at a = x.at a * y.at a * z.at a := by
  simp only [Cubic.lines, Cubic.at, Quad.ofLines, Line.at]
  ring
def windowCubic (L R xLine yLine : Line) (b d : ℤ) : Cubic :=
  let n := R.sub L
  let x := xLine.shift L b
  let y := yLine.shift L d
  let m := n.addConst (-1)
  let w := (n.scale 2).addConst (-1)
  let f := Cubic.lines n x y
  let g := Cubic.lines n m (x.scale d |>.shift y b)
  let k := Cubic.lines n m w
  ⟨6*f.c0+3*g.c0+b*d*k.c0, 6*f.c1+3*g.c1+b*d*k.c1,
    6*f.c2+3*g.c2+b*d*k.c2, 6*f.c3+3*g.c3+b*d*k.c3⟩
private theorem windowCubic_at (L R xLine yLine : Line) (b d a : ℤ) :
    (windowCubic L R xLine yLine b d).at a =
      let n := R.at a-L.at a
      let x := xLine.at a+b*L.at a
      let y := yLine.at a+d*L.at a
      6*n*x*y+3*n*(n-1)*(d*x+b*y)+b*d*n*(n-1)*(2*n-1) := by
  simp only [windowCubic, Cubic.at]
  let f := Cubic.lines (R.sub L) (xLine.shift L b) (yLine.shift L d)
  let g := Cubic.lines (R.sub L) ((R.sub L).addConst (-1))
    (((xLine.shift L b).scale d).shift (yLine.shift L d) b)
  let k := Cubic.lines (R.sub L) ((R.sub L).addConst (-1)) (((R.sub L).scale 2).addConst (-1))
  change (6*f.c0+3*g.c0+b*d*k.c0) + (6*f.c1+3*g.c1+b*d*k.c1)*a +
    (6*f.c2+3*g.c2+b*d*k.c2)*a^2 + (6*f.c3+3*g.c3+b*d*k.c3)*a^3 = _
  trans 6*f.at a+3*g.at a+b*d*k.at a
  · unfold Cubic.at
    ring
  simp only [f, g, k, Cubic.lines_at, Line.at, Line.sub, Line.shift, Line.addConst, Line.scale]
  ring
private theorem linePair_range (x y b d : ℤ) (n : ℕ) :
    6*(∑ t ∈ range n, (x+b*t)*(y+d*t)) =
      6*(n : ℤ)*x*y+3*n*(n-1)*(d*x+b*y)+b*d*n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    ring
theorem windowCubic_eq (L R xLine yLine : Line) (b d a : ℤ) (l r : ℕ)
    (hl : L.at a = l) (hr : R.at a = r) (hle : l ≤ r) :
    (windowCubic L R xLine yLine b d).at a =
      6*(∑ t ∈ Ico l r, (xLine.at a+b*t)*(yLine.at a+d*t)) := by
  rw [windowCubic_at, hl, hr, sum_Ico_eq_sum_range]
  have hs : (∑ t ∈ range (r-l), (xLine.at a+b*(↑(l+t) : ℤ))*(yLine.at a+d*(↑(l+t) : ℤ))) =
      ∑ t ∈ range (r-l), ((xLine.at a+b*l)+b*t)*((yLine.at a+d*l)+d*t) := by
    apply sum_congr rfl
    intro t _
    push_cast
    ring
  rw [hs, linePair_range, Nat.cast_sub hle]
def prefixCubic (p : Quad) (q : Cubic) (n : ℕ) : ℤ :=
  let x : ℤ := n
  let t := x*(x-1)
  let u := t*(2*x-1)
  60*x*(p.constant*q.c0) +
    30*t*(p.constant*q.c1+p.linear*q.c0) +
    10*u*(p.constant*q.c2+p.linear*q.c1+p.square*q.c0) +
    15*t*t*(p.constant*q.c3+p.linear*q.c2+p.square*q.c1) +
    2*u*(3*t-1)*(p.linear*q.c3+p.square*q.c2) +
    5*t*t*(2*t-1)*(p.square*q.c3)
theorem prefix_eq (p : Quad) (q : Cubic) (n : ℕ) :
    prefixCubic p q n = 60*(∑ a ∈ range n, p.eval a * q.at a) := by
  induction n with
  | zero => simp [prefixCubic]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih]
    simp only [prefixCubic, Quad.eval, Cubic.at, Nat.cast_succ]
    ring
end P1_7_6_4
end
section
namespace P1_7_6_4
open Finset
open K1_14 (Shape)
open P1 (agreement)
open P1_7_6
structure Core where
  column : ℕ
  offset : ℕ
  step : ℕ
  cap : ℕ
  seed : Quad
  countLine : Line
  widthLine : Line
  widthSlope : ℤ
def Core.term (C : Core) (a t : ℕ) : ℤ :=
  (C.countLine.at a-t)*(C.widthLine.at a+C.widthSlope*t)
def Core.slice (C : Core) (x c a : ℕ) : Finset ℕ :=
  Ico (a+c) (min x (C.column-(C.offset+C.step*a)))
def Core.nonemptyEnd (C : Core) (x c : ℕ) : ℕ :=
  linearEnd (c+C.offset) (C.step+1) C.column (min C.cap (x-c))
def Core.switchEnd (C : Core) (x c : ℕ) : ℕ :=
  linearEnd (x+C.offset) C.step (C.column+1) (C.nonemptyEnd x c)
private theorem lt_nonemptyEnd (C : Core) (x c a : ℕ) :
    a < C.nonemptyEnd x c ↔ a < C.cap ∧ a+c < min x (C.column-(C.offset+C.step*a)) := by
  rw [Core.nonemptyEnd, lt_linearEnd, lt_min_iff, lt_min_iff, Nat.add_mul, Nat.one_mul]
  omega
private theorem lt_switchEnd (C : Core) (x c a : ℕ) :
    a < C.switchEnd x c ↔ a < C.nonemptyEnd x c ∧ x+C.offset+C.step*a ≤ C.column := by
  rw [Core.switchEnd, lt_linearEnd, Nat.lt_succ_iff]
def cubicInterval (p : Quad) (q : Cubic) (l r : ℕ) : ℤ :=
  if l < r then prefixCubic p q r - if l = 0 then 0 else prefixCubic p q l else 0
private theorem cubicInterval_eq (p : Quad) (q : Cubic) (l r : ℕ) :
    cubicInterval p q l r = 60*(∑ a ∈ Ico l r, p.eval a*q.at a) := by
  unfold cubicInterval
  by_cases h : l < r
  · rw [ite_eq_left h, sum_Ico_eq_sub _ h.le, mul_sub, ← prefix_eq, ← prefix_eq]
    split
    · subst l
      simp [prefixCubic]
    · rfl
  · rw [ite_eq_right h, Ico_eq_empty_of_le (by omega), sum_empty, mul_zero]
def Core.window (C : Core) (x c : ℕ) : ℤ :=
  let b := C.switchEnd x c
  let n := C.nonemptyEnd x c
  let L : Line := ⟨c,1⟩
  let fixed : Line := ⟨x,0⟩
  let falling : Line := ⟨(C.column : ℤ)-C.offset,-(C.step : ℤ)⟩
  let f := fun R => windowCubic L R C.countLine C.widthLine (-1) C.widthSlope
  cubicInterval C.seed (f fixed) 0 b + cubicInterval C.seed (f falling) b n
theorem Core.window_eq (C : Core) (x c : ℕ) :
    C.window x c = 360*(∑ a ∈ range C.cap, C.seed.eval a * ∑ t ∈ C.slice x c a, C.term a t) := by
  let n := C.nonemptyEnd x c
  let b := C.switchEnd x c
  let f := fun a : ℕ => C.seed.eval a * ∑ t ∈ C.slice x c a, C.term a t
  have hb : b ≤ n := Nat.le_of_not_gt fun h => (Nat.lt_irrefl _) ((lt_switchEnd C x c n).mp h).1
  have hn : n ≤ C.cap := Nat.le_of_not_gt fun h => (Nat.lt_irrefl _) ((lt_nonemptyEnd C x c C.cap).mp h).1
  have hs : (∑ a ∈ range n, f a) = ∑ a ∈ range C.cap, f a := by
    apply sum_subset (range_subset_range.mpr hn)
    intro a ha ha'
    have ha := mem_range.mp ha
    have hz : min x (C.column-(C.offset+C.step*a)) ≤ a+c := by
      by_contra! h
      exact ha' (mem_range.mpr ((lt_nonemptyEnd C x c a).mpr ⟨ha,h⟩))
    simp [f, Core.slice, Ico_eq_empty_of_le hz]
  rw [← hs, ← sum_range_add_sum_Ico f hb, mul_add]
  simp only [Core.window, ← Nat.Ico_zero_eq_range b, cubicInterval_eq]
  change 60*(∑ a ∈ Ico 0 b, _) + 60*(∑ a ∈ Ico b n, _) =
    360*(∑ a ∈ Ico 0 b, f a) + 360*(∑ a ∈ Ico b n, f a)
  have hmul : (360 : ℤ) = 60*6 := rfl
  rw [hmul]
  simp only [mul_assoc, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro a ha
    have hab := (mem_Ico.mp ha).2
    obtain ⟨han,hfix⟩ := (lt_switchEnd C x c a).mp hab
    have hav := ((lt_nonemptyEnd C x c a).mp han).2
    rw [show min x (C.column-(C.offset+C.step*a)) = x by omega] at hav
    have hv := windowCubic_eq ⟨(c : ℤ),1⟩ ⟨(x : ℤ),0⟩ C.countLine C.widthLine (-1)
      C.widthSlope a (a+c) x (by simp [Line.at, add_comm]) (by simp [Line.at]) hav.le
    rw [hv]
    simp only [f, Core.slice, min_eq_left (by omega : x ≤ C.column-(C.offset+C.step*a)), Core.term]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    ring
  · apply sum_congr rfl
    intro a ha
    obtain ⟨ha₁,ha₂⟩ := mem_Ico.mp ha
    have hav := ((lt_nonemptyEnd C x c a).mp ha₂).2
    have hfall : C.column-(C.offset+C.step*a) ≤ x := by
      by_contra! h
      exact (not_lt_of_ge ha₁) ((lt_switchEnd C x c a).mpr ⟨ha₂,by omega⟩)
    have hle : C.offset+C.step*a ≤ C.column := by omega
    rw [min_eq_right hfall] at hav
    have hv := windowCubic_eq ⟨(c : ℤ),1⟩
      ⟨(C.column : ℤ)-C.offset,-(C.step : ℤ)⟩ C.countLine C.widthLine (-1)
      C.widthSlope a (a+c) (C.column-(C.offset+C.step*a))
      (by simp [Line.at, add_comm])
      (by simp only [Line.at, Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]; ring) hav.le
    rw [hv]
    simp only [f, Core.slice, min_eq_right hfall, Core.term]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    ring
theorem Core.prefix_eq (C : Core) (x J : ℕ) :
    C.window x 0 - C.window x (J+1) =
      360*(∑ t ∈ range x, ∑ a ∈ range C.cap,
        if a ≤ t ∧ t < a+(J+1) ∧ t+(C.offset+C.step*a) < C.column
        then C.seed.eval a*C.term a t else 0) := by
  rw [Core.window_eq, Core.window_eq, ← mul_sub, sum_comm (s := range x), ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro a _
  have hfilter (c : ℕ) :
      C.slice x c a = (range x).filter
        (fun t => a+c ≤ t ∧ t+(C.offset+C.step*a) < C.column) := by
    ext t
    simp only [Core.slice, mem_Ico, lt_min_iff, mem_filter, mem_range]
    omega
  simp_rw [hfilter, mul_sum, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  by_cases hl : a ≤ t <;> by_cases hu : t < a+(J+1) <;>
    by_cases hk : t+(C.offset+C.step*a) < C.column <;>
    have hu' : a+(J+1) ≤ t ↔ ¬t < a+(J+1) := by omega
  all_goals omega
end P1_7_6_4
end
section
namespace P1_7_6
open Finset
open P1 (agreement)
open K1_14 (Shape slots triangle)
open P1_7 (debit)
private theorem lt_seedEnd (s : Shape) (v d R a : ℕ) :
    a < seedEnd s v d R ↔ a < R ∧ (a+d)*v ≤ s.U := by
  unfold seedEnd
  by_cases hv : v = 0
  · simp [hv]
  · rw [ite_eq_right hv, lt_min_iff, ← Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)]
    omega
private theorem yStart_eq (E d t a : ℕ) (he : 0 < E) (ha : a ≤ t) :
    t-a+E*(a+d) = yStart E d t + (E-1)*a := by
  apply Int.ofNat_inj.mp
  simp only [yStart, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub he, Nat.cast_one]
  ring
private theorem seedQuad_eq (s : Shape) (v d a : ℕ) (ha : (a+d)*v ≤ s.U) :
    (seedQuad s v d).eval a = 2*(slots s.U ((a+d)*v) : ℤ) := by
  let n := s.U-(a+d)*v
  have hc : (n : ℤ) = (s.U : ℤ)-((a : ℤ)+d)*v := by
    simp only [n, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  have hp : ((n : ℤ)+1)*((n : ℤ)+2) = 2*(triangle n : ℤ) := by
    have ht := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self (n+1)))
    change (n+1)*(n+2)/2*2 = (n+1)*(n+2) at ht
    have hz := congrArg (fun k : ℕ => (k : ℤ)) ht
    change (↑(triangle n*2 : ℕ) : ℤ) = (↑((n+1)*(n+2) : ℕ) : ℤ) at hz
    push_cast at hz
    linarith
  rw [slots, ite_eq_left ha]
  change _ = 2*(triangle n : ℤ)
  rw [← hp, hc, seedQuad, Quad.eval_ofLines]
  ring
private theorem widthOrigin_eq (s : Shape) (h t a q : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    width s h q (t-a) t = widthOrigin s h t - a - ((131071-h : ℕ) : ℤ)*q := by
  simp only [width, widthOrigin, Nat.cast_sub hh, Nat.cast_sub ha, Nat.cast_ofNat]
  ring
private theorem innerQuad_eq (s : Shape) (h E d t a : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (ha : a ≤ t) (hl : t-a+E*(a+d) ≤ colEnd s h t) :
    2*(∑ q ∈ Ico (t-a+E*(a+d)) (colEnd s h t), width s h q (t-a) t) =
      (innerQuad s h E d t).eval a := by
  rw [twice_width_interval s h t (t-a) _ _ hh hl, innerQuad, Quad.eval_ofLines,
    yStart_eq E d t a he ha]
  simp only [widthOrigin, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  ring
private theorem outerQuad_eq (s : Shape) (h t a : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    2*width s h (colEnd s h t) (t-a) t = (outerQuad s h t).eval a := by
  rw [widthOrigin_eq s h t a _ hh ha]
  simp only [outerQuad, Quad.eval]
  ring
private theorem sum_clipped {f g : ℕ → ℤ} {L R T : ℕ}
    (hr : ∀ a, a < T → a < R)
    (hz : ∀ a ∈ Ico L R, T ≤ a → f a = 0)
    (he : ∀ a ∈ Ico L T, f a = g a) :
    (∑ a ∈ Ico L R, f a) = ∑ a ∈ Ico L T, g a := by
  calc
    _ = ∑ a ∈ Ico L T, f a := by
      symm
      apply sum_subset
      · intro a ha
        exact mem_Ico.mpr ⟨(mem_Ico.mp ha).1, hr a (mem_Ico.mp ha).2⟩
      · intro a ha hn
        exact hz a ha (le_of_not_gt fun h => hn (mem_Ico.mpr ⟨(mem_Ico.mp ha).1,h⟩))
    _ = _ := sum_congr rfl he
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
theorem blockSurplus_eq (b : P1_7.Bank) (h E v : ℕ)
    (hh : h ≤ 131071) (hj : b.shape.J ≤ 131071-h) (he : 0 < E) :
    blockSurplus b.shape b.nodeRows b.poleMoment h E v = 240*surplus h b E v := by
  unfold blockSurplus scaledDebit surplus debit
  rw [gain_eq_phases b.shape h E v hh he, mul_sub]
  push_cast
  congr 1
  unfold phase
  rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [phaseBlock_eq _ _ _ _ _ _ hh hj he, phaseBlock_eq _ _ _ _ _ _ hh hj he]
end P1_7_6
end
section
namespace P1_7_6_4
open Finset
open K1_14 (Shape)
open P1 (agreement)
open P1_7_6
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
def diagonalCore (C : Core) (J t : ℕ) : ℤ :=
  ∑ a ∈ range C.cap,
    if a ≤ t ∧ t < a+(J+1) ∧ t+(C.offset+C.step*a) < C.column
    then C.seed.eval a*C.term a t else 0
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
    simp only [C, bankCore, Core.term, Line.at, innerQuad, hk, Quad.eval_ofLines,
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
def corePrefix (C : Core) (J x : ℕ) : ℤ := C.window x 0 - C.window x (J+1)
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
end P1_7_6_4
end
