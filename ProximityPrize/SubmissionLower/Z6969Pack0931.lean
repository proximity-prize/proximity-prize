import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.UpperBranch6
import ProximityPrize.SubmissionLower.KoalaRectCutoff
import ProximityPrize.SubmissionLower.R6960TerminalReceipts
import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes
import ProximityPrize.SubmissionLower.Z6969Pack0424
import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks
import ProximityPrize.SubmissionLower.R6960RescueGeometryBills
import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6960TerminalDegrees
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0796
import ProximityPrize.SubmissionLower.Z6969Pack0920
import ProximityPrize.SubmissionLower.Z6969Pack0760
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0720
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0672
import ProximityPrize.SubmissionLower.Z6969Pack0673
import ProximityPrize.SubmissionLower.Z6969Pack0674
import ProximityPrize.SubmissionLower.Z6969Pack0676
import ProximityPrize.SubmissionLower.Z6969Pack0677
import ProximityPrize.SubmissionLower.Z6969Pack0678
import ProximityPrize.SubmissionLower.Z6969Pack0679
import ProximityPrize.SubmissionLower.Z6969Pack0681
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0683
import ProximityPrize.SubmissionLower.Z6969Pack0684
import ProximityPrize.SubmissionLower.Z6969Pack0686
import ProximityPrize.SubmissionLower.Z6969Pack0687
import ProximityPrize.SubmissionLower.Z6969Pack0688
import ProximityPrize.SubmissionLower.Z6969Pack0689
import ProximityPrize.SubmissionLower.Z6969Pack0700

set_option Elab.async false

-- Source: Research6969.FarTerminalArithmetic
section Z6969Source2531
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000
section
namespace Lower6960.Far6969TerminalArithmetic
abbrev agreement : ℕ := 179740
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
open HighCore82258 (Bank)
open P1_7_6 (linearEnd Quad prefixProduct intervalProduct yStart)
structure RectArgs where
  U : Fin 2 → ℕ
  order : Fin 2 → ℕ
abbrev RectArgs.slots (v : RectArgs) (r : ℕ) := KoalaRect.rectSlots v.U v.order r
def RectArgs.Fits (v : RectArgs) (r : ℕ) : Prop :=
  r * v.order 0 ≤ v.U 0 ∧ r * v.order 1 ≤ v.U 1
theorem slots_eq_zero (v : RectArgs) (a : ℕ) (ha : ¬ v.Fits a) : v.slots a = 0 := by
  unfold RectArgs.Fits at ha
  unfold RectArgs.slots KoalaRect.rectSlots
  by_cases h₀ : a * v.order 0 ≤ v.U 0
  · have h₁ : v.U 1 + 1 ≤ a * v.order 1 := by omega
    rw [Nat.sub_eq_zero_of_le h₁, mul_zero]
  · have h₀' : v.U 0 + 1 ≤ a * v.order 0 := by omega
    rw [Nat.sub_eq_zero_of_le h₀', zero_mul]
def seedEnd (s : Shape) (v : RectArgs) (d R : ℕ) : ℕ :=
  P1_7_6.seedEnd {s with U := v.U 1} (v.order 1) d
    (P1_7_6.seedEnd {s with U := v.U 0} (v.order 0) d R)
open P1_7_6 (lt_seedEnd) in
theorem lt_rectEnd (s : Shape) (v : RectArgs) (d R a : ℕ) :
    a < seedEnd s v d R ↔ a < R ∧ v.Fits (a+d) := by
  unfold seedEnd RectArgs.Fits
  rw [lt_seedEnd, lt_seedEnd]
  tauto
def orderEnd (s : Shape) (E : ℕ) (v : RectArgs) : ℕ :=
  seedEnd s v 0 (s.B/E+1)
theorem orderEnd_pos (s : Shape) (E : ℕ) (v : RectArgs) : 0 < orderEnd s E v :=
  (lt_rectEnd s v 0 (s.B/E+1) 0).mpr ⟨Nat.succ_pos _, by simp [RectArgs.Fits]⟩
def seedQuad (_ : Shape) (v : RectArgs) (d : ℕ) : Quad :=
  let x : ℤ := (v.U 0 : ℤ) + 1 - d * (v.order 0 : ℤ)
  let y : ℤ := (v.U 1 : ℤ) + 1 - d * (v.order 1 : ℤ)
  Quad.ofLines (2*x) (-2*(v.order 0 : ℤ)) y (-(v.order 1 : ℤ))
theorem seedQuad_eq (s : Shape) (v : RectArgs) (d a : ℕ) (ha : v.Fits (a+d)) :
    (seedQuad s v d).eval a = 2*(v.slots (a+d) : ℤ) := by
  have h₀ : (a+d)*v.order 0 ≤ v.U 0 + 1 := ha.1.trans (Nat.le_succ _)
  have h₁ : (a+d)*v.order 1 ≤ v.U 1 + 1 := ha.2.trans (Nat.le_succ _)
  simp only [seedQuad, Quad.eval_ofLines, RectArgs.slots, KoalaRect.rectSlots, Nat.cast_mul,
    Nat.cast_sub h₀, Nat.cast_sub h₁, Nat.cast_add, Nat.cast_one]
  ring
def scaledDebit (v : RectArgs) (N P h : ℕ) : ℤ :=
  240*(KoalaRect.rectDebit h N P v.U : ℤ)
def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m*agreement : ℕ)+(j : ℤ)-(131071-(h : ℤ))*q-2*(h : ℤ)*t
def surplus (h : ℕ) (b : Bank) (E : ℕ) (v : RectArgs) : ℤ :=
  (rectGain agreement h b.shape E v.U v.order : ℤ) - (rectDebit h b.nodeRows b.poleMoment v.U : ℤ)
def colEnd (s : Shape) (h t : ℕ) : ℕ :=
  linearEnd (2*h*t) (131071-h) (s.m*agreement) (s.B+1)
def edgeShift (s : Shape) (h t : ℕ) : ℕ :=
  2*h*t + (131071-h)*colEnd s h t + 1 - s.m*agreement
def innerEnd (s : Shape) (h E : ℕ) (v : RectArgs) (d t R : ℕ) : ℕ :=
  linearEnd (yStart E d t) (E-1) (colEnd s h t) (seedEnd s v d R)
def outerEnd (s : Shape) (h E : ℕ) (v : RectArgs) (d t R : ℕ) : ℕ :=
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
def phaseBlock (s : Shape) (h E : ℕ) (v : RectArgs) (d t : ℕ) : ℤ :=
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let c := seedQuad s v d
  intervalProduct c (innerQuad s h E d t) L (innerEnd s h E v d t R) +
    if colEnd s h t < s.B+1 then
      intervalProduct c (outerQuad s h t) L (outerEnd s h E v d t R)
    else 0
def blockSurplus (s : Shape) (N P h E : ℕ) (v : RectArgs) : ℤ :=
  (∑ t ∈ range (s.J+orderEnd s E v), (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) -
    scaledDebit v N P h
def BlockChecks (s : Shape) (N P h E : ℕ) (v : RectArgs) : Prop :=
  0 < blockSurplus s N P h E v ∧ blockSurplus s N P h E v ≤ blockSurplus s N P (h+1) E v
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape shapeSum slots)
open HighCore82258 (Bank)
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
private theorem gain_convex (s : Shape) (h E : ℕ) (v : RectArgs) (hh : h+2 ≤ 131071) :
    let f := fun h => (rectGain agreement h s E v.U v.order : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  simp only [rectGain, shapeSum, Nat.cast_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  let g := (q-j)/E
  let raw := fun k a => s.m*agreement+j-q*(131071-k)-2*k*(j+a)
  let A := fun k => (↑(∑ a ∈ range g, (v.slots a - v.slots (a+1))*raw k a : ℕ) : ℤ)
  let B := fun k => (↑(v.slots g*raw k g : ℕ) : ℤ)
  simp only [Nat.cast_add]
  change A (h+1) + B (h+1) + (A (h+1) + B (h+1)) ≤ A h + B h + (A (h+2) + B (h+2))
  rw [add_add_add_comm (A (h+1)), add_add_add_comm (A h)]
  apply add_le_add
  · simp only [A, Nat.cast_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro a _
    exact weighted_convex s h q j (j+a) (v.slots a - v.slots (a+1)) hh
  · exact weighted_convex s h q j (j+(q-j)/E) (v.slots ((q-j)/E)) hh
private theorem debit_affine (h : ℕ) (b : Bank) (v : RectArgs) :
    (rectDebit (h+1) b.nodeRows b.poleMoment v.U : ℤ) + (rectDebit (h+1) b.nodeRows b.poleMoment v.U : ℤ) =
      (rectDebit h b.nodeRows b.poleMoment v.U : ℤ) + (rectDebit (h+2) b.nodeRows b.poleMoment v.U : ℤ) := by
  simp only [rectDebit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring
private theorem surplus_convex (h : ℕ) (b : Bank) (E : ℕ) (v : RectArgs) (hh : h+2 ≤ 131071) :
    surplus (h+1) b E v + surplus (h+1) b E v ≤
      surplus h b E v + surplus (h+2) b E v := by
  have hg := gain_convex b.shape h E v hh
  have hd := debit_affine h b v
  dsimp only at hg
  unfold surplus
  omega
theorem strict_of_first_difference {lo h : ℕ} {b : Bank} {E : ℕ} {v : RectArgs}
    (hl : lo ≤ h) (hh : h < 131071)
    (hpos : 0 < surplus lo b E v) (hrise : surplus lo b E v ≤ surplus (lo+1) b E v) :
    rectDebit h b.nodeRows b.poleMoment v.U < rectGain agreement h b.shape E v.U v.order := by
  have hmon := rise_of_convex (f := fun h => surplus h b E v)
    (fun n hn => surplus_convex n b E v (by omega)) hl hrise
  have hsur := hpos.trans_le hmon.1
  unfold surplus at hsur
  omega
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P1_7_6 (sum_range_guard diagonal)
def phase (s : Shape) (h E : ℕ) (v : RectArgs) (d : ℕ) : ℤ :=
  ∑ t ∈ range (s.J + orderEnd s E v), ∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
    (v.slots (a+d) : ℤ) *
      ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)
private theorem position_phases (s : Shape) (h E : ℕ) (v : RectArgs) (q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => v.slots a
    let x := s.m*agreement+j-q*(131071-h)
    let g := (q-j)/E
    let f := fun d a => (c (a+d) : ℤ)*max 0 (width s h q j (j+a))
    (↑((∑ a ∈ range g, (c a - c (a+1))*(x-2*h*(j+a))) + c g*(x-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+0) ≤ q then f 0 a else 0) -
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+1) ≤ q then f 1 a else 0) := by
  dsimp only
  let g := (q-j)/E
  let f := fun d a => (v.slots (a+d) : ℤ)*max 0 (width s h q j (j+a))
  have step (a : ℕ) : v.slots (a+1) ≤ v.slots a :=
    rectSlots_antitone v.U v.order (by omega)
  have hdiff :
      (↑((∑ a ∈ range g, (v.slots a - v.slots (a+1)) *
          (s.m*agreement+j-q*(131071-h)-2*h*(j+a))) +
        v.slots g*(s.m*agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (g+1), f 0 a) - ∑ a ∈ range g, f 1 a := by
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sum]
    rw [show (∑ a ∈ range g, f 0 a) + f 0 g - (∑ a ∈ range g, f 1 a) =
        ((∑ a ∈ range g, f 0 a) - (∑ a ∈ range g, f 1 a)) + f 0 g by ring,
      ← sum_sub_distrib]
    simp only [Nat.cast_mul, width_cast s h _ _ _ hh, f, Nat.add_zero]
    have hs (a : ℕ) :
        (↑(v.slots a - v.slots (a+1) : ℕ) : ℤ) =
          (v.slots a : ℤ) - v.slots (a+1) := Int.ofNat_sub (step a)
    simp only [hs, sub_mul]
  rw [hdiff]
  have hz (d a : ℕ) (ha : orderEnd s E v ≤ a) (hg : a+d ≤ g) : f d a = 0 := by
    have hcap : g ≤ s.B/E := Nat.div_le_div_right (by omega)
    have hab : a < s.B/E+1 := by omega
    have hfit : ¬ v.Fits (a+d) := by
      intro h
      have hmono (i : Fin 2) : (a+0)*v.order i ≤ (a+d)*v.order i :=
        Nat.mul_le_mul_right _ (by omega)
      have hf : v.Fits (a+0) := ⟨(hmono 0).trans h.1, (hmono 1).trans h.2⟩
      exact (not_lt_of_ge ha) ((lt_rectEnd s v 0 (s.B/E+1) a).mpr ⟨hab,hf⟩)
    simp [f, slots_eq_zero v _ hfit]
  have hdiv (a d : ℕ) : j+E*(a+d) ≤ q ↔ a+d ≤ g := by
    rw [Nat.le_div_iff_mul_le he, Nat.mul_comm (a+d) E]
    omega
  rw [sum_range_guard (g+1) _ (fun a ha hb => hz 0 a ha (by omega)),
    sum_range_guard g _ (fun a ha hb => hz 1 a ha (by omega))]
  have hzero (a : ℕ) : j+E*a ≤ q ↔ a ≤ g := by simpa using hdiv a 0
  simp only [hzero, Nat.add_zero, Nat.lt_succ_iff, Nat.add_one_le_iff, f]
private def phaseQ (s : Shape) (h E : ℕ) (v : RectArgs) (d : ℕ) : ℤ :=
  ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
    if j + E*(a+d) ≤ q then
      (v.slots (a+d) : ℤ) * max 0 (width s h q j (j+a)) else 0
private theorem phaseQ_expand (s : Shape) (h E : ℕ) (v : RectArgs) (d q : ℕ) :
    (∑ j ∈ range (min q s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (v.slots (a+d) : ℤ)*max 0 (width s h q j (j+a)) else 0) =
    ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (v.slots (a+d) : ℤ)*max 0 (width s h q j (j+a)) else 0 := by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
private theorem gain_eq_phaseQ (s : Shape) (h E : ℕ) (v : RectArgs) (hh : h ≤ 131071) (he : 0 < E) :
    (rectGain agreement h s E v.U v.order : ℤ) = phaseQ s h E v 0 - phaseQ s h E v 1 := by
  unfold rectGain shapeSum phaseQ
  push_cast only [Nat.cast_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← phaseQ_expand s h E v 0 q, ← phaseQ_expand s h E v 1 q, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range, Nat.lt_succ_iff] at hq hj
  exact position_phases s h E v q j hh he hq (hj.trans (min_le_left _ _))
private theorem phaseQ_eq (s : Shape) (h E : ℕ) (v : RectArgs) (d : ℕ) : phaseQ s h E v d = phase s h E v d := by
  have hR : orderEnd s E v-1+1 = orderEnd s E v := by
    exact Nat.sub_add_cancel (orderEnd_pos s E v)
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
theorem gain_eq_phases (s : Shape) (h E : ℕ) (v : RectArgs) (hh : h ≤ 131071) (he : 0 < E) :
    (rectGain agreement h s E v.U v.order : ℤ) = phase s h E v 0 - phase s h E v 1 := by
  rw [gain_eq_phaseQ s h E v hh he, phaseQ_eq, phaseQ_eq]
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
export P1_7_6 (lt_linearEnd)
open K1_14_2_1 (twice_sum_linear)
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
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape slots triangle)
open P1_7_6 (intervalProduct_eq)
open P1_7_6 (yStart_eq sum_clipped)
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
theorem phaseBlock_eq (s : Shape) (h E : ℕ) (v : RectArgs) (d t : ℕ)
    (hh : h ≤ 131071) (hj : s.J ≤ 131071-h) (he : 0 < E) :
    240*(∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
      (v.slots (a+d) : ℤ) *
        ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)) =
      phaseBlock s h E v d t := by
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let k := colEnd s h t
  let l := fun a => t-a+E*(a+d)
  let c := fun a => (v.slots (a+d) : ℤ)
  let inner := fun a => ∑ q ∈ Ico (l a) k, width s h q (t-a) t
  let outer := fun a =>
    if k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a then width s h k (t-a) t else 0
  let R₁ := innerEnd s h E v d t R
  let R₂ := outerEnd s h E v d t R
  have ht (a : ℕ) (ha : a < R) : a ≤ t :=
    (Nat.le_of_lt_succ ha).trans (min_le_left _ _)
  have hcore (a : ℕ) : a < R₁ ↔ a < R ∧ v.Fits (a+d) ∧ l a < k := by
    simp only [R₁, innerEnd, lt_linearEnd, lt_rectEnd]
    constructor
    · rintro ⟨⟨ha,hv⟩,hk⟩
      exact ⟨ha,hv,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
    · rintro ⟨ha,hv,hk⟩
      exact ⟨⟨ha,hv⟩,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
  have hedge (a : ℕ) :
      a < R₂ ↔ a < R ∧ v.Fits (a+d) ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a := by
    simp only [R₂, outerEnd, lt_min_iff, lt_linearEnd, lt_rectEnd]
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
      by_cases hv : v.Fits (a+d)
      · have hl : k ≤ l a := by
          by_contra! hl
          exact (Nat.not_lt_of_ge hn) ((hcore a).mpr ⟨haR,hv,hl⟩)
        simp [inner, Ico_eq_empty_of_le hl]
      · simp [c, slots_eq_zero v _ hv]
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
        by_cases hv : v.Fits (a+d)
        · have hbound : ¬(k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a) :=
            fun ⟨_,hl,hs⟩ => (Nat.not_lt_of_ge hn) ((hedge a).mpr ⟨haR,hv,hl,hs⟩)
          simp only [outer, ite_eq_right hbound, mul_zero]
        · simp [c, slots_eq_zero v _ hv]
      · intro a ha
        obtain ⟨haR,hv,hl,hs⟩ := (hedge a).mp (mem_Ico.mp ha).2
        rw [normalize, seedQuad_eq s v d a hv, ← outerQuad_eq s h t a hh (ht a haR)]
        simp only [outer, hk, hl, hs, and_self, ite_true]
        rfl
    · simp [outer, hk]
  change _ = intervalProduct _ _ L R₁ + if k < s.B+1 then intervalProduct _ _ L R₂ else 0
  rw [hsplit, mul_add, ho, ← intervalProduct_eq (seedQuad s v d) (innerQuad s h E d t), ← hi]
  ring
theorem blockSurplus_eq (b : HighCore82258.Bank) (h E : ℕ) (v : RectArgs)
    (hh : h ≤ 131071) (hj : b.shape.J ≤ 131071-h) (he : 0 < E) :
    blockSurplus b.shape b.nodeRows b.poleMoment h E v = 240*surplus h b E v := by
  unfold blockSurplus scaledDebit surplus
  rw [gain_eq_phases b.shape h E v hh he, mul_sub]
  congr 1
  unfold phase
  rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [phaseBlock_eq _ _ _ _ _ _ hh hj he, phaseBlock_eq _ _ _ _ _ _ hh hj he]
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
open P1_7_6 (intervalProduct_eq)
open P1_7_6_4 (Core corePrefix diagonalCore)
def bankCore (s : Shape) (h E : ℕ) (v : RectArgs) (d k : ℕ) : Core :=
  let D : ℤ := (131071-h : ℕ)
  let p : ℤ := (E-1 : ℕ)
  let w : ℤ := (E*d : ℕ)
  ⟨k,E*d,E-1,seedEnd s v d (orderEnd s E v),seedQuad s v d,
    ⟨(k : ℤ)-w,-p⟩, ⟨2*(s.m*agreement : ℕ)-D*(w+k-1),-2-D*p⟩,
    2-4*(h : ℤ)-D⟩
def outerPart (s : Shape) (h E : ℕ) (v : RectArgs) (d t : ℕ) : ℤ :=
  if colEnd s h t < s.B+1 then
    intervalProduct (seedQuad s v d) (outerQuad s h t) (t-s.J)
      (outerEnd s h E v d t (min t (orderEnd s E v-1)+1))
  else 0
private theorem diagonal_eq (s : Shape) (h E : ℕ) (v : RectArgs) (d t k : ℕ) (hk : colEnd s h t = k) :
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
    have hend := orderEnd_pos s E v
    have hp (a : ℕ) : a < R ↔ a ≤ t ∧ a < orderEnd s E v := by
      dsimp [R]
      omega
    ext a
    simp only [mem_Ico, mem_filter, mem_range, C, bankCore, innerEnd, lt_linearEnd, lt_rectEnd,
      hk, yStart]
    rw [hp]
    constructor
    · rintro ⟨hla,⟨⟨hat,haord⟩,hfit⟩,hcol⟩
      exact ⟨⟨haord,hfit⟩,hat,by omega,by omega⟩
    · rintro ⟨⟨haord,hfit⟩,hat,htj,hcol⟩
      exact ⟨by omega,⟨⟨hat,haord⟩,hfit⟩,by omega⟩
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
private theorem outer_sum (s : Shape) (h E : ℕ) (v : RectArgs) (d l r k : ℕ) (hJ : s.J < 2*h)
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
def groupValue (s : Shape) (h E : ℕ) (v : RectArgs) (d l r k : ℕ) : ℤ :=
  if l < r then
    let C := bankCore s h E v d k
    corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l
  else 0
theorem groupValue_eq (s : Shape) (h E : ℕ) (v : RectArgs) (d l r k : ℕ) (hJ : s.J < 2*h)
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
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
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
def runValue (s : Shape) (h E : ℕ) (v : RectArgs) (n i : ℕ) : ℤ :=
  let l := boundary s h n i
  let r := boundary s h n (i+1)
  let k := s.B+1-i
  groupValue s h E v 0 l r k - groupValue s h E v 1 l r k
def runRow (s : Shape) (h E : ℕ) (v : RectArgs) (n i : ℕ) : Row :=
  ⟨true,runValue s h E v n i,runValue s (h+1) E v n i⟩
private theorem run_sum (s : Shape) (h E : ℕ) (v : RectArgs) (n count : ℕ) (hc : count ≤ s.B+1)
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
theorem checks_of_runs (s : Shape) (N P h E : ℕ) (v : RectArgs) (n count : ℕ) (left next cost costNext : ℤ)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hs : scan (runRow s h E v n) 0 count = ⟨true,left,next⟩)
    (hl : 6*scaledDebit v N P h = cost) (hr : 6*scaledDebit v N P (h+1) = costNext)
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
end Lower6960.Far6969TerminalArithmetic
end
section
namespace Lower6960.Far6969TerminalArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open K1_14 (Shape)
open P0_10_5 (Row scan joinRows)











end Lower6960.Far6969TerminalArithmetic
end
namespace Lower6960.Far6969TerminalArithmetic
open HighCore82258 (Bank)
open KoalaRect (rectGain rectDebit)
theorem strict_of_checks {lo h E : ℕ} {b : Bank} {v : RectArgs}
    (hl : lo ≤ h) (hh : h < 131071) (hf : lo+1 ≤ 131071)
    (hj : b.shape.J ≤ 131071 - (lo+1)) (he : 0 < E)
    (hc : BlockChecks b.shape b.nodeRows b.poleMoment lo E v) :
    rectDebit h b.nodeRows b.poleMoment v.U < rectGain agreement h b.shape E v.U v.order := by
  unfold BlockChecks at hc
  rw [blockSurplus_eq b lo E v (by omega) (by omega) he,
    blockSurplus_eq b (lo+1) E v hf hj he] at hc
  exact strict_of_first_difference hl hh (by omega) (by omega)
end Lower6960.Far6969TerminalArithmetic
end Z6969Source2531

-- Source: Research6969.FarTerminalChecks
section Z6969Source2532
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 0
namespace Lower6960.Far6969Terminal
open Far6969TerminalArithmetic
abbrev terminalBank:=TerminalReceipts.terminalBank
theorem bank_checked:P3_7_1.BankOK terminalBank:=TerminalReceipts.bank_checked
def witness : ℕ → RectArgs
  | 1 => ⟨![668833,79945],![0,1126]⟩
  | 2 => ⟨![669117,79661],![0,1122]⟩
  | 3 => ⟨![668355,80423],![0,1117]⟩
  | 4 => ⟨![668715,80063],![0,1112]⟩
  | 5 => ⟨![668926,79852],![0,1107]⟩
  | 6 => ⟨![668333,80445],![0,1102]⟩
  | 7 => ⟨![667601,81177],![0,1097]⟩
  | 8 => ⟨![667971,80807],![0,1092]⟩
  | 9 => ⟨![667329,81449],![0,1086]⟩
  | 10 => ⟨![667704,81074],![0,1081]⟩
  | 11 => ⟨![667003,81775],![0,1076]⟩
  | 12 => ⟨![667459,81319],![0,1070]⟩
  | 13 => ⟨![666774,82004],![0,1065]⟩
  | 14 => ⟨![666177,82601],![0,1059]⟩
  | 15 => ⟨![666567,82211],![0,1054]⟩
  | 16 => ⟨![665987,82791],![0,1048]⟩
  | 17 => ⟨![665419,83359],![0,1042]⟩
  | 18 => ⟨![664863,83915],![0,1036]⟩
  | 19 => ⟨![665349,83429],![0,1030]⟩
  | 20 => ⟨![664811,83967],![0,1024]⟩
  | 21 => ⟨![664285,84493],![0,1018]⟩
  | 22 => ⟨![663855,84923],![0,1011]⟩
  | 23 => ⟨![663354,85424],![0,1005]⟩
  | 24 => ⟨![662951,85827],![0,998]⟩
  | 25 => ⟨![662562,86216],![0,991]⟩
  | 26 => ⟨![662187,86591],![0,984]⟩
  | 27 => ⟨![661826,86952],![0,977]⟩
  | 28 => ⟨![660509,88269],![0,970]⟩
  | 29 => ⟨![660275,88503],![0,962]⟩
  | 30 => ⟨![660057,88721],![0,954]⟩
  | 31 => ⟨![658909,89869],![0,946]⟩
  | 32 => ⟨![657793,90985],![0,938]⟩
  | 33 => ⟨![656808,91970],![0,929]⟩
  | 34 => ⟨![655859,92919],![0,920]⟩
  | 35 => ⟨![655049,93729],![0,910]⟩
  | 36 => ⟨![653379,95399],![0,900]⟩
  | 37 => ⟨![650989,97789],![0,889]⟩
  | 38 => ⟨![648687,100091],![0,878]⟩
  | 39 => ⟨![644979,103799],![0,865]⟩
  | 40 => ⟨![637560,111218],![0,849]⟩
  | 41 => ⟨![581267,167511],![0,821]⟩
  | 42 => ⟨![517615,231163],![0,752]⟩
  | 43 => ⟨![473042,275736],![0,650]⟩
  | 44 => ⟨![439649,309129],![0,521]⟩
  | 45 => ⟨![413712,335066],![0,371]⟩
  | 46 => ⟨![392667,356111],![0,200]⟩
  | 47 => ⟨![375269,373509],![0,11]⟩
  | 48 => ⟨![374389,374389],![0,0]⟩
  | _ => ⟨![0,0],![0,0]⟩
private theorem receipt1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 50 207521300061309312638578442880 207522508706301764387731610880 207521285937350399165423059200 207521331273034114699938355200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 50 206872341177723963960526830720 206873546212024902594660798720 206872251968515099374712684800 206872297304198814909227980800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 50 208612332635728852393291572480 208613547413561953915118755200 208612261266334036087234003200 208612306602017751621749299200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 50 207790838343476432351650990080 207792048512176909971189120000 207790770981915189781683667200 207790816317598905316198963200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 50 207308878314217504983073117440 207310085775364685268244561920 207308819066513210150549356800 207308864402196925685064652800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 50 208662496646861824036619097600 208663711695061102954347621120 208662430852225996044066259200 208662476187909711578581555200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 50 210329637981151327244341482240 210330862372261847014953223680 210329568935339606258284396800 210329614271023321792799692800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 50 209487496005564017140628951040 209488715680196838170747105280 209487409387570382317352812800 209487454723254097851868108800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 50 210948003296812552907315606400 210949231124499644784327033600 210947992661748750409280160000 210948037997432465943795456000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 50 210095275056472779252344474400 210096498112329093458572065600 210095236599332802453056160000 210095281935016517987571456000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 50 211688506251268064830216903680 211689738246587275363463124480 211688435505763690459127251200 211688480841447405993642547200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 50 210652509059460231815749824000 210653735222588469612711264000 210652494102622417756367520000 210652539438306133290882816000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 50 212208134095434318526176840000 212209368993743915885967000000 212208069547243543309068960000 212208114882927258843584256000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 50 213560858889660228317997926400 213562101349593276305439646080 213560835922048945074796396800 213560881257732660609311692800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 50 212677519028935803848019302400 212678756559421813810209070080 212677432337235880584476524800 212677477672919596118991820800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 50 213990849674942743755239408640 213992094553804725858888468480 213990784574260842130896748800 213990829909944557665412044800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 50 215274484619912455618578163200 215275736682973497710204524800 215274434724622953862146720000 215274480060306669396662016000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 50 216528583972146051079423918080 216529843056705526119925063680 216528541419233922857262547200 216528586754917638391777843200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 50 215432507394064267127976960000 215433760334130428303576160000 215432457814932720220121760000 215432503150616435754637056000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 50 216645776153721270303609323520 216647035895789347370080665600 216645709338554241713764204800 216645754674237957248279500800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 51 217829823596129268183385071360 217831089980460107061330174720 217829728617186261765414355200 217829773952869977299929651200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 51 218796094922686821573001205760 218797366694070961902884728320 218796058590176964805877203200 218796103925860680340392499200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 51 219920226169805930976452784000 219921504257156368578255036000 219920136140101367055526560000 219920181475785082590041856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 51 220822979654150831941252485120 220824262782710466295657190400 220822921124496370393216876800 220822966460180085927732172800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 51 221693191079036079541588528320 221694479072147882179242230400 221693148813215455062849388800 221693194148899170597364684800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 51 222530988447303048013076951040 222532281129520669837823124480 222530945952729448052750188800 222530991288413163587265484800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 51 223336495173076031833958787840 223337792370127490165597842080 223336434727939532192282476800 223336480063623247726797772800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 51 226266544243359330140454624000 226267857867555183363334560000 226266446380932780459829920000 226266491716616495994345216000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 51 226785691025601381373781652480 226787007536028205086978144000 226785632927000101262941651200 226785678262683816797456947200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1422 51 227268976497634503200623357440 227270295701239894179089892480 227268937328407145267394412800 227268982664090860801909708800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1424 51 229808012269899491927687865600 229809345696761047803086054400 229807962165616958126697120000 229808007501300673661212416000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1426 51 232266502952809565711255930880 232267850162318873199677385600 232266412305502755476692435200 232266457641186471011207731200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1428 51 234428315108159145689051837760 234429674409108664163421606720 234428253636672357949464019200 234428298972356073483979315200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1430 51 236504038641231762802128384000 236505409566830418521704320000 236503964332995759821826720000 236504009668679475356342016000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 51 238270146696298033805648160000 238271527486846825197145920000 238270119151616145048742560000 238270164487299860583257856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1435 51 241895426605598294146275840000 241896827698787756634048000000 241895385898011086531340960000 241895431233694802065856256000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1439 52 247046021700274863963745430400 247047451623411442299875577600 247046003520332417213934240000 247046048856016132748449536000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1443 52 251965175738018499164905666560 251966633230802756481747425280 251965079187842442511578988800 251965124523526158046094284800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1449 52 259802249868186199681243968000 259803751236196585380196752000 259802153362560249578662560000 259802198698243965113177856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 52 275162457187302847577424817920 275164044516276563553608786400 275162435662992036089781715200 275162480998675751624297011200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1483 53 377799639943058791299071614080 377801801861774646169367642880 377799569359862773762291564800 377799614695546489296806860800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 53 464239888128679806838789079040 464242533894093910981818101760 464239839395343358604303827200 464239884731027074138819123200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 53 506059205827410860319884139840 506062085635966702960975674240 506059164330026983467579244800 506059209665710699002094540800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 53 527290428659547004620873264000 527293427240871512529142320000 527290427059463681452812960000 527290472395147396987328256000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 53 537812231172589990304691742080 537815288613201221549046828960 537812173355613347594172268800 537812218691297063128687564800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 53 542514254889968479733963443200 542517338589380751000167193600 542514209264053401057032044800 542514254599737116591547340800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 53 543807126464713728642557582400 543810217343384549787189508800 543807084102932813776693920000 543807129438616529311209216000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem receipt48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2535 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 52 543819092065601372339051952000 543822186605511409255165968000 543810087912059035461102240000 543810133247742750995617536000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem checked (i : Fin 49) (pos : 0 < i.val) :
    BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment 2535 i.val (witness i.val) := by
  fin_cases i
  · change 0 < 0 at pos; omega
  · exact receipt1
  · exact receipt2
  · exact receipt3
  · exact receipt4
  · exact receipt5
  · exact receipt6
  · exact receipt7
  · exact receipt8
  · exact receipt9
  · exact receipt10
  · exact receipt11
  · exact receipt12
  · exact receipt13
  · exact receipt14
  · exact receipt15
  · exact receipt16
  · exact receipt17
  · exact receipt18
  · exact receipt19
  · exact receipt20
  · exact receipt21
  · exact receipt22
  · exact receipt23
  · exact receipt24
  · exact receipt25
  · exact receipt26
  · exact receipt27
  · exact receipt28
  · exact receipt29
  · exact receipt30
  · exact receipt31
  · exact receipt32
  · exact receipt33
  · exact receipt34
  · exact receipt35
  · exact receipt36
  · exact receipt37
  · exact receipt38
  · exact receipt39
  · exact receipt40
  · exact receipt41
  · exact receipt42
  · exact receipt43
  · exact receipt44
  · exact receipt45
  · exact receipt46
  · exact receipt47
  · exact receipt48
theorem positive {h : ℕ} (lo : 2535 ≤ h) (hi : h ≤ 33735) (i : Fin 49) (pos : 0 < i.val) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179740 h terminalBank.shape i.val (witness i.val).U (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) pos (checked i pos)
end Lower6960.Far6969Terminal
end Z6969Source2532

-- Source: Research6969.FarRetained
section Z6969Source2533
set_option autoImplicit true
set_option Elab.async false

namespace Research6969.Far6969Retained
open Polynomial Finset
open K1 (I K p)
open K1_14 (Equation FX Seeds L atMark atX graphEval liftPoly seedEmbedding)
open KoalaRect (axisDegree axisDegree_le_iff)
open Lower6960
open Far6969Terminal (witness)
open RetainedCompression (MarkedFiber integral_project specialize incl)
open CurvatureSquares (zView Ordinate)
open RetainedShortening (Word)
open Far6969FactorPrice (agreement wordDegree rate)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1300000
set_option maxRecDepth 9000

abbrev cap : ℕ := 26211183496753400
def axisCap (e : ℕ) : ℕ := (witness e).order 1-1

private theorem budget (i : Fin 48) :
    (rate (max 3 i.val)+(2*i.val-1))*(p+1)*axisCap i.val+(max 3 i.val-1)*i.val≤cap ∧
      (2*i.val-1)*axisCap i.val<p := by
  fin_cases i <;> decide +kernel

private def determinant (f : Equation) : Seeds := f.resultant f.derivative f.natDegree (f.natDegree-1)

private theorem det_axis (f : Equation) (i : Fin 2) :
    (determinant f).degreeOf i≤(2*f.natDegree-1)*axisDegree f i := by
  have coeffs := (axisDegree_le_iff f i _).mp le_rfl
  have der (j : ℕ) : (f.derivative.coeff j).degreeOf i≤axisDegree f i := by
    rw [coeff_derivative]
    have eq : ((j:Seeds)+1)=MvPolynomial.C ((j:FX)+1) := by simp
    rw [eq]
    apply (MvPolynomial.degreeOf_mul_le ..).trans
    rw [MvPolynomial.degreeOf_C,Nat.add_zero]
    exact coeffs (j+1)
  exact (ThirdPole.resultant_axis f f.derivative _ _ _ _ i coeffs der).trans
    (by rw [←Nat.add_mul]; apply Nat.mul_le_mul_right; omega)

private theorem singular (f : Equation) (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (T : Finset K) (label : K→K) (inj : Function.Injective label)
    (small : (2*f.natDegree-1)*axisDegree f 0<p) :
    (T.filter (fun γ=>graphEval (label γ) (determinant f)=0)).card≤
      (2*f.natDegree-1)*(axisDegree f 0+p*axisDegree f 1) := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let coord (γ : K) := seedEmbedding (label γ)
  have eq : (B.image coord).card=B.card := card_image_of_injective _ (seedEmbedding.injective.comp inj)
  have nz : determinant f≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have bound := K1_10.frobenius_coefficient_exception_count p _ _ (by decide) _ nz
    (det_axis f 0) small (det_axis f 1) (B.image coord) (by
      intro z hz
      obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hγ).2)
  rw [eq] at bound
  exact bound.trans_eq (by ring)

/-- Every native retained word is paid by the projected factor tariff or
by the single mixed-axis discriminant charge. -/
theorem count {w : I→K} {s : K→K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K→K) (inj : Function.Injective label)
    (f : Equation) (pos : 0<f.natDegree) (small : f.natDegree<48)
    (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (axis : ∀ j : Fin 2, axisDegree f j<(witness f.natDegree).order 1)
    (roots : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤cap := by
  classical
  let e := f.natDegree
  let n := max 3 e
  let v := axisDegree f 0+p*axisDegree f 1
  have axis' (j : Fin 2) : axisDegree f j≤axisCap e := by
    have bound := axis j
    change axisDegree f j < (witness e).order 1 at bound
    change axisDegree f j≤(witness e).order 1-1
    omega
  obtain ⟨price, tame⟩ := budget ⟨e,small⟩
  change (rate n+(2*e-1))*(p+1)*axisCap e+(n-1)*e≤cap at price
  change (2*e-1)*axisCap e<p at tame
  have smallAxis := (Nat.mul_le_mul_left (2*e-1) (axis' 0)).trans_lt tame
  have fn : f≠0 := fun z=>by rw [z,natDegree_zero] at pos; omega
  have ep : 1≤2*e-1 := by dsimp only [e];omega
  have fp : axisDegree f 0<p := by
    have z := Nat.mul_le_mul_right (axisDegree f 0) ep
    rw [Nat.one_mul] at z
    exact z.trans_lt smallAxis
  obtain ⟨D,P,dn,pn,degree,seed,calls⟩ := integral_project f fn fp
  let B := T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let S := T\B
  have bad : B.card≤(2*e-1)*v := singular f sep T label inj smallAxis
  let z (γ : K) := algebraMap K L (label γ)
  have lift_inj : Function.Injective z := (algebraMap K L).injective.comp inj
  have dnon : incl D≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) FX)).mpr dn
  have marks (γ : K) (mem : γ∈S) : MarkedFiber P (z γ) (liftPoly (s γ)) := by
    obtain ⟨tg,good⟩:=mem_sdiff.mp mem
    have safe : graphEval (label γ) (determinant f)≠0 :=
      fun eq=>good (mem_filter.mpr ⟨tg,eq⟩)
    have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero (graphEval (label γ)) f le_rfl safe
    have separable := separable_map_of_resultant_derivative_padded_ne_zero (graphEval (label γ)) f le_rfl pos safe
    have root : (f.map (graphEval (label γ))).eval (atX (s γ))=0 := by rw [eval_map]; exact roots γ tg
    have eq := calls (label γ)
    have smap : ((specialize P (z γ)).map incl).natDegree=(specialize P (z γ)).natDegree :=
      natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX) _
    refine ⟨?_,?_,?_⟩
    · rw [← smap,eq,natDegree_C_mul dnon,full,degree]
    · rw [eq]; exact separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr dnon))
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq,map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr root)
  have sub : S⊆T := sdiff_subset
  have wordS : Word agreement wordDegree w s S :=
    ⟨words.distinct.mono sub,fun γ hγ=>words.degree γ (sub hγ),fun γ hγ=>words.hits γ (sub hγ)⟩
  have ord : P.natDegree≤n := degree.trans_le (le_max_right _ _)
  have nsmall : n<48 := max_lt (by decide) small
  have counted := Far6969FactorPrice.price wordS z lift_inj P pn n v (le_max_left _ _) nsmall ord seed marks
  have eq : S.card+B.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have axisSum : v≤(p+1)*axisCap e := by
    unfold v
    exact (Nat.add_le_add (axis' 0) (Nat.mul_le_mul_left p (axis' 1))).trans_eq (by ring)
  rw [←eq]
  calc
    _ ≤ rate n*v+(n-1)*e+(2*e-1)*v := Nat.add_le_add (by simpa only [degree] using counted) bad
    _ = (rate n+(2*e-1))*v+(n-1)*e := by rw [Nat.add_mul]; ring
    _ ≤ _ := (Nat.add_le_add_right (Nat.mul_le_mul_left _ axisSum) _).trans
      (by simpa only [Nat.mul_assoc] using price)

end
end Research6969.Far6969Retained
end Z6969Source2533

-- Source: Research6969.FarRescueRates
section Z6969Source2534
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960RescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Far6969RescueGeometry
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179740
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 164806

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164806) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179740 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164806 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 164806) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33735) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤164806
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33735) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164806)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 164806) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33735) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound


end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometryTariffs

section Merged_R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Far6969RescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometryRates
end Z6969Source2534

-- Source: Research6969.FarRescueInvoice
section Z6969Source2535
set_option autoImplicit true
set_option Elab.async false


noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.Far6969RescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [[250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 107178122, 90561210, 111399090, 159856701, 155401324, 198768055, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 102814332, 87000554, 107157326, 154005122, 149641067, 191596945, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 97959228, 82217852, 103210618, 149781012, 144393038, 187541220, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 88312895, 79543745, 98079150, 149905130, 145594273, 194227079, 257834722]]

def heightRates : List (List ℕ) :=
  [[1781322, 1738943, 2204556, 2425241, 3142167, 3232483, 3714722, 4465429, 3605461, 4986275, 4539361, 5417419, 4358418, 2967394, 3058869, 2328183, 3154375], [1781322, 1738943, 2204556, 2425241, 3142167, 3232483, 3714722, 4465429, 3605461, 4986275, 4736810, 5639144, 4540253, 3087535, 3177135, 2434967, 3154375], [1781322, 1738943, 2204556, 2425241, 3142167, 3232483, 3714722, 4465429, 3605461, 4986275, 4989849, 5989477, 4716157, 3174261, 3301582, 2495360, 3154375], [1781322, 1738943, 2204556, 2425241, 3142167, 3232483, 3714722, 4465429, 3605461, 4986275, 5557424, 6195846, 4983598, 3171713, 3269060, 2395802, 1736271]]

def degreeRate (rect : Fin 4) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 4) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (rect : Fin 4) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 4) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179740)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179740-endpointDegree : ℕ)

def rankB (rect : Fin 4) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 4) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 4) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 4) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 4) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 4) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 4) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 4) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 119941728025525398 := by
  fin_cases rect <;> decide +kernel




theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel


end Lower6960.Far6969RescueGeometry
end
end Z6969Source2535

-- Source: Research6969.FarMainInvoice
section Z6969Source2536
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960RescueGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Far6969RescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open P1_7_4_3 (mix)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6960.Far6969RescueGeometry (persistentTotal persistentTop siteRatio density)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>∃ J∈ini.rankExit,OnMark F J γ)
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤33735) :
    (ini.rankMarks.card : ℚ)≤dotQ (rankWeight rect) (massQ ini.rankExit)+rankRound rect := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap rect k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB rect := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ rect := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard rect
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau (pivot rect) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight rect 1 * J + rankWeight rect 2 * B + 2*lambda*pivot rect^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ (rankWeight rect) (massQ ini.rankExit) =
      rankWeight rect 1 * (mass S 1 : ℚ)+rankWeight rect 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hiM : M.overhead.toNat≤33735) {i : ℕ} (hi : i<17) :
    ((curveMarks F (C.cover i)).card : ℚ)≤
      dotQ (lossWeight R.rect i) (massQ (R.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit R.rect :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight R.rect 0 i) (history R.rect i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (R.live_history hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt (seed_limit_small R.rect)
  obtain ⟨ok,degree⟩ := rate_spec R.rect hi
  have count := rated_curve_count F (curve_tariff F hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate R.rect i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate R.rect i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate R.rect i : ℚ)*dotQ (cutWeight R.rect 0 i) (massQ (R.lost i)) +
          (heightRate R.rect i : ℚ)*dotQ (cutWeight R.rect 1 i) (massQ (R.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := R.initial.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks F (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤33735) : C.lossMarks.card ≤ (lossLimit R.rect).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (R.initial.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks F (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ R.initial.rankMarks.card +
      ∑ i∈range 17,(curveMarks F (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (R.initial.rank_count hi) sum_cuts
  have joint := R.joint_bill (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤33735) : C.paid.card≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid
  omega
theorem exceptional_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2535≤M.overhead.toNat) (hi : M.overhead.toNat≤33735)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (evaluated Crt (word M) Far6969HelperSource.helperBank.shape (Far6969HelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card ≤ 119941728025525398 ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R,C,S,geom,cover⟩ := inventory F Crt lo hi noPole residues common
  refine ⟨C.paid,S,(C.paid_count hi).trans (rescue_fee_bound R.rect),geom,?_⟩
  intro γ hγ zero
  rcases cover γ hγ zero with seed | ordinate | rank | point | ⟨i,hi,curve,mem,on⟩ | retained
  · exact Or.inl (mem_union_left _ (mem_union_right _ seed))
  · exact Or.inl (mem_union_right _ ordinate)
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ point)))
  · have cuts : γ∈(range 17).biUnion (fun i=>curveMarks F (C.cover i)) :=
      mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=F) hγ mem on⟩
    exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ cuts))))
  · exact Or.inr retained
end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometryFee

section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Far6969MainGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open Far6969HelperSource (helperBank helperCutoff)
open MainPrefixSource (copies hasse_at_mark)
open Far6969FreeSource (bank reserve cutoff)
open Far6969RescueGeometry (Model Family word OnMark terminalShape contact_at_mark zero_of_contact reserve_small)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def freeShape (i : Fin 17) : Shape := (bank i).shape

def movingShape (i : Fin 17) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 17) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 17) := [1,2,3,4,5,6,7,8,9,10,11,12]

def introAccount (k : Fin 4) : List (Fin 17) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old =>
      introJump cap old (movingShape 0) k +
        K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let s := freeShape i
      introJump cap old s k + introAccount k rest
        (fun j=>min (cap j) (degreeVector s j/(reserve i+1)))
        (fun j=>max (old j) (introWeight s k j))

def initialCap (k : Fin 4) : ℕ :=
  introAccount k introIndices (degreeVector (freeShape 0)) (fun _=>0)

theorem initial_small (k : Fin 4) : initialCap k < K1.p := by
  fin_cases k <;> decide +kernel

theorem free_ode_guard (i : Fin 17) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 17) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 17) : (freeShape i).U<K1.p :=
  (Far6969FreeSource.shape_guards i).2.2.2.1

theorem moving_seed_small (i : Fin 17) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 17} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 17) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 17 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 17→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2535≤M.overhead.toNat) (hi : M.overhead.toNat≤33735)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Rows F Crt) := by
  choose P inside nz using Far6969FreeSource.free_rows Crt (word M) lo hi
  obtain ⟨out⟩ := PrefixRows.prepare P freeShape copies _ _ nz
    (fun i => evaluated_shape Crt (word M) (inside i))
    (Far6969HelperSource.helper_nonzero Crt (word M) lo hi)
    (fun Q hQ => evaluated_shape Crt (word M) hQ)
    (fun _ _ g h cop => Far6969HelperSource.helper_not_two Crt (word M) lo hi
      g.1 h.1 cop g.2.1 h.2.1 g.2.2.1 h.2.2.1 g.2.2.2 h.2.2.2)
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by
      change reserve i+1≤((reserve i+11)/11)*11
      omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (Far6969FreeSource.cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := Far6969HelperSource.helper_width lo hi
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179740 :=
        FreeSource.buffered_fit helperBank 179740 _ 10 wh
      exact contact_at_mark F Crt noPole residues hm width γ mem
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)

def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩

theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometry

section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Far6969MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet Seeds FX jetAt graphEval seedHasse atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient OnJet ODE fixedAt)
open K1_14_2_2 (RowCaps Active dual Fits FixedPart fixedOn mass sectionDegree sum_union_le ordinateIncl ODECaps)
open K1_14_2_2_2 (ordinaryBudget ordinate_eq length_le_mass)
open K1_14_3 (NoMovingCommon SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P1_7_4 (degreeVector introJump introWeight)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono factorTariff
  weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover own_J_le_B own_caps retained_mass
  Stripped initial_factors strip)
open Far6969RescueGeometry (Model Family OnMark label_injective zero_of_contact)
open Far6969FreeSource (reserve)
open MainPrefixSource (copies)
open P1_7_4_1 (irreducible_cut terminal_piece)
open P0_10R_1 (seed_projection)
open scoped Classical BigOperators

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 17 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 17)),
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ reserve i →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro D cap hD hcap
    let t := movingShape 0
    have gt := moving_ode_guard 0
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.jb gt.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i
    let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (free_seed_small i) r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩

def Rows.fixedMarksOf {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)

def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  (univ : Finset (Fin 17)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 17)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 17)
    (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩

def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {J : Ideal Ambient} {γ : K} (mark : γ∈R.marks) (on : OnMark R.family J γ)
    (bad : ¬R.Clean J) : γ∈R.fixedMarks := by
  by_contra absent
  apply bad
  intro i
  constructor
  · intro h
    apply absent (R.mem_fixed_free mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)
  · intro h
    apply absent (R.mem_fixed_moving mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)

private theorem Rows.sections {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A,hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k
    simpa only [initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ
    obtain ⟨p,q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p) with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ)
        (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) where
  seed : SeedCover
  seed_cap : seed.curve.totalDegree ≤ initialCap 2
  seed_points : seed.points.card ≤ initialCap 3
  ordinates : Finset FX
  ordinate_cap : ordinates.card ≤ initialCap 0
  content : Seeds
  content_ne : content≠0
  content_cap : content.totalDegree≤(freeShape 0).U
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  fits : Fits (rankExit∪parents) initialCap
  disjoint : Disjoint rankExit parents
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J
  covers : ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨
    seed.Covers (M.label γ) ∨ atX (R.family.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark R.family J γ) ∨ ∃ J∈parents,OnMark R.family J γ

/-- Form the initial affine section cover, remove fixed-factor marks, and
split the remaining active parents at the actual rank-exit index zero. -/
theorem Rows.initial_cover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    Nonempty (Initial R) := by
  obtain ⟨S,geom,fit,content,cn,cc,cover⟩ := R.sections
  let noSeeds := S.filter (fun J=>sectionDegree J 0=0)
  let constY := S.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := S.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>R.Clean J ∧ ¬dual J)
  let parents := active.filter (fun J=>R.Clean J ∧ dual J)
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) :=
    (R.marks.filter (OnMark R.family J)).image fun γ=>atX (R.family.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,content,cn,cc,
    rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2.2 (mem_filter.mp b).2.2
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2.2⟩
  · intro J mem
    obtain ⟨hin,c,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,c⟩
  · intro γ hγ
    rcases cover γ hγ with fixed | seed | ⟨J,hin,on⟩
    · exact Or.inl fixed
    · exact Or.inr (Or.inl seed)
    · by_cases z : sectionDegree J 0=0
      · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
        exact Or.inr (Or.inr (Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))))
      · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
        · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          by_cases clean : R.Clean J
          · by_cases d : dual J
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
          · exact Or.inl (R.fixed_of_not_clean hγ on clean)
        · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
            mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometryIntro

section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Far6969MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_shape nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps Active dual mass mass_mono sectionDegree CutCover weight dot
  emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono pairedCap)
open Far6969RescueGeometry (Model Family OnMark OnSurface SurfacePass TerminalPass word terminalShape terminalCutoff
  contact_at_mark zero_of_contact reserve_small)
open MainPrefixSource (copies)
open Far6969FreeSource (reserve)
open HighCore82258_3 (envelope_caps)
open Lower6960.Far6969RescueGeometry (proper_cut)
open scoped Classical BigOperators

def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 17,0 < i.val → i.val≤n → R.Passes i J)

theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J
  constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h
    apply mem_filter.mpr
    refine ⟨h,fun i pos zero=>?_⟩
    omega

theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem
  obtain ⟨p,pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p,fun i hi hm=>pass i hi (hm.trans le)⟩

theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1

def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) :=
  (ini.kept 16).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<17 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<17),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<17
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=16 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 17) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := free_ode_guard i
  have t := moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (reserve_pos hi) (reserve_small i) s.small t.small
    (free_seed_small i) (moving_seed_small i) s.jb t.jb (R.out.free_ne i)
    (pow_ne_zero _ R.out.helper_ne) (R.out.free_caps i) (R.out.moving_caps i)
    (R.out.no_moving i) (R.fixedFree i) (R.fixedMoving i)
  · intro _ J mem
    exact (ini.kept_geom mem).2.1
  · intro J mem
    have geom := ini.kept_geom mem
    have pass := (mem_filter.mp mem).2 i hi step
    have clean := geom.2.2.2 i
    exact ⟨geom.1,pass.2.2,clean.1,clean.2,pass.1,pass.2.1⟩

/-- Every failing parent has a marked cutter with the exact stage envelope.
The terminal failure uses a row of the common full bank. -/
theorem Initial.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    have hf : ¬R.Passes j J := by
      intro p
      apply lost
      rw [Initial.live,ite_eq_left hn]
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp prev).1,?_⟩
      intro z hz ht
      by_cases same : z.val=i+1
      · exact (Fin.ext same : z=j) ▸ p
      · exact (mem_filter.mp prev).2 z hz (by omega)
    have geom := ini.kept_geom prev
    obtain ⟨C,cap,proper,zero⟩ := R.failed_cut j geom.1 geom.2.1 hf
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (free_ode_guard j).jb (moving_ode_guard j).jb cap
  · have eq : i=16 := by omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      lost (mem_filter.mpr ⟨prev,p⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := Far6969RescueGeometry.terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179740)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈ini.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := ini.marked_cutter noPole residues hi mem
    have prev := (mem_sdiff.mp mem).1
    rw [Initial.live,ite_eq_left hi] at prev
    let sub := R.marks.filter (OnMark R.family J)
    let G : Family M sub :=
      ⟨R.family.scalar,fun γ hγ=>R.family.mark γ (mem_filter.mp hγ).1,
        R.family.distinct.mono (filter_subset _ _)⟩
    obtain ⟨C,cost,cover⟩ := proper_cut G (cutShape i) (cutShape_fit i)
      (ini.kept_geom prev).1 cap proper
      (fun γ hγ=>zero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    exact ⟨C,cost,fun γ hγ on=>cover γ (mem_filter.mpr ⟨hγ,on⟩) on⟩
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈ini.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈ini.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark R.family Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (ini.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Initial.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) :
    J∈ini.final ∨ ∃ i<17,J∈ini.lost i := by
  by_cases h : ∃ i<17,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤17,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 17 le_rfl)

theorem Initial.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈ini.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  let geom (J : ini.final) := ini.kept_geom (mem_filter.mp J.property).1
  let surface (J : ini.final) := surfaceOf J.val (geom J).1.prime
  let S := ini.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := geom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : ini.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Initial.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=ini.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩

end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometryProcess

section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.Far6969MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts fixedFee fixed_count)
open Far6969FreeSource (reserve)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private def historyTable : List Mass :=
  [![10597, 106674, 492190, 2145993],
  ![5756, 165809/2, 375084, 1980456],
  ![22349/9, 351832/9, 375084, 1915456],
  ![13715/8, 390915/16, 1775816/9, 9168368/9],
  ![5216/5, 407313/25, 130626, 734373],
  ![4699/6, 145283/12, 248109/2, 2772225/4],
  ![34803/64, 501165/64, 80446, 1016044/3],
  ![39209/121, 579508/121, 2652560/49, 259081],
  ![39209/121, 579508/121, 48147, 259081],
  ![39209/121, 579508/121, 48147, 1006009/4],
  ![11153/40, 865023/200, 1943756/49, 216225],
  ![253791/961, 3699363/961, 4120626/121, 15944049/100],
  ![38497/150, 3699363/961, 4115580/121, 15944049/100],
  ![38497/150, 3699363/961, 4115580/121, 15944049/100],
  ![1173662/4761, 5666773/1587, 8407560/289, 99765932/729],
  ![1140713/5184, 17363647/5184, 141744/5, 99765932/729],
  ![1140713/5184, 17363647/5184, 3051745/108, 48750750/361]]

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by
  fin_cases k <;> decide +kernel

theorem history_step (i : Fin 16) (k : Fin 4) :
    let j : Fin 17 := ⟨i.val+1,by have := i.isLt; omega⟩
    history (i.val+1) k =
      min (history i.val k) (pairedCap (freeShape j) (movingShape j) (reserve j) true k) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k := by
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono
    ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<16 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 17 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 17 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 17, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

theorem seed_limit_small : seedLimit < (K1.p : ℚ) := by decide +kernel

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)).card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ))
    (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq
  exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
    (K1_14_3.scalar_atX_injective eq)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))).card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)

theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)) (label_injective M).injOn C
    (ini.content_cap.trans_lt (free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤(K1.p+1)*ini.content.totalDegree)
    |>.trans (Nat.mul_le_mul_left _ ini.content_cap)

theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤33735) :
    R.fixedMarks.card≤fixedLimit := by
  calc
    _ ≤ ∑ i : Fin 17, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (Far6969RescueGeometry.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (Far6969RescueGeometry.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<17,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i

private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Initial.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ ini.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 18 = ini.final := by simp [Initial.jointLive,Initial.live]
    simpa only [beforeCuts,Initial.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Initial.jointLive,ini.live_zero] using
        (subset_union_right : ini.parents⊆ ini.rankExit∪ini.parents)
    | succ i => exact ini.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Initial.jointLive,ini.live_zero]
      exact fun h=>(disjoint_left.mp ini.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (ini.fits k)
    | succ i => exact ini.cap_live (by omega) k


theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometryBills

section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.Far6969MainGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open Far6969RescueGeometry (RateOK beforeCuts lambda mu tau)
open Lower6960.Far6969RescueGeometry (heightBound height_spec)
open scoped Classical BigOperators

def degreeRates : List ℕ :=
  [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 88312895, 79543745, 90425937, 122251912, 122558590, 140293703, 218921550]

def heightRates : List ℕ :=
  [1781322, 1738943, 2204556, 2425241, 3142167, 3232483, 3714722, 4465429, 3605461, 4986275, 5557424, 6195846, 5425843, 3952275, 3941689, 3412569, 2103875]

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private theorem checked_rates (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<17) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min (47843/5) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 18 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 122500596345365350 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometryInvoice
end Z6969Source2536

-- Source: Research6969.FarPrefix
section Z6969Source2537
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Far6969MainGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open HighCore82268JointRank (fixed_fee_linear)
open Far6969RescueGeometry (Model Family OnMark OnSurface SurfacePass word curveMarks mem_curveMarks
  curve_tariff rated_curve_count fixedFee lambda mu tau)
open Lower6960.Far6969RescueGeometry (fixedFee_eq)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤33735) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    Far6969RescueGeometry.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤33735) {i : ℕ} (hi : i<17) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks R.family (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤33735) : C.lossMarks.card ≤ (lossLimit).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 17,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤33735) : C.paid.card≤mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤33735) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card≤122500596345365350 ∧ (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S,geom,surface⟩ := ini.terminal_surfaces
  refine ⟨C.paid,S,(C.paid_count hi).trans main_fee_bound,geom,?_⟩
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · have mark : γ∈C.pointMarks := mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ mark)))
      · have mark : γ∈(range 17).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometryFee

section Merged_R6960MainGeometryUnion
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Far6969MainGeometry
open Finset
open K1 (K)
open K1_14 (jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_3 (Surface Parent ProjectedProduct)
open Far6969RescueGeometry (Model Family OnSurface SurfacePass word exceptional_prefix)
open scoped Classical
def prefixCap : ℕ := 242442324370890748
theorem Rows.combined_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (lo : 2535≤M.overhead.toNat) (hi : M.overhead.toNat≤33735)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨main,left,fee,passing,cover⟩ := R.main_prefix hi noPole residues
  rcases R.out.kind with unit | common
  · refine ⟨main,left,fee.trans (by decide +kernel),passing,?_⟩
    intro γ hγ
    apply cover
    exact mem_filter.mpr ⟨hγ,by simp [unit,jetAt]⟩
  · obtain ⟨rescue,right,cost,retains,rescue_cover⟩ :=
      exceptional_prefix F Crt lo hi noPole residues common
    refine ⟨main∪rescue,left∪right,
      (card_union_le _ _).trans ((Nat.add_le_add fee cost).trans (by decide +kernel)),?_,?_⟩
    · intro q hq
      exact (mem_union.mp hq).elim (passing q) (retains q)
    · intro γ hγ
      let lift (paid' : Finset K) (S' : Finset Surface)
          (hp : paid'⊆main∪rescue) (hs : S'⊆left∪right)
          (on : γ∈paid' ∨ ∃ q∈S',OnSurface F q γ) :
          γ∈main∪rescue ∨ ∃ q∈left∪right,OnSurface F q γ := by
        rcases on with mark | ⟨q,hq,hmark⟩
        · exact Or.inl (hp mark)
        · exact Or.inr ⟨q,hs hq,hmark⟩
      by_cases e : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
      · exact lift rescue right subset_union_right subset_union_right (rescue_cover γ hγ e)
      · exact lift main left subset_union_left subset_union_left
          (cover γ (mem_filter.mpr ⟨hγ,e⟩))
theorem combined_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2535≤M.overhead.toNat) (hi : M.overhead.toNat≤33735)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (S.Nonempty → ∃ f,ProjectedProduct S f) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨paid,S,fee,geom,cover⟩ := R.combined_prefix lo hi noPole residues
  exact ⟨paid,S,fee,geom,fun hs=>K1_14_3_7.proof S hs (fun q hq=>(geom q hq).1),cover⟩
end Lower6960.Far6969MainGeometry

end
end Merged_R6960MainGeometryUnion
end Z6969Source2537

-- Source: Research6969.FarTerminalCount
section Z6969Source2538
set_option autoImplicit true
set_option Elab.async false

namespace Research6969.FarTerminalCount
open Polynomial Finset
open K1 (K)
open K1_14 (Equation L atMark jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open Lower6960
open Far6969RescueGeometry (Model Family SurfacePass terminalShape word)
open Far6969Terminal (terminalBank witness bank_checked positive)
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

private theorem reject {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2535≤h) (hi : h≤33735) {S : Finset Surface}
    (parents : ∀ q∈S, Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (e : ℕ)
    (ep : 0<e) (en : e≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179740 h terminalShape e U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179740 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179740 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 ep
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2.original)
    product.primitive.ne_zero en product slots)

private theorem box_guard (i : Fin 49) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel

private theorem one_sided (i : Fin 49) : (witness i.val).order 0=0 := by
  fin_cases i <;> decide +kernel

theorem degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2535≤h) (hi : h≤33735) {S : Finset Surface}
    (parents : ∀ q∈S, Parent q ∧ SurfacePass Crt w q) {f : Equation} (product : ProjectedProduct S f) :
    f.natDegree<48 ∧ ∀ j : Fin 2, axisDegree f j<(witness f.natDegree).order 1 := by
  have rule (i : Fin 49) (ip : 0 < i.val) (e : i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (witness i.val).U (axisDegree f) r≤
        rectSlots (witness i.val).U (witness i.val).order r) :=
    reject Crt w lo hi parents product i.val ip e _ _ (box_guard i) (positive lo hi i ip)
  have rev (i : Fin 49) (ip : 0 < i.val) (e : i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (swap (witness i.val).U) (axisDegree f) r≤
        rectSlots (swap (witness i.val).U) (swap (witness i.val).order) r) := by
    apply reject Crt w lo hi parents product i.val ip e
    · simpa [Nat.add_comm] using box_guard i
    · rw [KoalaRectAxes.debit_swap,KoalaRectAxes.gain_swap]
      exact positive lo hi i ip
  have grade : f.natDegree<48 := by
    by_contra! big
    apply rule 48 (by decide) (by simpa using big)
    intro r
    change (_+1-r*axisDegree f 0)*(_+1-r*axisDegree f 1) ≤ (_+1-r*0)*(_+1-r*0)
    simp only [Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨grade,?_⟩
  let i : Fin 49 := ⟨f.natDegree,by omega⟩
  let t:=witness f.natDegree
  have ip : 0 < i.val := product.positive
  have z0 : t.order 0=0 := one_sided i
  intro j
  by_contra! bad
  fin_cases j
  · apply rev i ip le_rfl
    intro r
    apply Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
    change _≤_+1-r*t.order 0
    rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
  · apply rule i ip le_rfl
    intro r
    apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
    change _≤_+1-r*t.order 0
    rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _

/-- The unchanged far-bank producer and its far-band terminal price
give the count for the actual family at every height 2535 through 33735. -/
theorem count {u deleted} (M : P1.ModelAt 33735 u deleted) {Γ : Finset K} (F : P1.FamilyAt 179740 M Γ)
    (lo : 2535≤M.overhead) (hi : M.overhead≤33735) :
    Γ.card≤274784969259510674 := by
  classical
  have hlo : 2535≤M.overhead.toNat := by omega
  have hhi : M.overhead.toNat≤33735 := by omega
  obtain ⟨D,⟨Crt⟩,regular,residues⟩ := Far6969PoleChart.of_family M F
  obtain ⟨paid,S,fee,geom,prod,cover⟩ := Far6969MainGeometry.combined_prefix F Crt hlo hhi regular residues
  by_cases surfaces : S.Nonempty
  · obtain ⟨f,project⟩ := prod surfaces
    obtain ⟨grade,axes⟩ := degrees Crt (word M) hlo hhi geom project
    let T := Γ\paid
    have sub : T⊆Γ := sdiff_subset
    have words : RetainedShortening.Word 179740 164806 M.word F.scalar T := by
      refine ⟨F.distinct.mono sub,?_,?_⟩
      · intro γ hγ
        rcases (F.mark γ (sub hγ)).scalar_degree with zero|degree
        · simp [zero]
        · change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at degree
          omega
      · intro γ hγ
        let mark:=F.mark γ (sub hγ)
        exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
    have remain := Far6969Retained.count words M.label (Far6969RescueGeometry.label_injective M) f
      project.positive grade project.separable axes (by
        intro γ hγ
        obtain ⟨mem,out⟩ := mem_sdiff.mp hγ
        obtain ⟨q,hq,on⟩ := (cover γ mem).resolve_left out
        simpa only [jetAt,eval₂_C,coe_eval₂RingHom,atMark] using on _ (project.vanishes q hq))
    have sizes := card_sdiff_add_card_inter Γ paid
    have left : (Γ∩paid).card≤paid.card := card_le_card inter_subset_right
    change T.card+(Γ∩paid).card=Γ.card at sizes
    have final := Nat.add_le_add remain (left.trans fee)
    rw [sizes] at final
    exact final.trans (by decide +kernel)
  · have contain : Γ⊆paid := by
      intro γ hγ
      exact (cover γ hγ).resolve_right (fun ⟨q,hq,_⟩=>surfaces ⟨q,hq⟩)
    exact (card_le_card contain).trans (fee.trans (by decide +kernel))

end Research6969.FarTerminalCount
end Z6969Source2538

-- Source: Research6969.Endpoint6969
section Z6969Source2539
set_option autoImplicit true
namespace Research6969.Endpoint
open K1 (K)
open ProximityPrize.Benchmark

/-- Precisely the transition interval between the certified low and far endpoints. -/
def Transition : Prop := ∀ {u deleted} (M:P1.ModelAt 33735 u deleted) {Γ:Finset K},
  P1.FamilyAt 179740 M Γ → 2293≤M.overhead → M.overhead≤2534 →
    Γ.card≤274784969259510674

theorem high_of_transition (transition:Transition) : Front6969.c7 := by
  intro u deleted M Γ F low high
  change 2293≤M.overhead at low
  change M.overhead≤33735 at high
  by_cases early:M.overhead≤2534
  · exact transition M F low early
  · have later : 2535≤M.overhead := by omega
    exact FarTerminalCount.count M F later high

theorem of_low_and_transition (low:Front6969.c6) (transition:Transition) :
    ProtocolClaim 6969 Profile.p Profile.q :=
  ProfileEndpoint.of_height_counts low (high_of_transition transition)

theorem of_transition (transition:Transition) : ProtocolClaim 6969 Profile.p Profile.q :=
  of_low_and_transition LowProfile6969.low_6969 transition

end Research6969.Endpoint
end Z6969Source2539

-- Source: Research6969.EndpointNear
section Z6969Source2540
set_option autoImplicit true
namespace Research6969.Endpoint
open ProximityPrize.Benchmark

def Near:Prop:=∀{u del}(M:P1.ModelAt 33735 u del){Γ},P1.FamilyAt 179740 M Γ →
  2293≤M.overhead → M.overhead≤2389 → Γ.card≤274784969259510674

theorem of_near (near:Near):ProtocolClaim 6969 Profile.p Profile.q:=by
  apply of_transition
  intro u del M Γ F lo hi
  by_cases first:M.overhead≤2389
  · exact near M F lo first
  · exact MiddleBand.count M F (by omega) hi

end Research6969.Endpoint
end Z6969Source2540

-- Source: Research6969.HighEndpoint
section Z6969Source2541
set_option autoImplicit true
namespace Research6969.HighEndpoint
open Lower6960
open Far6969RescueGeometry (Model Family)
open K1_14_1 (poleProduct nodeL)
open ProximityPrize.Benchmark
open Polynomial

/-- Everything outside the selected large-degree normal packets is
discharged on the concrete lower-track model. -/
theorem protocol (high:HighPackets.Goal):ProtocolClaim 6969 Profile.p Profile.q:=by
  apply Endpoint.of_near
  intro u del M Γ F lo hi
  obtain ⟨D,⟨Crt⟩,safe,res⟩:=Far6969PoleChart.of_family M F
  obtain ⟨out⟩:=Prefix6969Early.route F Crt (by omega) (by omega) safe res
  exact HighPackets.from_outcome high F Crt (by omega) (by omega) (fun i=>by
    change (poleProduct D).eval (nodeL i)≠0
    rw [poleProduct,eval_mul];exact mul_ne_zero (safe 0 i) (safe 1 i)) res out

end Research6969.HighEndpoint
end Z6969Source2541

-- Source: Research6969.FinalCoverage
section Z6969Source2542
set_option autoImplicit true
namespace Research6969.FinalCoverage
open ProximityPrize.Benchmark
structure Remaining : Prop where
  seed1:HighPendingSeed1.Required
  seed2:HighPendingSeed2.Required
  seed3:HighPendingSeed3.Required
  seed4:HighPendingSeed4.Required
  seed5:HighPendingSeed5.Required
  seed6:HighPendingSeed6.Required
  seed7:HighPendingSeed7.Required
  seed8:HighPendingSeed8.Required
  seed9:HighPendingSeed9.Required
  seed10:HighPendingSeed10.Required
  seed11:HighPendingSeed11.Required
  seed12:HighPendingSeed12.Required
  seed13:HighPendingSeed13.Required
  seed14:HighPendingSeed14.Required
  seed15:HighPendingSeed15.Required
  seed16:HighPendingSeed16.Required
  seed17:HighPendingSeed17.Required
  seed18:HighPendingSeed18.Required

theorem high (proof:Remaining):HighPackets.Goal:=by
  intro i
  fin_cases i
  · exact HighDispatchSeed1.count proof.seed1
  · exact HighDispatchSeed2.count proof.seed2
  · exact HighDispatchSeed3.count proof.seed3
  · exact HighDispatchSeed4.count proof.seed4
  · exact HighDispatchSeed5.count proof.seed5
  · exact HighDispatchSeed6.count proof.seed6
  · exact HighDispatchSeed7.count proof.seed7
  · exact HighDispatchSeed8.count proof.seed8
  · exact HighDispatchSeed9.count proof.seed9
  · exact HighDispatchSeed10.count proof.seed10
  · exact HighDispatchSeed11.count proof.seed11
  · exact HighDispatchSeed12.count proof.seed12
  · exact HighDispatchSeed13.count proof.seed13
  · exact HighDispatchSeed14.count proof.seed14
  · exact HighDispatchSeed15.count proof.seed15
  · exact HighDispatchSeed16.count proof.seed16
  · exact HighDispatchSeed17.count proof.seed17
  · exact HighDispatchSeed18.count proof.seed18

theorem protocol (proof:Remaining):ProtocolClaim 6969 Profile.p Profile.q:=HighEndpoint.protocol (high proof)

end Research6969.FinalCoverage
end Z6969Source2542
