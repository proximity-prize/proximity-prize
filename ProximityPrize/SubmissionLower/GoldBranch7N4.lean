import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.UpperBranch6
set_option autoImplicit true
section
namespace P3_7_4
open Finset
open K1_14 (Shape)
open P3 (HighBand agreement)
open P3_7 (Bank Test debit jointGain tested threshold seedThreshold)
export P1_7_6 (orderEnd linearEnd Quad prefixProduct intervalProduct seedEnd yStart seedQuad scaledDebit)
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
end P3_7_4
end
section
namespace P3_7_4
open Finset
open K1_14 (Shape shapeSum slots triangle)
open P3 (agreement)
open P3_7 (jointGain)
open private slots_anti sum_range_guard diagonal from ProximityPrize.SubmissionLower.UpperBranch6
end P3_7_4
end
section
namespace P3_7_4
open Finset
open P3 (agreement)
open K1_14 (Shape)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
export P1_7_6 (lt_linearEnd)
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
