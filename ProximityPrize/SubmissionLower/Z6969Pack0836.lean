import ProximityPrize.SubmissionLower.R6970LayerMass
import ProximityPrize.SubmissionLower.R6970FatMoments2297
import ProximityPrize.SubmissionLower.Low6966Monotone
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.Fat6966Chart
import ProximityPrize.SubmissionLower.Z6969Pack0832
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.Low6966Order

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.ActualDegreeChart
section Z6969Source2273
set_option autoImplicit true
namespace Research6969.ActualDegreeChart
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_1 (weight_const_mul_le top_le_index)
open K1_13_7_2_2 (stride topLinear denominator numerator hasseNumerator raw raw_bound sep_pow_bound)
open K1_13_1 (indexDegree_eq)
local notation "W" => MvPolynomial.weightedTotalDegree

/-- The weighted recurrence for the concrete numerator, at any positive Taylor length. -/
private theorem numerator_degree {n : ℕ} (w : Fin 4 → ℕ) (Δ : ℕ)
    (shift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g : Row 4} {B : ℕ} (room : w 3 ≤ B) (bound : W w g ≤ B) (i : Fin n) :
    W w (numerator g i) ≤ w 0 + n * (stride (topLinear g) * (B - w 3) + Δ) := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  apply (weight_const_mul_le _ _ _).trans
  unfold hasseNumerator
  apply (weight_const_mul_le _ _ _).trans
  apply (weightedTotalDegree_mul_le _ _ _).trans
  let k := stride (topLinear g)
  calc
    _ ≤ k * (n-j.val) * (B-w 3) + (w 0 + j.val * (k * (B-w 3) + Δ)) :=
      Nat.add_le_add (sep_pow_bound g w _ bound) (raw_bound _ w Δ shift room bound _)
    _ = w 0 + (n-j.val+j.val) * (k * (B-w 3)) + j.val * Δ := by ring
    _ ≤ _ := by
      rw [Nat.sub_add_cancel j.isLt.le, Nat.mul_add, ← Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right Δ j.isLt.le) _

private abbrev L : ℕ := 133379
def box : Shape := ⟨11*L,11*L,3*L⟩

private theorem support {g Q : Row 4} (shape_g : shape g = ⟨3,8,2⟩)
    (recurrence : ∀ (w : Fin 4 → ℕ) (Δ B : ℕ),
      (∀ i : Fin 3, w i.succ ≤ w i.castSucc+Δ) → w 3 ≤ B → W w g ≤ B →
      W w Q ≤ w 0 + L * (stride (topLinear g) * (B - w 3) + Δ)) :
    InBox (shape Q) box := by
  have gb : g.totalDegree = 3 := congrArg Shape.b shape_g
  have gj : indexDegree g = 8 := congrArg Shape.j shape_g
  have gt : g.degreeOf 3 = 2 := congrArg Shape.t shape_g
  have two : stride (topLinear g) = 2 := by simp [topLinear, stride, shape_g]
  have total := recurrence 1 0 3 (fun _ => by simp) (by decide)
    (by simpa only [weightedTotalDegree_one] using gb.le)
  have idx := recurrence Fin.val 1 8 (fun _ => le_rfl) (by decide)
    (by rw [← indexDegree_eq]; exact gj.le)
  let w : Fin 4 → ℕ := Pi.single 3 1
  have step : ∀ i : Fin 3, w i.succ ≤ w i.castSucc+1 := by intro i; fin_cases i <;> decide
  have top := recurrence w 1 2 step (by decide)
    (by simpa only [w, weightedTotalDegree_piSingle] using gt.le)
  rw [two] at total idx top
  change Q.totalDegree ≤ box.b ∧ indexDegree Q ≤ box.j ∧ Q.degreeOf 3 ≤ box.t
  refine ⟨?_,?_,?_⟩
  · simpa only [weightedTotalDegree_one] using total.trans (by decide : (1:Fin 4→ℕ) 0 + L*(2*(3-(1:Fin 4→ℕ) 3)+0) ≤ box.b)
  · rw [indexDegree_eq]; exact idx.trans (by decide)
  · simpa only [w, weightedTotalDegree_piSingle] using top.trans (by decide : w 0 + L*(2*(2-w 3)+1) ≤ box.t)

/-- These are the denominator, every numerator, and the test of the actual recovery chart. -/
theorem recovery_support (g : Row 4) (h : shape g = ⟨3,8,2⟩) :
    InBox (shape (denominator g 133379)) box ∧
    (∀ i : Fin 133379, InBox (shape (numerator g i)) box) ∧
    InBox (shape (raw (topLinear g) g 133379)) box := by
  refine ⟨support h ?_, fun i => support h ?_, support h ?_⟩
  · intro w Δ B _ _ hb
    apply (sep_pow_bound g w (stride (topLinear g)*L) hb).trans
    rw [Nat.mul_comm (stride (topLinear g)) L, Nat.mul_assoc]
    exact Nat.le_add_left_of_le (Nat.mul_le_mul_left L (Nat.le_add_right _ _))
  · intro w Δ B shift room bound
    exact numerator_degree w Δ shift room bound i
  · intro w Δ B shift room bound
    exact raw_bound _ w Δ shift room bound _


open K1_13_7_2 (evalTrajectory)





























end
end Research6969.ActualDegreeChart
end Z6969Source2273

namespace MiddleActualDegree6970
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_1 (weight_const_mul_le top_le_index)
open K1_13_7_2_2 (stride topLinear denominator numerator hasseNumerator raw raw_bound sep_pow_bound)
open K1_13_1 (indexDegree_eq)
local notation "W" => MvPolynomial.weightedTotalDegree

private theorem numerator_degree {n : ℕ} (w : Fin 4 → ℕ) (Δ : ℕ)
    (shift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g : Row 4} {B : ℕ} (room : w 3 ≤ B) (bound : W w g ≤ B) (i : Fin n) :
    W w (numerator g i) ≤ w 0 + n * (stride (topLinear g) * (B - w 3) + Δ) := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  apply (weight_const_mul_le _ _ _).trans
  unfold hasseNumerator
  apply (weight_const_mul_le _ _ _).trans
  apply (weightedTotalDegree_mul_le _ _ _).trans
  let k := stride (topLinear g)
  calc
    _ ≤ k * (n-j.val) * (B-w 3) + (w 0 + j.val * (k * (B-w 3) + Δ)) :=
      Nat.add_le_add (sep_pow_bound g w _ bound) (raw_bound _ w Δ shift room bound _)
    _ = w 0 + (n-j.val+j.val) * (k * (B-w 3)) + j.val * Δ := by ring
    _ ≤ _ := by
      rw [Nat.sub_add_cancel j.isLt.le, Nat.mul_add, ← Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right Δ j.isLt.le) _

def indexBound (x : Shape) (L : ℕ) : ℕ := L * (2 * (x.j - 3) + 1)

def box (x : Shape) (L : ℕ) : Shape :=
  let j := indexBound x L
  ⟨max (1 + L * (2 * (x.b - 1))) j, j, min (3 * L) (j / 3)⟩

theorem box_chamber_pos (x : Shape) (L : ℕ) (hj : 6 ≤ x.j) (hL : 0 < L) :
    K1_13_7_1.Chamber (box x L) ∧ 0 < (box x L).t := by
  have hindex : 3 ≤ indexBound x L := by
    unfold indexBound
    have hs : 3 ≤ 2 * (x.j - 3) + 1 := by omega
    exact (by omega : 3 ≤ L * 3).trans (Nat.mul_le_mul_left L hs)
  unfold box
  refine ⟨⟨le_max_right _ _, ?_⟩, ?_⟩
  · exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (Nat.mul_div_le _ _)
  · exact lt_min (by omega) (by omega)

private theorem support {g Q : Row 4} {L : ℕ} (ht : (shape g).t = 2)
    (recurrence : ∀ (w : Fin 4 → ℕ) (Δ B : ℕ),
      (∀ i : Fin 3, w i.succ ≤ w i.castSucc+Δ) → w 3 ≤ B → W w g ≤ B →
      W w Q ≤ w 0 + L * (stride (topLinear g) * (B - w 3) + Δ)) :
    InBox (shape Q) (box (shape g) L) := by
  have two : stride (topLinear g) = 2 := by simp [topLinear, stride, ht]
  have total := recurrence 1 0 (shape g).b (fun _ => by simp) (by
    change 1 ≤ g.totalDegree
    have h := K1_13_1.index_bounds g
    change 3 * g.degreeOf 3 ≤ indexDegree g ∧ indexDegree g ≤ 3 * g.totalDegree at h
    change g.degreeOf 3 = 2 at ht
    omega)
    (by rw [weightedTotalDegree_one]; exact le_rfl)
  have idx := recurrence Fin.val 1 (shape g).j (fun _ => le_rfl) (by
    have h := top_le_index g
    rw [← indexDegree_eq] at h
    change 3 ≤ indexDegree g
    change g.degreeOf 3 = 2 at ht
    omega) (by rw [← indexDegree_eq]; exact le_rfl)
  let w : Fin 4 → ℕ := Pi.single 3 1
  have step : ∀ i : Fin 3, w i.succ ≤ w i.castSucc+1 := by intro i; fin_cases i <;> decide
  have top := recurrence w 1 2 step (by decide)
    (by
      rw [show w = Pi.single (3 : Fin 4) 1 from rfl, weightedTotalDegree_piSingle]
      exact (show g.degreeOf 3 = 2 from ht).le)
  rw [two] at total idx top
  have hb : Q.totalDegree ≤ 1 + L * (2 * ((shape g).b - 1)) := by
    simpa only [weightedTotalDegree_one, Pi.one_apply, add_zero] using total
  have hj : indexDegree Q ≤ indexBound (shape g) L := by
    rw [← indexDegree_eq] at idx
    change indexDegree Q ≤ 0 + L * (2 * ((shape g).j - 3) + 1) at idx
    simpa only [indexBound, zero_add] using idx
  have ht' : Q.degreeOf 3 ≤ 3 * L := by
    simpa [w, weightedTotalDegree_piSingle, Nat.mul_comm L 3] using top
  have hj' := top_le_index Q
  rw [← indexDegree_eq] at hj'
  have htidx : Q.degreeOf 3 ≤ indexBound (shape g) L / 3 :=
    (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  exact ⟨hb.trans (le_max_left _ _), hj, le_min ht' htidx⟩

/-- The quadratic recovery chart keeps the actual total degree of its input. -/
theorem recovery_support (g : Row 4) {L : ℕ} (ht : (shape g).t = 2) :
    InBox (shape (denominator g L)) (box (shape g) L) ∧
    (∀ i : Fin L, InBox (shape (numerator g i)) (box (shape g) L)) ∧
    InBox (shape (raw (topLinear g) g L)) (box (shape g) L) := by
  refine ⟨support ht ?_, fun i => support ht ?_, support ht ?_⟩
  · intro w Δ B _ _ hb
    apply (sep_pow_bound g w (stride (topLinear g)*L) hb).trans
    rw [Nat.mul_comm (stride (topLinear g)) L, Nat.mul_assoc]
    exact Nat.le_add_left_of_le (Nat.mul_le_mul_left L (Nat.le_add_right _ _))
  · intro w Δ B shift room bound
    exact numerator_degree w Δ shift room bound i
  · intro w Δ B shift room bound
    exact raw_bound _ w Δ shift room bound _

end
end MiddleActualDegree6970

-- Source: ProximityPrize.SubmissionLower.Low6969CubicTariff
section Z6969Source2274
set_option autoImplicit true
set_option Elab.async false

namespace Research6969.Low6969CubicTariff

open K1_13 (Shape InBox ceilDiv mixed32 chart)

abbrev agreement : ℕ := 179730
abbrev degree : ℕ := 133378
abbrev length : ℕ := degree + 1
abbrev errors : ℕ := 262144 - agreement
abbrev gap : ℕ := agreement - degree
abbrev fatOrder : ℕ := 21437
abbrev divisorOrder : ℕ := 19755
abbrev isolatedOrder : ℕ := 170
abbrev curveLength : ℕ :=
  (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)

def commonBox : Shape := ⟨682, 239, 0⟩
def resultantBox : Shape := ⟨405380800, 137080000, 0⟩

def standardChart (x : Shape) : Shape :=
  if x.t = 1 then
    let p := x.chamber
    let j := 3 + length * (p.j - 2)
    ⟨max (1 + length * (p.b - 1)) j, j, min (length + 1) (j / 3)⟩
  else chart (length + 4) x.chamber

def divisorChart (x : Shape) : Shape :=
  if x.t = 2 then MiddleActualDegree6970.box x length else standardChart x

def divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder,
   commonBox.j + resultantBox.j / divisorOrder, 0⟩

def divisorCharge (p h : Shape) : ℕ :=
  let cut : Shape :=
    ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
     max h.j (divisorBox.j + 1), max 1 h.t⟩
  ceilDiv (errors * mixed32 p divisorBox cut h) (32 * gap) +
    ceilDiv (mixed32 p divisorBox cut p) 32 +
    20 * p.b * h.b ^ 2 + 5 * degree * p.b * h.b + 1

def singularCharge (x : Shape) : ℕ :=
  let p := x.chamber
  let h := standardChart x
  if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b ^ 2 + 1 else 0

def curveCharge (x : Shape) : ℕ :=
  let p := x.chamber
  let h := standardChart x
  ceilDiv (errors * mixed32 p resultantBox resultantBox h +
    gap * mixed32 p resultantBox resultantBox p) (32 * gap * curveLength)

def isolatedCharge : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)

def fatPrice (x : Shape) : ℕ :=
  divisorCharge x.chamber (divisorChart x) + singularCharge x + curveCharge x + isolatedCharge
















open K1_13 (Row shape)
open K1_13_7_2_2 (topLinear denominator numerator raw)

theorem quadratic_divisor_chart (g : Row 4) (h : (shape g).t = 2) :
    InBox (shape (denominator g length)) (divisorChart (shape g)) ∧
    (∀ i : Fin length, InBox (shape (numerator g i)) (divisorChart (shape g))) ∧
    InBox (shape (raw (topLinear g) g length)) (divisorChart (shape g)) := by
  simpa only [divisorChart, if_pos h] using MiddleActualDegree6970.recovery_support g (L := length) h

theorem quadratic_chart_chamber (f : Row 4) (h : (shape f).t = 2) :
    K1_13_7_1.Chamber (divisorChart (shape f)) ∧ 0 < (divisorChart (shape f)).t := by
  have hj := (K1_13_1.index_bounds f).1
  simpa only [divisorChart, if_pos h] using
    MiddleActualDegree6970.box_chamber_pos (shape f) length (by omega) (Nat.succ_pos _)

end Research6969.Low6969CubicTariff
end Z6969Source2274

-- Source: ProximityPrize.SubmissionLower.Low6969Prices
section Z6969Source2275
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit true

namespace Low6969Prices

open K1_13 (Row Shape shape extend OnFactor FatEligible)
open Research6969

abbrev agreement := Low6969Primary.agreement
abbrev physicalDegree := Low6969Primary.degree
abbrev anchorCutoff := LowProfile6969.anchorCutoff
abbrev taylorLength := Low6969CubicTariff.length
abbrev errors := Low6969CubicTariff.errors
abbrev incidenceGap := Low6969CubicTariff.gap
abbrev fatOrder := Low6969CubicTariff.fatOrder
abbrev divisorOrder := Low6969CubicTariff.divisorOrder
abbrev isolatedOrder := Low6969CubicTariff.isolatedOrder
abbrev Messages := Low6969Primary.Messages
abbrev SmallFactor := LowProfile6969.SmallFactor
abbrev TrueWeightLE := @LowProfile6969.TrueWeightLE
abbrev FatEquations := Low6969Fat.FatEquations
abbrev Holds := Low6969Fat.Holds
abbrev commonBox := Low6969Fat.commonBox
abbrev resultantBox := Low6969Fat.resultantBox
abbrev fatPrice := Low6969CubicTariff.fatPrice

def linearChart (p : Shape) : Shape :=
  let index := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) index, index, min (taylorLength + 1) (index / 3)⟩

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) :
    Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ mem => h.degree γ (hΔ mem), fun γ mem => h.hits γ (hΔ mem)⟩

def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, Holds E (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

end Low6969Prices
end Z6969Source2275

-- Source: ProximityPrize.SubmissionLower.Low6969LeadingPrices
section Z6969Source2276
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit true

namespace Low6969Prices

open K1_13 (atJet extend)

abbrev LowerRow := LowProfile6969.LowerRow

def lowerWidth (top : ℕ) : ℕ := 143 - top
def lowerIndex (top : ℕ) : ℕ := 60 - 3 * top
def lowerTop (top : ℕ) : ℕ := lowerIndex top / 2

def lowerCap : ℕ → ℕ
  | 0 => 32366760449246328
  | 1 => 29327847625153443
  | 2 => 26425863949989591
  | 3 => 23662310668877784
  | 4 => 21039929228222417
  | 5 => 18560350637172986
  | 6 => 16226192633808788
  | 7 => 14039202548103346
  | 8 => 12001888057905658
  | 9 => 10116098961026135
  | 10 => 8384246932962957
  | 11 => 6808269976591597
  | 12 => 5390498232723584
  | 13 => 4132943236742945
  | 14 => 3037868472223412
  | 15 => 2107343924716369
  | 16 => 1343581707791287
  | _ => 0

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top

end Low6969Prices
end Z6969Source2276

-- Source: ProximityPrize.SubmissionLower.Low6969FatBank24000
section Z6969Source2277
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969FatBank24000Defs
section Merged_R6960Low6969FatBank24000Defs

set_option Elab.async false
section
namespace Low6969FatBank24000
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 3975818
abbrev secondOrder : ℕ := 1815862
abbrev firstCut : ℕ := 5000 * 179730 - firstOrder
abbrev secondCut : ℕ := 5000 * 179730 - secondOrder
abbrev bankRank : ℕ := 1






/-- The low fat chain works with rows whose seed degree is at most 24,000. -/
abbrev seedCap : ℕ := 24400
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
open K1_13 (PoleData)
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2307 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
end
end Low6969FatBank24000
end
end Merged_R6960Low6969FatBank24000Defs

-- merged module R6960Low6969FatBank24000Seed
section Merged_R6960Low6969FatBank24000Seed
set_option Elab.async false
section
namespace Low6969FatBank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open MvPolynomial
open Low6969FatBank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (seedView seedCoeff flatCoeff coeff_mem_capped normalize normalize_mem_capped node_coeff toRow contactWeight_eq)
private theorem seedCoeff_eq_zero27 {F : PhysicalRow} (hS : seedDegree F ≤ 24400)
    {n : ℕ} (hn : 24400 < n) : seedCoeff n F = 0 := by
  have hdeg : (seedView F).natDegree ≤ 24400 := by
    simpa only [seedView, natDegree_optionEquivLeft, seedDegree] using hS
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn)
private theorem mem_contact_of_origin_eq_zero27 {x v : Geom} {F : PhysicalRow}
    (hS : seedDegree F ≤ 24400)
    (h : ∀ n : Fin 24401, origin (normalize x v (flatCoeff n F)) = 0) :
    F ∈ contactAt x v := by
  apply (mem_contactAt x v F).mpr
  intro e
  let P := (backwardShift x v F).coeff (e.some.optionElim (e none))
  let E := Polynomial.taylorEquiv x
  have hE : E ((Polynomial.X - Polynomial.C x) ^ (5000 - 3 * e (some 0))) =
      Polynomial.X ^ (5000 - 3 * e (some 0)) := by
    have hX : E (Polynomial.X - Polynomial.C x) = Polynomial.X := by
      rw [map_sub]
      change Polynomial.taylor x Polynomial.X - Polynomial.taylor x (Polynomial.C x) = _
      simp
    rw [map_pow, hX]
  have hP : P = (backwardShift x v F).coeff e := by simp [P]
  rw [← hP, ← map_dvd_iff E, hE, Polynomial.X_pow_dvd_iff]
  intro i hi
  have hcoeff : E P =
      (toRow (shear (normalize x v (flatCoeff (e none) F)))).coeff e.some :=
    (node_coeff x v F (e none) e.some).symm
  rw [hcoeff]
  change ((optionEquivRight Geom (Fin 3) _).coeff e.some).coeff i = 0
  rw [optionEquivRight_coeff_coeff]
  by_cases hn : e none < 24401
  · have hz := congrArg (fun Q : Flat => Q.coeff (e.some.optionElim i)) (h ⟨e none, hn⟩)
    change (weightedTruncation contactWeight 5000
      (shear (normalize x v (flatCoeff (e none) F)))).coeff (e.some.optionElim i) = 0 at hz
    have hlt : (e.some.optionElim i).weight contactWeight < 5000 := by
      rw [contactWeight_eq]
      change i + 3 * e (some 0) < 5000
      omega
    rw [coeff_weightedTruncation] at hz
    simpa only [hlt, ite_true] using hz
  · have hz := seedCoeff_eq_zero27 hS (n := e none) (by omega)
    have hz' : flatCoeff (e none) F = 0 := by
      change toRow.symm (seedCoeff (e none) F) = 0
      rw [hz, map_zero]
    simp [hz']
private def nodeInput (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) (n : Fin 24401) : V →ₗ[Geom] Capped b.box.b :=
  ((normalize x v).toLinearMap ∘ₗ flatCoeff n ∘ₗ V.subtype).codRestrict _
    (fun F => normalize_mem_capped (coeff_mem_capped (hcap F F.2).1 n) x v)
private def nodeMap (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) : V →ₗ[Geom] (Fin 24401 → cappedRange b.box.b) :=
  LinearMap.pi fun n =>
    (origin.domRestrict (Capped b.box.b)).rangeRestrict ∘ₗ nodeInput b x v V hcap n
theorem codim_le_cappedRange27 (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (hcap : ∀ F ∈ V, Caps27 b.box F) :
    codimIn V (contactAt x v) ≤ 24401 * Module.finrank Geom (cappedRange b.box.b) := by
  let A := nodeMap b x v V hcap
  have hzero (F : A.ker) : (F.1 : PhysicalRow) ∈ contactAt x v := by
    apply mem_contact_of_origin_eq_zero27 (hcap F.1 F.1.2).2
    intro n
    have h := congrFun (LinearMap.mem_ker.mp F.2) n
    have hval := congrArg (fun z : cappedRange b.box.b => z.val) h
    change origin (normalize x v (flatCoeff n F.1.1)) = 0 at hval
    exact hval
  let f : A.ker →ₗ[Geom] ↥(V ⊓ contactAt x v) :=
    (V.subtype ∘ₗ A.ker.subtype).codRestrict _ fun F => Submodule.mem_inf.mpr ⟨F.1.2, hzero F⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun s : ↥(V ⊓ contactAt x v) => (s : PhysicalRow)) h
    exact he
  have hk := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hr := Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr
  have hnull := LinearMap.finrank_range_add_finrank_ker (K := Geom)
    (V := ↥V) (V₂ := Fin 24401 → cappedRange b.box.b) A
  unfold codimIn
  omega
end
end Low6969FatBank24000Seed
end
section
namespace Low6969FatBank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open Low6969FatBank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (bank_bound plane_rank_le)
theorem contact_bound27 : ∀ (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow),
    Module.Finite Geom V → (∀ F ∈ V, Caps27 b.box F) →
    codimIn V (contactAt x v) ≤ 24401 * b.nodeRank := by
  intro b x v V hV hcap
  let : Module.Finite Geom V := hV
  obtain ⟨p, hp⟩ := bank_bound K1_13_4_2_2_3.proof K1_13_4_2_2_4.proof
    K1_13_4_2_2_5.proof K1_13_4_2_2_6.proof b
  apply (codim_le_cappedRange27 b x v V hcap).trans
  apply Nat.mul_le_mul_left
  apply (cappedRange_le_sum b.box.b (fun q k => blockBound q (offset k) (p q k)) ?_).trans hp
  intro q hq k hk
  have hB : b.box.b + 1 ≤ 6821 := by cases b <;> decide
  exact (rank_originBlock_le_plane q k).trans
    (plane_rank_le K1_13_4_2_2_1.proof K1_13_4_2_2_2.proof (hq.trans_le hB) hk (p q k))
end
end Low6969FatBank24000Seed
end
section
namespace Low6969FatBank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open Low6969FatBank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone dimension_of_debits)
def poleDebit27 (a : Shape) : ℕ :=
  ∑ q ∈ Finset.range (a.b + 1),
    (a.b + a.j - q) * gradeCount a q * (24401 + (a.b - q))
abbrev SeedCoeff27 (a : Shape) (q : ℕ) := Fin (24401 + (a.b - q))
def c2_27 : Prop :=
  ∀ (a : Shape) (α : Geom) (N D : (Polynomial Geom)), D ≠ 0 →
    N.natDegree ≤ 1 → D.natDegree ≤ 1 →
    let z₀ : GenericSeed := algebraMap (Polynomial Geom) GenericSeed N / algebraMap (Polynomial Geom) GenericSeed D
    ∃ p : ∀ q : Fin (a.b + 1), PhysicalRow →ₗ[Geom] (JetCoeff a q.val → (Polynomial Geom)),
      ∀ F : PhysicalRow, Caps27 a F →
        (∀ e ∈ (centered z₀ F).support, admissible a e) ∧
        ∀ (q : Fin (a.b + 1)) (c : JetCoeff a q.val),
          (p q F c).natDegree ≤ 24400 + (a.b - q.val) ∧
          algebraMap (Polynomial Geom) GenericSeed (p q F c) =
            (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q.val) *
              localCoeff a α q.val c (centered z₀ F)
end
end Low6969FatBank24000Seed
end
section
namespace Low6969FatBank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_3_2
open Low6969FatBank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3_2 (cleared cleared_apply clearedFactor support_bounds grade_sub centered_admissible map_cleared seedMap grade)
private theorem cleared_degree27 {a : Shape} {α : Geom} {N D : (Polynomial Geom)}
    (hN : N.natDegree ≤ 1) (hD : D.natDegree ≤ 1) {F : PhysicalRow} (hF : Caps27 a F)
    (q : Fin (a.b + 1)) (c : JetCoeff a q.val) :
    (cleared a α N D q F c).natDegree ≤ 24400 + (a.b - q.val) := by
  classical
  rw [cleared_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  split
  next he =>
    apply (Polynomial.natDegree_smul_le _ _).trans
    obtain ⟨hB, _, _, _⟩ := support_bounds hF.1 hm
    have hU : m none ≤ 24400 :=
      (MvPolynomial.le_degreeOf_of_mem_support none hm).trans hF.2
    have hq := grade_sub hB (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
    have hn : (N ^ (m (some 0) - k)).natDegree ≤ m (some 0) - k :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hN)
    have hd : (D ^ (a.b - grade m)).natDegree ≤ a.b - grade m :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hD)
    calc
      _ ≤ (m none + (m (some 0) - k)) + (a.b - grade m) := by
        unfold clearedFactor
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hd
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hn
        exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
      _ ≤ _ := by omega
  next => simp
theorem proof27 : c2_27 := by
  intro a α N D hD hNdeg hDdeg
  have hD' : seedMap D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)).2 hD
  refine ⟨cleared a α N D, fun F hF => ⟨centered_admissible _ hF.1, ?_⟩⟩
  intro q c
  exact ⟨cleared_degree27 hNdeg hDdeg hF q c, map_cleared hD' hF.1 q c⟩
end
end Low6969FatBank24000Seed
end
section
namespace Low6969FatBank24000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_1 Finset
open Low6969FatBank24000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone)
open K1_13_4_2_1 (credit extra grade_sum moment)
def c3_27 : Prop :=
  ∀ (Γ : Finset K) (s : K → (Polynomial K)) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (α : Geom) (V : Submodule Geom PhysicalRow), Module.Finite Geom V →
    (∀ F ∈ V, Caps27 a F) → P.H.IsRoot α → P.H.derivative.eval α ≠ 0 →
    codimIn V (poleCondition P L a (localPole α)) ≤ poleDebit27 a
private theorem coeff_test_zero_iff27 {a : Shape} {q : ℕ} {α : Geom}
    {F : PhysicalRow} {G : RawRow} {D : (Polynomial Geom)} (hD : D ≠ 0)
    (w : JetCoeff a q → Geom) (p : PhysicalRow →ₗ[Geom] (JetCoeff a q → (Polynomial Geom)))
    (hp : ∀ c, (p F c).natDegree ≤ 24400 + (a.b - q) ∧
      algebraMap (Polynomial Geom) GenericSeed (p F c) =
        (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * localCoeff a α q c G) :
    (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔ dot a α q w G = 0 := by
  have hdeg : (clearedTest w p F).natDegree ≤ 24400 + (a.b - q) := by
    rw [clearedTest_apply]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ =>
      (Polynomial.natDegree_smul_le _ _).trans (hp c).1
  have hz : (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔
      clearedTest w p F = 0 := by
    refine ⟨fun h => Polynomial.ext fun n => ?_, by intro h k; rw [h, Polynomial.coeff_zero]⟩
    rw [Polynomial.coeff_zero]
    by_cases hn : n < 24401 + (a.b - q)
    · exact h ⟨n, hn⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hmap : algebraMap (Polynomial Geom) GenericSeed (clearedTest w p F) =
      (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * dot a α q w G := by
    rw [clearedTest_apply, dot, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_def, map_mul, (hp c).2, IsScalarTower.algebraMap_apply Geom (Polynomial Geom) GenericSeed]
    ring
  rw [hz, ← (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)), hmap]
  have hne : algebraMap (Polynomial Geom) GenericSeed D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)).2 hD
  simp [pow_ne_zero _ hne]
theorem simple_pole27 (h2 : c2_27) : c3_27 := by
  classical
  intro Γ s P L a α V hV hcap hroot hsimple
  obtain ⟨N, D, hD, hNdeg, hDdeg, hnorm⟩ := normalization P L α hroot hsimple
  obtain ⟨w, hw⟩ := K1_13_4_2_3_1.proof a α
  obtain ⟨p, hp⟩ := h2 a α N D hD hNdeg hDdeg
  let E := ∀ q : Fin (a.b + 1), (Test a q.val × SeedCoeff27 a q.val) → Geom
  let f : V →ₗ[Geom] E :=
    LinearMap.pi fun q => LinearMap.pi fun ij =>
      (Polynomial.lcoeff Geom ij.2.val).comp ((clearedTest (w q ij.1) (p q)).comp V.subtype)
  have hker : LinearMap.ker f = (poleCondition P L a (localPole α)).comap V.subtype := by
    ext F
    have h := hp F.val (hcap F.val F.property)
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    simp only [Submodule.subtype_apply, hnorm, hw _ h.1]
    constructor
    · intro hf q i
      apply (coeff_test_zero_iff27 hD (w q i) (p q) (h.2 q)).mp
      intro k
      exact congrFun (congrFun hf q) (i, k)
    · intro hf
      funext q ij
      exact (coeff_test_zero_iff27 hD (w q ij.1) (p q) (h.2 q)).mpr (hf q ij.1) ij.2
  have hdim : Module.finrank Geom E = poleDebit27 a := by
    unfold E poleDebit27
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range
      (fun q => (a.b + a.j - q) * gradeCount a q * (24401 + (a.b - q))) (a.b + 1)
  exact (codim_le_test_finrank _ _ f hker).trans hdim.le
theorem separable_rank27 (h3 : c3_27) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (V : Submodule Geom PhysicalRow) [hV : Module.Finite Geom V]
    (hcap : ∀ F ∈ V, Caps27 a F) (hsep : P.H.Separable) :
    codimIn V (poleCondition P L a (liftX P.H)) ≤ P.H.natDegree * poleDebit27 a := by
  classical
  let T : Finset Geom := ⟨P.H.roots, Polynomial.nodup_roots hsep⟩
  have hcard : T.card = P.H.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot (α : Geom) (hα : α ∈ T) : P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod : (∏ α ∈ T, localPole α) = liftX P.H := by
    have he : (∏ α ∈ T, (Polynomial.X - Polynomial.C α)) = P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _ = Polynomial.mapRingHom (algebraMap Geom GenericSeed) P.H
    rw [← he, map_prod]
    simp [localPole]
  let W : Geom → Submodule Geom PhysicalRow := fun α => poleCondition P L a (localPole α)
  have hlocal (α : Geom) (hα : α ∈ T) : codimIn V (W α) ≤ poleDebit27 a := by
    apply h3 Γ s P L a α V hV hcap (hroot α hα)
    exact hsep.eval₂_derivative_ne_zero (RingHom.id Geom) (hroot α hα)
  have hsub : T.inf W ≤ poleCondition P L a (liftX P.H) := by
    intro F hF
    have hd (α : Geom) (hα : α ∈ T) :
        (MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣ restore P L F := by
      have hle : T.inf W ≤ W α := Finset.inf_le hα
      exact (mem_poleCondition P L a _ _).mp (hle hF)
    have hcop (α β : Geom) (hne : α ≠ β) :
        IsCoprime ((MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j))
          ((MvPolynomial.C (localPole β) : RawRow) ^ (a.b + a.j)) := by
      apply IsCoprime.pow
      apply IsCoprime.map (f := MvPolynomial.C)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr ((FaithfulSMul.algebraMap_injective Geom GenericSeed).ne hne)).isUnit
    have h := Finset.prod_dvd_of_coprime (t := T) (fun α _ β _ hne => hcop α β hne) hd
    rw [Finset.prod_pow, ← map_prod (MvPolynomial.C : Polynomial GenericSeed →+* RawRow), hprod] at h
    exact (mem_poleCondition P L a _ _).mpr h
  have hdim := codim_finset_inf_le V T W (poleDebit27 a) hlocal
  rw [hcard] at hdim
  exact (codim_antitone V hsub).trans hdim
theorem pole_eq27 (b : Bank) : poleDebit27 b.box = 24401 * credit b.box.b + extra b.box.b := by
  have hb : b.box = ⟨b.box.b, 2300, 1150⟩ := by cases b <;> rfl
  have hgrade (q : ℕ) : gradeCount b.box q = gradeCount ⟨b.box.b, 2300, 1150⟩ q :=
    congrArg (fun a => gradeCount a q) hb
  calc
    _ = jetSum b.box.b (fun q _ _ => (2300 + (b.box.b - q)) * (24401 + (b.box.b - q))) := by
      rw [grade_sum, poleDebit27]
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      have he : b.box.b + b.box.j - q = 2300 + (b.box.b - q) := by
        rw [box_index]
        omega
      rw [hgrade, he]
      ring
    _ = _ := by
      simp only [credit, extra, moment, jetSum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      ring
end
end Low6969FatBank24000Seed
end

end Merged_R6960Low6969FatBank24000Seed

-- merged module R6960Low6969FatBank24000Banks
section Merged_R6960Low6969FatBank24000Banks

set_option Elab.async false
section
namespace Low6969FatBank24000Banks
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => Low6969FatBank24000.firstCut
  | .second => Low6969FatBank24000.secondCut
def targetRank : Bank → ℕ
  | .first => 1
  | .second => Low6969FatBank24000.bankRank
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end Low6969FatBank24000Banks
end
section
namespace Low6969FatBank24000Banks
open K1_13 (Geom)
open K1_13_4 K1_13_4_2
open K1_13_4_2_1 (jetSum)
open Function
open scoped BigOperators Polynomial
noncomputable section
open P0_9_4_1 (Column colExp colX column column_li coordinate coordinate_column column_bounds space space_bounds)
open P0_9_4_1 (exponent_none)
open Low6969FatBank24000 (Caps27)
private abbrev NewColumn (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 24401
private def offset (b : Bank) : ℕ := P0_9_4_1.cut b - cut b
private theorem cut_shift (b : Bank) : cut b + offset b = P0_9_4_1.cut b := by
  have h : cut b ≤ P0_9_4_1.cut b := by cases b <;> decide
  unfold offset
  omega
private theorem width_shift (b : Bank) (h q k l : ℕ) :
    width b h q k l + offset b = P0_9_4_1.width b h q k l := by
  have hc := cut_shift b
  have hl := cut_large b
  unfold width P0_9_4_1.width rawBase P0_9_4_1.rawBase
  omega
private def inOld (b : Bank) (h d : ℕ) (hd : d ≤ offset b) : NewColumn b h ↪ Column b h :=
  (Embedding.refl _).sigmaMap fun q =>
    (Embedding.refl _).sigmaMap fun k =>
      (Embedding.refl _).sigmaMap fun l =>
        ((Fin.addNatEmb d).trans (Fin.castLEEmb
          ((Nat.add_le_add_left hd _).trans_eq (width_shift b h q.val k.val l.val)))).prodMap
          (Fin.castLEEmb (by decide : 24401 ≤ 70001))
private abbrev base (b : Bank) (h : ℕ) := inOld b h 0 (Nat.zero_le _)
private def newSpace (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column ∘ base b h))
private theorem occurs {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ newSpace b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : NewColumn b h, colExp (base b h c) = e ∧ colX (base b h c) = x := by
  classical
  by_contra! hn
  have hle : newSpace b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column (base b h c)) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem seed_fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    seedDegree F ≤ 24400 := by
  unfold seedDegree
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  obtain ⟨c, hc, _⟩ := occurs hF (x := (F.coeff m).natDegree) (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp hm)
  rcases c with ⟨q,k,l,x,u⟩
  have hu := u.isLt
  have h0 : colExp (base b h ⟨q,k,l,x,u⟩) none = u.val := by
    simp only [colExp, exponent_none]
    rfl
  rw [← hc, h0]
  omega
private theorem fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    Caps27 b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F := by
  have hle : newSpace b h ≤ space b h := Submodule.span_mono (by
    rintro _ ⟨c, rfl⟩
    exact ⟨base b h c, rfl⟩)
  refine ⟨⟨(space_bounds b h F (hle hF)).1, seed_fits b h F hF⟩, ?_⟩
  intro e he
  obtain ⟨c, hc, hx⟩ := occurs hF (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp he)
  rcases c with ⟨q,k,l,x,u⟩
  let shifted := inOld b h (offset b) le_rfl ⟨q,k,l,x,u⟩
  have hw := (column_bounds shifted).2.2.2.2
  have he' : colExp shifted = e := hc
  have hx' : colX shifted = (F.coeff e).natDegree + offset b :=
    congrArg (· + offset b) hx
  rw [he', hx'] at hw
  have hs := cut_shift b
  omega
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps27 b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 24401 * jetSum b.box.b (width b h) := by
  refine ⟨newSpace b h, Module.Finite.span_of_finite _ (Set.finite_range _), fits b h, ?_⟩
  rw [newSpace, finrank_span_eq_card ((column_li b h).comp _ (base b h).injective)]
  simp only [NewColumn, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 24401]
  unfold jetSum
  simp only [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.sum_univ_eq_sum_range]
end
end Low6969FatBank24000Banks
end
section
namespace Low6969FatBank24000Banks
open K1_13_4_2 (Bank poleDebit)
open K1_13_4_2_1 (jetSum)
open Finset
open scoped BigOperators
open K1_13_4_2_1 (moment moment_eq slice antidifference credit extra pole_eq bank_moments)
private def rawVolume (b : Bank) : ℕ := moment b.box.b (rawBase b) 1 131071 0
private theorem volume_eq (b : Bank) (h : ℕ) :
    jetSum b.box.b (width b h) = rawVolume b + credit b.box.b * h := by
  simp only [width, rawVolume, moment, credit, jetSum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring
private theorem first_raw : rawVolume .first = 2816561543316172140 := by
  change moment 6789 4833164 1 131071 0 = _
  exact moment_eq 6789 4833164 1 131071 0 _ (by decide) (by decide +kernel)
private theorem second_raw : rawVolume .second = 2832901605560799359 := by
  change moment 6820 2929919 1 131071 0 = _
  exact moment_eq 6820 2929919 1 131071 0 _ (by decide) (by decide +kernel)
private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (24401 * b.nodeRank) + 2307 * extra b.box.b ≤
      24401 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 0x1cc973f372d9cdc := hfirst
    have ha : (1 : ℕ) + 262144 * (24401 * 0x9bab8f5dfb7) + 2307 * 0x1cc973f372d9cdc ≤
        24401 * 2816561543316172140 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (24401 * Bank.first.nodeRank) + 2307 * x ≤ 24401 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 0x1d32fca954a0ef7 := hsecond
    have ha : (1 : ℕ) + 262144 * (24401 * 0x9bac59312df) +
        2307 * 0x1d32fca954a0ef7 ≤ 24401 * 2832901605560799359 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (24401 * Bank.second.nodeRank) + 2307 * x ≤ 24401 * y)
      he second_raw).mpr ha
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2307) :
    targetRank b + 262144 * (24401 * b.nodeRank) + h * Low6969FatBank24000Seed.poleDebit27 b.box ≤
      24401 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [Low6969FatBank24000Seed.pole_eq27, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (24401 * credit b.box.b) = 24401 * (credit b.box.b * h) := by ring
  omega
end Low6969FatBank24000Banks
end
section
namespace Low6969FatBank24000Banks
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open Low6969FatBank24000 (Caps27)
open scoped Polynomial BigOperators
open K1_13_4_2 (codim_inf_le codim_finset_inf_le separable_rank dimension_of_debits)
private theorem simple_pole_bound : Low6969FatBank24000Seed.c3_27 :=
  Low6969FatBank24000Seed.simple_pole27 Low6969FatBank24000Seed.proof27
private theorem deformation_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof
private theorem rank_of_bounds (b : Bank) (w : I → K) {Γ s}
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2307) :
    Low6969FatBank24000.HasRank27 w P L b.box (cut b) (targetRank b) := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := (budget b P.H.natDegree hh).trans_eq hdimV.symm
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps27 b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (24401 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 24401 * b.nodeRank :=
      Low6969FatBank24000Seed.contact_bound27 b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (24401 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * Low6969FatBank24000Seed.poleDebit27 b.box := by
    apply deformation_bound Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact Low6969FatBank24000Seed.separable_rank27 simple_pole_bound P' L' b.box V hcap hsep
  have hdebit := (codim_inf_le V U W).trans (Nat.add_le_add hU hW)
  let S : Submodule Geom PhysicalRow := V ⊓ (U ⊓ W)
  have hdim : targetRank b ≤ Module.finrank Geom S := dimension_of_debits hsize hdebit
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Geom) (M := ↥S) hdim
  let e : Fin (targetRank b) → PhysicalRow := fun i => (f i).val
  refine ⟨e, hf.map_injOn S.subtype Subtype.val_injective.injOn, ?_⟩
  intro i
  have hm := Submodule.mem_inf.mp (f i).property
  have hUW : e i ∈ U ⊓ W := hm.2
  have hb := hbox (e i) hm.1
  refine ⟨⟨hb.1.1, hb.2, ?_, (mem_poleCondition P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩, hb.1.2⟩
  intro j
  have hmem : e i ∈ A j := (Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (mem_contactAt (embed (node j)) (embed (w j)) (e i)).mp hmem
theorem proof : Low6969FatBank24000.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩
end
end Low6969FatBank24000Banks
end


end Merged_R6960Low6969FatBank24000Banks
end Z6969Source2277

-- Source: ProximityPrize.SubmissionLower.Low6969FatBank32000
section Z6969Source2278
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969FatBank32000Defs
section Merged_R6960Low6969FatBank32000Defs

set_option Elab.async false
section
namespace Low6969FatBank32000
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 3975818
abbrev secondOrder : ℕ := 1815862
abbrev firstCut : ℕ := 5000 * 179730 - firstOrder
abbrev secondCut : ℕ := 5000 * 179730 - secondOrder
abbrev bankRank : ℕ := 701329375673955677026






/-- The low fat chain works with rows whose seed degree is at most 32,000. -/
abbrev seedCap : ℕ := 35200
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
open K1_13 (PoleData)
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2307 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
end
end Low6969FatBank32000
end
end Merged_R6960Low6969FatBank32000Defs

-- merged module R6960Low6969FatBank32000Seed
section Merged_R6960Low6969FatBank32000Seed
set_option Elab.async false
section
namespace Low6969FatBank32000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open MvPolynomial
open Low6969FatBank32000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (seedView seedCoeff flatCoeff coeff_mem_capped normalize normalize_mem_capped node_coeff toRow contactWeight_eq)
private theorem seedCoeff_eq_zero27 {F : PhysicalRow} (hS : seedDegree F ≤ 35200)
    {n : ℕ} (hn : 35200 < n) : seedCoeff n F = 0 := by
  have hdeg : (seedView F).natDegree ≤ 35200 := by
    simpa only [seedView, natDegree_optionEquivLeft, seedDegree] using hS
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn)
private theorem mem_contact_of_origin_eq_zero27 {x v : Geom} {F : PhysicalRow}
    (hS : seedDegree F ≤ 35200)
    (h : ∀ n : Fin 35201, origin (normalize x v (flatCoeff n F)) = 0) :
    F ∈ contactAt x v := by
  apply (mem_contactAt x v F).mpr
  intro e
  let P := (backwardShift x v F).coeff (e.some.optionElim (e none))
  let E := Polynomial.taylorEquiv x
  have hE : E ((Polynomial.X - Polynomial.C x) ^ (5000 - 3 * e (some 0))) =
      Polynomial.X ^ (5000 - 3 * e (some 0)) := by
    have hX : E (Polynomial.X - Polynomial.C x) = Polynomial.X := by
      rw [map_sub]
      change Polynomial.taylor x Polynomial.X - Polynomial.taylor x (Polynomial.C x) = _
      simp
    rw [map_pow, hX]
  have hP : P = (backwardShift x v F).coeff e := by simp [P]
  rw [← hP, ← map_dvd_iff E, hE, Polynomial.X_pow_dvd_iff]
  intro i hi
  have hcoeff : E P =
      (toRow (shear (normalize x v (flatCoeff (e none) F)))).coeff e.some :=
    (node_coeff x v F (e none) e.some).symm
  rw [hcoeff]
  change ((optionEquivRight Geom (Fin 3) _).coeff e.some).coeff i = 0
  rw [optionEquivRight_coeff_coeff]
  by_cases hn : e none < 35201
  · have hz := congrArg (fun Q : Flat => Q.coeff (e.some.optionElim i)) (h ⟨e none, hn⟩)
    change (weightedTruncation contactWeight 5000
      (shear (normalize x v (flatCoeff (e none) F)))).coeff (e.some.optionElim i) = 0 at hz
    have hlt : (e.some.optionElim i).weight contactWeight < 5000 := by
      rw [contactWeight_eq]
      change i + 3 * e (some 0) < 5000
      omega
    rw [coeff_weightedTruncation] at hz
    simpa only [hlt, ite_true] using hz
  · have hz := seedCoeff_eq_zero27 hS (n := e none) (by omega)
    have hz' : flatCoeff (e none) F = 0 := by
      change toRow.symm (seedCoeff (e none) F) = 0
      rw [hz, map_zero]
    simp [hz']
private def nodeInput (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) (n : Fin 35201) : V →ₗ[Geom] Capped b.box.b :=
  ((normalize x v).toLinearMap ∘ₗ flatCoeff n ∘ₗ V.subtype).codRestrict _
    (fun F => normalize_mem_capped (coeff_mem_capped (hcap F F.2).1 n) x v)
private def nodeMap (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    (hcap : ∀ F ∈ V, Caps27 b.box F) : V →ₗ[Geom] (Fin 35201 → cappedRange b.box.b) :=
  LinearMap.pi fun n =>
    (origin.domRestrict (Capped b.box.b)).rangeRestrict ∘ₗ nodeInput b x v V hcap n
theorem codim_le_cappedRange27 (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (hcap : ∀ F ∈ V, Caps27 b.box F) :
    codimIn V (contactAt x v) ≤ 35201 * Module.finrank Geom (cappedRange b.box.b) := by
  let A := nodeMap b x v V hcap
  have hzero (F : A.ker) : (F.1 : PhysicalRow) ∈ contactAt x v := by
    apply mem_contact_of_origin_eq_zero27 (hcap F.1 F.1.2).2
    intro n
    have h := congrFun (LinearMap.mem_ker.mp F.2) n
    have hval := congrArg (fun z : cappedRange b.box.b => z.val) h
    change origin (normalize x v (flatCoeff n F.1.1)) = 0 at hval
    exact hval
  let f : A.ker →ₗ[Geom] ↥(V ⊓ contactAt x v) :=
    (V.subtype ∘ₗ A.ker.subtype).codRestrict _ fun F => Submodule.mem_inf.mpr ⟨F.1.2, hzero F⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun s : ↥(V ⊓ contactAt x v) => (s : PhysicalRow)) h
    exact he
  have hk := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hr := Submodule.finrank_le A.range
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr
  have hnull := LinearMap.finrank_range_add_finrank_ker (K := Geom)
    (V := ↥V) (V₂ := Fin 35201 → cappedRange b.box.b) A
  unfold codimIn
  omega
end
end Low6969FatBank32000Seed
end
section
namespace Low6969FatBank32000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_2
open Low6969FatBank32000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_2 (bank_bound plane_rank_le)
theorem contact_bound27 : ∀ (b : Bank) (x v : Geom) (V : Submodule Geom PhysicalRow),
    Module.Finite Geom V → (∀ F ∈ V, Caps27 b.box F) →
    codimIn V (contactAt x v) ≤ 35201 * b.nodeRank := by
  intro b x v V hV hcap
  let : Module.Finite Geom V := hV
  obtain ⟨p, hp⟩ := bank_bound K1_13_4_2_2_3.proof K1_13_4_2_2_4.proof
    K1_13_4_2_2_5.proof K1_13_4_2_2_6.proof b
  apply (codim_le_cappedRange27 b x v V hcap).trans
  apply Nat.mul_le_mul_left
  apply (cappedRange_le_sum b.box.b (fun q k => blockBound q (offset k) (p q k)) ?_).trans hp
  intro q hq k hk
  have hB : b.box.b + 1 ≤ 6821 := by cases b <;> decide
  exact (rank_originBlock_le_plane q k).trans
    (plane_rank_le K1_13_4_2_2_1.proof K1_13_4_2_2_2.proof (hq.trans_le hB) hk (p q k))
end
end Low6969FatBank32000Seed
end
section
namespace Low6969FatBank32000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3
open Low6969FatBank32000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone dimension_of_debits)
def poleDebit27 (a : Shape) : ℕ :=
  ∑ q ∈ Finset.range (a.b + 1),
    (a.b + a.j - q) * gradeCount a q * (35201 + (a.b - q))
abbrev SeedCoeff27 (a : Shape) (q : ℕ) := Fin (35201 + (a.b - q))
def c2_27 : Prop :=
  ∀ (a : Shape) (α : Geom) (N D : (Polynomial Geom)), D ≠ 0 →
    N.natDegree ≤ 1 → D.natDegree ≤ 1 →
    let z₀ : GenericSeed := algebraMap (Polynomial Geom) GenericSeed N / algebraMap (Polynomial Geom) GenericSeed D
    ∃ p : ∀ q : Fin (a.b + 1), PhysicalRow →ₗ[Geom] (JetCoeff a q.val → (Polynomial Geom)),
      ∀ F : PhysicalRow, Caps27 a F →
        (∀ e ∈ (centered z₀ F).support, admissible a e) ∧
        ∀ (q : Fin (a.b + 1)) (c : JetCoeff a q.val),
          (p q F c).natDegree ≤ 35200 + (a.b - q.val) ∧
          algebraMap (Polynomial Geom) GenericSeed (p q F c) =
            (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q.val) *
              localCoeff a α q.val c (centered z₀ F)
end
end Low6969FatBank32000Seed
end
section
namespace Low6969FatBank32000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_3_2
open Low6969FatBank32000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3_2 (cleared cleared_apply clearedFactor support_bounds grade_sub centered_admissible map_cleared seedMap grade)
private theorem cleared_degree27 {a : Shape} {α : Geom} {N D : (Polynomial Geom)}
    (hN : N.natDegree ≤ 1) (hD : D.natDegree ≤ 1) {F : PhysicalRow} (hF : Caps27 a F)
    (q : Fin (a.b + 1)) (c : JetCoeff a q.val) :
    (cleared a α N D q F c).natDegree ≤ 35200 + (a.b - q.val) := by
  classical
  rw [cleared_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  split
  next he =>
    apply (Polynomial.natDegree_smul_le _ _).trans
    obtain ⟨hB, _, _, _⟩ := support_bounds hF.1 hm
    have hU : m none ≤ 35200 :=
      (MvPolynomial.le_degreeOf_of_mem_support none hm).trans hF.2
    have hq := grade_sub hB (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
    have hn : (N ^ (m (some 0) - k)).natDegree ≤ m (some 0) - k :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hN)
    have hd : (D ^ (a.b - grade m)).natDegree ≤ a.b - grade m :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hD)
    calc
      _ ≤ (m none + (m (some 0) - k)) + (a.b - grade m) := by
        unfold clearedFactor
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hd
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hn
        exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
      _ ≤ _ := by omega
  next => simp
theorem proof27 : c2_27 := by
  intro a α N D hD hNdeg hDdeg
  have hD' : seedMap D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)).2 hD
  refine ⟨cleared a α N D, fun F hF => ⟨centered_admissible _ hF.1, ?_⟩⟩
  intro q c
  exact ⟨cleared_degree27 hNdeg hDdeg hF q c, map_cleared hD' hF.1 q c⟩
end
end Low6969FatBank32000Seed
end
section
namespace Low6969FatBank32000Seed
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_3 K1_13_4_2_1 Finset
open Low6969FatBank32000 (Caps27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open K1_13_4_2_3 (clearedTest clearedTest_apply codim_le_test_finrank)
open K1_13_4_2 (codim_inf_le codim_finset_inf_le codim_antitone)
open K1_13_4_2_1 (credit extra grade_sum moment)
def c3_27 : Prop :=
  ∀ (Γ : Finset K) (s : K → (Polynomial K)) (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (α : Geom) (V : Submodule Geom PhysicalRow), Module.Finite Geom V →
    (∀ F ∈ V, Caps27 a F) → P.H.IsRoot α → P.H.derivative.eval α ≠ 0 →
    codimIn V (poleCondition P L a (localPole α)) ≤ poleDebit27 a
private theorem coeff_test_zero_iff27 {a : Shape} {q : ℕ} {α : Geom}
    {F : PhysicalRow} {G : RawRow} {D : (Polynomial Geom)} (hD : D ≠ 0)
    (w : JetCoeff a q → Geom) (p : PhysicalRow →ₗ[Geom] (JetCoeff a q → (Polynomial Geom)))
    (hp : ∀ c, (p F c).natDegree ≤ 35200 + (a.b - q) ∧
      algebraMap (Polynomial Geom) GenericSeed (p F c) =
        (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * localCoeff a α q c G) :
    (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔ dot a α q w G = 0 := by
  have hdeg : (clearedTest w p F).natDegree ≤ 35200 + (a.b - q) := by
    rw [clearedTest_apply]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ =>
      (Polynomial.natDegree_smul_le _ _).trans (hp c).1
  have hz : (∀ k : SeedCoeff27 a q, (clearedTest w p F).coeff k.val = 0) ↔
      clearedTest w p F = 0 := by
    refine ⟨fun h => Polynomial.ext fun n => ?_, by intro h k; rw [h, Polynomial.coeff_zero]⟩
    rw [Polynomial.coeff_zero]
    by_cases hn : n < 35201 + (a.b - q)
    · exact h ⟨n, hn⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hmap : algebraMap (Polynomial Geom) GenericSeed (clearedTest w p F) =
      (algebraMap (Polynomial Geom) GenericSeed D) ^ (a.b - q) * dot a α q w G := by
    rw [clearedTest_apply, dot, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_def, map_mul, (hp c).2, IsScalarTower.algebraMap_apply Geom (Polynomial Geom) GenericSeed]
    ring
  rw [hz, ← (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)), hmap]
  have hne : algebraMap (Polynomial Geom) GenericSeed D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericSeed)).2 hD
  simp [pow_ne_zero _ hne]
theorem simple_pole27 (h2 : c2_27) : c3_27 := by
  classical
  intro Γ s P L a α V hV hcap hroot hsimple
  obtain ⟨N, D, hD, hNdeg, hDdeg, hnorm⟩ := normalization P L α hroot hsimple
  obtain ⟨w, hw⟩ := K1_13_4_2_3_1.proof a α
  obtain ⟨p, hp⟩ := h2 a α N D hD hNdeg hDdeg
  let E := ∀ q : Fin (a.b + 1), (Test a q.val × SeedCoeff27 a q.val) → Geom
  let f : V →ₗ[Geom] E :=
    LinearMap.pi fun q => LinearMap.pi fun ij =>
      (Polynomial.lcoeff Geom ij.2.val).comp ((clearedTest (w q ij.1) (p q)).comp V.subtype)
  have hker : LinearMap.ker f = (poleCondition P L a (localPole α)).comap V.subtype := by
    ext F
    have h := hp F.val (hcap F.val F.property)
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    simp only [Submodule.subtype_apply, hnorm, hw _ h.1]
    constructor
    · intro hf q i
      apply (coeff_test_zero_iff27 hD (w q i) (p q) (h.2 q)).mp
      intro k
      exact congrFun (congrFun hf q) (i, k)
    · intro hf
      funext q ij
      exact (coeff_test_zero_iff27 hD (w q ij.1) (p q) (h.2 q)).mpr (hf q ij.1) ij.2
  have hdim : Module.finrank Geom E = poleDebit27 a := by
    unfold E poleDebit27
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range
      (fun q => (a.b + a.j - q) * gradeCount a q * (35201 + (a.b - q))) (a.b + 1)
  exact (codim_le_test_finrank _ _ f hker).trans hdim.le
theorem separable_rank27 (h3 : c3_27) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (V : Submodule Geom PhysicalRow) [hV : Module.Finite Geom V]
    (hcap : ∀ F ∈ V, Caps27 a F) (hsep : P.H.Separable) :
    codimIn V (poleCondition P L a (liftX P.H)) ≤ P.H.natDegree * poleDebit27 a := by
  classical
  let T : Finset Geom := ⟨P.H.roots, Polynomial.nodup_roots hsep⟩
  have hcard : T.card = P.H.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot (α : Geom) (hα : α ∈ T) : P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod : (∏ α ∈ T, localPole α) = liftX P.H := by
    have he : (∏ α ∈ T, (Polynomial.X - Polynomial.C α)) = P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _ = Polynomial.mapRingHom (algebraMap Geom GenericSeed) P.H
    rw [← he, map_prod]
    simp [localPole]
  let W : Geom → Submodule Geom PhysicalRow := fun α => poleCondition P L a (localPole α)
  have hlocal (α : Geom) (hα : α ∈ T) : codimIn V (W α) ≤ poleDebit27 a := by
    apply h3 Γ s P L a α V hV hcap (hroot α hα)
    exact hsep.eval₂_derivative_ne_zero (RingHom.id Geom) (hroot α hα)
  have hsub : T.inf W ≤ poleCondition P L a (liftX P.H) := by
    intro F hF
    have hd (α : Geom) (hα : α ∈ T) :
        (MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣ restore P L F := by
      have hle : T.inf W ≤ W α := Finset.inf_le hα
      exact (mem_poleCondition P L a _ _).mp (hle hF)
    have hcop (α β : Geom) (hne : α ≠ β) :
        IsCoprime ((MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j))
          ((MvPolynomial.C (localPole β) : RawRow) ^ (a.b + a.j)) := by
      apply IsCoprime.pow
      apply IsCoprime.map (f := MvPolynomial.C)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr ((FaithfulSMul.algebraMap_injective Geom GenericSeed).ne hne)).isUnit
    have h := Finset.prod_dvd_of_coprime (t := T) (fun α _ β _ hne => hcop α β hne) hd
    rw [Finset.prod_pow, ← map_prod (MvPolynomial.C : Polynomial GenericSeed →+* RawRow), hprod] at h
    exact (mem_poleCondition P L a _ _).mpr h
  have hdim := codim_finset_inf_le V T W (poleDebit27 a) hlocal
  rw [hcard] at hdim
  exact (codim_antitone V hsub).trans hdim
theorem pole_eq27 (b : Bank) : poleDebit27 b.box = 35201 * credit b.box.b + extra b.box.b := by
  have hb : b.box = ⟨b.box.b, 2300, 1150⟩ := by cases b <;> rfl
  have hgrade (q : ℕ) : gradeCount b.box q = gradeCount ⟨b.box.b, 2300, 1150⟩ q :=
    congrArg (fun a => gradeCount a q) hb
  calc
    _ = jetSum b.box.b (fun q _ _ => (2300 + (b.box.b - q)) * (35201 + (b.box.b - q))) := by
      rw [grade_sum, poleDebit27]
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      have he : b.box.b + b.box.j - q = 2300 + (b.box.b - q) := by
        rw [box_index]
        omega
      rw [hgrade, he]
      ring
    _ = _ := by
      simp only [credit, extra, moment, jetSum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      ring
end
end Low6969FatBank32000Seed
end

end Merged_R6960Low6969FatBank32000Seed

-- merged module R6960Low6969FatBank32000Banks
section Merged_R6960Low6969FatBank32000Banks

set_option Elab.async false
section
namespace Low6969FatBank32000Banks
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => Low6969FatBank32000.firstCut
  | .second => Low6969FatBank32000.secondCut
def targetRank : Bank → ℕ
  | .first => 1
  | .second => Low6969FatBank32000.bankRank
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end Low6969FatBank32000Banks
end
section
namespace Low6969FatBank32000Banks
open K1_13 (Geom)
open K1_13_4 K1_13_4_2
open K1_13_4_2_1 (jetSum)
open Function
open scoped BigOperators Polynomial
noncomputable section
open P0_9_4_1 (Column colExp colX column column_li coordinate coordinate_column column_bounds space space_bounds)
open P0_9_4_1 (exponent_none)
open Low6969FatBank32000 (Caps27)
private abbrev NewColumn (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 35201
private def offset (b : Bank) : ℕ := P0_9_4_1.cut b - cut b
private theorem cut_shift (b : Bank) : cut b + offset b = P0_9_4_1.cut b := by
  have h : cut b ≤ P0_9_4_1.cut b := by cases b <;> decide
  unfold offset
  omega
private theorem width_shift (b : Bank) (h q k l : ℕ) :
    width b h q k l + offset b = P0_9_4_1.width b h q k l := by
  have hc := cut_shift b
  have hl := cut_large b
  unfold width P0_9_4_1.width rawBase P0_9_4_1.rawBase
  omega
private def inOld (b : Bank) (h d : ℕ) (hd : d ≤ offset b) : NewColumn b h ↪ Column b h :=
  (Embedding.refl _).sigmaMap fun q =>
    (Embedding.refl _).sigmaMap fun k =>
      (Embedding.refl _).sigmaMap fun l =>
        ((Fin.addNatEmb d).trans (Fin.castLEEmb
          ((Nat.add_le_add_left hd _).trans_eq (width_shift b h q.val k.val l.val)))).prodMap
          (Fin.castLEEmb (by decide : 35201 ≤ 70001))
private abbrev base (b : Bank) (h : ℕ) := inOld b h 0 (Nat.zero_le _)
private def newSpace (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column ∘ base b h))
private theorem occurs {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ newSpace b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : NewColumn b h, colExp (base b h c) = e ∧ colX (base b h c) = x := by
  classical
  by_contra! hn
  have hle : newSpace b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column (base b h c)) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem seed_fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    seedDegree F ≤ 35200 := by
  unfold seedDegree
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  obtain ⟨c, hc, _⟩ := occurs hF (x := (F.coeff m).natDegree) (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp hm)
  rcases c with ⟨q,k,l,x,u⟩
  have hu := u.isLt
  have h0 : colExp (base b h ⟨q,k,l,x,u⟩) none = u.val := by
    simp only [colExp, exponent_none]
    rfl
  rw [← hc, h0]
  omega
private theorem fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    Caps27 b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F := by
  have hle : newSpace b h ≤ space b h := Submodule.span_mono (by
    rintro _ ⟨c, rfl⟩
    exact ⟨base b h c, rfl⟩)
  refine ⟨⟨(space_bounds b h F (hle hF)).1, seed_fits b h F hF⟩, ?_⟩
  intro e he
  obtain ⟨c, hc, hx⟩ := occurs hF (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp he)
  rcases c with ⟨q,k,l,x,u⟩
  let shifted := inOld b h (offset b) le_rfl ⟨q,k,l,x,u⟩
  have hw := (column_bounds shifted).2.2.2.2
  have he' : colExp shifted = e := hc
  have hx' : colX shifted = (F.coeff e).natDegree + offset b :=
    congrArg (· + offset b) hx
  rw [he', hx'] at hw
  have hs := cut_shift b
  omega
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps27 b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 35201 * jetSum b.box.b (width b h) := by
  refine ⟨newSpace b h, Module.Finite.span_of_finite _ (Set.finite_range _), fits b h, ?_⟩
  rw [newSpace, finrank_span_eq_card ((column_li b h).comp _ (base b h).injective)]
  simp only [NewColumn, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 35201]
  unfold jetSum
  simp only [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.sum_univ_eq_sum_range]
end
end Low6969FatBank32000Banks
end
section
namespace Low6969FatBank32000Banks
open K1_13_4_2 (Bank poleDebit)
open K1_13_4_2_1 (jetSum)
open Finset
open scoped BigOperators
open K1_13_4_2_1 (moment moment_eq slice antidifference credit extra pole_eq bank_moments)
private def rawVolume (b : Bank) : ℕ := moment b.box.b (rawBase b) 1 131071 0
private theorem volume_eq (b : Bank) (h : ℕ) :
    jetSum b.box.b (width b h) = rawVolume b + credit b.box.b * h := by
  simp only [width, rawVolume, moment, credit, jetSum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring
private theorem first_raw : rawVolume .first = 2816561543316172140 := by
  change moment 6789 4833164 1 131071 0 = _
  exact moment_eq 6789 4833164 1 131071 0 _ (by decide) (by decide +kernel)
private theorem second_raw : rawVolume .second = 2832901605560799359 := by
  change moment 6820 2929919 1 131071 0 = _
  exact moment_eq 6820 2929919 1 131071 0 _ (by decide) (by decide +kernel)
private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (35201 * b.nodeRank) + 2307 * extra b.box.b ≤
      35201 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 0x1cc973f372d9cdc := hfirst
    have ha : (1 : ℕ) + 262144 * (35201 * 0x9bab8f5dfb7) + 2307 * 0x1cc973f372d9cdc ≤
        35201 * 2816561543316172140 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (35201 * Bank.first.nodeRank) + 2307 * x ≤ 35201 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 0x1d32fca954a0ef7 := hsecond
    have ha : (701329375673955677026 : ℕ) + 262144 * (35201 * 0x9bac59312df) +
        2307 * 0x1d32fca954a0ef7 ≤ 35201 * 2832901605560799359 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (35201 * Bank.second.nodeRank) + 2307 * x ≤ 35201 * y)
      he second_raw).mpr ha
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2307) :
    targetRank b + 262144 * (35201 * b.nodeRank) + h * Low6969FatBank32000Seed.poleDebit27 b.box ≤
      35201 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [Low6969FatBank32000Seed.pole_eq27, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (35201 * credit b.box.b) = 35201 * (credit b.box.b * h) := by ring
  omega
end Low6969FatBank32000Banks
end
section
namespace Low6969FatBank32000Banks
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open Low6969FatBank32000 (Caps27)
open scoped Polynomial BigOperators
open K1_13_4_2 (codim_inf_le codim_finset_inf_le separable_rank dimension_of_debits)
private theorem simple_pole_bound : Low6969FatBank32000Seed.c3_27 :=
  Low6969FatBank32000Seed.simple_pole27 Low6969FatBank32000Seed.proof27
private theorem deformation_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof
private theorem rank_of_bounds (b : Bank) (w : I → K) {Γ s}
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2307) :
    Low6969FatBank32000.HasRank27 w P L b.box (cut b) (targetRank b) := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := (budget b P.H.natDegree hh).trans_eq hdimV.symm
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps27 b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (35201 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 35201 * b.nodeRank :=
      Low6969FatBank32000Seed.contact_bound27 b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (35201 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * Low6969FatBank32000Seed.poleDebit27 b.box := by
    apply deformation_bound Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact Low6969FatBank32000Seed.separable_rank27 simple_pole_bound P' L' b.box V hcap hsep
  have hdebit := (codim_inf_le V U W).trans (Nat.add_le_add hU hW)
  let S : Submodule Geom PhysicalRow := V ⊓ (U ⊓ W)
  have hdim : targetRank b ≤ Module.finrank Geom S := dimension_of_debits hsize hdebit
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Geom) (M := ↥S) hdim
  let e : Fin (targetRank b) → PhysicalRow := fun i => (f i).val
  refine ⟨e, hf.map_injOn S.subtype Subtype.val_injective.injOn, ?_⟩
  intro i
  have hm := Submodule.mem_inf.mp (f i).property
  have hUW : e i ∈ U ⊓ W := hm.2
  have hb := hbox (e i) hm.1
  refine ⟨⟨hb.1.1, hb.2, ?_, (mem_poleCondition P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩, hb.1.2⟩
  intro j
  have hmem : e i ∈ A j := (Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (mem_contactAt (embed (node j)) (embed (w j)) (e i)).mp hmem
theorem proof : Low6969FatBank32000.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩
end
end Low6969FatBank32000Banks
end


end Merged_R6960Low6969FatBank32000Banks
end Z6969Source2278

-- Source: ProximityPrize.SubmissionLower.Low6969FatFactors
section Z6969Source2279
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969FatBanks
section Merged_Low6969FatBanks

namespace Low6969FatBanks
theorem proof : Low6969Fat.c1 := by
  intro w Γ s P L h
  exact ⟨(Low6969FatBank24000Banks.proof w Γ s P L h).1,
    (Low6969FatBank32000Banks.proof w Γ s P L h).2⟩
end Low6969FatBanks

end Merged_Low6969FatBanks

-- merged module Low6969FatFactors
section Merged_Low6969FatFactors

-- merged module R6960Low6969FatSlots
section Merged_R6960Low6969FatSlots

set_option Elab.async false
/-! Low-specific copies of the seed-cap dependent slot count of `Fast050` (K1_13_4_4),
at seed degree at most 27,000, i.e. 27,001 seed slots. -/
section
namespace Low6969FatSlots
noncomputable section
open K1 K1_13 K1_13_4
open K1_13_4_4 (capSpace mem_capSpace toGeneric_caps toGeneric_injective)
open Low6969Fat (Caps27 Source27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 1024
open K1_13_4_4 (Exponent slotExponent sum_value_choices sum_index_choices sum_odds rank_le_coeffs sum_squares)
def topSlots (a : ℕ) : ℕ := 35201 * 5671 * (1151 - a)^2
def capSpace27 (a : Shape) : Submodule GenericX GenericRow :=
  capSpace a ⊓
  MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) (Low6969Fat.seedCap a)
theorem mem_capSpace27 {a : Shape} {F : GenericRow} : F ∈ capSpace27 a ↔ Caps27 a F := by
  classical
  simp only [capSpace27, Submodule.mem_inf, mem_capSpace,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, Caps27, Low6969Fat.seedCap, seedDegree]
theorem seedDegree_toGeneric (F : PhysicalRow) : seedDegree (toGeneric F) = seedDegree F := by
  have hs : (toGeneric F).support = F.support :=
    MvPolynomial.support_map_of_injective F (IsFractionRing.injective (Polynomial Geom) GenericX)
  simp only [seedDegree, MvPolynomial.degreeOf_eq_sup, hs]
theorem toGeneric_caps27 {a : Shape} {F : PhysicalRow} (h : Caps27 a F) :
    Caps27 a (toGeneric F) :=
  ⟨toGeneric_caps h.1, by rw [seedDegree_toGeneric]; exact h.2⟩
def layerSpan {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) : Submodule GenericX GenericRow :=
  Submodule.span GenericX {R | ∃ F, Source27 w P L secondBox t F ∧ toGeneric F = R}
theorem layerSpan_caps {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {t : ℕ} {F : GenericRow} (hF : F ∈ layerSpan w P L t) : Caps27 secondBox F := by
  apply mem_capSpace27.mp
  apply (Submodule.span_le.mpr ?_) hF
  rintro _ ⟨Q, hQ, rfl⟩
  exact mem_capSpace27.mpr (toGeneric_caps27 ⟨hQ.1.1, hQ.2⟩)
private def slotTuples (a : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Ico a 1151).biUnion (fun k =>
    (Finset.range (2301 - 2*k)).biUnion (fun j =>
      (Finset.range (6821 - k - j)).biUnion (fun i =>
        (Finset.range 35201).image (fun z => (k, j, i, z)))))
private theorem tuples_card (a : ℕ) : (slotTuples a).card ≤ topSlots a := by
  unfold slotTuples
  calc
    _ ≤ ∑ k ∈ Finset.Ico a 1151, ∑ j ∈ Finset.range (2301 - 2*k),
        ∑ _ ∈ Finset.range (6821 - k - j), 35201 := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = topSlots a := by
      unfold topSlots
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      calc
        _ = ∑ k ∈ Finset.Ico a 1151, (35201 * 5671) * (2301 - 2*k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ 1150 := by have h := (Finset.mem_Ico.mp hk).2; omega
          rw [← Finset.sum_mul, sum_value_choices hk']
          ring
        _ = _ := by rw [← Finset.mul_sum, sum_index_choices]
private theorem exponent_mem {a : ℕ} {R : GenericRow} (hR : Caps27 secondBox R)
    {m : Exponent} (hm : m ∈ R.support) (ha : a ≤ m (some 2)) :
    m ∈ (slotTuples a).image slotExponent := by
  classical
  have ht := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 (fun _ => 1)) hm).trans hR.1.1
  have hj := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 Fin.val) hm).trans hR.1.2.1
  have hz := (MvPolynomial.le_degreeOf_of_mem_support (none : SeedVar) hm).trans hR.2
  have hk := (MvPolynomial.le_degreeOf_of_mem_support (some 2 : SeedVar) hm).trans hR.1.2.2.1
  have htotal : m (some 0) + m (some 1) + m (some 2) ≤ 6820 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.add_assoc] using ht
  have hindex : m (some 1) + 2 * m (some 2) ≤ 2300 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.mul_comm] using hj
  change m (some 2) ≤ 1150 at hk
  change m none ≤ 35200 at hz
  refine Finset.mem_image.mpr ⟨(m (some 2), m (some 1), m (some 0), m none), ?_, ?_⟩
  · simp only [slotTuples, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_range,
      Finset.mem_image]
    exact ⟨m (some 2), ⟨ha, by omega⟩, m (some 1), by omega, m (some 0), by omega,
      m none, by omega, rfl⟩
  · ext i
    cases i with
    | none => simp [slotExponent]
    | some i => fin_cases i <;> simp [slotExponent]
theorem count_symbols (a r : ℕ) (e : Fin r → GenericRow) (he : LinearIndependent GenericX e)
    (h : ∀ R ∈ Submodule.span GenericX (Set.range e),
      Caps27 secondBox R ∧ (R ≠ 0 → a ≤ R.degreeOf (some 2))) :
    r ≤ topSlots a := by
  have hc := rank_le_coeffs ((slotTuples a).image slotExponent) e he (by
    intro R hR hn
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u => u (some 2))
    have hdeg := (h R hR).2 hn
    rw [MvPolynomial.degreeOf_eq_sup, hmax] at hdeg
    exact ⟨m, exponent_mem (h R hR).1 hm hdeg, MvPolynomial.mem_support_iff.mp hm⟩)
  exact hc.trans (Finset.card_image_le.trans (tuples_card a))
theorem count_layer {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {a r t : ℕ}
    (hb : ∃ e : Fin r → GenericRow, LinearIndependent GenericX e ∧
      ∀ i, e i ∈ layerSpan w P L t)
    (hdeg : ∀ R ∈ layerSpan w P L t, R ≠ 0 → a ≤ R.degreeOf (some 2)) :
    r ≤ topSlots a := by
  obtain ⟨e, he, hs⟩ := hb
  have hspan : Submodule.span GenericX (Set.range e) ≤ layerSpan w P L t :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hs i)
  exact count_symbols a r e he (fun R hR => ⟨layerSpan_caps (hspan hR), hdeg R (hspan hR)⟩)
theorem slot_sum : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) = 101333532101424025 := by
  have hs : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) =
      (35201 * 5671) * ∑ k ∈ Finset.range 1150, (1150 - k)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hk : 1151 - (1 + k) = 1150 - k := by omega
    rw [topSlots, hk]
  rw [hs]
  have hsquare : (∑ k ∈ Finset.range 1150, (1150 - k)^2) = 507619775 := by
    have h := sum_squares 1150
    omega
  rw [hsquare]
end
end Low6969FatSlots
end

end Merged_R6960Low6969FatSlots

-- merged module R6960Low6969FatFactors
section Merged_R6960Low6969FatFactors

set_option Elab.async false
section
namespace Low6969FatFactors
noncomputable section
open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4_1 (Exponent polePower weight)
open K1_13_4 (SeedVar seedDegree)
open Low6969Fat (secondCut bankRank)
open scoped BigOperators
open K1_13_4_4_1 (bank bankEval mem_bank kernel_le boundary below_boundary independent_generic)
open K1_13_4_4_1 (endpoint)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def seedSpace : Submodule Geom PhysicalRow :=
  (MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 35200).restrictScalars Geom
theorem mem_seedSpace {F : PhysicalRow} : F ∈ seedSpace ↔ seedDegree F ≤ 35200 := by
  simp only [seedSpace, Submodule.restrictScalars_mem,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, seedDegree]
private def bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Submodule Geom PhysicalRow := bank w P L t ⊓ seedSpace
private theorem mem_bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) (F : PhysicalRow) : F ∈ bank27 w P L t ↔ Low6969Fat.Source27 w P L secondBox t F := by
  rw [bank27, Submodule.mem_inf, mem_bank, mem_seedSpace]
  rfl
private instance finite27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.Finite Geom (bank27 w P L t) :=
  Submodule.finiteDimensional_of_le (inf_le_left : bank27 w P L t ≤ bank w P L t)
private def bankEval27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    bank27 w P L t →ₗ[Geom] (K1_13_4_4_1.Exponent → Geom) :=
  (boundary P.H.natDegree t).comp (bank27 w P L t).subtype
private theorem kernel_le27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.finrank Geom (bankEval27 w P L (t + 1)).ker ≤
      Module.finrank Geom (bank27 w P L t) := by
  let f := (bank27 w P L (t + 1)).subtype.comp (bankEval27 w P L (t + 1)).ker.subtype
  have hm (F : (bankEval27 w P L (t + 1)).ker) : f F ∈ bank27 w P L t := by
    obtain ⟨⟨hc, hcut, hphys, hpole⟩, hseed⟩ := (mem_bank27 w P L _ _).mp F.val.property
    have hz : boundary P.H.natDegree (t + 1) F.val.val = 0 := LinearMap.mem_ker.mp F.property
    apply (mem_bank27 w P L _ _).mpr
    refine ⟨⟨hc, fun m hm => ?_, hphys, hpole⟩, hseed⟩
    have h := below_boundary hcut hz m hm
    change ((F.val.val).coeff m).natDegree + weight P.H.natDegree m ≤ t + polePower * P.H.natDegree
    omega
  apply LinearMap.finrank_le_finrank_of_injective (f := f.codRestrict _ hm)
  intro F G he
  have heq := congrArg (fun Q : bank27 w P L t => Q.val) he
  exact Subtype.ext (Subtype.ext heq)
theorem telescope (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) (P : PoleData Γ s)
    (L : ResidueChart P) (hr : Low6969Fat.HasRank27 w P L secondBox secondCut bankRank) :
    ∃ r : ℕ → ℕ, bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t ∧
      ∀ t ≤ secondCut, ∃ e : Fin (r t) → GenericRow,
        LinearIndependent GenericX e ∧ ∀ i, e i ∈ Low6969FatSlots.layerSpan w P L t := by
  classical
  let r (t : ℕ) := Module.finrank Geom (bankEval27 w P L t).range
  refine ⟨r, ?_, fun t _ => ?_⟩
  · have hzero : (bankEval27 w P L 0).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro F hz
      have hsrc := ((mem_bank27 w P L _ _).mp F.property).1
      refine Subtype.ext (K1_13_4_4_1.endpoint Γ s P L F.val (fun m hm => ?_) hsrc.2.2.2)
      simpa only [Nat.zero_add] using below_boundary hsrc.2.1 hz m hm
    have hsum (t : ℕ) : Module.finrank Geom (bank27 w P L t) ≤
        ∑ v ∈ Finset.range (t + 1), r v := by
      induction t with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank27 w P L 0) (V₂ := Exponent → Geom) (bankEval27 w P L 0)
        rw [hzero, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.ge
      | succ t ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank27 w P L (t + 1)) (V₂ := Exponent → Geom) (bankEval27 w P L (t + 1))
        rw [Finset.sum_range_succ, ← h, add_comm]
        exact Nat.add_le_add (le_trans (kernel_le27 w P L t) ih) le_rfl
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom
        (fun i => (⟨e i, (mem_bank27 w P L _ _).mpr (hmem i)⟩ : bank27 w P L secondCut)) :=
      LinearIndependent.of_comp (bank27 w P L secondCut).subtype he
    exact (by simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank :
      bankRank ≤ Module.finrank Geom (bank27 w P L secondCut)).trans (hsum secondCut)
  · let b := Module.finBasis Geom (bankEval27 w P L t).range
    choose e he using fun i : Fin (r t) => LinearMap.mem_range.mp (b i).property
    have hsrc (i : Fin (r t)) : Low6969Fat.Source27 w P L secondBox t (e i).val :=
      (mem_bank27 w P L _ _).mp (e i).property
    refine ⟨fun i => toGeneric (e i).val,
      independent_generic (fun i => (e i).val) (fun i => (hsrc i).1.2.1) ?_,
      fun i => Submodule.subset_span ⟨(e i).val, hsrc i, rfl⟩⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (bankEval27 w P L t).range.subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => boundary P.H.natDegree t (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Low6969FatFactors
end
section
namespace Low6969FatFactors
noncomputable section
open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps cutoff_sum_le)
open Low6969FatSlots (topSlots)
open Low6969Fat (mixedWeight secondCut bankRank)
open scoped Polynomial BigOperators
open K1_13_4_4_2 (line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree)
def reserveCost (moving : Bool) : ℕ := if moving then 6921 else 48661
def layerPower (e t : ℕ) : ℕ := 1 + (secondCut - t) / e
private theorem choose_coordinate {moving : Bool} {A : Finset GenericRow}
    (hA : FactorsFor moving A) {F f : GenericRow} (hF : F ≠ 0) (hcap : Caps secondBox F)
    (hf : f ∈ A) (hd : f ∣ F) :
    ∃ i : SeedVar, (∀ n, mixedWeight (Finsupp.single i n) = n * reserveCost moving) ∧
      ¬ f ∣ (line i f).coeff 1 := by
  classical
  cases moving with
  | false =>
    obtain ⟨j, hj⟩ := positive_jet_degree (hA.jets f hf)
    have hjet : jetTotal f ≤ 6820 :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd _ hd hF).trans hcap.1
    have hdeg : f.degreeOf (some j) ≤ jetTotal f :=
      MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i : SeedVar => i.elim 0 (fun _ => 1)) (some j) Nat.one_pos f
    refine ⟨some j, ?_, transverse hj (hdeg.trans_lt (hjet.trans_lt (by decide)))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
  | true =>
    have hs : 0 < seedDegree f := hA.seed f hf
    have hdeg : seedDegree f ≤ 70000 := by
      simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
        (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hd hF).trans
          (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hcap.2.2.2)
    refine ⟨none, ?_, transverse hs (hdeg.trans_lt (by decide))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
theorem factor_power (moving : Bool) (A : Finset GenericRow) (F : PhysicalRow) (t : ℕ)
    (hA : FactorsFor moving A) (hcap : Caps secondBox F) (ht : t ≤ secondCut)
    (htest : ∀ f ∈ A, ∀ a, t + mixedWeight a ≤ secondCut → f ∣ toGeneric (mixedHasse a F)) :
    factorProduct A ^ layerPower (reserveCost moving) t ∣ toGeneric F := by
  classical
  by_cases hF : toGeneric F = 0
  · rw [hF]
    exact dvd_zero _
  unfold factorProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hfg
    refine IsRelPrime.pow ((hA.irreducible f hf).isRelPrime_iff_not_dvd.mpr ?_)
    intro hd
    exact hA.different hf hg hfg ((hA.irreducible f hf).associated_of_dvd (hA.irreducible g hg) hd)
  · intro f hf
    have hdiv : f ∣ toGeneric F := by
      simpa [mixedWeight, mixedHasse_zero] using htest f hf 0 (by simpa [mixedWeight] using ht)
    obtain ⟨i, hi, hsep⟩ := choose_coordinate hA hF (toGeneric_caps hcap) hf hdiv
    apply pow_dvd_of_coeff (line i) (line_zero i)
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hA.irreducible f hf)) hsep
    intro a ha
    rw [line_toGeneric]
    apply htest f hf
    rw [hi]
    have ha' : a ≤ (secondCut - t) / reserveCost moving := by
      unfold layerPower at ha
      omega
    have hm := (Nat.mul_le_mul_right (reserveCost moving) ha').trans
      (Nat.div_mul_le_self (secondCut - t) (reserveCost moving))
    omega
set_option maxRecDepth 1024
theorem top_exclusion (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 6921 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 6921)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  rw [Low6969FatSlots.slot_sum] at hb
  exact (not_le_of_gt (by decide : 6921 * 101333532101424025 < bankRank)) (hr.trans hb)
end
end Low6969FatFactors
end
section
namespace Low6969FatQuotient
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut
open K1_13_4_4 (Exponent slotExponent rank_le_coeffs multiples mem_multiples weighted_pow)
open Low6969Fat (Caps27 secondCut bankRank)
open Low6969FatSlots (layerSpan layerSpan_caps)
open Low6969FatFactors (layerPower)
open MvPolynomial
open scoped BigOperators

@[irreducible] def tuples (b j k u : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (1151-k)).biUnion (fun a =>
    (Finset.range (2301-j-2*a)).biUnion (fun q =>
      (Finset.range (6821-b-a-q)).biUnion (fun i =>
        (Finset.range (35201-u)).image (fun z => (a,q,i,z)))))

private theorem exponent_mem {b j k u : ℕ} {m : Exponent}
    (hB : b + (m (some 0) + m (some 1) + m (some 2)) ≤ 6820)
    (hJ : j + (m (some 1) + 2 * m (some 2)) ≤ 2300)
    (hT : k + m (some 2) ≤ 1150)
    (hU : u + m none ≤ 35200) :
    m ∈ (tuples b j k u).image slotExponent := by
  refine Finset.mem_image.mpr ⟨(m (some 2), m (some 1), m (some 0), m none), ?_, ?_⟩
  · simp only [tuples, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    exact ⟨m (some 2), by omega, m (some 1), by omega, m (some 0), by omega, m none, by omega, rfl⟩
  · ext i
    cases i with
    | none => simp [slotExponent]
    | some i => fin_cases i <;> simp [slotExponent]

private theorem quotient_degree (v : SeedVar → ℕ) {D Q : GenericRow}
    (hD : D ≠ 0) (hQ : Q ≠ 0) (n : ℕ) :
    (D^n*Q).weightedTotalDegree v = n * D.weightedTotalDegree v + Q.weightedTotalDegree v := by
  rw [weightedTotalDegree_mul v _ _ (pow_ne_zero n hD) hQ, weighted_pow _ _ hD]

private theorem quotient_caps {D Q : GenericRow} (hD : D ≠ 0) (hQ : Q ≠ 0)
    {n : ℕ} (hc : Caps27 secondBox (D^n*Q)) :
    n * jetTotal D + jetTotal Q ≤ 6820 ∧
    n * jetIndex D + jetIndex Q ≤ 2300 ∧
    n * D.degreeOf (some 2) + Q.degreeOf (some 2) ≤ 1150 ∧
    n * seedDegree D + seedDegree Q ≤ 35200 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [secondBox, jetTotal, quotient_degree _ hD hQ] using hc.1.1
  · simpa only [secondBox, jetIndex, quotient_degree _ hD hQ] using hc.1.2.1
  · let v : SeedVar → ℕ := Pi.single (some 2) 1
    have eq := quotient_degree v hD hQ n
    simp only [v, weightedTotalDegree_piSingle] at eq
    rw [← eq]
    exact hc.1.2.2.1
  · let v : SeedVar → ℕ := Pi.single none 1
    have eq := quotient_degree v hD hQ n
    simp only [v, weightedTotalDegree_piSingle] at eq
    unfold seedDegree
    rw [← eq]
    exact hc.2

private theorem exponent_caps {Q : GenericRow} {m : Exponent} (hm : m ∈ Q.support) :
    m (some 0) + m (some 1) + m (some 2) ≤ jetTotal Q ∧
    m (some 1) + 2 * m (some 2) ≤ jetIndex Q ∧
    m (some 2) ≤ Q.degreeOf (some 2) ∧ m none ≤ seedDegree Q := by
  refine ⟨?_, ?_, le_degreeOf_of_mem_support _ hm, le_degreeOf_of_mem_support _ hm⟩
  · simpa [jetTotal, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, Nat.add_assoc, Nat.nsmul_eq_mul, Nat.mul_one, Nat.mul_zero] using
        (le_weightedTotalDegree (fun i : SeedVar => i.elim (0 : ℕ) (fun _ => 1)) hm)
  · simpa [jetIndex, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, Nat.nsmul_eq_mul, Nat.mul_comm] using
        (le_weightedTotalDegree (fun i : SeedVar => i.elim 0 Fin.val) hm)

private theorem independent_quotients {V : Submodule GenericX GenericRow} {r : ℕ}
    {f : GenericRow}
    (hb : ∃ u : Fin r → GenericRow, LinearIndependent GenericX u ∧ ∀ i, u i ∈ V)
    (hdvd : V ≤ multiples f) :
    ∃ q : Fin r → GenericRow, LinearIndependent GenericX q ∧
      ∀ Q ∈ Submodule.span GenericX (Set.range q), f * Q ∈ V := by
  obtain ⟨u, hu, hs⟩ := hb
  choose q hq using fun i => mem_multiples.mp (hdvd (hs i))
  let mul := LinearMap.mulLeft GenericX f
  have hmul : mul ∘ q = u := funext (fun i => (hq i).symm)
  have hspan : Submodule.span GenericX (Set.range q) ≤ V.comap mul := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f * q i ∈ V
    rw [← hq i]
    exact hs i
  exact ⟨q, LinearIndependent.of_comp mul (hmul.symm ▸ hu), fun _ hQ => hspan hQ⟩

@[irreducible] def axisBox : Finset (ℕ × ℕ × ℕ × ℕ) := tuples 0 0 0 0

private theorem coord_disjoint {α β : Type*} [DecidableEq β]
    {S : Finset α} {A : α → Finset β} (coord : β → α)
    (h : ∀ a ∈ S, ∀ b ∈ A a, coord b = a) :
    (↑S : Set α).PairwiseDisjoint A := by
  intro i hi j hj neq
  apply Finset.disjoint_left.mpr
  intro b bi bj
  exact neq ((h i hi b bi).symm.trans (h j hj b bj))

theorem sum_axisBox (F : (ℕ × ℕ × ℕ × ℕ) → ℕ) :
    ∑ x ∈ axisBox, F x =
      ∑ k ∈ Finset.range 1151, ∑ j ∈ Finset.range (2301-2*k),
        ∑ i ∈ Finset.range (6821-k-j), ∑ z ∈ Finset.range 35201, F (k,j,i,z) := by
  classical
  simp only [axisBox, tuples, Nat.sub_zero]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_image (fun a _ b _ h => congrArg (fun x => x.2.2.2) h)
      · apply coord_disjoint (fun x => x.2.2.1)
        intro i _ x hx
        obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
        rfl
    · apply coord_disjoint (fun x => x.2.1)
      intro j _ x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
      rfl
  · apply coord_disjoint Prod.fst
    intro k _ x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
    rfl

def axisWeight (v : SeedVar → ℕ) (x : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  Finsupp.weight v (slotExponent x)

def totalAxis : SeedVar → ℕ := fun i => i.elim 0 (fun _ => 1)
def indexAxis : SeedVar → ℕ := fun i => i.elim 0 Fin.val
def seedAxis : SeedVar → ℕ := Pi.single none 1

theorem total_axisWeight (x : ℕ × ℕ × ℕ × ℕ) :
    axisWeight totalAxis x = x.2.2.1 + x.2.1 + x.1 := by
  simp [axisWeight, totalAxis, slotExponent, Finsupp.weight_apply, Finsupp.sum_fintype,
    Fintype.sum_option, Fin.sum_univ_succ, Nat.add_assoc]

theorem index_axisWeight (x : ℕ × ℕ × ℕ × ℕ) :
    axisWeight indexAxis x = x.2.1 + 2 * x.1 := by
  simp [axisWeight, indexAxis, slotExponent, Finsupp.weight_apply, Finsupp.sum_fintype,
    Fintype.sum_option, Fin.sum_univ_succ, Nat.mul_comm]

theorem seed_axisWeight (x : ℕ × ℕ × ℕ × ℕ) :
    axisWeight seedAxis x = x.2.2.2 := by
  simp [axisWeight, seedAxis, slotExponent, Finsupp.weight_apply, Finsupp.sum_fintype,
    Fintype.sum_option]

private theorem axisBox_mem {m : Exponent}
    (hB : m (some 0) + m (some 1) + m (some 2) ≤ 6820)
    (hJ : m (some 1) + 2 * m (some 2) ≤ 2300)
    (hT : m (some 2) ≤ 1150) (hU : m none ≤ 35200) :
    m ∈ axisBox.image slotExponent := by
  unfold axisBox
  exact exponent_mem (b := 0) (j := 0) (k := 0) (u := 0) (m := m)
    (by simpa only [Nat.zero_add] using hB) (by simpa only [Nat.zero_add] using hJ)
    (by simpa only [Nat.zero_add] using hT) (by simpa only [Nat.zero_add] using hU)

theorem axis_rank {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {t r n : ℕ} {D : GenericRow} (hD : D ≠ 0)
    (hb : ∃ u : Fin r → GenericRow, LinearIndependent GenericX u ∧
      ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : layerSpan w P L t ≤ multiples (D ^ n))
    (v : SeedVar → ℕ) (V : ℕ)
    (fit : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
    r ≤ (axisBox.filter (fun x => n * D.weightedTotalDegree v + axisWeight v x ≤ V)).card := by
  classical
  obtain ⟨q, hli, hmap⟩ := independent_quotients hb hdvd
  let good := axisBox.filter (fun x => n * D.weightedTotalDegree v + axisWeight v x ≤ V)
  apply (rank_le_coeffs (good.image slotExponent) q hli ?_).trans Finset.card_image_le
  intro Q hQ hn
  obtain ⟨m, hm⟩ := support_nonempty.mpr hn
  have hcap := layerSpan_caps (hmap Q hQ)
  have ⟨Qb, Qj, Qk, Qu⟩ := quotient_caps hD hn hcap
  have ⟨mb, mj, mk, mu⟩ := exponent_caps hm
  have hbase : m ∈ axisBox.image slotExponent :=
    axisBox_mem (m := m)
      (mb.trans ((Nat.le_add_left _ _).trans Qb))
      (mj.trans ((Nat.le_add_left _ _).trans Qj))
      (mk.trans ((Nat.le_add_left _ _).trans Qk))
      (mu.trans ((Nat.le_add_left _ _).trans Qu))
  have hweight := fit _ hcap
  rw [quotient_degree v hD hn n] at hweight
  have hmq := le_weightedTotalDegree v hm
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hbase
  have hgood : x ∈ good :=
    Finset.mem_filter.mpr ⟨hx, (Nat.add_le_add_left hmq _).trans hweight⟩
  have inImage : slotExponent x ∈ good.image slotExponent :=
    Finset.mem_image_of_mem slotExponent hgood
  exact ⟨slotExponent x, inImage, mem_support_iff.mp hm⟩

end
end Low6969FatQuotient

namespace Low6969FatQuotient
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut
open K1_13_4_4 (multiples cutoff_sum_le)
open Low6969Fat (Caps27 secondCut bankRank)
open Low6969FatSlots (layerSpan)
open Low6969FatFactors (layerPower)
open scoped BigOperators

private theorem filter_tail {ι : Type*} (sites : Finset ι) (w : ι → ℕ)
    {cap d k : ℕ} (hd : 0 < d) (hk : cap/d ≤ k) :
    (sites.filter (fun x => (k+1)*d + w x ≤ cap)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have fit := (Finset.mem_filter.mp hx).2
  have hlt : cap/d < k+1 := by omega
  have above : cap < (k+1)*d := (Nat.div_lt_iff_lt_mul hd).mp hlt
  omega

theorem axis_resource {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {e : ℕ} (he : 0 < e) {r : ℕ → ℕ} {D : GenericRow} (hD : D ≠ 0)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow, LinearIndependent GenericX u ∧
      ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : ∀ t ≤ secondCut, layerSpan w P L t ≤ multiples (D ^ layerPower e t))
    (v : SeedVar → ℕ) (V : ℕ)
    (hcap : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
    bankRank * D.weightedTotalDegree v ≤ e * ∑ x ∈ axisBox, (V - axisWeight v x) := by
  classical
  let d := D.weightedTotalDegree v
  change bankRank * d ≤ _
  by_cases hdZero : d = 0
  · simp [hdZero]
  have positive : 0 < d := Nat.pos_of_ne_zero hdZero
  let q (k : ℕ) := (axisBox.filter (fun x => (k+1)*d + axisWeight v x ≤ V)).card
  have qtail (k : ℕ) (hk : V/d ≤ k) : q k = 0 :=
    filter_tail axisBox (axisWeight v) positive hk
  have fits : bankRank ≤ e * ∑ k ∈ Finset.range (V/d), q k := by
    apply hr.trans
    apply cutoff_sum_le (W := secondCut) (n := V/d) he r q _ qtail
    intro t ht
    simpa only [q, d, layerPower, Nat.add_comm 1] using
      axis_rank hD (hb t ht) (hdvd t ht) v V hcap
  exact R6970LayerMass.degree_budget axisBox (axisWeight v) V d (V/d) e bankRank fits

end
end Low6969FatQuotient
end
section
namespace Low6969FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open Low6969Fat (CommonPair Caps27)
open scoped Polynomial BigOperators
open K1_13_4_4 (pureEval pureEval_section pure_degree_le caps_of_dvd)
private theorem seed_of_dvd {F Q : GenericRow} {cap : ℕ} (hF : F ≠ 0) (hs : seedDegree F ≤ cap)
    (hQ : Q ∣ F) : seedDegree Q ≤ cap := by
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hQ hF).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
theorem factor_pair27
    (F G : GenericRow) (hF : F ≠ 0) (hG : G ≠ 0)
    (hFCap : Caps27 firstBox F) (hGCap : Caps27 secondBox G)
    (hfixed : ∀ A, FactorsFor false A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 52 ∧ jetIndex (factorProduct A) ≤ 14)
    (hmoving : ∀ A, FactorsFor true A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 7 ∧ jetIndex (factorProduct A) ≤ 2 ∧
      seedDegree (factorProduct A) ≤ 45 ∧ ∀ f ∈ A, f.degreeOf (some 2) = 0) :
    Nonempty (CommonPair F G) := by
  classical
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : GCDMonoid GenericRow := UniqueFactorizationMonoid.toGCDMonoid GenericRow
  let g := gcd F G
  have hg : g ≠ 0 := gcd_ne_zero_of_left hF
  let N := UniqueFactorizationMonoid.normalizedFactors g
  let A := N.toFinset
  let pureFactors := A.filter (fun f => jetTotal f = 0)
  let jetFactors := A.filter (fun f => ¬ jetTotal f = 0)
  let fixed := jetFactors.filter (fun f => seedDegree f = 0)
  let moving := jetFactors.filter (fun f => ¬ seedDegree f = 0)
  let powCount : GenericRow → ℕ := N.count
  let pure : (Polynomial GenericX) := ∏ f ∈ pureFactors, (pureEval f) ^ powCount f
  have hpure : pureSeed pure = ∏ f ∈ pureFactors, f ^ powCount f := by
    let φ : (Polynomial GenericX) →+* GenericRow :=
      Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none)
    change φ (∏ f ∈ pureFactors, (pureEval f) ^ powCount f) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun f hf => ?_
    rw [map_pow]
    exact congrArg (fun R => R ^ powCount f)
      (pureEval_section (Finset.mem_filter.mp hf).2)
  let D := pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) * (∏ f ∈ moving, f ^ powCount f)
  have hD : Associated D g := by
    suffices D = N.prod by
      rw [this]
      exact UniqueFactorizationMonoid.prod_normalizedFactors hg
    change pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) *
      (∏ f ∈ moving, f ^ powCount f) = _
    rw [hpure, mul_assoc]
    unfold fixed moving
    rw [Finset.prod_filter_mul_prod_filter_not]
    unfold pureFactors jetFactors
    rw [Finset.prod_filter_mul_prod_filter_not]
    exact (Finset.prod_multiset_count N).symm
  have hDne : D ≠ 0 := ne_zero_of_dvd_ne_zero hg hD.dvd
  have hDF : D ∣ F := hD.dvd.trans (gcd_dvd_left F G)
  have hDG : D ∣ G := hD.dvd.trans (gcd_dvd_right F G)
  obtain ⟨F', hF'⟩ := hDF
  obtain ⟨G', hG'⟩ := hDG
  have hl : F' ≠ 0 := right_ne_zero_of_mul (hF' ▸ hF)
  have hr : G' ≠ 0 := right_ne_zero_of_mul (hG' ▸ hG)
  have hrel : IsRelPrime F' G' := by
    intro d hdF hdG
    have hdF' : D * d ∣ F := hF' ▸ mul_dvd_mul_left D hdF
    have hdG' : D * d ∣ G := hG' ▸ mul_dvd_mul_left D hdG
    have hd := (dvd_gcd hdF' hdG').trans hD.symm.dvd
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left hDne).mp (by simpa only [mul_one] using hd)
  have hcommon (f : GenericRow) (hf : f ∈ A) : f ∣ F ∧ f ∣ G := by
    have hfg : f ∣ g := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hf)
    exact ⟨hfg.trans (gcd_dvd_left F G), hfg.trans (gcd_dvd_right F G)⟩
  have hmake (b : Bool) (B : Finset GenericRow) (hBA : B ⊆ A)
      (hj : ∀ f ∈ B, 0 < jetTotal f)
      (hs : ∀ f ∈ B, if b then 0 < seedDegree f else seedDegree f = 0) :
      FactorsFor b B := by
    refine ⟨?_, ?_, hj, hs⟩
    · intro f hf q hq hne hassoc
      exact hne (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
        (Multiset.mem_toFinset.mp (hBA hf)) (Multiset.mem_toFinset.mp (hBA hq)) hassoc)
    · intro f hf
      exact UniqueFactorizationMonoid.irreducible_of_normalized_factor _
        (Multiset.mem_toFinset.mp (hBA hf))
  have hfixedA : fixed ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmovingA : moving ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hfix := hmake false fixed hfixedA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => (Finset.mem_filter.mp hf).2)
  have hmov := hmake true moving hmovingA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp hf).2)
  obtain ⟨hft, hfi⟩ := hfixed fixed hfix (fun f hf => hcommon f (hfixedA hf))
  obtain ⟨hmt, hmi, hms, hlow⟩ := hmoving moving hmov (fun f hf => hcommon f (hmovingA hf))
  have hpureF : pureSeed pure ∣ F :=
    (show pureSeed pure ∣ D by
      exact ⟨_, mul_assoc _ _ _⟩).trans ⟨F', hF'⟩
  have hpure_ne : pure ≠ 0 := by
    intro hz
    apply hDne
    simp [D, hz, pureSeed]
  refine ⟨{
    fixed := fixed
    moving := moving
    pure := pure
    exponent := powCount
    left := F'
    right := G'
    pure_ne := hpure_ne
    pure_degree := (pure_degree_le hF hpureF).trans (hFCap.2.trans (by decide))
    fixed_kind := fun f hf => ⟨hfix.irreducible f hf, hfix.jets f hf, hfix.seed f hf⟩
    moving_kind := fun f hf => ⟨hmov.irreducible f hf, hmov.jets f hf, hmov.seed f hf, hlow f hf⟩
    fixed_total := hft
    fixed_index := hfi
    moving_total := hmt
    moving_index := hmi
    moving_seed := hms
    left_eq := hF'
    right_eq := hG'
    left_ne := hl
    right_ne := hr
    proper := hrel
    left_caps := ⟨caps_of_dvd hF hFCap.1 ⟨D, hF'.trans (mul_comm _ _)⟩, seed_of_dvd hF hFCap.2 ⟨D, hF'.trans (mul_comm _ _)⟩⟩
    right_caps := ⟨caps_of_dvd hG hGCap.1 ⟨D, hG'.trans (mul_comm _ _)⟩, seed_of_dvd hG hGCap.2 ⟨D, hG'.trans (mul_comm _ _)⟩⟩
  }⟩
end
end Low6969FatFactors
end
section
namespace Low6969FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps)
open Low6969FatSlots (topSlots layerSpan layerSpan_caps count_layer capSpace27 mem_capSpace27
  toGeneric_caps27)
open Low6969Fat (Caps27 HasRank27)
open Low6969Fat (Necessary mixedWeight secondCut bankRank)
open scoped BigOperators
open K1_13_4_4 (multiples mem_multiples weighted_pow)
set_option maxRecDepth 1024
private theorem mixedHasse_seed27 (a : SeedVar →₀ ℕ) (F : PhysicalRow)
    (hs : seedDegree F ≤ 35200) : seedDegree (mixedHasse a F) ≤ 35200 := by
  classical
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (K1_13_4_4.mixedHasse_weightedDegree_le (Pi.single (none : SeedVar) 1) a F).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
private theorem has_nonzero_necessary {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} (hr : HasRank27 w P L secondBox secondCut bankRank) :
    ∃ G : Necessary w P L, G ≠ 0 := by
  obtain ⟨e, he, hs⟩ := hr
  let i : Fin bankRank := ⟨0, by decide⟩
  have hmem : e i ∈ Necessary w P L := by
    apply Submodule.subset_span
    exact ⟨secondCut, e i, 0, hs i, by simp [mixedWeight], (mixedHasse_zero _).symm⟩
  refine ⟨⟨e i, hmem⟩, fun h => he.ne_zero i ?_⟩
  exact congrArg (fun Q : Necessary w P L => Q.val) h
private theorem necessary_caps {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {Q : PhysicalRow} (hQ : Q ∈ Necessary w P L) :
    Caps27 secondBox (toGeneric Q) := by
  have hle : Necessary w P L ≤ ((capSpace27 secondBox).restrictScalars Geom).comap rowMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, F, a, hF, _, rfl⟩
    exact mem_capSpace27.mpr (toGeneric_caps27 ⟨mixedHasse_caps a F hF.1.1, mixedHasse_seed27 a F hF.2⟩)
  exact mem_capSpace27.mp (hle hQ)
private theorem select_row {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {F : PhysicalRow} (hF : F ≠ 0) (hr : HasRank27 w P L secondBox secondCut bankRank) :
    ∃ G, G ∈ Necessary w P L ∧ G ≠ 0 ∧
      ∀ f : GenericRow, Irreducible f → f ∣ toGeneric F → f ∣ toGeneric G →
        ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q := by
  classical
  let N := Necessary w P L
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let bad := (UniqueFactorizationMonoid.normalizedFactors (toGeneric F)).toFinset.filter
    (fun f => ∃ Q ∈ N, ¬ f ∣ toGeneric Q)
  let sub : Option ↥bad → Submodule Geom N
    | none => ⊥
    | some f => ((multiples f.val).restrictScalars Geom).comap (rowMap.comp N.subtype)
  have hproper (i : Option ↥bad) : sub i ≠ ⊤ := by
    cases i with
    | none =>
      obtain ⟨Q, hQ⟩ := has_nonzero_necessary hr
      intro h
      have hm : Q ∈ sub none := h ▸ Submodule.mem_top
      exact hQ ((Submodule.mem_bot Geom).mp hm)
    | some f =>
      obtain ⟨Q, hQ, hnd⟩ := (Finset.mem_filter.mp f.property).2
      intro h
      have hm : (⟨Q, hQ⟩ : N) ∈ sub (some f) := h ▸ Submodule.mem_top
      exact hnd (mem_multiples.mp hm)
  obtain ⟨G, hG⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option ↥bad) (K := Geom) (M := N) sub hproper
  refine ⟨G.val, G.property, ?_, fun f hf hdf hdg Q hQ => ?_⟩
  · intro h
    exact hG none ((Submodule.mem_bot Geom).mpr (Subtype.ext h))
  · by_contra hn
    obtain ⟨p, hp, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (toGeneric_ne_zero hF) hf hdf
    have hp' : p ∈ bad := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hp, Q, hQ, fun h => hn (hassoc.dvd_iff_dvd_left.mpr h)⟩
    exact hG (some ⟨p, hp'⟩) (mem_multiples.mpr (hassoc.dvd_iff_dvd_left.mp hdg))
private theorem layer_divides {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A)
    (hcommon : ∀ f ∈ A, ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q)
    {t : ℕ} (ht : t ≤ secondCut) :
    layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower (reserveCost moving) t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F, hF, rfl⟩
  apply mem_multiples.mpr (factor_power moving A F t hA hF.1.1 ht ?_)
  intro f hf a ha
  exact hcommon f hf _ (Submodule.subset_span ⟨t, F, a, hF, ha, rfl⟩)
private theorem product_ne_zero {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A) :
    factorProduct A ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun f hf => (hA.irreducible f hf).ne_zero
private theorem excludes_top {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {r : ℕ → ℕ} {A : Finset GenericRow} (hA : FactorsFor true A)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow,
      LinearIndependent GenericX u ∧ ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : ∀ t ≤ secondCut,
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 6921 t)) :
    ∀ f ∈ A, f.degreeOf (some 2) = 0 := by
  classical
  let v : SeedVar → ℕ := Pi.single (some 2) 1
  have hzero : (factorProduct A).weightedTotalDegree v = 0 := by
    by_contra hn
    apply top_exclusion r hr
    intro t ht
    apply count_layer (hb t ht)
    intro R hR hRne
    have h := MvPolynomial.weightedTotalDegree_le_of_dvd v
      (mem_multiples.mp (hdvd t ht hR)) hRne
    rw [weighted_pow _ _ (product_ne_zero hA)] at h
    have hle := Nat.mul_le_mul_left (layerPower 6921 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h
private theorem total_room :
    (∑ x ∈ Low6969FatQuotient.axisBox,
      (6820 - Low6969FatQuotient.axisWeight Low6969FatQuotient.totalAxis x)) =
      35201 * 21445461275685 := by
  rw [Low6969FatQuotient.sum_axisBox]
  simp only [Low6969FatQuotient.total_axisWeight, R6970FatMoments2297.with_seed,
    R6970FatMoments2297.total_room]

private theorem index_room :
    (∑ x ∈ Low6969FatQuotient.axisBox,
      (2300 - Low6969FatQuotient.axisWeight Low6969FatQuotient.indexAxis x)) =
      35201 * 6053692758425 := by
  rw [Low6969FatQuotient.sum_axisBox]
  simp only [Low6969FatQuotient.index_axisWeight, R6970FatMoments2297.with_seed,
    R6970FatMoments2297.index_room]

private theorem seed_room :
    (∑ x ∈ Low6969FatQuotient.axisBox,
      (35200 - Low6969FatQuotient.axisWeight Low6969FatQuotient.seedAxis x)) =
      4654552825571809600 := by
  rw [Low6969FatQuotient.sum_axisBox]
  simpa only [Low6969FatQuotient.seed_axisWeight, R6970FatMoments.sumJets]
    using R6970FatMoments2297.seed_room

theorem proof : Low6969Fat.c2 := by
  classical
  intro w Γ s P L F hF hFCaps hRank
  obtain ⟨r, hr, hb⟩ := telescope w Γ s P L hRank
  obtain ⟨G, hG, hGne, hchoose⟩ := select_row hF hRank
  have hdiv (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G) :
      ∀ t ≤ secondCut, layerSpan w P L t ≤
        multiples (factorProduct A ^ layerPower (reserveCost moving) t) :=
    fun _ ht => layer_divides hA
      (fun f hf => hchoose f (hA.irreducible f hf) (hcomm f hf).1 (hcomm f hf).2) ht
  have hbound (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G)
      (v : SeedVar → ℕ) (V : ℕ)
      (hc : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
      bankRank * (factorProduct A).weightedTotalDegree v ≤
        reserveCost moving * ∑ x ∈ Low6969FatQuotient.axisBox,
          (V - Low6969FatQuotient.axisWeight v x) :=
    Low6969FatQuotient.axis_resource (by cases moving <;> decide) (product_ne_zero hA) hr hb
      (hdiv moving A hA hcomm) v V hc
  have hbcap (R : GenericRow) (h : Caps27 secondBox R) :
      R.weightedTotalDegree Low6969FatQuotient.totalAxis ≤ 6820 := h.1.1
  have hjcap (R : GenericRow) (h : Caps27 secondBox R) :
      R.weightedTotalDegree Low6969FatQuotient.indexAxis ≤ 2300 := h.1.2.1
  have hscap (R : GenericRow) (h : Caps27 secondBox R) :
      R.weightedTotalDegree Low6969FatQuotient.seedAxis ≤ 35200 := by
    rw [Low6969FatQuotient.seedAxis, MvPolynomial.weightedTotalDegree_piSingle]
    exact h.2
  refine ⟨G, hG, factor_pair27 _ _ (toGeneric_ne_zero hF) (toGeneric_ne_zero hGne)
    (toGeneric_caps27 hFCaps) (necessary_caps hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt := hbound false A hA hcomm _ _ hbcap
    have hji := hbound false A hA hcomm _ _ hjcap
    rw [total_room] at hbt
    rw [index_room] at hji
    change bankRank * jetTotal (factorProduct A) ≤ 48661 * (35201 * 21445461275685) at hbt
    change bankRank * jetIndex (factorProduct A) ≤ 48661 * (35201 * 6053692758425) at hji
    norm_num [Low6969Fat.bankRank] at hbt hji
    exact ⟨by omega, by omega⟩
  · intro A hA hcomm
    have hbt := hbound true A hA hcomm _ _ hbcap
    have hji := hbound true A hA hcomm _ _ hjcap
    have hse := hbound true A hA hcomm _ _ hscap
    rw [total_room] at hbt
    rw [index_room] at hji
    rw [seed_room, Low6969FatQuotient.seedAxis, MvPolynomial.weightedTotalDegree_piSingle] at hse
    change bankRank * jetTotal (factorProduct A) ≤ 6921 * (35201 * 21445461275685) at hbt
    change bankRank * jetIndex (factorProduct A) ≤ 6921 * (35201 * 6053692758425) at hji
    change bankRank * seedDegree (factorProduct A) ≤ 6921 * 4654552825571809600 at hse
    norm_num [Low6969Fat.bankRank] at hbt hji hse
    exact ⟨by omega, by omega, by omega, excludes_top hA hr hb (hdiv true A hA hcomm)⟩

end
end Low6969FatFactors
end


end Merged_R6960Low6969FatFactors

end Merged_Low6969FatFactors
end Z6969Source2279

-- Source: ProximityPrize.SubmissionLower.Low6969FatContacts
section Z6969Source2280
set_option autoImplicit true
set_option Elab.async false
section
namespace Low6969FatContacts
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open P0_9_4 (line eval_line coeff_contact order_of_locator_lines translate_map)
set_option maxRecDepth 12000
private def Bounded (F : Polynomial (Polynomial Geom)) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 48661 * j
private theorem bounded_mul {F G : Polynomial (Polynomial Geom)} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : (Polynomial Geom)) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial (Polynomial Geom)) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial (Polynomial Geom)} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (Q : Row 3) (T U : (Polynomial Geom)) (t : ℕ)
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 179732)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 48661 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial (Polynomial Geom) :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 48661 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 179732 - i.val ≤ (131071 - i.val) + 48661
      omega
    change ((F i).coeff k).natDegree ≤ b i + 48661 * k
    rw [show F i = _ from rfl, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using ht
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hterm := bounded_mul (bounded_C (Q.coeff a) le_rfl)
    (bounded_prod a.support (fun i => F i ^ a i) (fun i => b i * a i)
      (fun i _ => bounded_pow (hF i) (a i))) j
  exact hterm.trans (Nat.add_le_add_right (hQ a ha) _)
private theorem line_coeff_zero (w : I → K) (H res T : (Polynomial Geom)) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 179730)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : (Polynomial Geom)) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 48661 * j < r * 179730) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 179732 :=
    natDegree_mul_le.trans (by rw [locator_natDegree, hA]; omega)
  have hc (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ r ∣ (line Q T U).eval (C c) := by
    rw [eval_line]
    apply hcontact i
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    have ht : (T + c • U).eval (x i) = T.eval (x i) := by simp [eval_smul, hU0]
    change (H * (T + c • U) + res).eval (x i) = _
    rw [eval_add, eval_mul, ht, ← eval_mul, ← eval_add]
    exact hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  apply K1_11.eq_zero_of_many_contacts A x hx r
  · exact fun i hi => coeff_contact _ _ _ (hc i hi) j
  · rw [hA]
    exact (line_degree Q T U t hQ hT hU j).trans_lt hj
theorem raw_locator_order (w : I → K) (H res T : (Polynomial Geom)) (t k : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071)
    (hhits : ∃ A : Finset I, 179730 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (hc : RawContact 5000 w H res Q) (hQ : RawCut t Q)
    (hcut : t + 48661 * k < 5000 * 179730) :
    LowerOrder (MvPolynomial.map inclX Q) (trajectory T) (k + 1) := by
  obtain ⟨B, hB, hhits⟩ := hhits
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq hB
  let x (i : I) := embed (node i)
  have ho : OrderAt Q T (k + 1) := by
    apply order_of_locator_lines Q T (locator x A) (locator_monic x A).ne_zero
    intro V hV j hj
    exact line_coeff_zero w H res T t 5000 Q hT hQ hc A hA
      (fun i hi => hhits i (hAB hi)) V hV j (by omega)
  intro a
  rw [translate_map]
  intro ha
  exact ho a (MvPolynomial.support_map_subset _ _ ha)
end
end Low6969FatContacts
end
section
namespace Low6969FatContacts
noncomputable section
open K1 K1_13 K1_13_4_3 Low6969Fat
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open K1_13_4_3_1 (coeff_scalar support_seed weight_shift)
open K1_13_4_3 (coeff_eq_zero_of_lowerOrder)
private theorem trueCut_seed (H : (Polynomial Geom)) (i t : ℕ) (F : PhysicalRow)
    (hH : H.natDegree ≤ 2307) (hF : TrueCut H.natDegree t F) :
    TrueCut H.natDegree (t + 6921 * i) (clearedSeed H i F) := by
  intro b hb
  obtain ⟨u, hu⟩ := coeff_scalar F i b
  have hbefore := hF _ (support_seed hb)
  let w : SeedVar → ℕ := fun j => j.elim 0 (fun k => 131071 + H.natDegree - k.val)
  have hw (a : SeedVar →₀ ℕ) :
      a.sum (fun j e => j.elim 0 (fun k => (131071 + H.natDegree - k.val) * e)) =
        Finsupp.weight w a := by
    rw [Finsupp.weight_apply]
    congr 1
    funext j e
    cases j <;> simp [w, Nat.mul_comm]
  rw [hw, weight_shift w rfl] at hbefore
  rw [hw]
  have hcoeff : ((clearedSeed H i F).coeff b).natDegree ≤
      (H ^ (3 * i)).natDegree + (F.coeff (Finsupp.single none i + b)).natDegree := by
    simp only [clearedSeed, ← partial_eq_mixedHasse, MvPolynomial.coeff_C_mul, hu]
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add_left (Polynomial.natDegree_mul_C_le _ _) _)
  have hp' : (H ^ (3 * i)).natDegree ≤ 6921 * i := by
    calc
      _ ≤ (3 * i) * H.natDegree := Polynomial.natDegree_pow_le
      _ ≤ (3 * i) * 2307 := Nat.mul_le_mul_left _ hH
      _ = 6921 * i := by ring
  omega
private theorem seed_motion (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hh : P.H.natDegree ≤ 2307) (box : Shape) (t : ℕ) (F : PhysicalRow)
    (hF : Source w P L box t F) (i : ℕ) :
    Source w P L box (t + 6921 * i) (clearedSeed P.H i F) := by
  obtain ⟨hcap, hcut, hcontact, hpole⟩ := hF
  refine ⟨K1_13_4_3_1.caps_seed P.H i F box hcap, ?_, K1_13_4_3_1.contact_seed P.H i w F hcontact,
    K1_13_4_3_1.pole_seed P L _ i F hpole⟩
  simpa only [Nat.add_right_comm] using trueCut_seed P.H i _ F hh hcut
private theorem mixedOrder_iff_coeff {F : GenericRow} {z : GenericX}
    {y : Fin 3 → GenericX} {d : ℕ} :
    MixedOrder F z y d ↔
      ∀ a, mixedWeight a < d → (K1_13_4.translate (atPoint z y) F).coeff a = 0 := by
  constructor
  · intro h a ha
    by_contra hz
    exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
  · intro h a ha
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hlt)
private theorem fixed_seed_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : Low6969Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 48661 * k < 5000 * 179730) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 179730 ≤ B.card ∧
      ∀ i ∈ B, (P.H * T + res).eval (embed (node i)) = embed (w i) := by
    refine ⟨A, hA, fun i hi => ?_⟩
    rw [← hST, extend, Polynomial.eval_map, Polynomial.eval₂_at_apply, hhits i hi]
  have hcontact := rawContact_of_restore 5000 w P.H res (P.z γ) (box.b + box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho := raw_locator_order w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact trueOrder_of_raw P.H res T (P.z γ) (box.b + box.j) (k + 1) F Q
    P.monic.ne_zero hrestore ho
private theorem source_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : Low6969Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (hh : P.H.natDegree ≤ 2307) {d : ℕ} (hd : t + d ≤ 5000 * 179730) :
    MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) d := by
  set z := inclConst (P.z γ)
  set y := trajectory (extend (s γ))
  apply mixedOrder_iff_coeff.mpr
  intro m hm
  let a : SeedVar →₀ ℕ := Finsupp.single none (m none)
  let b : SeedVar →₀ ℕ := m.some.optionElim 0
  have hab : a + b = m := by
    ext i
    cases i <;> simp [a, b]
  have hdis : ∀ i, i ∉ a.support ∨ i ∉ b.support := by
    intro i
    cases i <;> simp [a, b, Finsupp.mem_support_iff]
  have hlt : t + 6921 * m none + 48661 * m.some.degree < 5000 * 179730 := by
    change 6921 * m none + 48661 * m.some.degree < d at hm
    omega
  have hD := seed_motion w P L hh box t F hF (m none)
  have ho := fixed_seed_order h2 hw P L hD hγ m.some.degree hlt
  have hc := coeff_eq_zero_of_lowerOrder ho m.some (Nat.lt_succ_self _)
  change (K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F)))).coeff m.some = 0 at hc
  have hmap :
      K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F))) =
        MvPolynomial.C (inclX (P.H ^ (3 * m none))) *
          K1_13_4.translate y (atSeed z (toGeneric (mixedHasse a F))) := by
    simp [clearedSeed, toGeneric, a, atSeed, K1_13_4.translate]
  rw [hmap, MvPolynomial.coeff_C_mul] at hc
  have hn : inclX (P.H ^ (3 * m none)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericX)).mpr (pow_ne_zero _ P.monic.ne_zero)
  have hcoef := (mul_eq_zero.mp hc).resolve_left hn
  rw [translate_atSeed, coeff_atSeed_zero, ← partial_eq_mixedHasse, toGeneric, map_partial,
    translate_partial] at hcoef
  change (hasse a (K1_13_4.translate (atPoint z y) (toGeneric F))).coeff b = 0 at hcoef
  rw [coeff_partial_eq_of_disjoint _ _ _ hdis, hab] at hcoef
  exact hcoef
private theorem mixedHasse_order (F : PhysicalRow) (a : SeedVar →₀ ℕ)
    (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hF : MixedOrder (toGeneric F) z y (d + mixedWeight a)) :
    MixedOrder (toGeneric (mixedHasse a F)) z y d := by
  apply mixedOrder_iff_coeff.mpr
  intro b hb
  have hlt : mixedWeight (a + b) < d + mixedWeight a := by rw [mixedWeight_add]; omega
  have hz := mixedOrder_iff_coeff.mp hF _ hlt
  rw [← partial_eq_mixedHasse, toGeneric, map_partial, translate_partial]
  exact coeff_partial_eq_zero _ _ _ hz
theorem proof : Low6969Fat.c3 := by
  intro w Γ s hw P L hh
  let h2 := K1_13_4_3_2.proof
  constructor
  · intro F hF γ hγ
    exact source_order h2 hw P L hF.1 hγ hh (Nat.sub_add_cancel (show 3975818 ≤ 898650000 from by decide)).le
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h2 hw P L hF.1 hγ hh
      change t + mixedWeight a ≤ 5000 * 179730 - 1815862 at ht
      change t + (1815862 + mixedWeight a) ≤ 5000 * 179730
      omega
    | zero =>
      exact mixedOrder_iff_coeff.mpr (fun _ _ => by simp [toGeneric])
    | add Q R _ _ hQ hR =>
      exact mixedOrder_iff_coeff.mpr (fun a ha => by
        simp only [toGeneric, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
        exact (congrArg₂ (· + ·)
          (mixedOrder_iff_coeff.mp hQ a ha) (mixedOrder_iff_coeff.mp hR a ha)).trans (add_zero 0))
    | smul c Q _ hQ =>
      apply mixedOrder_iff_coeff.mpr
      intro a ha
      have hsmul : c • Q = MvPolynomial.C (Polynomial.C c) * Q := by
        rw [Algebra.smul_def]
        rfl
      rw [hsmul]
      simp only [toGeneric, map_mul, MvPolynomial.map_C, K1_13_4.translate, MvPolynomial.eval₂Hom_C,
        MvPolynomial.coeff_C_mul]
      exact mul_eq_zero.mpr (Or.inr (mixedOrder_iff_coeff.mp hQ a ha))
end
end Low6969FatContacts
end

end Z6969Source2280

-- Source: ProximityPrize.SubmissionLower.Low6969FatPadding
section Z6969Source2281
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969FatEliminate
section Merged_R6960Low6969FatEliminate

set_option Elab.async false
section
namespace Low6969Fat
noncomputable section
open K1 K1_13 K1_13_4_5
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
private theorem mixedWeight_pos {a : SeedVar →₀ ℕ} (ha : a ≠ 0) : 0 < mixedWeight a := by
  by_contra! h
  change 6921 * a none + 48661 * a.some.degree ≤ 0 at h
  have hn : a none = 0 := by omega
  have hd : a.some.degree = 0 := by omega
  have hs := (Finsupp.degree_eq_zero_iff _).mp hd
  apply ha
  ext i
  cases i with
  | none => simpa using hn
  | some i => simpa using DFunLike.congr_fun hs i
private theorem order_cancel_coeff (A B : GenericRow) (d : ℕ) (hA : A.coeff 0 ≠ 0)
    (hAB : ∀ a, mixedWeight a < d → (A * B).coeff a = 0) :
    ∀ a, mixedWeight a < d → B.coeff a = 0 := by
  classical
  suffices h : ∀ n a, mixedWeight a = n → n < d → B.coeff a = 0 by
    exact fun a ha => h _ a rfl ha
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a ha hd
    have hab := hAB a (ha.symm ▸ hd)
    rw [MvPolynomial.coeff_mul, Finset.sum_eq_single_of_mem (0, a) (by simp)] at hab
    · exact (mul_eq_zero.mp hab).resolve_left hA
    · intro b hb hbne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hb₁ : b.1 ≠ 0 := by
        intro hz
        apply hbne
        exact Prod.ext hz (by simpa [hz] using hs)
      have hw := mixedWeight_add b.1 b.2
      rw [hs, ha] at hw
      have hpos := mixedWeight_pos hb₁
      rw [ih (mixedWeight b.2) (by omega) b.2 rfl (by omega), mul_zero]
private theorem translated_const (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) :
    (translate (atPoint z y) F).coeff 0 = MvPolynomial.eval (atPoint z y) F := by
  let e : GenericRow →+* GenericX := MvPolynomial.eval (fun _ => 0)
  have he : e.comp (K1_13_4.translate (atPoint z y)) = MvPolynomial.eval (atPoint z y) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [e, K1_13_4.translate]
    · intro i
      simp [e, K1_13_4.translate]
  rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero']
  exact DFunLike.congr_fun he F
private theorem mixedOrder_cancel (A B : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hA : MvPolynomial.eval (atPoint z y) A ≠ 0) (h : MixedOrder (A * B) z y d) :
    MixedOrder B z y d := by
  intro a ha
  by_contra! hlt
  refine (MvPolynomial.mem_support_iff.mp ha) (order_cancel_coeff
    (translate (atPoint z y) A) (translate (atPoint z y) B) d ?_ ?_ a hlt)
  · rwa [translated_const]
  · intro b hb
    rw [← map_mul]
    by_contra hne
    exact (Nat.not_lt_of_ge (h b (MvPolynomial.mem_support_iff.mpr hne))) hb
open P3_6_4 (moving_lower total_prod index_prod eval_prod_factor_ne_zero)
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → (Polynomial Geom))
    (hzinj : Function.Injective z) {F G : GenericRow} (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, PairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
      ∃ (book : Finset K) (Q : Lower), book.card ≤ 59600 ∧ Q ≠ 0 ∧
        Q.totalDegree ≤ 682 ∧ lowerIndex Q ≤ 239 ∧
        ∀ γ ∈ Γ, γ ∉ book → MvPolynomial.eval (trajectory (S γ)) Q = 0 ∨
          PairOrders D.left D.right (inclConst (z γ)) (trajectory (S γ)) := by
  classical
  have fix_ne (f : GenericRow) (hf : f ∈ D.fixed) : f ≠ 0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f : GenericRow) (hf : f ∈ D.moving) : f ≠ 0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total : (∑ f ∈ D.moving, jetTotal f) ≤ 7 := by
    simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f ∈ D.moving, jetIndex f) ≤ 2 := by
    simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 45 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 45 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_seed
  choose! q qn qt qi qe using
    (fun f hf => fixed_lower f (fix_ne f hf) (D.fixed_kind f hf).2.2)
  have exists_moving (f : GenericRow) (hf : f ∈ D.moving) :=
    moving_lower f (D.moving_kind f hf).1 (D.moving_kind f hf).2.1
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (mov_total.trans (by decide)))
      (D.moving_kind f hf).2.2.1 (D.moving_kind f hf).2.2.2
  choose! r rn rt ri re using exists_moving
  let P : Lower := ∏ f ∈ D.fixed, q f
  let R : Lower := ∏ f ∈ D.moving, r f
  have Pn : P ≠ 0 := Finset.prod_ne_zero_iff.mpr qn
  have Rn : R ≠ 0 := Finset.prod_ne_zero_iff.mpr rn
  have Pt : P.totalDegree ≤ 52 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 52
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 14 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 14
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 45 * 7 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 45 * 7
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 45) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 2 + 1) * 45 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 2 + 1) * 45
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 45) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 45) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 59600 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 52 + 2 * 45 * 7 ≤ 682 by decide)
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 14 + (2 * 2 + 1) * 45 ≤ 239 by decide)
  · intro γ hγ hnot
    let a := inclConst (z γ)
    let y := trajectory (S γ)
    change MvPolynomial.eval y (P * R) = 0 ∨ PairOrders D.left D.right a y
    by_cases hn : MvPolynomial.eval y (P * R) = 0
    · exact Or.inl hn
    rw [map_mul] at hn
    have hfixed (f : GenericRow) (hf : f ∈ D.fixed) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      rw [qe f hf]
      exact eval_prod_factor_ne_zero (left_ne_zero_of_mul hn) hf
    have hmoving (f : GenericRow) (hf : f ∈ D.moving) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      intro h0
      exact (eval_prod_factor_ne_zero (right_ne_zero_of_mul hn) hf) (re f hf _ _ h0)
    have hp : D.pure.eval a ≠ 0 := fun he => hnot (mem_seedBook.mpr ⟨hγ, he⟩)
    let A := pureSeed D.pure * (∏ f ∈ D.fixed, f ^ D.exponent f) *
      (∏ f ∈ D.moving, f ^ D.exponent f)
    have hA : MvPolynomial.eval (atPoint a y) A ≠ 0 := by
      simp only [A, map_mul, map_prod, map_pow, pure_eval]
      exact mul_ne_zero (mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hfixed f hf))) (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hmoving f hf))
    refine Or.inr ⟨mixedOrder_cancel A D.left a y _ hA ?_,
      mixedOrder_cancel A D.right a y _ hA ?_⟩
    · simpa only [A, ← D.left_eq] using (hOrders γ hγ).1
    · simpa only [A, ← D.right_eq] using (hOrders γ hγ).2
end
end Low6969Fat
end
section
namespace Low6969Fat
open Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open P3_6_4 (resultant_taylor_formal)
private def weight (d i : ℕ) : ℕ := d - 6921 * i
private def power (w : ℕ) : ℕ := (48660 + w) / 48661
private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : (Polynomial (Polynomial k))) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 6921 * i + 48661 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 48661 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstOrder j) (fun j : Fin n => weight secondOrder j)
private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : (Polynomial (Polynomial k))) (m n : ℕ)
    (hF : ∀ i l : ℕ, 6921 * i + 48661 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 6921 * i + 48661 * l < secondOrder → (G.coeff i).coeff l = 0)
    (i j : Fin (m + n)) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (firstOrder + secondOrder) i - columnWeight j) ∣
      sylvester F G m n i j := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, columnWeight, Set.mem_Icc]
    split_ifs with h
    · simpa only [add_comm secondOrder firstOrder] using
        coefficient_bound G secondOrder firstOrder i j h.1 hG
    · exact dvd_zero _
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right, columnWeight, Set.mem_Icc]
    split_ifs with h
    · exact coefficient_bound F firstOrder secondOrder i j h.1 hF
    · exact dvd_zero _
private theorem det_bound {k : Type*} [CommRing k] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial k)) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : (Polynomial k)) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 48661 * D ≤ (∑ i, row i) + 48660) :
    (Polynomial.X : (Polynomial k)) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : (Polynomial k)) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 48661 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _
private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 6921 * t)
    (hbefore : ∀ i < t, 6921 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 6921 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 6921 * (∑ i ∈ Finset.range t, i) =
      t * d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range t, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := hbefore i (Finset.mem_range.mp hi)
        unfold weight
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [Finset.sum_range_id] at hsum
  omega
private theorem benchmark_budget :
    (∑ j : Fin (24400 + 35200), columnWeight (m := 24400) (n := 35200) j) + 48661 * 21437 ≤
      (∑ i : Fin (24400 + 35200), weight (firstOrder + secondOrder) i) + 48660 := by
  have hF : (∑ i : Fin 24400, weight firstOrder i) = 1143957325 := by
    rw [sum_weight (t := 575) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder]; omega)]
    decide
  have hG : (∑ i : Fin 35200, weight secondOrder i) = 239122493 := by
    rw [sum_weight (t := 263) (by decide) (by decide)
      (by intro i hi; simp only [secondOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (24400 + 35200), weight (firstOrder + secondOrder) i) =
      2426213574 := by
    rw [sum_weight (t := 837) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder, secondOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide
private theorem resultant_bound
    (F G : (Polynomial (Polynomial GenericX))) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 6921 * i + 48661 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 6921 * i + 48661 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 48661 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 48660) :
    (Polynomial.X : (Polynomial GenericX)) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget
theorem line_resultant_order (F G : (Polynomial (Polynomial GenericX))) (z : GenericX)
    (hF : F.natDegree ≤ 24400) (hG : G.natDegree ≤ 35200)
    (hFO : ∀ i j, 6921 * i + 48661 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 6921 * i + 48661 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : (Polynomial GenericX)) ^ 21437 ∣ Polynomial.resultant F G 24400 35200 := by
  exact resultant_bound F G z (m := 24400) (n := 35200) (D := 21437)
    hF hG hFO hGO benchmark_budget
end Low6969Fat
end
section
namespace Low6969Fat
noncomputable section
open K1_13 Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped BigOperators
set_option maxRecDepth 4000
private def ray (v : Fin 3 → GenericX) : Lower →+* (Polynomial GenericX) :=
  MvPolynomial.eval₂Hom C (fun i => C (v i) * Polynomial.X)
private theorem ray_monomial (v : Fin 3 → GenericX) (a : Fin 3 →₀ ℕ) (c : GenericX) :
    ray v (MvPolynomial.monomial a c) =
      monomial a.degree (MvPolynomial.eval v (MvPolynomial.monomial a c)) := by
  rw [← C_mul_X_pow_eq_monomial]
  simp only [ray, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial, mul_pow,
    Finsupp.prod]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, ← mul_assoc]
  simp only [map_mul, map_prod, map_pow]
private theorem ray_coeff (v : Fin 3 → GenericX) (Q : Lower) (j : ℕ) :
    (ray v Q).coeff j = MvPolynomial.eval v (MvPolynomial.homogeneousComponent j Q) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [ray_monomial, coeff_monomial,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases h : a.degree = j
    · simp [h]
    · simp [h, Ne.symm h]
  | add Q R hQ hR =>
    rw [map_add, coeff_add, hQ, hR, map_add, map_add]
private theorem line_translation (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX) :
    ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp (Polynomial.X + C (C z)) =
      (asSeedPoly (K1_13_4.translate (atPoint z y) F)).map (ray v) := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let left := (compRingHom (Polynomial.X + C (C z))).comp ((mapRingHom ((ray v).comp (K1_13_4.translate y))).comp e)
  let right := (mapRingHom (ray v)).comp (e.comp (K1_13_4.translate (atPoint z y)))
  have he : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, e, K1_13_4.translate, ray]
    · intro i
      cases i <;>
        simp [left, right, e, K1_13_4.translate, ray, atPoint]
  exact DFunLike.congr_fun he F
private theorem line_order (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX)
    (d : ℕ) (hF : MixedOrder F z y d) :
    ∀ i j, 6921 * i + 48661 * j < d →
      ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).taylor (C z)).coeff i).coeff j = 0 := by
  intro i j h
  change ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp
    (Polynomial.X + C (C z))).coeff i).coeff j = 0
  rw [line_translation, coeff_map, ray_coeff]
  suffices hc : MvPolynomial.homogeneousComponent j
      ((asSeedPoly (K1_13_4.translate (atPoint z y) F)).coeff i) = 0 by
    rw [hc, map_zero]
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro a ha hj
  have hmem : a.optionElim i ∈ (K1_13_4.translate (atPoint z y) F).support := by
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    exact ha
  have hb := hF _ hmem
  have hweight : mixedWeight (a.optionElim i) = 6921 * i + 48661 * j := by
    change 6921 * a.optionElim i none + 48661 * (a.optionElim i).some.degree = _
    rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim, hj]
  rw [hweight] at hb
  exact (Nat.not_lt_of_ge hb) h
private theorem order_of_rays (Q : Lower) (y : Fin 3 → GenericX) (d : ℕ)
    (h : ∀ v, Polynomial.X ^ d ∣ ray v (K1_13_4.translate y Q)) :
    LowerOrder Q y d := by
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  intro a ha
  change d ≤ a.degree
  by_contra! ha'
  have hm : MvPolynomial.homogeneousComponent a.degree (K1_13_4.translate y Q) = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, ← ray_coeff]
    exact (X_pow_dvd_iff (n := d) (f := ray v (K1_13_4.translate y Q))).mp (h v) a.degree ha'
  have hc := congrArg (fun P : Lower => P.coeff a) hm
  simp [MvPolynomial.coeff_homogeneousComponent] at hc
  exact (MvPolynomial.mem_support_iff.mp ha) hc
def seedResultant27 (F G : GenericRow) : Lower :=
  Polynomial.resultant (asSeedPoly F) (asSeedPoly G) 24400 35200
private theorem line_resultant (F G : GenericRow) (y v : Fin 3 → GenericX) :
    resultant ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y)))
      ((asSeedPoly G).map ((ray v).comp (K1_13_4.translate y))) 24400 35200 =
        ray v (K1_13_4.translate y (seedResultant27 F G)) := by
  unfold seedResultant27
  rw [resultant_map_map, RingHom.comp_apply]
theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : (Polynomial Geom)) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)
theorem resultant_order (F G : GenericRow) (z : GenericX)
    (y : Fin 3 → GenericX) (hF : (asSeedPoly F).natDegree ≤ 24400)
    (hG : (asSeedPoly G).natDegree ≤ 35200) (h : PairOrders F G z y) :
    LowerOrder (seedResultant27 F G) y 21437 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact line_resultant_order _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)
end
end Low6969Fat
end


end Merged_R6960Low6969FatEliminate

-- merged module Low6969FatPadding
section Merged_Low6969FatPadding

set_option Elab.async false
/-! Low-specific padding of a coprime pair to seed degree exactly 27,000 and the resulting
resultant box (367,443,000, 124,200,000); a copy of the padding part of `Fast074`. -/
section
namespace Low6969Fat
noncomputable section
open K1_13 K1_13_4 Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open K1_13_4_6 (Fiber toFiber embedConstant toFiber_injective coprime_in_fiber exists_constant_nonroot coprime_linear asSeedPoly_ne_zero deg deg_pad_coeff deg_resultant)
structure PaddedPair27 (F G : GenericRow) where
  a : (Polynomial Geom)
  b : (Polynomial Geom)
  degree_left : (asSeedPoly (pad F a)).natDegree = 24400
  degree_right : (asSeedPoly (pad G b)).natDegree = 35200
  nonzero : seedResultant27 (pad F a) (pad G b) ≠ 0
  total : (seedResultant27 (pad F a) (pad G b)).totalDegree ≤ 405380800
  index : lowerIndex (seedResultant27 (pad F a) (pad G b)) ≤ 137080000
  keeps_order : ∀ z y, PairOrders F G z y → PairOrders (pad F a) (pad G b) z y
private theorem pad_degree27 {cap : ℕ} (F : GenericRow) (hF : F ≠ 0)
    (hcap : seedDegree F ≤ cap) (a : Geom) :
    (asSeedPoly (pad F (((Polynomial.X : (Polynomial Geom)) - C a) ^
      (cap - (asSeedPoly F).natDegree)))).natDegree = cap := by
  have hcap' : (asSeedPoly F).natDegree ≤ cap := by
    simpa only [asSeedPoly, MvPolynomial.natDegree_optionEquivLeft, seedDegree] using hcap
  rw [K1_13_4_6.asSeedPoly_pad, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    natDegree_mul (asSeedPoly_ne_zero hF) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_X_sub_C, mul_one, Nat.add_sub_of_le hcap']
theorem padding_exists27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0)
    (hfg : IsRelPrime F G) (hf : seedDegree F ≤ 24400) (hg : seedDegree G ≤ 35200) :
    ∃ a b : (Polynomial Geom), (asSeedPoly (pad F a)).natDegree = 24400 ∧
      (asSeedPoly (pad G b)).natDegree = 35200 ∧ seedResultant27 (pad F a) (pad G b) ≠ 0 := by
  classical
  let f := (asSeedPoly F).map toFiber
  let g := (asSeedPoly G).map toFiber
  have hf0 : f ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hF)
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hG)
  have hcop : IsCoprime f g := by
    apply coprime_in_fiber (asSeedPoly_ne_zero hF)
    intro d hdf hdg
    let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
    have hu : IsUnit (e.symm d) :=
      hfg (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdf)
        (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdg)
    have he := hu.map e.toRingHom
    change IsUnit (e (e.symm d)) at he
    rwa [e.apply_symm_apply] at he
  obtain ⟨a, ha, _⟩ := exists_constant_nonroot g hg0 ∅
  obtain ⟨b, hb, hba⟩ := exists_constant_nonroot f hf0 {toFiber (embedConstant a)}
  let p := ((Polynomial.X : (Polynomial Geom)) - C a) ^ (24400 - (asSeedPoly F).natDegree)
  let q := ((Polynomial.X : (Polynomial Geom)) - C b) ^ (35200 - (asSeedPoly G).natDegree)
  have hp : (asSeedPoly (pad F p)).natDegree = 24400 := pad_degree27 F hF hf a
  have hq : (asSeedPoly (pad G q)).natDegree = 35200 := pad_degree27 G hG hg b
  refine ⟨p, q, hp, hq, ?_⟩
  have hab : toFiber (embedConstant a) ≠ toFiber (embedConstant b) := by
    simpa using (Finset.notMem_singleton.mp hba).symm
  have hpad : IsCoprime ((asSeedPoly (pad F p)).map toFiber)
      ((asSeedPoly (pad G q)).map toFiber) := by
    simp only [K1_13_4_6.asSeedPoly_pad, Polynomial.map_mul, p, q, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact (hcop.mul_right (coprime_linear f hb).symm.pow_right).mul_left
      ((coprime_linear g ha).pow_left.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow)
  have hn := resultant_ne_zero _ _ hpad
  rw [natDegree_map_eq_of_injective toFiber_injective,
    natDegree_map_eq_of_injective toFiber_injective, hp, hq, resultant_map_map] at hn
  intro hz
  exact hn ((congrArg toFiber hz).trans (map_zero _))

theorem padded27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0) (hp : IsRelPrime F G)
    (hf : Low6969Fat.Caps27 firstBox F) (hg : Low6969Fat.Caps27 secondBox G) :
    Nonempty (PaddedPair27 F G) := by
  obtain ⟨a, b, ha, hb, hn⟩ := padding_exists27 hF hG hp (hf.2.trans (by decide)) (hg.2.trans (by decide))
  refine ⟨⟨a, b, ha, hb, hn, ?_, ?_, ?_⟩⟩
  · have h := deg_resultant (1 : Fin 3 → ℕ) (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      24400 35200 6789 6820 (fun i => (deg_pad_coeff _ F a i).trans hf.1.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.1)
    simpa only [MvPolynomial.weightedTotalDegree_one, seedResultant27,
      ← Nat.mul_add, Nat.add_comm 6820 6789] using h.trans_eq (by norm_num)
  · have h := deg_resultant Fin.val (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      24400 35200 2300 2300 (fun i => (deg_pad_coeff _ F a i).trans hf.1.2.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.2.1)
    simpa only [MvPolynomial.weightedTotalDegree, Finsupp.weight_apply, Nat.nsmul_eq_mul,
      Nat.mul_comm, lowerIndex, seedResultant27, ← Nat.mul_add] using h.trans_eq (by norm_num)
  · intro z y h
    exact ⟨mixedOrder_pad a h.1, mixedOrder_pad b h.2⟩
end
end Low6969Fat
end

end Merged_Low6969FatPadding
end Z6969Source2281

-- Source: ProximityPrize.SubmissionLower.Low6969FatFamily
section Z6969Source2282
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969Fat
section Merged_R6960Low6969Fat


set_option Elab.async false
section
namespace Low6969Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
open P3_6_4 (eval_cleared order_cleared)
set_option maxRecDepth 2400 in
/-- Fat equations through height 2,292 at 179,740 agreements. -/
theorem fat_equations (h2 : c2) : Equations := by
  have h1 := Low6969FatBanks.proof
  have h3 := Low6969FatContacts.proof
  intro w Γ s _ hhits P hheight
  have hw : Messages w Γ s := ⟨hhits⟩
  obtain ⟨L⟩ := K1_13_4_1.proof Γ s P
  obtain ⟨⟨F, neF, hF⟩, rank2⟩ := h1 w Γ s P L hheight
  obtain ⟨vanishes1, vanishes2⟩ := h3 w Γ s hw P L hheight
  obtain ⟨G, hG, ⟨D⟩⟩ := h2 w Γ s P L F neF ⟨hF.1.1, hF.2⟩ rank2
  have hOrders : ∀ γ ∈ Γ, PairOrders (toGeneric F) (toGeneric G)
      (inclConst (P.z γ)) (trajectory (extend (s γ))) := fun γ hγ =>
    ⟨vanishes1 F hF γ hγ, vanishes2 G hG γ hγ⟩
  obtain ⟨book, Q, hcard, hQ, htQ, hiQ, hcover⟩ :=
    eliminate_common Γ P.z (fun γ => extend (s γ)) P.injective D hOrders
  obtain ⟨J⟩ := padded27 D.left_ne D.right_ne D.proper D.left_caps D.right_caps
  let R := seedResultant27 (pad D.left J.a) (pad D.right J.b)
  obtain ⟨_, Q', _, suppQ, mapQ⟩ := clear_denominators Q
  obtain ⟨_, R', _, suppR, mapR⟩ := clear_denominators R
  have neQ : Q' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppQ
    exact hQ suppQ
  have neR : R' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppR
    exact J.nonzero suppR
  have totalQ : Q'.totalDegree ≤ 682 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 239 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 405380800 := by
    have htR : R.totalDegree ≤ 405380800 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 137080000 := by
    have hiR : lowerIndex R ≤ 137080000 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hres : LowerOrder R (trajectory (extend (s γ))) 21437 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ)) _
        J.degree_left.le J.degree_right.le ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact hres
end
end Low6969Fat
end


namespace LowProfile6969
open K1_13 (extend)
open Low6969Fat (Holds)

/-- The actual low family supplies common and resultant equations with the
revised resultant order. -/
theorem fat_of_family (h2 : Low6969Fat.c2) {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179730 M Γ) (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2307) :
    ∃ (book : Finset P1.K) (E : Low6969Fat.FatEquations), book.card≤59600 ∧
      ∀ γ∈Γ,γ∉book → Holds E (extend (F.scalar γ)) := by
  have marks := Research6969.Low6969Primary.messages_of_family M F hi
  have deg := marks.degree
  have hits := marks.hits
  obtain ⟨pole,hpole⟩ := ModelExactPole6966.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree≤2307 := by rw [hpole]; omega
  exact Low6969Fat.fat_equations h2 M.word Γ F.scalar deg hits pole small

end LowProfile6969

end Merged_R6960Low6969Fat
end Z6969Source2282

-- Source: ProximityPrize.SubmissionLower.Low6969MarkInventory
section Z6969Source2283
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace LowProfile6969
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K)
open K1_13 (Row shape InBox extend atJet OnFactor)
open K1_13_1 (indexDegree_eq index_bounds)
open Final50GeoCover (activeDegree activeFits_iff)
open scoped BigOperators Polynomial Classical









































































end
end LowProfile6969
end Z6969Source2283

-- Source: ProximityPrize.SubmissionLower.Low6969SurfaceLinearFour
section Z6969Source2284
set_option autoImplicit true
set_option Elab.async false

namespace Low6969Prices

open K1_13 (Shape chart liftedChart mixed32 ceilDiv OnFactor shape extend)

def primaryBox : Shape := ⟨4024, 1679, 500⟩
abbrev primaryCutoff := LowProfile6969.primaryCutoff
abbrev layerWidth := LowProfile6969.layerWidth
abbrev layerNeed : ℕ := 21230822871131
abbrev symbolCount : ℕ := 427286700047
abbrev LayerBudget := @LowProfile6969.LayerBudget
abbrev remaining := Final50Price.remaining
def ProperCut (f : K1_13.Row 4) (Γ : Finset P3.K)
    (s : P3.K → Polynomial P3.K) (l : ℕ) : Prop :=
  ∃ Q : K1_13.Row 4, (¬ f ∣ Q) ∧ K1_13.InBox (shape Q) primaryBox ∧
    TrueWeightLE Q primaryCutoff ∧ Final50Price.ActiveFits Q 5192 ∧
    ∀ γ∈Γ, K1_13.OrderAt Q (extend (s γ)) l
abbrev ActiveFits := Final50Price.ActiveFits
abbrev Fits := @LowProfile6969.Fits
abbrev fullCap := LowProfile6969.fullCap

set_option autoImplicit true

def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l K

end Low6969Prices

-- merged module R6960Low6969Monotone
section Merged_R6960Low6969Monotone
set_option Elab.async false
section
namespace Low6969Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    Low6969Prices.surfaceNumerator32 p q ≤ Low6969Prices.surfaceNumerator32 p' q := by
  let L := Low6969Prices.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : Low6969Prices.physicalPriceOld x l ≤ Low6969Prices.physicalPriceOld y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6969Prices.primaryBox
  let L := Low6969Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, by decide⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6969Prices.errors + 2*Low6969Prices.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (Low6969Prices.errors + 2*Low6969Prices.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6969Prices.errors hc) (Nat.mul_le_mul_left (2*Low6969Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6969Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end Low6969Monotone
end

namespace Low6969Monotone
open K1_13 (Shape)
open Low6969Prices (physicalPrice physicalPriceOld physicalPriceTilted physicalPriceActive physicalPriceWith)

theorem physicalPrice_le_old (x : Shape) (l K : ℕ) : physicalPrice x l K ≤ physicalPriceOld x l := by
  unfold physicalPrice
  split
  · split
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  · exact le_rfl





















end Low6969Monotone

end Merged_R6960Low6969Monotone

-- merged module Low6969SurfaceLinearFour
section Merged_Low6969SurfaceLinearFour

-- merged module R6960Low6969SharedPrice
section Merged_R6960Low6969SharedPrice
set_option Elab.async false
set_option autoImplicit false
namespace Low6969SharedPrice
open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Low6969Prices (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial
abbrev slope : Shape := ⟨62,28,7⟩
inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq
def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920
def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q
def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)
def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩
structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance
private theorem expression_line (w f : Shape) (r a : ℕ) (u t : Bool)
    (hb : a*f.b ≤ r*slope.b) (hj : a*f.j ≤ r*slope.j) (ht : a*f.t ≤ r*slope.t) :
    expression w (deficit r a f) u t + a*expression w f u t = r*expression w slope u t := by
  have b := Nat.sub_add_cancel hb
  have j := Nat.sub_add_cancel hj
  have h := Nat.sub_add_cancel ht
  cases u <;> cases t <;> simp only [expression, deficit, Bool.false_eq_true, ↓reduceIte, ite_true]
  all_goals
    rw [mul_add, mul_add]
    simp only [mul_assoc, ← mul_add, ← add_assoc] <;> ring_nf at b j h ⊢
    <;> nlinarith only [congrArg (fun z => w.b*z) b, congrArg (fun z => w.b*z) j,
      congrArg (fun z => w.j*z) j, congrArg (fun z => w.t*z) j, congrArg (fun z => w.t*z) h]
private theorem affine_of_endpoints (p q s x y W r a : ℕ)
    (hp : 0 < p) (hb : a*q ≤ r*p)
    (h₀ : x ≤ W) (h₁ : (q : ℤ)*x-p*y ≤ (q-(s:ℤ)*p)*W) :
    (r : ℤ)*x-a*y ≤ (r-(s:ℤ)*a)*W := by
  have hq : (0 : ℤ) < p := by exact_mod_cast hp
  have hr : (a : ℤ)*q ≤ (r : ℤ)*p := by exact_mod_cast hb
  have hzero : (0 : ℤ) ≤ (W : ℤ)-x := sub_nonneg.mpr (by exact_mod_cast h₀)
  have hA := mul_nonneg (sub_nonneg.mpr hr) hzero
  have hB := mul_nonneg (Int.natCast_nonneg a)
    (show 0 ≤ (p : ℤ)*((y:ℤ)-s*W)-q*((x:ℤ)-W) by linarith)
  apply sub_nonneg.mp
  refine nonneg_of_mul_nonneg_left ?_ hq
  have ident : (p : ℤ)*(((r:ℤ)-s*a)*W-((r:ℤ)*x-a*y)) =
      ((r:ℤ)*p-a*q)*((W:ℤ)-x)+a*(p*((y:ℤ)-s*W)-q*((x:ℤ)-W)) := by ring
  rw [mul_comm, ident]
  exact add_nonneg hA hB
private theorem pivot_pos (i : Fin 3) : 0 < coord slope i := by fin_cases i <;> decide
theorem rate_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (chooseWidth : Bool) :
    expression (weights u.kind f) (deficit r a f) chooseWidth u.topIndex ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let W := 3*surfaceScale u.kind*u.amount
  let w := weights u.kind f
  obtain ⟨_,hs,hpos,hcoord,h₀,h₁⟩ := hu
  have hp : 0 < p := pivot_pos u.pivot
  have hfitPivot : a*q ≤ r*p := hfit u.pivot
  have har : u.split*a ≤ r := by
    by_contra! hbad
    have hleft := Nat.mul_lt_mul_of_pos_right hbad hp
    have hright := Nat.mul_le_mul_left a (Nat.le_of_lt hpos)
    exact (not_lt_of_ge (hfitPivot.trans' (by
      simpa only [mul_left_comm, mul_assoc, mul_comm] using hright : u.split*a*p ≤ a*q))) hleft
  have f0 := expression_line w f q p chooseWidth u.topIndex
    (hcoord 0) (hcoord 1) (hcoord 2)
  have f1 := expression_line w f r a chooseWidth u.topIndex
    (hfit 0) (hfit 1) (hfit 2)
  have hend : ((q : ℤ)*expression w slope chooseWidth u.topIndex -
      p*expression w f chooseWidth u.topIndex) ≤ (q-(u.split:ℤ)*p)*W := by
    have hnum : expression w (deficit q p f) chooseWidth u.topIndex ≤ W*(q-u.split*p) := h₁ chooseWidth
    have hnum' : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤
        (W:ℤ)*(q-(u.split:ℤ)*p) := by
      have hh : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤ (W:ℤ) * ((q-u.split*p : ℕ) : ℤ) := by exact_mod_cast hnum
      change u.split*p < q at hpos
      rwa [Int.ofNat_sub (Nat.le_of_lt hpos)] at hh
    have hline : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) +
        p*expression w f chooseWidth u.topIndex = q*expression w slope chooseWidth u.topIndex := by
      exact_mod_cast f0
    nlinarith
  have haff := affine_of_endpoints p q u.split _ _ W r a hp hfitPivot (h₀ chooseWidth) hend
  have hline : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) +
      a*expression w f chooseWidth u.topIndex = r*expression w slope chooseWidth u.topIndex := by
    exact_mod_cast f1
  have hgoal : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) ≤
      (W:ℤ)*(r-(u.split:ℤ)*a) := by nlinarith
  rw [← Nat.cast_mul, ← Nat.cast_sub har, ← Nat.cast_mul] at hgoal
  exact_mod_cast hgoal











theorem chamber_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (g : Shape)
    (hg : K1_13.InBox g (deficit r a f)) (hgt : 3*g.t ≤ g.j) :
    3*((weights u.kind f).b*g.chamber.b + (weights u.kind f).j*g.j + (weights u.kind f).t*g.t) ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let w := weights u.kind f
  let d := deficit r a f
  have hgB : g.b ≤ d.b := hg.1
  have hgJ : g.j ≤ d.j := hg.2.1
  have hgT : g.t ≤ d.t := hg.2.2
  have hTop : 3*g.t ≤ (if u.topIndex then d.j else 3*d.t) := by
    split
    · exact hgt.trans hgJ
    · exact Nat.mul_le_mul_left _ hgT
  have component (i : Bool)
      (hB : max g.b g.j ≤ (if i then d.j else d.b)) :
      3*(w.b*g.chamber.b + w.j*g.j + w.t*g.t) ≤ expression w d i u.topIndex := by
    change 3*(w.b*max g.b g.j + w.j*g.j + w.t*g.t) ≤ _
    unfold expression
    calc
      _ = 3*w.b*max g.b g.j + 3*w.j*g.j + w.t*(3*g.t) := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ hB) (Nat.mul_le_mul_left _ hgJ)) (Nat.mul_le_mul_left _ hTop)
  rcases le_total d.b d.j with h | h
  · exact (component true (max_le (hgB.trans h) hgJ)).trans (rate_bound hu r a hfit true)
  · exact (component false (max_le hgB (hgJ.trans h))).trans (rate_bound hu r a hfit false)
def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l
def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l
def cShared : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → ∀ u, RateFits (shape f) u →
      Γ.card ≤ price (shape f) l K u
end Low6969SharedPrice

end Merged_R6960Low6969SharedPrice

-- merged module R6960Low6969SurfaceLinearFour
section Merged_R6960Low6969SurfaceLinearFour
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6969SharedPrice
open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)
open Low6969Prices (taylorLength)
open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)
theorem surface_eq_weights_of_signed (kind : Surface) (f : Shape) (b j t : ℤ)
    (hb : 0 ≤ b) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (h : ∀ q : Shape, (surface kind f q : ℤ) = b*q.b + j*q.j + t*q.t) (q : Shape) :
    surface kind f q = (weights kind f).b*q.b + (weights kind f).j*q.j +
      (weights kind f).t*q.t := by
  have hn (u : Shape) : surface kind f u = b.toNat*u.b + j.toNat*u.j + t.toNat*u.t := by
    apply Int.ofNat.inj
    change (surface kind f u : ℤ) = ((b.toNat*u.b + j.toNat*u.j + t.toNat*u.t : ℕ) : ℤ)
    rw [h u]
    push_cast
    rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg ht]
  have hw : weights kind f = ⟨b.toNat,j.toNat,t.toNat⟩ := by
    unfold weights
    simp only [hn ⟨1,0,0⟩, hn ⟨1,1,0⟩, hn ⟨3,3,1⟩, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel_left]
    congr 1
    omega
  rw [hw]
  exact hn q
private theorem signed_four_linear (q p r s : Shape) :
    signedMixed q p r s = signedMixed ⟨1,0,0⟩ p r s*q.b +
      signedMixed ⟨0,1,0⟩ p r s*q.j + signedMixed ⟨0,0,1⟩ p r s*q.t := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero,
    Nat.cast_one]
  ring
theorem surface_ordinary_eq_weights {f : Shape} (hf : Valid f) (q : Shape) :
    surface .ordinary f q = (weights .ordinary f).b*q.b + (weights .ordinary f).j*q.j +
      (weights .ordinary f).t*q.t := by
  let p := f.chamber
  let r := chart (taylorLength+1) p
  let s := chart (taylorLength+2) p
  have hp : K1_13_8_2.Chamber p := ⟨le_max_right _ _,hf.2.1⟩
  have hr : K1_13_8_2.Chamber r := K1_13_7_1.chart_chamber _ _
  have hs : K1_13_8_2.Chamber s := K1_13_7_1.chart_chamber _ _
  have hnonneg (u : Shape) : 0 ≤ signedMixed u r s p := signed_nonneg u r s p hr hs hp
  refine surface_eq_weights_of_signed .ordinary f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedMixed p u r s).toNat : ℤ) = _
  rw [signed_rotate, Int.toNat_of_nonneg (hnonneg u)]
  exact signed_four_linear u r s p
end Low6969SharedPrice

end Merged_R6960Low6969SurfaceLinearFour

end Merged_Low6969SurfaceLinearFour
end Z6969Source2284

-- H2298 precise third-cut fee
namespace Low6969SharedThirdCut
open K1_13 (Shape chart)
open Low6969Prices (taylorLength primaryBox)

def preciseFee (x : Shape) (l : ℕ) : ℕ :=
  min (Low6969SharedPrice.nonsharedFee x l)
    (K1_13.ceilDiv
      ((Low6969Prices.errors * (chart (taylorLength+2) x.chamber).b +
        Low6969Prices.incidenceGap) * (x.b * primaryBox.b * primaryBox.b))
      (Low6969Prices.incidenceGap * l))



end Low6969SharedThirdCut
