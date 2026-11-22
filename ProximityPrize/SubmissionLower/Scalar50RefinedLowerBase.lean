import ProximityPrize.SubmissionLower.Scalar70LeadingLower

set_option Elab.async false
set_option autoImplicit true

namespace ScalarRefined

open K1_13 (Row Shape indexDegree)
open scoped BigOperators

abbrev physicalDegree : ℕ := 131071
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev lowBox := Scalar70LeadingLower.lowBox

def lowerWidth (i : Fin 3) : ℕ := ![72,75,113] i
def lowerIndex (i : Fin 3) : ℕ := ![21,22,35] i
def lowerTop (i : Fin 3) : ℕ := ![10,10,16] i

abbrev graphBox (top : Fin 3) : Shape :=
  ⟨lowerWidth top, lowerIndex top + 1, min (lowerTop top + 1) ((lowerIndex top + 1) / 2)⟩

def liftedBox (top : Fin 3) (L : ℕ) : Shape :=
  let k := L - 4
  let j := 3 + k * (lowerIndex top - 1)
  ⟨1 + k * (lowerWidth top - 1), j, min (2 + k * lowerTop top) (j / 2)⟩

def mixedCoefficients (top : Fin 3) : ℕ × ℕ × ℕ :=
  ![(10994828707253,59475073180271,31981201),
    (12059952023115,61605351793196,6545313498489),
    (30854215897357,144513111708402,19584452660769)] top

def mixedBudget (top : Fin 3) : ℕ :=
  let (b,j,t) := mixedCoefficients top
  b * lowerWidth top + j * lowerIndex top + t * lowerTop top

structure SecondFactors (top : Fin 3) {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  total : (∑ i, (f i).totalDegree) ≤ lowerWidth top
  index : (∑ i, indexDegree (f i)) ≤ lowerIndex top
  coordinate : (∑ i, (f i).degreeOf 2) ≤ lowerTop top

abbrev Whole := Scalar70LeadingLower.Whole
end ScalarRefined

namespace ScalarRefined_1
noncomputable section
open ScalarRefined (taylorLength physicalDegree graphBox liftedBox mixedBudget)
open K1_13 (Row Geom atJet)
open K1_13_5 (RegularAt)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph regularLocus jetPoint genericRow)

abbrev CoefficientIdeal := Scalar70LeadingLower_1.CoefficientIdeal
abbrev CurveIndex := Scalar70LeadingLower_1.CurveIndex
abbrev coefficientPoint := Scalar70LeadingLower_1.coefficientPoint
abbrev oldCut := Scalar70LeadingLower_1.oldCut
abbrev oldNext := Scalar70LeadingLower_1.oldNext
abbrev oldCutIdeal := Scalar70LeadingLower_1.oldCutIdeal
abbrev properComponents {n : ℕ} (f : Fin n → Row 3) := Scalar70LeadingLower_1.properComponents f
abbrev componentLength := Scalar70LeadingLower_1.componentLength
abbrev nextCutLocus := Scalar70LeadingLower_1.nextCutLocus
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) :=
  fun i => MvPolynomial.eval (K1_13_5_4.graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (K1_13_5.separant f)) ^ (taylorLength - 4)
open scoped BigOperators Polynomial
structure LiftedChart (top : Fin 3) (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) (graphBox top) 1
  cut_box : InLiftedBox cut (liftedBox top (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox top (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox top taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections (top : Fin 3) {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart top (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget top
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
end
end ScalarRefined_1
section
namespace ScalarRefined_1
noncomputable section
variable {top : Fin 3}
open ScalarRefined (physicalDegree taylorLength)
open ScalarRefined (SecondFactors)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant)
open ScalarRefined (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open private mul_bound K1_13_5_4_1_1.partialFlow_bound liftSep_eq liftedStep_bound generic_bound
  totalWeight indexWeight topWeight heightWeight lift_weight fits
  from ProximityPrize.SubmissionLower.Fast070
open private represents from ProximityPrize.SubmissionLower.Fast076
open private atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero
  actual_zero_of_represents from ProximityPrize.SubmissionLower.Fast048
local notation "W" => weightedTotalDegree
private def coefficientNumerator (m : ℕ) (f : Row 3) (i : Fin m) : GeoRow 4 :=
  ∑ j : Fin m, MvPolynomial.C (((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i.val) *
    genericRow (padJet f (m - 4) j.val)
private def cut (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 3))
private def next (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 2))
private theorem padded_bound (w : Fin 4 → ℕ) {initial step m : ℕ} {f : Row 3}
    (hinit : ∀ i, w i ≤ initial) (hs : W w (liftSep f) ≤ step)
    (hthird : ∀ k, W w (thirdNumerator f k) ≤ w 3 + k * step) (j : Fin m) :
    W w (padJet f (m - 4) j.val) ≤ initial + (m - 4) * step := by
  unfold padJet jetNumerator
  have hpow := (weightedTotalDegree_pow_le w (liftSep f) (m - 4 - (j.val - 3))).trans
    (Nat.mul_le_mul_left _ hs)
  split_ifs with hj
  · have hz : j.val - 3 = 0 := by omega
    rw [hz, Nat.sub_zero] at hpow ⊢
    exact (mul_bound hpow ((weight_X_le w _).trans (hinit _))).trans_eq (Nat.add_comm _ _)
  · have hsum : (m - 4 - (j.val - 3)) + (j.val - 3) = m - 4 := by
      have hj' := j.isLt
      omega
    calc
      _ ≤ (m - 4 - (j.val - 3)) * step + (w 3 + (j.val - 3) * step) :=
        mul_bound hpow ((weight_const_mul_le w _ _).trans (hthird _))
      _ = w 3 + ((m - 4 - (j.val - 3)) + (j.val - 3)) * step := by ring
      _ ≤ _ := by rw [hsum]; exact Nat.add_le_add_right (hinit 3) _
private theorem weight_bounds (w : Fin 4 → ℕ) (base delta step initial m : ℕ) {f : Row 3}
    (hf : W w (liftRaw f) ≤ base)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + delta)
    (hsep : base - w 2 + delta ≤ step) (hvelocity : base + 2 * delta ≤ w 3 + step)
    (hinit : ∀ i, w i ≤ initial) :
    W w (graph f) ≤ base + delta ∧
    (∀ k, W w (genericRow (thirdNumerator f k)) ≤ w 3 + k * step) ∧
    (∀ i, W w (coefficientNumerator m f i) ≤ initial + (m - 4) * step) := by
  have hg : W w (graphRaw f) ≤ base + delta := by
    rw [← partialFlow_lift]
    exact K1_13_5_4_1_1.partialFlow_bound w hshift hf
  have hs : W w (liftSep f) ≤ base - w 2 := by
    rw [liftSep_eq]
    exact (weightedTotalDegree_pderiv_le_sub w 2 _).trans (Nat.sub_le_sub_right hf _)
  have hu : W w (thirdVelocityNumerator f) ≤ w 3 + step := by
    unfold thirdVelocityNumerator
    exact ((weight_const_mul_le w _ _).trans (K1_13_5_4_1_1.partialFlow_bound w hshift hg)).trans (by omega)
  have hthird (k : ℕ) : W w (thirdNumerator f k) ≤ w 3 + k * step := by
    induction k with
    | zero =>
      simpa only [thirdNumerator, Nat.zero_mul, Nat.add_zero] using weight_X_le (R := Geom[X]) w 3
    | succ k ih =>
      rw [thirdNumerator, Nat.succ_mul, ← Nat.add_assoc]
      exact liftedStep_bound w hshift ih hs hsep hu k
  refine ⟨?_, fun k => (generic_bound w _).trans (hthird k), ?_⟩
  · rw [← generic_graph]
    exact (generic_bound w _).trans hg
  · intro i
    unfold coefficientNumerator
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sum_mem
    intro j _
    exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_const_mul_le w _ _).trans ((generic_bound w _).trans
        (padded_bound w hinit (hs.trans ((Nat.le_add_right _ _).trans hsep)) hthird j)))
private abbrev sharpB : Fin 4 → ℕ := ![1,1,1,1]
private abbrev sharpJ : Fin 4 → ℕ := ![0,1,2,3]
private abbrev sharpT : Fin 4 → ℕ := ![0,0,1,2]

private theorem fit_sharp {p : GeoRow 4} (L H : ℕ)
    (hb : W sharpB p ≤ 1 + (L - 4) * (ScalarRefined.lowerWidth top - 1))
    (hj : W sharpJ p ≤ 3 + (L - 4) * (ScalarRefined.lowerIndex top - 1))
    (ht : W sharpT p ≤ 2 + (L - 4) * ScalarRefined.lowerTop top)
    (hh : W heightWeight p ≤ H) :
    InLiftedBox p (liftedBox top L) H := by
  intro a ha
  have hB := (le_weightedTotalDegree sharpB ha).trans hb
  have hJ := (le_weightedTotalDegree sharpJ ha).trans hj
  have hT := (le_weightedTotalDegree sharpT ha).trans ht
  have hH := (le_weightedTotalDegree heightWeight ha).trans hh
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm] at hB hJ hT hH
  simp only [liftedBox]
  exact ⟨by omega, by omega, le_min (by omega) (by omega), hH⟩

private theorem support (f : Row 3)
    (hb : f.totalDegree ≤ (ScalarRefined.lowerWidth top)) (hj : indexDegree f ≤ (ScalarRefined.lowerIndex top)) (ht : f.degreeOf 2 ≤ (ScalarRefined.lowerTop top)) :
    InLiftedBox (graph f) (graphBox top) 1 ∧
    InLiftedBox (cut taylorLength f) (liftedBox top (taylorLength + 1)) (taylorLength - 1) ∧
    InLiftedBox (next taylorLength f) (liftedBox top (taylorLength + 2)) taylorLength ∧
    ∀ i, InLiftedBox (coefficientNumerator taylorLength f i) (liftedBox top taylorLength) (taylorLength - 2) := by
  have htotal : W totalWeight (liftRaw f) ≤ (ScalarRefined.lowerWidth top) := by
    rw [lift_weight, show totalWeight ∘ Fin.castSucc = (1 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_one]
    exact hb
  have hindex : W indexWeight (liftRaw f) ≤ (ScalarRefined.lowerIndex top) := by
    rw [lift_weight, show indexWeight ∘ Fin.castSucc = (Fin.val : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, ← K1_13_1.indexDegree_eq]
    exact hj
  have htop : W topWeight (liftRaw f) ≤ (ScalarRefined.lowerTop top) := by
    rw [lift_weight, show topWeight ∘ Fin.castSucc = Pi.single (2 : Fin 3) 1 from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_piSingle]
    exact ht
  have hheight : W heightWeight (liftRaw f) ≤ 0 := by
    rw [lift_weight, show heightWeight ∘ Fin.castSucc = (0 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree, Finset.sup_le_iff]
    intro a _
    simp [Finsupp.weight_eq_sum]
  obtain ⟨bg, _, _⟩ := weight_bounds totalWeight (ScalarRefined.lowerWidth top) 0 (ScalarRefined.lowerWidth top) 1 taylorLength htotal
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨jg, _, _⟩ := weight_bounds indexWeight (ScalarRefined.lowerIndex top) 1 (ScalarRefined.lowerIndex top + 2) 2 taylorLength hindex
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨tg, _, _⟩ := weight_bounds topWeight (ScalarRefined.lowerTop top) 1 (ScalarRefined.lowerTop top + 2) 1 taylorLength htop
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨hg, hn, hc⟩ := weight_bounds heightWeight 0 1 1 1 taylorLength hheight
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  have hGraphB : W totalWeight (graph f) ≤ ScalarRefined.lowerWidth top := bg
  have hGraphH : W heightWeight (graph f) ≤ 1 := hg
  have B0 : W sharpB (liftRaw f) ≤ ScalarRefined.lowerWidth top := by
    rw [lift_weight, show sharpB ∘ Fin.castSucc = (1 : Fin 3 → ℕ) from by decide, weightedTotalDegree_one]
    exact hb
  have J0 : W sharpJ (liftRaw f) ≤ ScalarRefined.lowerIndex top := by
    rw [lift_weight, show sharpJ ∘ Fin.castSucc = (Fin.val : Fin 3 → ℕ) from by decide, ← K1_13_1.indexDegree_eq]
    exact hj
  have T0 : W sharpT (liftRaw f) ≤ ScalarRefined.lowerTop top := by
    rw [lift_weight, show sharpT ∘ Fin.castSucc = Pi.single (2 : Fin 3) (1 : ℕ) from by decide,
      weightedTotalDegree_piSingle]
    exact ht
  obtain ⟨_, bN, bC⟩ := weight_bounds sharpB (ScalarRefined.lowerWidth top) 0
    (ScalarRefined.lowerWidth top - 1) 1 taylorLength B0 (by decide) (by fin_cases top <;> decide)
    (by fin_cases top <;> decide) (by decide)
  obtain ⟨_, jN, jC⟩ := weight_bounds sharpJ (ScalarRefined.lowerIndex top) 1
    (ScalarRefined.lowerIndex top - 1) 3 taylorLength J0 (by decide) (by fin_cases top <;> decide)
    (by fin_cases top <;> decide) (by decide)
  obtain ⟨_, tN, tC⟩ := weight_bounds sharpT (ScalarRefined.lowerTop top) 1
    (ScalarRefined.lowerTop top) 2 taylorLength T0 (by decide) (by fin_cases top <;> decide)
    (by fin_cases top <;> decide) (by decide)
  exact ⟨by simpa only [graphBox] using fits hGraphB jg tg hGraphH,
    fit_sharp (taylorLength + 1) _ (bN (taylorLength - 3)) (jN _) (tN _) ((hn _).trans (by decide)),
    fit_sharp (taylorLength + 2) _ (bN (taylorLength - 2)) (jN _) (tN _) ((hn _).trans (by decide)),
    fun i => fit_sharp taylorLength _ (bC i) (jC i) (tC i) ((hc i).trans (by decide))⟩
private theorem atJet_padded (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0)
    {m : ℕ} (hm : m < K1.p) (j : Fin m) :
    atJet (padJet f (m - 4) j.val) S =
      atJet (separant f) S ^ (m - 4) * hasseDeriv j.val S := by
  have hj := j.isLt
  exact atJet_padJet f S hf (m - 4) j.val (by omega) (hj.trans hm)
private theorem reconstruct_actual {f : Row 3} {S : Geom[X]} (hdeg : S.natDegree < taylorLength)
    (hS : RegularAt 2 f S) :
    reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  funext i
  rw [reconstruct, graphPoint_of_actual hS, eval_genericRow]
  let s := genericCoeff (atJet (separant f) S)
  have hs : s ≠ 0 := genericCoeff_ne_zero hS.2
  have hp : taylorLength < K1.p := by decide
  unfold coefficientNumerator
  rw [map_sum]
  change (∑ j : Fin taylorLength, MvPolynomial.eval (jetPoint S) _) /
    s ^ (taylorLength - 4) = _
  simp only [map_mul, MvPolynomial.eval_C, eval_genericRow, atJet_padded f S hS.1 hp, map_pow]
  change _ = algebraMap Geom GeometricX (S.coeff i)
  rw [div_eq_iff (pow_ne_zero _ hs), ← taylor_coefficients_aux S taylorLength hdeg i.val,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change _ * (s ^ (taylorLength - 4) * _) = _ * s ^ (taylorLength - 4)
  rw [mul_comm (s ^ (taylorLength - 4)), ← mul_assoc]
private theorem actual {f : Row 3}
    (hcut : RepresentsOnGraph f (oldCut f) (cut taylorLength f))
    (hnext : RepresentsOnGraph f (oldNext f) (next taylorLength f))
    (S : Geom[X]) (hdeg : S.natDegree ≤ physicalDegree) (hS : RegularAt 2 f S) :
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  have hlength (d m : ℕ) (hd : d < m) (hm : 4 ≤ m) : d - 3 < m - 3 := by omega
  have hdeg' : S.natDegree < taylorLength := Nat.lt_succ_of_le hdeg
  have hfirst := hlength S.natDegree taylorLength hdeg' (by decide)
  have hsecond : S.natDegree - 3 < taylorLength - 2 :=
    hfirst.trans_le (Nat.sub_le_sub_left (by decide : 2 ≤ 3) _)
  refine ⟨actual_zero_of_represents hS hcut ?_, actual_zero_of_represents hS hnext ?_,
    reconstruct_actual hdeg' hS⟩
  · rw [cut, eval_genericRow, third_atJet_zero hS.1 _ hfirst, map_zero]
  · rw [next, eval_genericRow, third_atJet_zero hS.1 _ hsecond, map_zero]
theorem lifted_chart (n : ℕ) (f : Fin n → Row 3) (hf : SecondFactors top f) (i : Fin n) :
    Nonempty (LiftedChart top (f i)) := by
  have hb := (Finset.single_le_sum (f := fun k => (f k).totalDegree)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj := (Finset.single_le_sum (f := fun k => indexDegree (f k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht := (Finset.single_le_sum (f := fun k => (f k).degreeOf 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.coordinate
  obtain ⟨hg, he, hn, hc⟩ := support (f i) hb hj ht
  have hrep : RepresentsOnGraph (f i) (oldCut (f i)) (cut taylorLength (f i)) :=
    represents (f i) (taylorLength - 3)
  have hrep' : RepresentsOnGraph (f i) (oldNext (f i)) (next taylorLength (f i)) :=
    represents (f i) (taylorLength - 2)
  exact ⟨{
    cut := cut taylorLength (f i)
    next := next taylorLength (f i)
    numerator := coefficientNumerator taylorLength (f i)
    graph_box := hg
    cut_box := he
    next_box := hn
    coefficient_box := hc
    cut_represents := hrep
    next_represents := hrep'
    actual := actual hrep hrep'
  }⟩
end
end ScalarRefined_1
end
