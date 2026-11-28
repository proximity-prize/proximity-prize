import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast058

set_option Elab.async false

-- merged module Fast059
section Merged_Fast059
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option maxHeartbeats 450000
private def bbPack : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + 65536 * bbPack n (fun i => f (i+1))
private structure BBVec where
  atOffset : ℕ → ℕ
  word : ℕ
  limit : ℕ
  correct : bbPack 138 atOffset = word
  bound : ∀ i, atOffset i ≤ limit
end K1_13_1_1
end
section
namespace K1_13_2_3_5
namespace DataC2344
open K1_13_2_3
open K1_13_2_3_5 (unpack)
set_option maxHeartbeats 3000000
set_option maxRecDepth 50000
private structure CEntry where
  row : Row
  cut : Nat
end DataC2344
end K1_13_2_3_5
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open K1_13_2_3_5
open K1_13_2_3_6 (sumFrom)
private def dRegion (s j a b c : ℕ) : Prop :=
  3162 ≤ s ∧ s ≤ 3213 ∧ 3383 ≤ s+j ∧ a+4*c ≤ 512 ∧ b ≤ 256 ∧ a ≤ b+384
private instance (s j a b c : ℕ) : Decidable (dRegion s j a b c) := by
  unfold dRegion
  infer_instance
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end K1_13_2_3_6
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7
local notation "W" => MvPolynomial.weightedTotalDegree
theorem topPartial_bound (w : Fin 4 → ℕ) (P : Row 4) :
    W w (separant P) ≤ W w P - w 3 :=
  weightedTotalDegree_pderiv_le_sub w 3 P
private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + (B - w 3) + Δ := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (partialFlow_bound w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h : w 3 ≤ d
    · have hp := (topPartial_bound w P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (partialFlow_bound w Δ hshift g hg) hp).trans (by omega))
    · rw [separant, pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero, weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem step_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) (a : ℕ) :
    W w (clearedStep g a P) ≤ d + (2 * (B - w 3) + Δ) := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (flow_bound w Δ hshift hB hg hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [← map_natCast (MvPolynomial.C : (Polynomial Geom) →+* Row 4)]
    exact (Nat.add_le_add ((weight_const_mul_le _ _ _).trans (flow_bound w Δ hshift hB hg hsep))
      hP).trans (by omega)
theorem jet_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {g : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hg : W w g ≤ B) (n : ℕ) :
    W w (jetNumerator g n) ≤ w 0 + n * (2 * (B - w 3) + Δ) := by
  induction n with
  | zero => simpa only [jetNumerator, zero_mul, add_zero] using weight_X_le (R := (Polynomial Geom)) w 0
  | succ n ih =>
    simpa only [jetNumerator, Nat.add_mul, one_mul, Nat.add_assoc] using
      step_bound w Δ hshift hB hg ih (2 * n)
def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)
private def numerator (L : ℕ) (g : Row 4) (i : TaylorIndex) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)
private def taylorChart (L : ℕ) (g : Row 4) : TaylorChart where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
  initial i := by
    unfold numerator toGeneric
    have hi : (i.castLE (by decide : 4 ≤ taylorLength)).val < 4 := i.isLt
    rw [dite_eq_left hi, map_mul, MvPolynomial.map_X]
    rfl
theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {g : Row 4} {B : ℕ} (hg : W w g ≤ B) :
    W w (denominator L g) ≤ 2 * L * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans
    (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
private theorem numerator_bound {L : ℕ} (hL : taylorLength ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : TaylorIndex) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le.trans hL
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hg)).trans
        (Nat.le_add_right _ _))
  · have hp := (weightedTotalDegree_pow_le w (separant g) (2 * (L - i.val))).trans
      (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add hp (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)
private theorem chart_box {L : ℕ} (hL : taylorLength ≤ L) (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    (taylorChart L g).Fits (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ p.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : w 3 = 1 := by decide
  have pkg (P : Row 4) (hb' : W 1 P ≤ 1 + 2 * L * (p.b - 1))
      (hj' : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
      (ht' : W w P ≤ 2 * L * (p.t - 1) + L + 1) :
      GeoFits (toGeneric P) (chart L p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ _
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  constructor
  · apply pkg
    · exact (denominator_bound L _ h₁).trans (Nat.le_add_left _ _)
    · exact (denominator_bound L _ h₂).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · have h := denominator_bound L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro i
    apply pkg
    · have h := numerator_bound hL 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb h₁ i
      change W 1 (numerator L g i) ≤ 1 + 2 * L * (p.b - 1) + L * 0 at h
      simpa only [mul_zero, add_zero] using h
    · have h := numerator_bound hL Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂ i
      change W Fin.val (numerator L g i) ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
      simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
    · have hwle : w 3 ≤ p.t := hw3.symm ▸ ht
      have h := numerator_bound hL w 1 1 hshift hw hwle h₃ i
      simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
theorem ordinary_eq_hasse (S : (Polynomial Geom)) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
theorem evalGeneric_toGeneric (S : (Polynomial Geom)) (P : Row 4) :
    evalGeneric S (toGeneric P) = genericCoeffs (atJet P S) := by
  exact (MvPolynomial.map_eval genericCoeffs (jet S) P).symm
private theorem chart_recovers {L : ℕ} (hL : taylorLength ≤ L) (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (hr : RegularAt g S) : (taylorChart L g).Recovers S := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [evalGeneric_toGeneric]
    apply (map_ne_zero_iff _ genericCoeffs_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero
          (i.isLt.trans (by decide : taylorLength < K1.p))), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        have hi : i.val ≤ L := i.isLt.le.trans hL
        rw [← Nat.mul_add, Nat.sub_add_cancel hi]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by
          rw [hinv, one_mul, ← pow_add, hpow, hden]
theorem exists_chart (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    ∃ C : TaylorChart, C.Fits (chart (taylorLength + 4) p) ∧
      ∀ S : (Polynomial Geom), atJet g S = 0 → RegularAt g S → C.Recovers S :=
  ⟨taylorChart (taylorLength + 4) g, chart_box (Nat.le_add_right _ _) g p hB hp ht,
    chart_recovers (Nat.le_add_right _ _) g⟩
end
end K1_13_7_1
end
section
namespace K1_13_7_4_2
open K1_13_7
abbrev Local (q : PrimeSpectrum Lower) := Localization.AtPrime q.asIdeal
def remainingIdeal {R ι : Type*} [CommRing R] (f : ι → R) (i : ι) : Ideal R :=
  Ideal.span (f '' {j | j ≠ i})
end K1_13_7_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4
open scoped Polynomial
abbrev FreshField := FractionRing (Polynomial GeometricX)
abbrev FreshJetRing := MvPolynomial (Fin 3) FreshField
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) FreshField
abbrev FreshJetIdeal := Ideal FreshJetRing
def freshArgument : FreshField := algebraMap (Polynomial GeometricX) FreshField Polynomial.X
def freshCoeff : (Polynomial Geom) →+* FreshField :=
  (algebraMap (Polynomial GeometricX) FreshField).comp
    (Polynomial.mapRingHom (algebraMap Geom GeometricX))
def freshRow (g : Row 3) : FreshJetRing := MvPolynomial.map freshCoeff g
def freshHypersurface (f : Row 3) : FreshJetIdeal := Ideal.span {freshRow f}
def freshDivisor (f : Row 3) : FreshJetIdeal :=
  freshHypersurface f ⊔ Ideal.span {freshRow (oldCut f)}
def extendIdeal (Q : CoefficientIdeal) : Ideal FreshCoeffRing :=
  Q.map (MvPolynomial.map (algebraMap GeometricX FreshField))
def freshProjection : FreshJetRing →ₐ[FreshField] FreshCoeffRing :=
  MvPolynomial.aeval fun j => K1_13_5_5.jetForm freshArgument j.val
def freshImage (Q : CoefficientIdeal) : FreshJetIdeal := (extendIdeal Q).comap freshProjection
def FreshBirational (Q : CoefficientIdeal) : Prop :=
  ∀ j : Fin taylorLength, ∃ u v : FreshJetRing,
    v ∉ freshImage Q ∧
      freshProjection v * MvPolynomial.X j - freshProjection u ∈ extendIdeal Q
structure FreshChart (f : Row 3) (Q : CoefficientIdeal) : Prop where
  extended_prime : (extendIdeal Q).IsPrime
  on_divisor : freshDivisor f ≤ freshImage Q
  regular : freshRow (separant f) ∉ freshImage Q
  birational : FreshBirational Q
end
end K1_13_5_4_4
end
section
namespace K1_13_7_2_1
open K1_13 K1_13_6 K1_13_7_2
def LocalGenerators (f : Row 4) (q : Row 3) (surface : Ideal GeoJets)
    (hp : surface.IsPrime) : Prop :=
  letI := hp
  let A := Localization.AtPrime surface
  (intersectionIdeal f (liftLower q)).map (algebraMap GeoJets A) = IsLocalRing.maximalIdeal A
end K1_13_7_2_1
end

end Merged_Fast059

-- merged module Fast061
section Merged_Fast061
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3_5
open K1_13_2_3_5 (unpack)
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end K1_13_2_3_5
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3 K1_13_2_3_5
open K1_13_2_3_6 (sumFrom)
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3 K1_13_2_3_5
open K1_13_2_3_6 (sumFrom)
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2_3_6 (sumFrom)
end K1_13_2_3_6
end
section
namespace K1_13_2_3_7
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private def formula (D S : ℕ → ℕ) (t j : ℕ) :=
  let b := 1136-t
  let h := b-j
  let z := 1650-j
  let v := b-4*j
  let r := (1139-t)/4
  let common := D h + D z
  let chosen := D 1651 + S (621-2*t-8*j) + S (622-2*t-5*j) + D (v-3) -
    (common + S (622-2*t-7*j) + S (620-2*t-7*j))
  let original := D 1651 + D (b-3*r-j) + S (r-j) - common
  Nat.min (D 1651 - D z) chosen - original
private theorem sum_split (f : ℕ → ℕ) (a b : ℕ) :
    rangeSum f (a+b) = rangeSum f a + rangeSum (fun k => f (a+k)) b := by
  induction b with
  | zero => simp [rangeSum]
  | succ b ih =>
    change rangeSum f (a+b) + f (a+b) = _
    rw [ih]
    simp [rangeSum, Nat.add_assoc]
private theorem sum_zero {n : ℕ} {f : ℕ → ℕ} (h : ∀ k < n, f k = 0) :
    rangeSum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rangeSum, ih (fun k hk => h k (by omega)), h n (by omega), Nat.add_zero]
private abbrev radix : ℕ := 1099511627776
private def digits (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => digits f n * radix + f n
private def units (n : ℕ) := (radix ^ n - 1)/(radix-1)
private structure Checked (n : ℕ) (f : ℕ → ℕ) (value bound : ℕ) : Prop where
  val_eq : digits f n = value
  bounded : ∀ i < n, f i ≤ bound
end K1_13_2_3_7
end
section
namespace K1_13_6_1_4_3
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_7_1 K1_13_7_1_1
open MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (J : Ideal GeoJets) (a h : Shape), FullChamber a → FullChamber h →
    (∀ P, J.IsMinimalPrime P → ringKrullDim (GeoJets ⧸ P) ≤ 2) →
    Module.Finite (PairSectionField a h) (SliceAlgebra J a h)
def c2 : Prop :=
  ∀ (J : Ideal GeoJets) (a h : Shape), FullChamber a → FullChamber h →
    Module.Finite (PairSectionField a h) (SliceAlgebra J a h) →
    ∀ (surfaces : Finset (Ideal GeoJets)) (v : Ideal GeoJets → ℕ),
      (∀ P ∈ surfaces, ∃ hP : J.IsMinimalPrime P, cycleLength J P hP.isPrime = (v P : ℕ∞)) →
      (∑ P ∈ surfaces, v P * surfaceDegree P a h) ≤
        Module.finrank (PairSectionField a h) (SliceAlgebra J a h)
def c3 : Prop :=
  ∀ (p q a h : Shape), Chamber p → Chamber q → Chamber a → Chamber h →
    ∀ (F G U V : SliceJets a h), CapSupported F p → CapSupported G q →
      CapSupported U a → CapSupported V h →
      Module.Finite (PairSectionField a h) (SliceJets a h ⧸ Ideal.span {F, G, U, V}) →
      (Module.finrank (PairSectionField a h)
        (SliceJets a h ⧸ Ideal.span {F, G, U, V}) : ℝ) ≤
        mixedVolume (cap p) (cap q) (cap a) (cap h)
private theorem full_scale_six {p : Shape} (hp : FullChamber p) :
    FullChamber (p.scale 6) := by
  obtain ⟨⟨hb, hj⟩, ht⟩ := hp
  change (6 * p.j ≤ 6 * p.b ∧ 3 * (6 * p.t) ≤ 6 * p.j) ∧ 0 < 6 * p.t
  omega
private theorem supports_section {σ : Type*} (p : Shape) (ι : SectionIndex p → σ) :
    CapSupported (sectionWith p ι) p := by
  classical
  intro e he
  unfold sectionWith at he
  obtain ⟨m, hm, he⟩ := Finset.mem_biUnion.mp (support_sum he)
  obtain ⟨hb, hj, ht⟩ := (Finset.mem_filter.mp hm).2
  rw [MvPolynomial.prod_X_pow, C_mul_monomial] at he
  have heq := Finset.mem_singleton.mp (support_monomial_subset he)
  have heval (i : Fin 4) : e i = (m i).val := by
    rw [heq]
    simp [Finsupp.indicator]
  simp only [Fin.sum_univ_four] at hb hj
  have hindex : (m 1).val + 2 * (m 2).val + 3 * (m 3).val ≤ p.j := by
    change 0 * (m 0).val + 1 * (m 1).val + 2 * (m 2).val + 3 * (m 3).val ≤ p.j at hj
    omega
  change (∀ i, 0 ≤ (e i : ℝ)) ∧ (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ p.b ∧
    (e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ p.j ∧ (e 3 : ℝ) ≤ p.t
  simp only [heval]
  exact ⟨fun _ => Nat.cast_nonneg _, by exact_mod_cast hb,
    by exact_mod_cast hindex, by exact_mod_cast ht⟩
private theorem supports_extend {F : GeoJets} {p : Shape} (hF : GeoFits F p)
    (a h : Shape) : CapSupported (extendCoeffs a h F) p :=
  fun e he => supportedIn_cap hF e (support_map_subset _ _ he)
private theorem slice_pair_ideal (F G : GeoJets) (a h : Shape) :
    (pairIdeal F G).map (extendCoeffs a h) ⊔ Ideal.span {firstSection a h, secondSection a h} =
      Ideal.span {extendCoeffs a h F, extendCoeffs a h G, firstSection a h, secondSection a h} := by
  rw [pairIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, ← Ideal.span_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto
private theorem scaled_difference {F : Set RealPoint → ℝ} {G : Shape → ℤ}
    (heq : ∀ x : Shape, Chamber x → 32 * F (cap x) = (G x : ℝ))
    {a : Shape} (ha : Chamber a) (x : Shape) (hx : Chamber x) :
    32 * bodyDifference F (cap a) (cap x) = (difference G a x : ℝ) := by
  rw [bodyDifference, difference, Int.cast_sub, mul_sub, ← cap_add hx ha,
    heq _ (chamber_plus hx ha), heq _ hx]
private def signedMixed (p q a h : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) a) h ⟨0, 0, 0⟩
private theorem mixed_eq (p q a h : Shape)
    (hp : Chamber p) (hq : Chamber q) (ha : Chamber a) (hh : Chamber h) :
    32 * mixedVolume (cap p) (cap q) (cap a) (cap h) = (signedMixed p q a h : ℝ) := by
  have hv := scaled_difference
    (F := fun P => (volume P).toReal) (G := volume32) cap_volume32 hp
  have hm := scaled_difference (scaled_difference (scaled_difference hv hq) ha) hh
    ⟨0, 0, 0⟩ (⟨by decide, by decide⟩ : Chamber ⟨0, 0, 0⟩)
  rw [cap_zero] at hm
  exact hm
private theorem mixed_scale_six (p q a h : Shape) :
    signedMixed p q (a.scale 6) (h.scale 6) = 36 * signedMixed p q a h := by
  simp only [signedMixed, difference, volume32, Shape.plus, Shape.scale,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]
  ring
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_1_4.c3 := by
  intro F G p q a h hF _ hproper hp hq ha hh hFp hGq surfaces v hsurfaces
  let A := a.scale 6
  let H := h.scale 6
  let J := pairIdeal F G
  let d := Module.finrank (PairSectionField A H) (SliceAlgebra J A H)
  have hA : FullChamber A := full_scale_six ha
  have hH : FullChamber H := full_scale_six hh
  have hfin := h1 J A H hA hH (fun P hP => (pair_dimension hF hproper hP).le)
  have hcycle := h2 J A H hA hH hfin surfaces v hsurfaces
  have hfin' : Module.Finite (PairSectionField A H)
      (SliceJets A H ⧸ Ideal.span {extendCoeffs A H F, extendCoeffs A H G,
        (firstSection A H), secondSection A H}) := by
    rw [← slice_pair_ideal]
    exact hfin
  have hsparse := h3 p q A H hp.1 hq.1 hA.1 hH.1
    (extendCoeffs A H F) (extendCoeffs A H G) (firstSection A H) (secondSection A H)
    (supports_extend hFp _ _) (supports_extend hGq _ _)
    (supports_section _ _) (supports_section _ _) hfin'
  rw [← slice_pair_ideal] at hsparse
  change (d : ℝ) ≤ _ at hsparse
  have hb := mul_le_mul_of_nonneg_left hsparse (by norm_num : (0 : ℝ) ≤ 32)
  rw [mixed_eq p q A H hp.1 hq.1 hA.1 hH.1, mixed_scale_six, Int.cast_mul] at hb
  have hz : (↑(32 * d) : ℤ) ≤ 36 * signedMixed p q a h := by exact_mod_cast hb
  have hn : 0 ≤ signedMixed p q a h := by
    have hnonneg : (0 : ℤ) ≤ ↑(32 * d) := Int.natCast_nonneg _
    omega
  have hd : 32 * d ≤ 36 * mixed32 p q a h := by
    change 32 * d ≤ 36 * (signedMixed p q a h).toNat
    exact_mod_cast (show (↑(32 * d) : ℤ) ≤ ↑(36 * (signedMixed p q a h).toNat) by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.toNat_of_nonneg hn] using hz)
  exact (Nat.mul_le_mul_left 32 hcycle).trans hd
end K1_13_6_1_4_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_13_6_1_4_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_3
open MvPolynomial
open scoped BigOperators
private theorem trdeg_le_of_dim_le (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {n : ℕ} (hd : ringKrullDim A ≤ n) :
    Algebra.trdeg k A ≤ n := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin s) k
  let : Algebra B A := g.toRingHom.toAlgebra
  have : IsScalarTower k B A := .of_algebraMap_eq fun c => (g.commutes c).symm
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  have : Algebra.IsIntegral B A := algebraMap_isIntegral_iff.mp hint
  have hdB : ringKrullDim B = s := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (le_of_eq hdB.symm)
  obtain ⟨Q, -, hQ, he⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
    (⊥ : Ideal A) (by simp [← RingHom.ker_eq_comap_bot])
  let : Q.IsPrime := hQ
  have : Q.LiesOver l.head.asIdeal := (Ideal.liesOver_iff _ _).mpr he.symm
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  have hsA : (s : WithBot ℕ∞) ≤ ringKrullDim A :=
    Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  have hs : s ≤ n := by exact_mod_cast hsA.trans hd
  have hz : Algebra.trdeg B A = 0 :=
    trdeg_eq_zero_iff.mpr (Algebra.IsIntegral.isAlgebraic (R := B) (A := A))
  rw [← trdeg_add_eq k B (A := A), hz, add_zero]
  simpa [B] using (show (s : Cardinal.{0}) ≤ n by exact_mod_cast hs)
private theorem image_algebraic (k σ A D : Type) [Field k] [Fintype σ]
    [CommRing A] [Algebra k A] [CommRing D]
    [Algebra k D] [Algebra (FractionRing (MvPolynomial σ k)) D]
    [IsScalarTower k (FractionRing (MvPolynomial σ k)) D]
    (f : A →ₐ[k] D) (hd : Algebra.trdeg k A ≤ Fintype.card σ)
    (c : σ → A) (hc : ∀ i, f (c i) =
      algebraMap (FractionRing (MvPolynomial σ k)) D
        (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (MvPolynomial.X i)))
    (x : A) : IsAlgebraic (FractionRing (MvPolynomial σ k)) (f x) := by
  let B := MvPolynomial σ k
  let F := FractionRing B
  by_contra hx
  have hX : AlgebraicIndependent k (fun i : σ => algebraMap B F (MvPolynomial.X i)) :=
    (algebraicIndependent_X σ k).map'
      (f := IsScalarTower.toAlgHom k B F) (IsFractionRing.injective B F)
  have hx' : AlgebraicIndependent F (fun _ : Unit => f x) := by
    apply algebraicIndependent_unique_type_iff.mpr
    exact (show Transcendental F (f x) from hx)
  have h := hX.sumElim_comp hx'
  have h' : AlgebraicIndependent k (f ∘ Sum.elim (fun _ : Unit => x) c) := by
    convert h using 1
    funext i
    cases i with
    | inl _ => rfl
    | inr i => exact hc i
  have hle := (AlgebraicIndependent.of_comp f h').cardinalMk_le_trdeg.trans hd
  rw [Cardinal.mk_fintype, Fintype.card_sum, Fintype.card_unit] at hle
  have : 1 + Fintype.card σ ≤ Fintype.card σ := by exact_mod_cast hle
  omega
private theorem card_nonzero (σ : Type) [Fintype σ] [Zero σ]
    [DecidablePred (fun x : σ => x = 0)] [DecidablePred (fun x : σ => x ≠ 0)] :
    Fintype.card {x : σ // x ≠ 0} + 1 = Fintype.card σ := by
  rw [Fintype.card_subtype_compl (fun x : σ => x = 0)]
  have h : Fintype.card {x : σ // x = 0} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun x => Subtype.ext x.property⟩
  rw [h]
  have : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨0⟩
  omega
private theorem constant_mem_of_section_zero {D : Type} [CommRing D]
    (S : Subring D) (a : Shape) (c : SectionIndex a → D) (x : Fin 4 → D)
    (hc : ∀ m ≠ 0, c m ∈ S) (hx : ∀ i, x i ∈ S)
    (hz : ∑ m ∈ boxMonomials a, c m * ∏ i : Fin 4, x i ^ (m i).val = 0) :
    c 0 ∈ S := by
  classical
  let t (m : SectionIndex a) := c m * ∏ i : Fin 4, x i ^ (m i).val
  have ht : t 0 = c 0 := by simp [t]
  have hm : 0 ∈ boxMonomials a := by simp [boxMonomials]
  have hsum := Finset.sum_erase_add (boxMonomials a) t hm
  rw [ht, show (∑ m ∈ boxMonomials a, t m) = 0 from hz] at hsum
  have hneg : c 0 = -(∑ m ∈ (boxMonomials a).erase 0, t m) :=
    eq_neg_of_add_eq_zero_right (by simpa [add_comm] using hsum)
  rw [hneg]
  exact S.neg_mem (S.sum_mem fun m hm => S.mul_mem
    (hc m (Finset.mem_erase.mp hm).1) (S.prod_mem fun i _ => S.pow_mem (hx i) _))
set_option backward.isDefEq.respectTransparency false in
private theorem prime_is_maximal (J : Ideal GeoJets) (a h : Shape)
    (hd : ∀ P, J.IsMinimalPrime P → ringKrullDim (GeoJets ⧸ P) ≤ 2)
    (Q : Ideal (SliceAlgebra J a h)) (hQ : Q.IsPrime) : Q.IsMaximal := by
  classical
  let : Q.IsPrime := hQ
  let k := GeoField
  let σ := PairSectionIndex a h
  let τ := {m : SectionIndex a // m ≠ 0} ⊕ {m : SectionIndex h // m ≠ 0}
  let B := MvPolynomial σ k
  let F := PairSectionField a h
  let I : Ideal (SliceJets a h) :=
    J.map (extendCoeffs a h) ⊔ Ideal.span {firstSection a h, secondSection a h}
  let : CommRing (SliceAlgebra J a h) := Ideal.Quotient.commRing I
  let D := SliceAlgebra J a h ⧸ Q
  let : CommRing D := Ideal.Quotient.commRing Q
  let q : SliceJets a h →ₐ[F] D :=
    (Ideal.Quotient.mkₐ F Q).comp (Ideal.Quotient.mkₐ F I)
  let e : GeoJets →ₐ[k] D :=
    (q.restrictScalars k).comp (MvPolynomial.mapAlgHom (Algebra.ofId k F))
  have hJe : J ≤ RingHom.ker e.toRingHom := by
    intro z hz
    change q (extendCoeffs a h z) = 0
    have hzI : extendCoeffs a h z ∈ I :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem (extendCoeffs a h) hz)
    change Ideal.Quotient.mk Q (Ideal.Quotient.mk I (extendCoeffs a h z)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzI, map_zero]
  have : (RingHom.ker e.toRingHom).IsPrime := RingHom.ker_isPrime e.toRingHom
  obtain ⟨P, hP, hPe⟩ := J.exists_minimalPrimes_le hJe
  have : P.IsPrime := hP.isPrime
  let A := GeoJets ⧸ P
  let : CommRing A := Ideal.Quotient.commRing P
  let W := MvPolynomial τ A
  let r : A →ₐ[k] D := Ideal.Quotient.liftₐ P e fun z hz => hPe hz
  let coeff (i : σ) : D := algebraMap F D (algebraMap B F (MvPolynomial.X i))
  let param : τ → D :=
    (Sum.elim (fun m => coeff (Sum.inl m.val)) (fun m => coeff (Sum.inr m.val)))
  let f : W →ₐ[k] D := aevalTower r param
  let coord (i : Fin 4) : D := q (MvPolynomial.X i)
  let S := f.toRingHom.range
  have hcoord (i : Fin 4) : coord i ∈ S := by
    let z : A := Ideal.Quotient.mk P (MvPolynomial.X i)
    refine ⟨C z, ?_⟩
    change f (C z) = coord i
    calc
      f (C z) = r z := aevalTower_C r param z
      _ = e (MvPolynomial.X i) := rfl
      _ = coord i := by simp [e, coord, MvPolynomial.mapAlgHom_apply]
  have hcoeff₁ (m : SectionIndex a) (hm : m ≠ 0) : coeff (Sum.inl m) ∈ S :=
    ⟨MvPolynomial.X (Sum.inl ⟨m, hm⟩), aevalTower_X r param (Sum.inl ⟨m, hm⟩)⟩
  have hcoeff₂ (m : SectionIndex h) (hm : m ≠ 0) : coeff (Sum.inr m) ∈ S :=
    ⟨MvPolynomial.X (Sum.inr ⟨m, hm⟩), aevalTower_X r param (Sum.inr ⟨m, hm⟩)⟩
  have hzero (p : SliceJets a h) (hp : p ∈ I) : q p = 0 := by
    change Ideal.Quotient.mk Q (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hcut (b : Shape) (ι : SectionIndex b → σ) (hb : sectionWith b ι ∈ I) :
      ∑ m ∈ boxMonomials b, coeff (ι m) * ∏ i : Fin 4, coord i ^ (m i).val = 0 := by
    calc
      _ = q (sectionWith b ι) := by
        rw [sectionWith, map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, map_prod]
        simp only [map_pow]
        exact congrArg (· * ∏ i : Fin 4, coord i ^ (m i).val)
          (q.commutes (algebraMap B F (MvPolynomial.X (ι m)))).symm
      _ = 0 := hzero _ hb
  have hcoeff (i : σ) : coeff i ∈ S := by
    cases i with
    | inl m =>
      by_cases hm : m = 0
      · subst m
        exact constant_mem_of_section_zero S a (fun m => coeff (Sum.inl m)) coord
          hcoeff₁ hcoord (hcut a Sum.inl (Ideal.mem_sup_right (Ideal.subset_span (by simp))))
      · exact hcoeff₁ m hm
    | inr m =>
      by_cases hm : m = 0
      · subst m
        exact constant_mem_of_section_zero S h (fun m => coeff (Sum.inr m)) coord
          hcoeff₂ hcoord (hcut h Sum.inr (Ideal.mem_sup_right (Ideal.subset_span (by simp))))
      · exact hcoeff₂ m hm
  have hcard : Fintype.card τ + 2 = Fintype.card σ := by
    change Fintype.card (_ ⊕ _) + 2 = Fintype.card (_ ⊕ _)
    rw [Fintype.card_sum, Fintype.card_sum]
    have ha := card_nonzero (SectionIndex a)
    have hh := card_nonzero (SectionIndex h)
    omega
  have hdW : ringKrullDim W ≤ Fintype.card σ := by
    change ringKrullDim (MvPolynomial τ A) ≤ _
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card,
      ← hcard, Nat.cast_add]
    rw [Nat.cast_ofNat, add_comm (Fintype.card τ : WithBot ℕ∞) 2]
    exact add_le_add_left (hd P hP) (Fintype.card τ : WithBot ℕ∞)
  have hw := trdeg_le_of_dim_le k W hdW
  have hlift (i : σ) : ∃ z : W, f z = coeff i := hcoeff i
  choose u hu using hlift
  have halg (i : Fin 4) : IsAlgebraic F (coord i) := by
    obtain ⟨z, hz⟩ := hcoord i
    change f z = coord i at hz
    rw [← hz]
    exact image_algebraic k σ W D f hw u hu z
  have hsurj : Function.Surjective q :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hadj : Algebra.adjoin F (Set.range coord) = ⊤ := by
    rw [show coord = q ∘ MvPolynomial.X from rfl, Set.range_comp, Algebra.adjoin_image,
      MvPolynomial.adjoin_range_X, Algebra.map_top, (AlgHom.range_eq_top q).mpr hsurj]
  have h := Algebra.isAlgebraic_adjoin_iff.mpr (Set.forall_mem_range.mpr halg)
  rw [hadj] at h
  have : Algebra.IsIntegral F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.isAlgebraic_iff.mpr h)
  exact Ideal.Quotient.maximal_of_isField Q
    (isField_of_isIntegral_of_isField' (Field.toIsField F))
set_option backward.isDefEq.respectTransparency false in
theorem proof : K1_13_6_1_4_3.c1 := by
  intro J a h _ _ hd
  let F := PairSectionField a h
  let S := SliceAlgebra J a h
  let : Field F := inferInstanceAs (Field (PairSectionField a h))
  have : IsArtinianRing F := DivisionRing.instIsArtinianRing
  have hS : Ring.KrullDimLE 0 S :=
    Ring.krullDimLE_zero_iff.mpr (prime_is_maximal J a h hd)
  exact (Module.finite_iff_krullDimLE_zero F S).mpr hS
end
end K1_13_6_1_4_3_1
end
section
namespace K1_14_3_4
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
def c2 : Prop :=
  ∀ (f : Equation), Irreducible f → 0 < f.natDegree → f.natDegree < p →
    ∃ (g : ClearedEquation) (a : (Polynomial L)), IsClearing f g a ∧
      ProperPair (C f) (graphCutter g) ∧
      RowCaps (C f) ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ∧
      RowCaps (graphCutter g) ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
end
end K1_14_3_4
end
section
namespace K1_14_3_4_2
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 K1_14_3_4 Polynomial
private theorem ordinary_caps (f : Equation) (j : ℕ) :
    RowCaps (C f) ⟨0, f.natDegree, j, ordinarySeedDegree f⟩ := by
  intro v y hv
  cases v with
  | zero =>
    rw [coeff_C_zero] at hv
    change y + 0 ≤ f.natDegree ∧ 0 ≤ j ∧
      (((C f : Jet).coeff 0).coeff y).totalDegree ≤ ordinarySeedDegree f
    rw [coeff_C_zero, Nat.add_zero]
    exact ⟨le_natDegree_of_ne_zero hv, Nat.zero_le j,
      Finset.le_sup (f := fun i => (f.coeff i).totalDegree)
        (Polynomial.mem_support_iff.mpr hv)⟩
  | succ v =>
    rw [coeff_C_succ, coeff_zero] at hv
    exact (hv rfl).elim
theorem proof : K1_14_3_4.c2 := by
  intro f hi hd hp
  obtain ⟨g, a, ha, hproper, _⟩ := K1_14_3R.ordinary_graph f hi hd hp
  refine ⟨g, a, ha, hproper, ordinary_caps f 0, ?_⟩
  change RowCaps (K1_14_3R.chainCutter g) ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
  exact K1_14_3R.chainCutter_caps_of_dvd hproper.left_ne (ordinary_caps f 1)
    le_rfl (dvd_refl (C f : Jet)) ha
end
end K1_14_3_4_2
end

end Merged_Fast061
