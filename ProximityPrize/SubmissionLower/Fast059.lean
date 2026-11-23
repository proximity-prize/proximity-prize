import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast057
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
open private   unpack from ProximityPrize.SubmissionLower.Numeric5Certificate
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
open private    sumFrom   from ProximityPrize.SubmissionLower.Numeric6AuxCert
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
private theorem topPartial_bound (w : Fin 4 → ℕ) (P : Row 4) :
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
    rw [← map_natCast (MvPolynomial.C : Geom[X] →+* Row 4)]
    exact (Nat.add_le_add ((weight_const_mul_le _ _ _).trans (flow_bound w Δ hshift hB hg hsep))
      hP).trans (by omega)
private theorem jet_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {g : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hg : W w g ≤ B) (n : ℕ) :
    W w (jetNumerator g n) ≤ w 0 + n * (2 * (B - w 3) + Δ) := by
  induction n with
  | zero => simpa only [jetNumerator, zero_mul, add_zero] using weight_X_le (R := Geom[X]) w 0
  | succ n ih =>
    simpa only [jetNumerator, Nat.add_mul, one_mul, Nat.add_assoc] using
      step_bound w Δ hshift hB hg ih (2 * n)
private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
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
private theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {g : Row 4} {B : ℕ} (hg : W w g ≤ B) :
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
private theorem ordinary_eq_hasse (S : Geom[X]) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
theorem evalGeneric_toGeneric (S : Geom[X]) (P : Row 4) :
    evalGeneric S (toGeneric P) = genericCoeffs (atJet P S) := by
  exact (MvPolynomial.map_eval genericCoeffs (jet S) P).symm
private theorem chart_recovers {L : ℕ} (hL : taylorLength ≤ L) (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (hr : RegularAt g S) : (taylorChart L g).Recovers S := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
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
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
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
      ∀ S : Geom[X], atJet g S = 0 → RegularAt g S → C.Recovers S :=
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
abbrev FreshField := FractionRing GeometricX[X]
abbrev FreshJetRing := MvPolynomial (Fin 3) FreshField
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) FreshField
abbrev FreshJetIdeal := Ideal FreshJetRing
def freshArgument : FreshField := algebraMap GeometricX[X] FreshField Polynomial.X
def freshCoeff : Geom[X] →+* FreshField :=
  (algebraMap GeometricX[X] FreshField).comp
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
