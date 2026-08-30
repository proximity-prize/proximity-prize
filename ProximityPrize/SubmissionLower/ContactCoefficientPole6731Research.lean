import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactComponentPencils
import ProximityPrize.SubmissionLower.ContactRationalRegularZero6676Research
import ProximityPrize.SubmissionLower.ContactMovingPoleTransport6719Research
namespace ProximityPrize.SubmissionLower.ContactCoefficientPole6731Research
open scoped Classical BigOperators WithZero
open ContactLocalPoleBound ContactMovingPoleTransport6719Research
open CoordinateBoxZeroCount ActualCurveCoordinateField
open ContactComponentPencils ContactGenericSurface ContactGlobalPolynomiality
open ContactAgreementEvaluation ContactTaylorNumerators ContactPolynomiality
open ContactPrimeSeedIncidence ContactWeakSeparableSeparatorResearch
open ContactRegularZeroBudget6676Research ContactRationalRegularZero6676Research
open ContactFlagBezout6543Research ContactFlagPoleInequality6543Research ContactSparsePoleSupportResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {L:Type} [Field L]
def coefficientPoleWeight (v:Valuation L (WithZero (Multiplicative ℤ)))
    (T:Polynomial L) (z:L):ℤ:=
  (insert (0:ℤ) (insert (poleOrder v z)
    (T.support.image (fun j↦poleOrder v (T.coeff j))))).max'
    ⟨0,Finset.mem_insert_self _ _⟩
theorem coefficientPoleWeight_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
    (T:Polynomial L) (z:L):0 ≤ coefficientPoleWeight v T z:=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)
theorem seedPole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
    (T:Polynomial L) (z:L):poleOrder v z ≤ coefficientPoleWeight v T z:=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
theorem coeffPole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
    (T:Polynomial L) (z:L) (j:ℕ) (hj:j∈T.support):
    poleOrder v (T.coeff j) ≤ coefficientPoleWeight v T z:=by
  unfold coefficientPoleWeight
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
private theorem pole_le_of_exp (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:L) (q:ℤ) (hq:0 ≤ q) (hx:v x ≤ WithZero.exp q):poleOrder v x ≤ q:=by
  apply max_le hq
  by_cases hzero:v x=0
  · simpa [hzero] using hq
  · simpa only [WithZero.log_exp] using (WithZero.log_le_log hzero WithZero.exp_ne_zero).mpr hx
theorem eval_pole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
    (T:Polynomial L) (z a:L) (ha:v a ≤ 1):
    poleOrder v (T.eval a) ≤ coefficientPoleWeight v T z:=by
  apply pole_le_of_exp _ _ _ (coefficientPoleWeight_nonneg v T z)
  rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  apply v.map_sum_le
  intro j hj
  rw [map_mul,map_pow]
  have hc:v (T.coeff j) ≤ WithZero.exp (coefficientPoleWeight v T z):=
    WithZero.le_exp_of_log_le ((le_max_right _ _).trans (coeffPole_le v T z j hj))
  have hp:v a^j ≤ 1:=pow_le_one₀ zero_le ha
  simpa only [mul_one] using mul_le_mul' hc hp
theorem affine_eval_pole_le {Ω:Type} [Field Ω] [Algebra Ω L]
    (v:Place Ω L) (T:Polynomial L) (z:L) (a u0 u1:Ω):
    poleOrder v.val (T.eval (algebraMap Ω L a)-algebraMap Ω L u0-z*algebraMap Ω L u1) ≤
      coefficientPoleWeight v.val T z:=by
  have ht:=eval_pole_le v.val T z _ (constant_value_le_one Ω L v a)
  have h0:=pole_const_le v.val (constant_value_le_one Ω L v) u0
  have hz:=pole_const_mul_le v.val (constant_value_le_one Ω L v) u1 z
  have hseed:=seedPole_le v.val T z
  have hn:=coefficientPoleWeight_nonneg v.val T z
  have hsub (x y:L):poleOrder v.val (x-y) ≤ max (poleOrder v.val x) (poleOrder v.val y):=by
    simpa only [sub_eq_add_neg,pole_neg] using pole_add_le v.val x (-y)
  exact (hsub _ _).trans (max_le ((hsub _ _).trans (max_le ht (h0.trans hn)))
    (by simpa only [mul_comm] using hz.trans hseed))
variable {K Ω:Type} [Field K] [Field Ω]
variable (φ:Polynomial K →+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
variable (F:MvPolynomial (Fin 4) K)
variable (hF:surfaceMap φ F∈P)
variable (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
def CoefficientPoleProfile (w cost:ℕ):Prop:=
  ∀ W:Finset (Place Ω (CoordinateField Ω P)),
    (∑ v∈W,coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w)
      (coordinate Ω P 2)) ≤ (cost:ℤ)
theorem coefficientPoleProfile_of_coordinate [IsAlgClosed Ω] (w:ℕ)
    (J:Coordinate Ω (CoordinateField Ω P))
    (hprofile:∀ v:Place Ω (CoordinateField Ω P),
      coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2) ≤
        CoordinatePoleMass.poleOrder Ω (CoordinateField Ω P) v
          (coordinateValue Ω (CoordinateField Ω P) J)):
    CoefficientPoleProfile φ P F hF hH w (coordinateDegree Ω (CoordinateField Ω P) J):=by
  intro W
  exact (Finset.sum_le_sum (fun v _↦hprofile v)).trans
    (finite_sum_coordinate_pole_le_degree Ω (CoordinateField Ω P) J W)
theorem coefficientPoleProfile_of_unitYZ_bound (w cost:ℕ)
    (hcoeff:∀ (v:Place Ω (CoordinateField Ω P)) (j:ℕ),
      poleOrder v.val ((truncatedPolynomial φ P F hF hH w).coeff j) ≤
        poleOrder v.val (coordinate Ω P 0))
    (hyz:∀ W:Finset (Place Ω (CoordinateField Ω P)),
      (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω P) (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
    CoefficientPoleProfile φ P F hF hH w cost:=by
  have hp (v:Place Ω (CoordinateField Ω P)):
      coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2) ≤
        max (poleOrder v.val (coordinate Ω P 0)) (poleOrder v.val (coordinate Ω P 2)):=by
    unfold coefficientPoleWeight
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (le_max_left _ _).trans (le_max_left _ _)
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_max_right _ _
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hz
    exact (hcoeff v j).trans (le_max_left _ _)
  intro W
  exact (Finset.sum_le_sum (fun v _↦hp v)).trans
    (by simpa only [exponentSetPoleWeight_unitYZ] using hyz W)
theorem normalized_agreement_eq (w:ℕ) (x u0 u1:K):
    coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
      (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)=
    (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x)-
      componentCoefficients φ P u0-coordinate Ω P 2*componentCoefficients φ P u1:=by
  have hclear:=eval_factorial_agreementNumerator (componentCoefficients φ P) F
    (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)
    w x u0 u1
  rw [component_evaluation] at hclear
  have hbase:MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) (polyH K F)=
      coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)):=by
    exact component_evaluation φ P _
  rw [hbase,←globalPolynomial_eval] at hclear
  have hz:componentPoint φ P (3:Fin 4)=coordinate Ω P 2:=rfl
  rw [hz] at hclear
  have hne:coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0:=by
    rw [←component_evaluation]
    exact component_regular φ P F hH
  apply (div_eq_iff (pow_ne_zero _ hne)).mpr
  simpa only [agreementPolynomial,truncatedPolynomial,mul_comm] using hclear
include hH in
theorem normalized_agreement_ne_zero_iff (w:ℕ) (x u0 u1:K):
    coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
      (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)≠0 ↔
      agreementPolynomial φ F w x u0 u1∉P:=by
  have hn:coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0:=by
    rw [←component_evaluation]
    exact component_regular φ P F hH
  constructor
  · intro h hmem
    apply h
    have hz:coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)=0:=by
      change agreementPolynomial φ F w x u0 u1∈RingHom.ker (coordinateEvaluation Ω P).toRingHom
      rwa [coordinateEvaluation_ker]
    rw [hz,zero_div]
  · intro h
    apply div_ne_zero _ (pow_ne_zero _ hn)
    intro hz
    apply h
    rw [←coordinateEvaluation_ker Ω P]
    exact hz
theorem agreement_regular_zero_le [IsAlgClosed Ω] (base:SeparableLiteralCoordinate P)
    (w cost:ℕ) (hprofile:CoefficientPoleProfile φ P F hF hH w cost)
    (x u0 u1:K) (hproper:agreementPolynomial φ F w x u0 u1∉P):
    FiniteRegularZeroSetBound P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
      (agreementPolynomial φ F w x u0 u1) cost:=by
  apply finite_regular_zero_bound_of_separator Ω P base _ _ (2*w) cost hproper hH
  intro W
  have hlocal (v:Place Ω (CoordinateField Ω P)):
      poleOrder v.val (coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
        (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)) ≤
      coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2):=by
    rw [normalized_agreement_eq φ P F hF hH]
    exact affine_eval_pole_le v _ _ (φ (Polynomial.C x)) (φ (Polynomial.C u0)) (φ (Polynomial.C u1))
  simpa only [CoordinatePoleMass.poleOrder,coordinateEvaluation_eq_aeval] using
    (Finset.sum_le_sum (fun v _↦hlocal v)).trans (hprofile W)
end
end ProximityPrize.SubmissionLower.ContactCoefficientPole6731Research
