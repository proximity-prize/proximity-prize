import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveGraphSeedInheritance6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphNormRigidity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveRecursiveNormObstruction6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusRationalOwnerLocator6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveRecursiveGraphSeedInheritance6401
open BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
open BCHKSExtremePrimitiveGraphNormRigidity6401
open BCHKSExtremePrimitiveFaithfulGraphGauge6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section Algebra
variable {F : Type} [Field F] [DecidableEq F]
theorem graphFrobeniusNormSix_mul6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) :
    graphFrobeniusNormSix6401 sigma q (A * B) =
      graphFrobeniusNormSix6401 sigma q A *
        graphFrobeniusNormSix6401 sigma q B := by
  simp only [graphFrobeniusNormSix6401, graphTwist6401,
    graphTwistTwo6401, graphTwistThree6401, graphTwistFour6401,
    graphTwistFive6401, Polynomial.map_mul]
  ring
theorem graphFrobeniusNormSix_natDegree_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (K : F[X][X]) (hK : K ≠ 0) :
    (graphFrobeniusNormSix6401 sigma q K).natDegree =
      6 * K.natDegree := by
  let T1 := graphTwist6401 sigma q K
  let T2 := graphTwistTwo6401 sigma q K
  let T3 := graphTwistThree6401 sigma q K
  let T4 := graphTwistFour6401 sigma q K
  let T5 := graphTwistFive6401 sigma q K
  have hT1 : T1 ≠ 0 := graphTwist_ne_zero6401 sigma q hq K hK
  have hT2 : T2 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT1
  have hT3 : T3 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT2
  have hT4 : T4 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT3
  have hT5 : T5 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT4
  have hd1 : T1.natDegree = K.natDegree :=
    graphTwist_natDegree_eq6401 sigma q hq K
  have hd2 : T2.natDegree = K.natDegree := by
    calc
      T2.natDegree = T1.natDegree :=
        graphTwist_natDegree_eq6401 sigma q hq T1
      _ = K.natDegree := hd1
  have hd3 : T3.natDegree = K.natDegree := by
    calc
      T3.natDegree = T2.natDegree :=
        graphTwist_natDegree_eq6401 sigma q hq T2
      _ = K.natDegree := hd2
  have hd4 : T4.natDegree = K.natDegree := by
    calc
      T4.natDegree = T3.natDegree :=
        graphTwist_natDegree_eq6401 sigma q hq T3
      _ = K.natDegree := hd3
  have hd5 : T5.natDegree = K.natDegree := by
    calc
      T5.natDegree = T4.natDegree :=
        graphTwist_natDegree_eq6401 sigma q hq T4
      _ = K.natDegree := hd4
  change (K * T1 * T2 * T3 * T4 * T5).natDegree = _
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hK hT1) hT2)
        hT3) hT4) hT5,
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hK hT1) hT2) hT3) hT4,
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero hK hT1) hT2) hT3,
    Polynomial.natDegree_mul (mul_ne_zero hK hT1) hT2,
    Polynomial.natDegree_mul hK hT1,
    hd1, hd2, hd3, hd4, hd5]
  omega
theorem graphFrobeniusNormSix_ne_zero6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (K : F[X][X]) (hK : K ≠ 0) :
    graphFrobeniusNormSix6401 sigma q K ≠ 0 := by
  let T1 := graphTwist6401 sigma q K
  let T2 := graphTwistTwo6401 sigma q K
  let T3 := graphTwistThree6401 sigma q K
  let T4 := graphTwistFour6401 sigma q K
  let T5 := graphTwistFive6401 sigma q K
  have hT1 : T1 ≠ 0 := graphTwist_ne_zero6401 sigma q hq K hK
  have hT2 : T2 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT1
  have hT3 : T3 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT2
  have hT4 : T4 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT3
  have hT5 : T5 ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT4
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hK hT1) hT2)
      hT3) hT4) hT5
end Algebra
section Recursive
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {P : F → Polynomial F}
variable (W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset P)
noncomputable def recursiveFamilyNormObstruction6401
    (C : RecursivePrimitiveLaneState6401 W) : F[X][X] :=
  graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 -
    graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401
theorem primitiveFamilyNormObstruction_recursiveFactor6401
    (C : RecursivePrimitiveLaneState6401 W) :
    primitiveFamilyNormObstruction6401 W =
      graphFrobeniusNormSix6401 sigma q6401 C.cumulativeFactor *
        recursiveFamilyNormObstruction6401 W C := by
  rw [primitiveFamilyNormObstruction6401,
    originalLaneZero_factor6401 C, originalLaneOne_factor6401 C,
    graphFrobeniusNormSix_mul6401,
    graphFrobeniusNormSix_mul6401]
  unfold recursiveFamilyNormObstruction6401
  ring
theorem recursiveFamilyNormObstruction_ne_zero6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hnorm : primitiveFamilyNormObstruction6401 W ≠ 0) :
    recursiveFamilyNormObstruction6401 W C ≠ 0 := by
  intro hzero
  apply hnorm
  rw [primitiveFamilyNormObstruction_recursiveFactor6401 W C, hzero,
    mul_zero]
theorem recursiveFamilyNormObstruction_degreeLedger6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hnorm : primitiveFamilyNormObstruction6401 W ≠ 0) :
    (primitiveFamilyNormObstruction6401 W).natDegree =
      6 * C.cumulativeFactor.natDegree +
        (recursiveFamilyNormObstruction6401 W C).natDegree := by
  have hfactorNorm : graphFrobeniusNormSix6401 sigma q6401
      C.cumulativeFactor ≠ 0 := by
    exact graphFrobeniusNormSix_ne_zero6401 sigma q6401
      (by native_decide) C.cumulativeFactor C.cumulativeFactor_ne_zero
  have hquotientNorm := recursiveFamilyNormObstruction_ne_zero6401 W C hnorm
  rw [primitiveFamilyNormObstruction_recursiveFactor6401 W C,
    Polynomial.natDegree_mul hfactorNorm hquotientNorm,
    graphFrobeniusNormSix_natDegree_eq6401 sigma q6401
      (by native_decide) C.cumulativeFactor C.cumulativeFactor_ne_zero]
theorem recursiveFamilyNormObstruction_specialize6401
    (C : RecursivePrimitiveLaneState6401 W)
    (z : F) (hz : sigma z = z ^ q6401) :
    specializeCoeffZ z (recursiveFamilyNormObstruction6401 W C) =
      polynomialFrobeniusNormSix sigma
          (specializeCoeffZ z C.laneZero6401) -
        polynomialFrobeniusNormSix sigma
          (specializeCoeffZ z C.laneOne6401) := by
  simp only [recursiveFamilyNormObstruction6401, map_sub]
  rw [graphFrobeniusNormSix_specialize6401 sigma q6401 _ z hz,
    graphFrobeniusNormSix_specialize6401 sigma q6401 _ z hz]
private theorem ownerLocator_dvd_of_eval_zero_recursive6401
    {I : Type*} [DecidableEq I]
    (beta : I ↪ F) (T : Finset I) (N : Polynomial F)
    (hzero : ∀ i ∈ T, Polynomial.eval (beta i) N = 0) :
    ownerLocator beta T ∣ N := by
  classical
  unfold ownerLocator
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C beta.injective hij
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero i hi
theorem puncturedErrorLocator_dvd_recursiveFamilyNormSpecialization6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (z : F) (hz : z ∈ C.goodChallenges6401) :
    puncturedErrorLocator6401 W z ∣
      specializeCoeffZ z (recursiveFamilyNormObstruction6401 W C) := by
  classical
  let L0 := specializeCoeffZ z C.laneZero6401
  let L1 := specializeCoeffZ z C.laneOne6401
  have hfailure := recursivePuncturedTwoLaneFailureRelation6401
    W C hsigma hfixed z hz
  rw [recursiveFamilyNormObstruction_specialize6401 W C z (hsigma z)]
  apply ownerLocator_dvd_of_eval_zero_recursive6401 W.puncturedAlpha
    (puncturedErrorSupport6401 W z)
  intro i hi
  have herror : W.puncturedOwnerError z i ≠ 0 :=
    (Finset.mem_filter.mp hi).2
  have hvalue := scalarFrobeniusNormSix_eq_of_relation sigma horder
    (Polynomial.eval (W.puncturedAlpha i) L0)
    (Polynomial.eval (W.puncturedAlpha i) L1)
    (W.puncturedOwnerError z i) herror (hfailure i)
  have hfixedAt : sigma (W.puncturedAlpha i) = W.puncturedAlpha i :=
    hfixed i.1
  have hnorm0 := polynomialFrobeniusNormSix_eval_of_fixed
    sigma L0 (W.puncturedAlpha i) hfixedAt
  have hnorm1 := polynomialFrobeniusNormSix_eval_of_fixed
    sigma L1 (W.puncturedAlpha i) hfixedAt
  simp only [Polynomial.eval_sub]
  rw [hnorm0, hnorm1, hvalue, sub_self]
theorem recursiveFamilyNormObstruction_natDegree_le_135042_6401
    (C : RecursivePrimitiveLaneState6401 W) :
    (recursiveFamilyNormObstruction6401 W C).natDegree ≤ 135042 := by
  have hzero : C.laneZero6401.natDegree ≤ 22507 := by
    simpa [RecursivePrimitiveLaneState6401.laneZero6401,
      primitiveThreeShiftXCap6401] using C.quotient_caps6401 2
  have hone : C.laneOne6401.natDegree ≤ 22507 := by
    simpa [RecursivePrimitiveLaneState6401.laneOne6401,
      primitiveThreeShiftXCap6401] using C.quotient_caps6401 1
  have hnormZero := graphFrobeniusNormSix_natDegree_le6401 sigma q6401
    22507 C.laneZero6401 hzero
  have hnormOne := graphFrobeniusNormSix_natDegree_le6401 sigma q6401
    22507 C.laneOne6401 hone
  unfold recursiveFamilyNormObstruction6401
  norm_num at hnormZero hnormOne
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le hnormZero hnormOne)
end Recursive
end BCHKSExtremePrimitiveRecursiveNormObstruction6401
end ProximityPrize.SubmissionLower
