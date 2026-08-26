import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveNormObstruction6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveRecursiveNormTerminal6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
open BCHKSExtremePrimitiveRecursiveNormObstruction6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section ExactNormDegree
variable {F : Type} [Field F]
theorem polynomialFrobeniusNormSix_natDegree_eq6401
    (sigma : F →+* F) (Q : F[X]) (hQ : Q ≠ 0) :
    (polynomialFrobeniusNormSix sigma Q).natDegree = 6 * Q.natDegree := by
  let Q1 := Q.map sigma
  let Q2 := Q1.map sigma
  let Q3 := Q2.map sigma
  let Q4 := Q3.map sigma
  let Q5 := Q4.map sigma
  have h1 : Q1 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 hQ
  have h2 : Q2 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h1
  have h3 : Q3 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h2
  have h4 : Q4 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h3
  have h5 : Q5 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h4
  have hd1 : Q1.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective sigma.injective Q
  have hd2 : Q2.natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective sigma.injective, hd1]
  have hd3 : Q3.natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective sigma.injective, hd2]
  have hd4 : Q4.natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective sigma.injective, hd3]
  have hd5 : Q5.natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective sigma.injective, hd4]
  change (Q * Q1 * Q2 * Q3 * Q4 * Q5).natDegree = _
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hQ h1) h2) h3)
        h4) h5,
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hQ h1) h2) h3) h4,
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero hQ h1) h2) h3,
    Polynomial.natDegree_mul (mul_ne_zero hQ h1) h2,
    Polynomial.natDegree_mul hQ h1,
    hd1, hd2, hd3, hd4, hd5]
  omega
theorem polynomialFrobeniusNormSix_ne_zero6401
    (sigma : F →+* F) (Q : F[X]) (hQ : Q ≠ 0) :
    polynomialFrobeniusNormSix sigma Q ≠ 0 := by
  let Q1 := Q.map sigma
  let Q2 := Q1.map sigma
  let Q3 := Q2.map sigma
  let Q4 := Q3.map sigma
  let Q5 := Q4.map sigma
  have h1 : Q1 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 hQ
  have h2 : Q2 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h1
  have h3 : Q3 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h2
  have h4 : Q4 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h3
  have h5 : Q5 ≠ 0 := (Polynomial.map_ne_zero_iff sigma.injective).2 h4
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hQ h1) h2) h3)
      h4) h5
theorem natDegree_eq_zero_of_norm_eq_constantNorm6401
    (sigma : F →+* F) (A B : F[X])
    (hB : B ≠ 0) (hBdegree : B.natDegree = 0)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B) :
    A.natDegree = 0 := by
  have hnormB : polynomialFrobeniusNormSix sigma B ≠ 0 := by
    exact polynomialFrobeniusNormSix_ne_zero6401 sigma B hB
  have hA : A ≠ 0 := by
    intro hzero
    apply hnormB
    rw [← hnorm, hzero]
    simp [polynomialFrobeniusNormSix]
  have hdegreeA := polynomialFrobeniusNormSix_natDegree_eq6401 sigma A hA
  have hdegreeB := polynomialFrobeniusNormSix_natDegree_eq6401 sigma B hB
  rw [hnorm] at hdegreeA
  rw [hdegreeB, hBdegree] at hdegreeA
  omega
end ExactNormDegree
section Terminal
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {P : F → Polynomial F}
variable (W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset P)
noncomputable def recursiveNormDegenerateChallenges6401
    (C : RecursivePrimitiveLaneState6401 W) (T : Finset F) : Finset F :=
  T.filter fun z ↦
    specializeCoeffZ z (recursiveFamilyNormObstruction6401 W C) = 0
theorem terminalSpecializedLanes_natDegree_eq_zero_of_normDegenerate6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hterminal :
      (C.quotient W.sourcePuncture.pivot).natDegree = 0)
    (z : F) (hz : z ∈ recursiveMassCore6401 W C)
    (hzero :
      specializeCoeffZ z (recursiveFamilyNormObstruction6401 W C) = 0) :
    (specializeCoeffZ z C.laneZero6401).natDegree = 0 ∧
      (specializeCoeffZ z C.laneOne6401).natDegree = 0 := by
  have hlane := recursiveSpecializedLanes_not_both_zero_of_mem_massCore6401
    W C hz
  have hnorm : polynomialFrobeniusNormSix sigma
        (specializeCoeffZ z C.laneZero6401) =
      polynomialFrobeniusNormSix sigma
        (specializeCoeffZ z C.laneOne6401) := by
    have hspec := recursiveFamilyNormObstruction_specialize6401
      W C z (hsigma z)
    rw [hzero] at hspec
    exact sub_eq_zero.mp hspec.symm
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · have hBdegree :
        (specializeCoeffZ z C.laneOne6401).natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Polynomial.natDegree_map_le.trans (by
        simpa [RecursivePrimitiveLaneState6401.laneOne6401, hpivot] using
          hterminal)
    have hB : specializeCoeffZ z C.laneOne6401 ≠ 0 := by
      have hzparts := Finset.mem_filter.mp hz
      have hQ : specializeCoeffZ z
          (C.quotient W.sourcePuncture.pivot) ≠ 0 := by
        intro hzeroQ
        apply hzparts.2
        rw [C.component_factor W.sourcePuncture.pivot, map_mul]
        exact mul_eq_zero.mpr (Or.inr hzeroQ)
      simpa [hpivot, RecursivePrimitiveLaneState6401.laneOne6401] using
        (neg_ne_zero.mpr hQ)
    exact ⟨natDegree_eq_zero_of_norm_eq_constantNorm6401
      sigma _ _ hB hBdegree hnorm, hBdegree⟩
  · have hAdegree :
        (specializeCoeffZ z C.laneZero6401).natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Polynomial.natDegree_map_le.trans (by
        simpa [RecursivePrimitiveLaneState6401.laneZero6401, hpivot] using
          hterminal)
    have hA : specializeCoeffZ z C.laneZero6401 ≠ 0 := by
      have hzparts := Finset.mem_filter.mp hz
      intro hzeroLane
      apply hzparts.2
      rw [C.component_factor W.sourcePuncture.pivot, map_mul]
      apply mul_eq_zero.mpr
      right
      simpa [hpivot, RecursivePrimitiveLaneState6401.laneZero6401]
        using hzeroLane
    have hBdegree := natDegree_eq_zero_of_norm_eq_constantNorm6401
      sigma _ _ hA hAdegree hnorm.symm
    exact ⟨hAdegree, hBdegree⟩
theorem terminalNormDegenerate_card_le_or_bothLanesConstant6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hterminal :
      (C.quotient W.sourcePuncture.pivot).natDegree = 0) :
    (recursiveNormDegenerateChallenges6401 W C
        (recursiveMassCore6401 W C)).card ≤
          primitiveLaneFactorDescentExceptionCap6401 ∨
      (C.laneZero6401.natDegree = 0 ∧
        C.laneOne6401.natDegree = 0) := by
  classical
  by_cases hboth : C.laneZero6401.natDegree = 0 ∧
      C.laneOne6401.natDegree = 0
  · exact Or.inr hboth
  · left
    let D := recursiveNormDegenerateChallenges6401 W C
      (recursiveMassCore6401 W C)
    have hcoeff := recursiveLanes_coeffDegreeLE6401 W C
    by_cases hzeroDegree : C.laneZero6401.natDegree = 0
    · have honePositive : 0 < C.laneOne6401.natDegree := by
        have : C.laneOne6401.natDegree ≠ 0 := by
          intro h
          exact hboth ⟨hzeroDegree, h⟩
        exact Nat.pos_of_ne_zero this
      have hlead : C.laneOne6401.leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (by
          intro h
          rw [h, Polynomial.natDegree_zero] at honePositive
          omega)
      have hsub : D ⊆ (recursiveMassCore6401 W C).filter fun z ↦
          Polynomial.eval z C.laneOne6401.leadingCoeff = 0 := by
        intro z hz
        have hzparts := Finset.mem_filter.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨hzparts.1, ?_⟩
        by_contra hleadEval
        have hdegreeExact :
            (specializeCoeffZ z C.laneOne6401).natDegree =
              C.laneOne6401.natDegree := by
          exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl (by
            simpa [specializeCoeffZ_apply] using hleadEval))
        have hdegrees :=
          terminalSpecializedLanes_natDegree_eq_zero_of_normDegenerate6401
            W C hsigma hterminal z hzparts.1 hzparts.2
        rw [hdegrees.2] at hdegreeExact
        omega
      calc
        D.card ≤ ((recursiveMassCore6401 W C).filter fun z ↦
            Polynomial.eval z C.laneOne6401.leadingCoeff = 0).card :=
          Finset.card_le_card hsub
        _ ≤ C.laneOne6401.leadingCoeff.natDegree :=
          card_filter_eval_eq_zero_le_natDegree _ _ hlead
        _ ≤ primitiveLaneOneChallengeCap6401 :=
          hcoeff.2 C.laneOne6401.natDegree
        _ ≤ primitiveLaneFactorDescentExceptionCap6401 := by native_decide
    · have hzeroPositive : 0 < C.laneZero6401.natDegree :=
        Nat.pos_of_ne_zero hzeroDegree
      have hlead : C.laneZero6401.leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (by
          intro h
          rw [h, Polynomial.natDegree_zero] at hzeroPositive
          omega)
      have hsub : D ⊆ (recursiveMassCore6401 W C).filter fun z ↦
          Polynomial.eval z C.laneZero6401.leadingCoeff = 0 := by
        intro z hz
        have hzparts := Finset.mem_filter.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨hzparts.1, ?_⟩
        by_contra hleadEval
        have hdegreeExact :
            (specializeCoeffZ z C.laneZero6401).natDegree =
              C.laneZero6401.natDegree := by
          exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl (by
            simpa [specializeCoeffZ_apply] using hleadEval))
        have hdegrees :=
          terminalSpecializedLanes_natDegree_eq_zero_of_normDegenerate6401
            W C hsigma hterminal z hzparts.1 hzparts.2
        rw [hdegrees.1] at hdegreeExact
        omega
      calc
        D.card ≤ ((recursiveMassCore6401 W C).filter fun z ↦
            Polynomial.eval z C.laneZero6401.leadingCoeff = 0).card :=
          Finset.card_le_card hsub
        _ ≤ C.laneZero6401.leadingCoeff.natDegree :=
          card_filter_eval_eq_zero_le_natDegree _ _ hlead
        _ ≤ primitiveLaneZeroChallengeCap6401 :=
          hcoeff.1 C.laneZero6401.natDegree
        _ ≤ primitiveLaneFactorDescentExceptionCap6401 := by native_decide
end Terminal
end BCHKSExtremePrimitiveRecursiveNormTerminal6401
end ProximityPrize.SubmissionLower
