import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphNormRigidity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveResultantFractionField6401
open Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
section FractionFieldResultant
variable {F : Type} [Field F] [DecidableEq F]
theorem zero_one_resultant_ne_zero6401 :
    Polynomial.resultant (0 : F[X][X]) 1 ≠ 0 := by
  simp
theorem zero_zero_resultant_ne_zero_and_not_isCoprime6401 :
    Polynomial.resultant (0 : F[X][X]) 0 ≠ 0 ∧
      ¬ IsCoprime (0 : F[X][X]) 0 := by
  constructor
  · simp
  · intro hcop
    have hunit : IsUnit (0 : F[X][X]) :=
      hcop.isUnit_of_dvd' (dvd_refl 0) (dvd_refl 0)
    exact hunit.ne_zero rfl
theorem resultant_ne_zero_isCoprime_fractionMap6401
    (A B : F[X][X]) (hnonzero : A ≠ 0 ∨ B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0) :
    IsCoprime
      (A.map (algebraMap F[X] (FractionRing F[X])))
      (B.map (algebraMap F[X] (FractionRing F[X]))) := by
  let K := FractionRing F[X]
  let f : F[X] →+* K := algebraMap F[X] K
  have hf : Function.Injective f := IsFractionRing.injective F[X] K
  let AK : Polynomial K := A.map f
  let BK : Polynomial K := B.map f
  have hnonzeroK : AK ≠ 0 ∨ BK ≠ 0 := by
    rcases hnonzero with hA | hB
    · exact Or.inl ((Polynomial.map_ne_zero_iff hf).2 hA)
    · exact Or.inr ((Polynomial.map_ne_zero_iff hf).2 hB)
  have hAdegree : AK.natDegree = A.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf A
  have hBdegree : BK.natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf B
  have hresFixed :
      Polynomial.resultant AK BK A.natDegree B.natDegree ≠ 0 := by
    rw [Polynomial.resultant_map_map]
    exact (map_ne_zero_iff f hf).2 hresultant
  have hresK : Polynomial.resultant AK BK ≠ 0 := by
    simpa only [hAdegree, hBdegree] using hresFixed
  have hcop : IsCoprime AK BK := by
    by_contra hnot
    exact hresK (Polynomial.resultant_eq_zero_iff.mpr
      ⟨hnonzeroK, hnot⟩)
  simpa only [AK, BK, K, f] using hcop
end FractionFieldResultant
end BCHKSExtremePrimitiveResultantFractionField6401
end ProximityPrize.SubmissionLower
