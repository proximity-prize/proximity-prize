import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch
import ProximityPrize.SubmissionLower.TrivariateShearResearch

/-! .












 -/

namespace ProximityPrize.SubmissionLower.ContactFlagAffineResidualAutomorphismResearch

open scoped Classical BigOperators
open ContactFlagBezout6543Research
open TrivariateShearResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

/-- .
 -/
def residualImage (aY v bY aS bS cS : K) (i : Fin 3) : Poly3 K :=
  ![MvPolynomial.C aY + MvPolynomial.C v * MvPolynomial.X 0 +
      MvPolynomial.C bY * MvPolynomial.X 2,
    MvPolynomial.C aS + MvPolynomial.C v * MvPolynomial.X 1 +
      MvPolynomial.C bS * MvPolynomial.X 0 +
      MvPolynomial.C cS * MvPolynomial.X 2,
    MvPolynomial.X 2] i

/-- . -/
def originalImage (aY v bY aS bS cS : K) (i : Fin 3) : Poly3 K :=
  let y := MvPolynomial.C v⁻¹ *
    (MvPolynomial.X 0 - MvPolynomial.C aY -
      MvPolynomial.C bY * MvPolynomial.X 2)
  ![y,
    MvPolynomial.C v⁻¹ *
      (MvPolynomial.X 1 - MvPolynomial.C aS -
        MvPolynomial.C bS * y - MvPolynomial.C cS * MvPolynomial.X 2),
    MvPolynomial.X 2] i

def residualAlgHom (aY v bY aS bS cS : K) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (residualImage aY v bY aS bS cS)

def originalAlgHom (aY v bY aS bS cS : K) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (originalImage aY v bY aS bS cS)

@[simp] theorem residualAlgHom_X
    (aY v bY aS bS cS : K) (i : Fin 3) :
    residualAlgHom aY v bY aS bS cS (MvPolynomial.X i) =
      residualImage aY v bY aS bS cS i := by
  simp [residualAlgHom]

@[simp] theorem originalAlgHom_X
    (aY v bY aS bS cS : K) (i : Fin 3) :
    originalAlgHom aY v bY aS bS cS (MvPolynomial.X i) =
      originalImage aY v bY aS bS cS i := by
  simp [originalAlgHom]

theorem original_comp_residual
    (aY v bY aS bS cS : K) (hv : v ≠ 0) :
    (originalAlgHom aY v bY aS bS cS).comp
        (residualAlgHom aY v bY aS bS cS) =
      AlgHom.id K (Poly3 K) := by
  have hvC : (MvPolynomial.C v : Poly3 K) * MvPolynomial.C v⁻¹ = 1 := by
    rw [← map_mul]
    simp [hv]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [residualImage, originalImage, residualAlgHom, originalAlgHom]
    linear_combination
      (MvPolynomial.X 0 - MvPolynomial.C bY * MvPolynomial.X 2 -
        MvPolynomial.C aY) * hvC
  · simp [residualImage, originalImage, residualAlgHom, originalAlgHom]
    linear_combination
      (MvPolynomial.X 1 - MvPolynomial.C cS * MvPolynomial.X 2 -
        (MvPolynomial.C aS + MvPolynomial.C v⁻¹ * MvPolynomial.C bS *
          (MvPolynomial.X 0 - MvPolynomial.C aY -
            MvPolynomial.C bY * MvPolynomial.X 2))) * hvC
  · simp [residualImage, originalImage, residualAlgHom, originalAlgHom]

theorem residual_comp_original
    (aY v bY aS bS cS : K) (hv : v ≠ 0) :
    (residualAlgHom aY v bY aS bS cS).comp
        (originalAlgHom aY v bY aS bS cS) =
      AlgHom.id K (Poly3 K) := by
  have hvC : (MvPolynomial.C v⁻¹ : Poly3 K) * MvPolynomial.C v = 1 := by
    rw [← map_mul]
    simp [hv]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [residualImage, originalImage, residualAlgHom, originalAlgHom]
    linear_combination MvPolynomial.X 0 * hvC
  · simp [residualImage, originalImage, residualAlgHom, originalAlgHom]
    linear_combination
      (MvPolynomial.X 1 -
        MvPolynomial.C v⁻¹ * MvPolynomial.C bS * MvPolynomial.X 0) * hvC
  · simp [residualImage, originalImage, residualAlgHom, originalAlgHom]

def residualEquiv (aY v bY aS bS cS : K) (hv : v ≠ 0) :
    Poly3 K ≃ₐ[K] Poly3 K :=
  AlgEquiv.ofAlgHom
    (residualAlgHom aY v bY aS bS cS)
    (originalAlgHom aY v bY aS bS cS)
    (residual_comp_original aY v bY aS bS cS hv)
    (original_comp_residual aY v bY aS bS cS hv)

@[simp] theorem residualEquiv_apply
    (aY v bY aS bS cS : K) (hv : v ≠ 0) (F : Poly3 K) :
    residualEquiv aY v bY aS bS cS hv F =
      residualAlgHom aY v bY aS bS cS F := rfl

theorem residual_irreducible_iff
    (aY v bY aS bS cS : K) (hv : v ≠ 0) (F : Poly3 K) :
    Irreducible (residualAlgHom aY v bY aS bS cS F) ↔ Irreducible F := by
  simpa only [residualEquiv_apply] using
    (MulEquiv.irreducible_iff (residualEquiv aY v bY aS bS cS hv))

theorem residual_dvd_iff
    (aY v bY aS bS cS : K) (hv : v ≠ 0) (F G : Poly3 K) :
    residualAlgHom aY v bY aS bS cS F ∣
        residualAlgHom aY v bY aS bS cS G ↔ F ∣ G := by
  simpa only [residualEquiv_apply] using
    (map_dvd_iff (residualEquiv aY v bY aS bS cS hv))

theorem residual_ne_zero
    (aY v bY aS bS cS : K) (hv : v ≠ 0) {F : Poly3 K}
    (hF : F ≠ 0) : residualAlgHom aY v bY aS bS cS F ≠ 0 :=
  (residualEquiv aY v bY aS bS cS hv).injective.ne hF

/-- .
 -/
theorem eval₂Hom_residual
    {A : Type} [CommRing A] [Algebra K A]
    (F : Poly3 K) (y s z : A) (aY v bY aS bS cS : K) :
    MvPolynomial.eval₂Hom (algebraMap K A) ![y, s, z]
        (residualAlgHom aY v bY aS bS cS F) =
      MvPolynomial.eval₂Hom (algebraMap K A)
        ![algebraMap K A aY + algebraMap K A v * y +
            algebraMap K A bY * z,
          algebraMap K A aS + algebraMap K A v * s +
            algebraMap K A bS * y + algebraMap K A cS * z,
          z] F := by
  have hhom :
      (MvPolynomial.eval₂Hom (algebraMap K A) ![y, s, z]).comp
          (residualAlgHom aY v bY aS bS cS).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap K A)
          ![algebraMap K A aY + algebraMap K A v * y +
              algebraMap K A bY * z,
            algebraMap K A aS + algebraMap K A v * s +
              algebraMap K A bS * y + algebraMap K A cS * z,
            z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, residualAlgHom]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, residualAlgHom, residualImage] <;> ring
  exact RingHom.congr_fun hhom F

/-- . -/
theorem pderiv_residual
    (aY v bY aS bS cS : K) (F : Poly3 K) :
    MvPolynomial.pderiv (1 : Fin 3)
        (residualAlgHom aY v bY aS bS cS F) =
      MvPolynomial.C v *
        residualAlgHom aY v bY aS bS cS
          (MvPolynomial.pderiv (1 : Fin 3) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, mul_add]
  | mul_X P i hP =>
      fin_cases i <;>
        simp [residualImage, hP, Derivation.leibniz] <;> ring

/-! . -/

theorem wt_add_le_residual
    (weights : Fin 3 → ℕ) (F G : Poly3 K) :
    wt weights (F + G) ≤ max (wt weights F) (wt weights G) := by
  unfold wt
  rw [← degree_weightedLift, map_add]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_add_le (3 : Fin 4)
      (weightedLift weights F) (weightedLift weights G)

theorem residualImage_wt_le
    (weights : Fin 3 → ℕ) (aY v bY aS bS cS : K) (i : Fin 3) :
    wt weights (residualImage aY v bY aS bS cS i) ≤
      ContactFlagTriangularProjectionResearch.flagPullWeights weights i := by
  fin_cases i
  · dsimp [residualImage,
      ContactFlagTriangularProjectionResearch.flagPullWeights]
    have hvx := wt_mul_le weights (MvPolynomial.C v : Poly3 K)
      (MvPolynomial.X 0)
    have hbx := wt_mul_le weights (MvPolynomial.C bY : Poly3 K)
      (MvPolynomial.X 2)
    rw [wt_C, Nat.zero_add, wt_X] at hvx hbx
    have hleft := wt_add_le_residual weights (MvPolynomial.C aY : Poly3 K)
      (MvPolynomial.C v * MvPolynomial.X 0)
    have hall := wt_add_le_residual weights
      (MvPolynomial.C aY + MvPolynomial.C v * MvPolynomial.X 0 : Poly3 K)
      (MvPolynomial.C bY * MvPolynomial.X 2)
    rw [wt_C] at hleft
    exact hall.trans (by omega)
  · dsimp [residualImage,
      ContactFlagTriangularProjectionResearch.flagPullWeights]
    have hvx := wt_mul_le weights (MvPolynomial.C v : Poly3 K)
      (MvPolynomial.X 1)
    have hbx := wt_mul_le weights (MvPolynomial.C bS : Poly3 K)
      (MvPolynomial.X 0)
    have hcx := wt_mul_le weights (MvPolynomial.C cS : Poly3 K)
      (MvPolynomial.X 2)
    rw [wt_C, Nat.zero_add, wt_X] at hvx hbx hcx
    have h0 := wt_add_le_residual weights (MvPolynomial.C aS : Poly3 K)
      (MvPolynomial.C v * MvPolynomial.X 1)
    have h1 := wt_add_le_residual weights
      (MvPolynomial.C aS + MvPolynomial.C v * MvPolynomial.X 1 : Poly3 K)
      (MvPolynomial.C bS * MvPolynomial.X 0)
    have h2 := wt_add_le_residual weights
      (MvPolynomial.C aS + MvPolynomial.C v * MvPolynomial.X 1 +
        MvPolynomial.C bS * MvPolynomial.X 0 : Poly3 K)
      (MvPolynomial.C cS * MvPolynomial.X 2)
    rw [wt_C] at h0
    exact h2.trans (by omega)
  · simp [residualImage,
      ContactFlagTriangularProjectionResearch.flagPullWeights, wt_X]

theorem residual_monomial_product_wt_le
    (weights : Fin 3 → ℕ) (aY v bY aS bS cS : K)
    (d : Fin 3 →₀ ℕ) :
    wt weights
        (∏ i ∈ d.support, residualImage aY v bY aS bS cS i ^ d i) ≤
      Finsupp.weight
        (ContactFlagTriangularProjectionResearch.flagPullWeights weights) d := by
  apply (wt_finset_prod_le_sum weights d.support
    (fun i ↦ residualImage aY v bY aS bS cS i ^ d i)).trans
  calc
    (∑ i ∈ d.support,
        wt weights (residualImage aY v bY aS bS cS i ^ d i)) ≤
        ∑ i ∈ d.support, d i *
          ContactFlagTriangularProjectionResearch.flagPullWeights weights i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (wt_pow_le weights (residualImage aY v bY aS bS cS i) (d i)).trans
        (Nat.mul_le_mul_left _
          (residualImage_wt_le weights aY v bY aS bS cS i))
    _ = Finsupp.weight
        (ContactFlagTriangularProjectionResearch.flagPullWeights weights) d := by
      rw [Finsupp.weight_apply]
      simp only [Finsupp.sum, nsmul_eq_mul]
      simp

theorem residualAlgHom_wt_le_pulled
    (weights : Fin 3 → ℕ) (aY v bY aS bS cS : K) (F : Poly3 K) :
    wt weights (residualAlgHom aY v bY aS bS cS F) ≤
      wt (ContactFlagTriangularProjectionResearch.flagPullWeights weights) F := by
  change wt weights
      (MvPolynomial.eval₂ MvPolynomial.C
        (residualImage aY v bY aS bS cS) F) ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply wt_finset_sum_le
  intro d hd
  have hprod := residual_monomial_product_wt_le weights
    aY v bY aS bS cS d
  have hcoeff :
      wt weights (MvPolynomial.C (F.coeff d) : Poly3 K) = 0 := wt_C weights _
  have hmul := wt_mul_le weights (MvPolynomial.C (F.coeff d) : Poly3 K)
    (∏ i ∈ d.support, residualImage aY v bY aS bS cS i ^ d i)
  rw [hcoeff, Nat.zero_add] at hmul
  exact hmul.trans (hprod.trans
    (MvPolynomial.le_weightedTotalDegree
      (ContactFlagTriangularProjectionResearch.flagPullWeights weights) hd))

/-- .

 -/
theorem polynomialInFlag_residualAlgHom
    (p : FlagDegree) (F : Poly3 K) (aY v bY aS bS cS : K)
    (hF : ContactFlagTriangularProjectionResearch.PolynomialInFlag p F) :
    ContactFlagTriangularProjectionResearch.PolynomialInFlag p
      (residualAlgHom aY v bY aS bS cS F) := by
  intro d hd
  let sWeight := ContactFlagTriangularProjectionResearch.sWeight
  let ysWeight := ContactFlagTriangularProjectionResearch.ysWeight
  let totalWeight := ContactFlagTriangularProjectionResearch.totalWeight
  have hs := MvPolynomial.le_weightedTotalDegree sWeight hd
  have hys := MvPolynomial.le_weightedTotalDegree ysWeight hd
  have htot := MvPolynomial.le_weightedTotalDegree totalWeight hd
  have hsw := (residualAlgHom_wt_le_pulled sWeight
    aY v bY aS bS cS F).trans (by
      simpa [sWeight] using
        ContactFlagTriangularProjectionResearch.wt_s_le_of_inFlag hF)
  have hysw := (residualAlgHom_wt_le_pulled ysWeight
    aY v bY aS bS cS F).trans (by
      simpa [ysWeight] using
        ContactFlagTriangularProjectionResearch.wt_ys_le_of_inFlag hF)
  have htotw := (residualAlgHom_wt_le_pulled totalWeight
    aY v bY aS bS cS F).trans (by
      simpa [totalWeight] using
        ContactFlagTriangularProjectionResearch.wt_total_le_of_inFlag hF)
  refine ⟨?_, ?_, ?_⟩
  · have := hs.trans hsw
    simpa [sWeight, ContactFlagTriangularProjectionResearch.sWeight,
      weight_fin3] using this
  · have := hys.trans hysw
    simpa [ysWeight, ContactFlagTriangularProjectionResearch.ysWeight,
      weight_fin3,
      Nat.add_comm] using this
  · have := htot.trans htotw
    simpa [totalWeight, ContactFlagTriangularProjectionResearch.totalWeight,
      weight_fin3,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

end

end ProximityPrize.SubmissionLower.ContactFlagAffineResidualAutomorphismResearch
