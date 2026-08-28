import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.TrivariateShearResearch
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds

/-!
# Two-stage triangular coordinates for flag projections

The flag support function uses the nested linear spans

`Z ⊂ span(Y,Z) ⊂ span(S,Y,Z)`.

This module implements the simultaneous characteristic-free change

`U = Y + λ Z`, `V = S + μ Y + ν Z`, `Z = Z`.

Its inverse substitution on polynomials is

`Y = U - λ Z`,
`S = V - μ U + (μλ-ν) Z`.

The substitution is an algebra automorphism, preserves every `InFlag`
support bound, and turns the three desired affine projections into literal
coordinates.  The last theorem is the narrow bridge from explicit
joint-support degree data of the transformed equations to the existing
`JointOrderCertificate` API.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch

open scoped Classical BigOperators
open ContactFlagBezout6543Research
open TrivariateShearResearch
open ActualCurveJointProjectionBounds
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open TrivariateRationalCollection ActualPlaneJointProjection
open ActualPlanePositiveOrder

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

/-- Inverse coordinate substitution, from `(Y,S,Z)` polynomials to
literal `(U,V,Z)` polynomials. -/
def flagImage (lam μ ν : K) (i : Fin 3) : Poly3 K :=
  ![MvPolynomial.X 0 - MvPolynomial.C lam * MvPolynomial.X 2,
    MvPolynomial.X 1 -
      (MvPolynomial.C μ * MvPolynomial.X 0 -
        MvPolynomial.C (μ * lam - ν) * MvPolynomial.X 2),
    MvPolynomial.X 2] i

/-- Forward coordinate substitution `U=Y+λZ`, `V=S+μY+νZ`. -/
def unflagImage (lam μ ν : K) (i : Fin 3) : Poly3 K :=
  ![MvPolynomial.X 0 + MvPolynomial.C lam * MvPolynomial.X 2,
    MvPolynomial.X 1 + MvPolynomial.C μ * MvPolynomial.X 0 +
      MvPolynomial.C ν * MvPolynomial.X 2,
    MvPolynomial.X 2] i

def flagAlgHom (lam μ ν : K) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (flagImage lam μ ν)

def unflagAlgHom (lam μ ν : K) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (unflagImage lam μ ν)

@[simp] theorem flagAlgHom_X (lam μ ν : K) (i : Fin 3) :
    flagAlgHom lam μ ν (MvPolynomial.X i) = flagImage lam μ ν i := by
  simp [flagAlgHom]

@[simp] theorem unflagAlgHom_X (lam μ ν : K) (i : Fin 3) :
    unflagAlgHom lam μ ν (MvPolynomial.X i) = unflagImage lam μ ν i := by
  simp [unflagAlgHom]

theorem unflag_comp_flag (lam μ ν : K) :
    (unflagAlgHom lam μ ν).comp (flagAlgHom lam μ ν) =
      AlgHom.id K (Poly3 K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [flagImage, unflagImage, flagAlgHom, unflagAlgHom] <;> ring

theorem flag_comp_unflag (lam μ ν : K) :
    (flagAlgHom lam μ ν).comp (unflagAlgHom lam μ ν) =
      AlgHom.id K (Poly3 K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [flagImage, unflagImage, flagAlgHom, unflagAlgHom] <;> ring

def flagEquiv (lam μ ν : K) : Poly3 K ≃ₐ[K] Poly3 K :=
  AlgEquiv.ofAlgHom (flagAlgHom lam μ ν) (unflagAlgHom lam μ ν)
    (flag_comp_unflag lam μ ν) (unflag_comp_flag lam μ ν)

@[simp] theorem flagEquiv_apply (lam μ ν : K) (F : Poly3 K) :
    flagEquiv lam μ ν F = flagAlgHom lam μ ν F := rfl

theorem flag_irreducible_iff (lam μ ν : K) (F : Poly3 K) :
    Irreducible (flagAlgHom lam μ ν F) ↔ Irreducible F := by
  simpa only [flagEquiv_apply] using
    (MulEquiv.irreducible_iff (flagEquiv lam μ ν))

theorem flag_dvd_iff (lam μ ν : K) (F G : Poly3 K) :
    flagAlgHom lam μ ν F ∣ flagAlgHom lam μ ν G ↔ F ∣ G := by
  simpa only [flagEquiv_apply] using
    (map_dvd_iff (flagEquiv lam μ ν))

theorem flag_ne_zero (lam μ ν : K) {F : Poly3 K} (hF : F ≠ 0) :
    flagAlgHom lam μ ν F ≠ 0 :=
  (flagEquiv lam μ ν).injective.ne hF

/-- Evaluation of the transformed polynomial at literal `(U,V,Z)`. -/
theorem eval₂Hom_flag
    {A : Type} [CommRing A] [Algebra K A]
    (F : Poly3 K) (u v z : A) (lam μ ν : K) :
    MvPolynomial.eval₂Hom (algebraMap K A) ![u, v, z]
        (flagAlgHom lam μ ν F) =
      MvPolynomial.eval₂Hom (algebraMap K A)
        ![u - algebraMap K A lam * z,
          v - algebraMap K A μ * u +
            algebraMap K A (μ * lam - ν) * z,
          z] F := by
  have hhom :
      (MvPolynomial.eval₂Hom (algebraMap K A) ![u, v, z]).comp
          (flagAlgHom lam μ ν).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap K A)
          ![u - algebraMap K A lam * z,
            v - algebraMap K A μ * u +
              algebraMap K A (μ * lam - ν) * z,
            z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, flagAlgHom]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, flagAlgHom, flagImage] <;> ring
  exact RingHom.congr_fun hhom F

/-- Substituting the actual affine forms recovers the original evaluation. -/
theorem eval₂Hom_flag_at_affine
    {A : Type} [CommRing A] [Algebra K A]
    (F : Poly3 K) (y s z : A) (lam μ ν : K) :
    MvPolynomial.eval₂Hom (algebraMap K A)
        ![y + algebraMap K A lam * z,
          s + algebraMap K A μ * y + algebraMap K A ν * z,
          z] (flagAlgHom lam μ ν F) =
      MvPolynomial.eval₂Hom (algebraMap K A) ![y, s, z] F := by
  rw [eval₂Hom_flag]
  congr 2
  funext i
  fin_cases i <;> simp <;> ring

/-! ## Exact flag-support transport -/

def flagPullWeights (weights : Fin 3 → ℕ) : Fin 3 → ℕ :=
  ![max (weights 0) (weights 2),
    max (weights 1) (max (weights 0) (weights 2)),
    weights 2]

theorem flagImage_wt_le (weights : Fin 3 → ℕ) (lam μ ν : K) (i : Fin 3) :
    wt weights (flagImage lam μ ν i) ≤ flagPullWeights weights i := by
  fin_cases i
  · dsimp [flagImage, flagPullWeights]
    have hm := wt_mul_le weights (MvPolynomial.C lam : Poly3 K)
      (MvPolynomial.X 2)
    rw [wt_C, Nat.zero_add, wt_X] at hm
    exact (wt_sub_le weights (MvPolynomial.X 0)
      (MvPolynomial.C lam * MvPolynomial.X 2)).trans
        (max_le_max (by rw [wt_X]) hm)
  · dsimp [flagImage, flagPullWeights]
    have hμ := wt_mul_le weights (MvPolynomial.C μ : Poly3 K)
      (MvPolynomial.X 0)
    have hν := wt_mul_le weights (MvPolynomial.C (μ * lam - ν) : Poly3 K)
      (MvPolynomial.X 2)
    rw [wt_C, Nat.zero_add, wt_X] at hμ hν
    have hinner := wt_sub_le weights
      (MvPolynomial.C μ * MvPolynomial.X 0)
      (MvPolynomial.C (μ * lam - ν) * MvPolynomial.X 2)
    have houter := wt_sub_le weights (MvPolynomial.X 1)
      (MvPolynomial.C μ * MvPolynomial.X 0 -
        MvPolynomial.C (μ * lam - ν) * MvPolynomial.X 2)
    exact houter.trans (max_le_max (by rw [wt_X])
      (hinner.trans (max_le_max hμ hν)))
  · simp [flagImage, flagPullWeights, wt_X]

theorem flag_monomial_product_wt_le
    (weights : Fin 3 → ℕ) (lam μ ν : K) (d : Fin 3 →₀ ℕ) :
    wt weights (∏ i ∈ d.support, flagImage lam μ ν i ^ d i) ≤
      Finsupp.weight (flagPullWeights weights) d := by
  apply (wt_finset_prod_le_sum weights d.support
    (fun i ↦ flagImage lam μ ν i ^ d i)).trans
  calc
    (∑ i ∈ d.support, wt weights (flagImage lam μ ν i ^ d i)) ≤
        ∑ i ∈ d.support, d i * flagPullWeights weights i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (wt_pow_le weights (flagImage lam μ ν i) (d i)).trans
        (Nat.mul_le_mul_left _ (flagImage_wt_le weights lam μ ν i))
    _ = Finsupp.weight (flagPullWeights weights) d := by
      rw [Finsupp.weight_apply]
      simp only [Finsupp.sum, nsmul_eq_mul]
      simp

theorem flagAlgHom_wt_le_pulled
    (weights : Fin 3 → ℕ) (lam μ ν : K) (F : Poly3 K) :
    wt weights (flagAlgHom lam μ ν F) ≤ wt (flagPullWeights weights) F := by
  change wt weights
      (MvPolynomial.eval₂ MvPolynomial.C (flagImage lam μ ν) F) ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply wt_finset_sum_le
  intro d hd
  have hprod := flag_monomial_product_wt_le weights lam μ ν d
  have hcoeff : wt weights (MvPolynomial.C (F.coeff d) : Poly3 K) = 0 :=
    wt_C weights _
  have hmul := wt_mul_le weights (MvPolynomial.C (F.coeff d) : Poly3 K)
    (∏ i ∈ d.support, flagImage lam μ ν i ^ d i)
  rw [hcoeff, Nat.zero_add] at hmul
  exact hmul.trans (hprod.trans
    (MvPolynomial.le_weightedTotalDegree (flagPullWeights weights) hd))

def sWeight : Fin 3 → ℕ := ![0, 1, 0]
def ysWeight : Fin 3 → ℕ := ![1, 1, 0]
def totalWeight : Fin 3 → ℕ := ![1, 1, 1]

@[simp] theorem flagPullWeights_sWeight : flagPullWeights sWeight = sWeight := by
  funext i
  fin_cases i <;> simp [flagPullWeights, sWeight]

@[simp] theorem flagPullWeights_ysWeight : flagPullWeights ysWeight = ysWeight := by
  funext i
  fin_cases i <;> simp [flagPullWeights, ysWeight]

@[simp] theorem flagPullWeights_totalWeight :
    flagPullWeights totalWeight = totalWeight := by
  funext i
  fin_cases i <;> simp [flagPullWeights, totalWeight]

def PolynomialInFlag (p : FlagDegree) (F : Poly3 K) : Prop :=
  ∀ d ∈ F.support, InFlag p d

theorem wt_s_le_of_inFlag {p : FlagDegree} {F : Poly3 K}
    (hF : PolynomialInFlag p F) : wt sWeight F ≤ p.all := by
  unfold wt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := (hF d hd).1
  simpa [sWeight, weight_fin3] using h

theorem wt_ys_le_of_inFlag {p : FlagDegree} {F : Poly3 K}
    (hF : PolynomialInFlag p F) : wt ysWeight F ≤ p.yz + p.all := by
  unfold wt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := (hF d hd).2.1
  simpa [ysWeight, weight_fin3, Nat.add_comm] using h

theorem wt_total_le_of_inFlag {p : FlagDegree} {F : Poly3 K}
    (hF : PolynomialInFlag p F) :
    wt totalWeight F ≤ p.zOnly + p.yz + p.all := by
  unfold wt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := (hF d hd).2.2
  simpa [totalWeight, weight_fin3, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

/-- The nested flag polytope is invariant under the two-stage triangular
change.  This is the support fact that makes the flag projection route lose
no additional degree. -/
theorem polynomialInFlag_flagAlgHom
    (p : FlagDegree) (F : Poly3 K) (lam μ ν : K)
    (hF : PolynomialInFlag p F) :
    PolynomialInFlag p (flagAlgHom lam μ ν F) := by
  intro d hd
  have hs := MvPolynomial.le_weightedTotalDegree sWeight hd
  have hys := MvPolynomial.le_weightedTotalDegree ysWeight hd
  have htot := MvPolynomial.le_weightedTotalDegree totalWeight hd
  have hsw := (flagAlgHom_wt_le_pulled sWeight lam μ ν F).trans
    (by simpa using wt_s_le_of_inFlag hF)
  have hysw := (flagAlgHom_wt_le_pulled ysWeight lam μ ν F).trans
    (by simpa using wt_ys_le_of_inFlag hF)
  have htotw := (flagAlgHom_wt_le_pulled totalWeight lam μ ν F).trans
    (by simpa using wt_total_le_of_inFlag hF)
  refine ⟨?_, ?_, ?_⟩
  · have := hs.trans hsw
    simpa [sWeight, weight_fin3] using this
  · have := hys.trans hysw
    simpa [ysWeight, weight_fin3, Nat.add_comm] using this
  · have := htot.trans htotw
    simpa [totalWeight, weight_fin3, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using this

/-! ## Literal-coordinate joint-certificate interface -/

def uOrder : Fin 3 ≃ Fin 3 := Equiv.refl _
def vOrder : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def zOrder : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

/-- The three transformed literal-coordinate certificates needed for the
nested flag projections.  Constructing these certificates is finite
joint-support/resultant arithmetic; no valuation or BKK premise remains in
this interface. -/
structure FlagJointCertificateProvider
    (lam μ ν : K) (G H : Poly3 K) (p : ℕ) : Prop where
  u : JointOrderCertificate K uOrder
    (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
  v : JointOrderCertificate K vOrder
    (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
  z : JointOrderCertificate K zOrder
    (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p

/-- Explicit joint-support projection data for the transformed equations
produces the existing literal-coordinate certificate.  This theorem is the
formal handoff from flag support arithmetic to the already verified plane
resultant/separability machinery. -/
theorem flag_jointOrderCertificate_of_projection_data
    (lam μ ν : K) (order : Fin 3 ≃ Fin 3)
    (P : Ideal (Poly3 K)) [P.IsPrime]
    (G H : Poly3 K) (p n mCap totalG totalH cap gOuter hInner : ℕ)
    (hG : Irreducible G)
    (hGmem : flagAlgHom lam μ ν G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0)))
    (hHne : H ≠ 0)
    (hGouter : (ActualPlaneCoordinateKernel.planeMap K order
      (flagAlgHom lam μ ν G)).natDegree ≤ n)
    (hHouter : (ActualPlaneCoordinateKernel.planeMap K order
      (flagAlgHom lam μ ν H)).natDegree ≤ mCap)
    (hGsupport : ∀ d ∈ (TrivariateRationalCollection.rationalMap K order
      (flagAlgHom lam μ ν G)).support, d 0 + d 1 ≤ totalG)
    (hHsupport : ∀ d ∈ (TrivariateRationalCollection.rationalMap K order
      (flagAlgHom lam μ ν H)).support, d 0 + d 1 ≤ totalH)
    (hGswapOuter : (ActualPlaneCoordinateKernel.planeMap K
      (ActualPlanePositiveOrder.swapOtherOrder order)
      (flagAlgHom lam μ ν G)).natDegree ≤ gOuter)
    (hHswapInner : Polynomial.Bivariate.degreeX
      (ActualPlaneCoordinateKernel.planeMap K
        (ActualPlanePositiveOrder.swapOtherOrder order)
        (flagAlgHom lam μ ν H)) ≤ hInner)
    (hnp : n < p) (hgOuterP : gOuter < p) (hcapP : cap < p)
    (hswapP : gOuter * hInner < p)
    (hbudget : ∀ m, m ≤ mCap →
      m * totalG + n * totalH - m * n ≤ cap) :
    JointOrderCertificate K order
      (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p := by
  exact jointOrderCertificate_of_projection_data K order P
    (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H)
    p n mCap totalG totalH cap gOuter hInner
    ((flag_irreducible_iff lam μ ν G).mpr hG) hGmem ht
    (flag_ne_zero lam μ ν hHne) hGouter hHouter hGsupport hHsupport
    hGswapOuter hHswapInner hnp hgOuterP hcapP hswapP hbudget

end

end ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch

#print axioms ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch.unflag_comp_flag
#print axioms ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch.polynomialInFlag_flagAlgHom
#print axioms ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch.flag_jointOrderCertificate_of_projection_data
