import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactFactorCaps

/-!
# Full-triangle support inherited by factors

The tetrahedral interpolation support is equivalently the weighted support
bound for the surface variables `(Y,R,Z)`.  Weighted total degree is
monotone under divisibility, so every nonzero factor of the interpolant
inherits the same tetrahedral support.
-/

namespace ProximityPrize.SubmissionLower.ContactFullTriangleInheritance

open ContactInterpolation ContactFactorCaps ContactGenericSurface

noncomputable section

variable {K : Type*} [Field K]

def fullSurfaceWeights : Fin 4 → ℕ := ![0, 1, 1, 1]

local notation:1000 "WF " P:1000 =>
  MvPolynomial.weightedTotalDegree fullSurfaceWeights P

theorem full_surface_weight (d : Fin 4 →₀ ℕ) :
    Finsupp.weight fullSurfaceWeights d = d 1 + d 2 + d 3 := by
  rw [weight_fin4]
  simp [fullSurfaceWeights]

lemma fullTriangleBox_wt_le (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hF : F ∈ fullTriangleBox K L) : WF F ≤ L := by
  apply (weightedTotalDegree_le_iff fullSurfaceWeights F L).mpr
  intro d hd
  have ht : d 1 + d 2 + d 3 ≤ L := hF hd
  simpa only [full_surface_weight] using ht

lemma fullTriangleBox_of_wt_le (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hF : WF F ≤ L) : F ∈ fullTriangleBox K L := by
  intro d hd
  have hw := (MvPolynomial.le_weightedTotalDegree fullSurfaceWeights hd).trans hF
  rw [full_surface_weight] at hw
  exact hw

lemma fullTriangleBox_of_dvd (F Q : MvPolynomial (Fin 4) K) (L : ℕ)
    (hQ : Q ≠ 0) (hdiv : F ∣ Q) (hfull : Q ∈ fullTriangleBox K L) :
    F ∈ fullTriangleBox K L := by
  apply fullTriangleBox_of_wt_le F L
  exact (weightedTotalDegree_le_of_dvd fullSurfaceWeights F Q hdiv hQ).trans
    (fullTriangleBox_wt_le Q L hfull)

end

end ProximityPrize.SubmissionLower.ContactFullTriangleInheritance
