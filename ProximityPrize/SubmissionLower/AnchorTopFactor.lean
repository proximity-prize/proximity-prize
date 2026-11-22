import ProximityPrize.SubmissionLower.Fast054

set_option Elab.async false

/- The four-factor kernel argument is from the accepted KoalaBear proof.
   Multiplication by a power of the third derivative raises the old index by
   three and the contact order by two for each copy. -/
namespace SoundnessAnchor
open K1_13 K1_13_1_1 MvPolynomial
open private smallContact smallContact_order bandSpace_pow monomial_band capX from ProximityPrize.SubmissionLower.Fast054
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

structure Powers where
  base : FactorPowers
  top : ℕ

def Powers.degree (v : Powers) := v.base.degree + v.top
def Powers.minIndex (v : Powers) := v.base.minIndex + v.top * 3
def Powers.maxIndex (v : Powers) := v.base.maxIndex + v.top * 3
def Powers.maxTop (v : Powers) := v.base.maxTop + v.top
def Powers.minOrder (v : Powers) := v.base.minOrder + v.top * 2
def Powers.factor (v : Powers) : Form := flagFactor v.base * MvPolynomial.X 3 ^ v.top

private theorem factor_band (v : Powers) :
    v.factor ∈ bandSpace v.degree v.minIndex v.maxIndex v.maxTop := by
  have hx : (MvPolynomial.X 3 : Form) ∈ bandSpace 1 3 3 1 := by
    simpa using monomial_band 0 0 0 1 (d := 1) (lo := 3) (hi := 3) (top := 1)
      (by decide) (by decide) (by decide) (by decide)
  simpa [Powers.factor, Powers.degree, Powers.minIndex, Powers.maxIndex, Powers.maxTop]
    using bandSpace_mul (flagFactor_mem_band v.base) (bandSpace_pow hx v.top)

private theorem factor_order (v : Powers) :
    backShift v.factor ∈ restrictWeightedOrder targetOrder v.minOrder := by
  have hx : backShift (MvPolynomial.X 3) ∈ restrictWeightedOrder targetOrder 2 := by
    rw [backShift_X_of_ne 3 (by decide)]
    exact capX 3
  simpa only [Powers.factor, Powers.minOrder, map_pow, map_mul]
    using mul_mem_restrictWeightedOrder (flagFactor_target_order v.base)
      (pow_mem_restrictWeightedOrder hx v.top)

private theorem factor_ne (v : Powers) : v.factor ≠ 0 :=
  mul_ne_zero (flagFactor_ne_zero v.base) (pow_ne_zero _ (MvPolynomial.X_ne_zero _))

/-- Truncate a homogeneous band after the change of jet coordinates. -/
def blockAt (d s : ℕ) (g : ℤ) : bandSpace d (-g) 48 10 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _





end
end SoundnessAnchor
