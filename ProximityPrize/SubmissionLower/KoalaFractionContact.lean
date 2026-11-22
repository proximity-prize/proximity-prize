import ProximityPrize.SubmissionLower.Shared50ShapeRank
import ProximityPrize.SubmissionLower.KoalaVariableSelect

set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace KoalaFractionContact
noncomputable section

open K1_13 (Row Geom shape)
open K1_13_2_2 (gradeWeight oldWeight)
open K1_13_6 (GenericField GeoJets cycleLength intersectionIdeal toGeneric genericCoeffs)
open K1_13_6_1_2 (VanishesTo hassePartial multiOrder cycleLength_ge_order)
open K1_13_6_1_2_2 (vanishesTo_of_hasse)
open Shared50Rational
open private hasse_C_mul from ProximityPrize.SubmissionLower.Shared50ShapeRank
open scoped Polynomial
open MvPolynomial

private theorem frac_map (Q : Row 4) :
    toFraction Q = MvPolynomial.map (algebraMap Geom[X] GenericField) Q := rfl

private theorem contact_clear {Q : Row 4} {v : FractionJet} {k : GenericField} {r : ℕ}
    {P : Ideal GeoJets} [P.IsPrime]
    (hd : toFraction Q = MvPolynomial.C k * v)
    (hc : ∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric v) ∈ P) :
    VanishesTo P (toGeneric Q) r := by
  apply vanishesTo_of_hasse _ P r
  intro a ha
  rw [← fraction_geometric Q, hd, map_mul, toGeometric, MvPolynomial.map_C, hasse_C_mul]
  exact P.mul_mem_left _ (hc a ha)

private theorem proper_after_clear {f C : Row 4} {c : FractionJet} {k : GenericField}
    (hk : k ≠ 0) (hC : toFraction C = MvPolynomial.C k * c) (hc : ¬ toFraction f ∣ c) :
    ¬ f ∣ C := by
  intro hh
  apply hc
  obtain ⟨d, hd⟩ := map_dvd (MvPolynomial.map (algebraMap Geom[X] GenericField)) hh
  have he : MvPolynomial.C k * c = toFraction f * d := hC.symm.trans hd
  refine ⟨MvPolynomial.C k⁻¹ * d, ?_⟩
  calc
    c = MvPolynomial.C k⁻¹ * (MvPolynomial.C k * c) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
    _ = _ := by rw [he]; ring

end
end KoalaFractionContact
