import ProximityPrize.SubmissionLower.Shared50MultiplicityLocal

set_option Elab.async false
set_option maxHeartbeats 750000

namespace Shared50Multiplicity

open K1_13 (Row)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height)
open K1_13_6_3 (cycleWeight)
open scoped ENat BigOperators

/-- Prescribed orders on the two cutting equations multiply in the original
height-two local intersection length. The gain feeds the existing cycle ledger. -/
theorem cycleLength_ge_product {f Q : Row 4} {P : Ideal GeoJets} [P.IsPrime] {a b : ℕ}
    (hheight : P.height = 2) (hf : VanishesTo P (toGeneric f) a)
    (hQ : VanishesTo P (toGeneric Q) b) :
    ((a*b : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P ‹P.IsPrime› := by
  let L := Localization.AtPrime P
  let φ := algebraMap GeoJets L
  let : IsRegularLocalRing L := by
    change IsRegularLocalRing (Localization.AtPrime P)
    infer_instance
  have hm2 : (IsLocalRing.maximalIdeal L).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := L)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P L, hheight] at h
    exact_mod_cast h
  have hmap : (intersectionIdeal f Q).map φ =
      Ideal.span {φ (toGeneric f), φ (toGeneric Q)} := by
    rw [intersectionIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change ((a*b : ℕ) : ℕ∞) ≤ Module.length L (L ⧸ (intersectionIdeal f Q).map φ)
  rw [hmap]
  exact length_ge_product hm2 hf hQ

theorem cycleLength_ge_product_of_minimal {f Q : Row 4} {P : Ideal GeoJets} {a b : ℕ}
    (hP : (intersectionIdeal f Q).IsMinimalPrime P) (hfn : toGeneric f ≠ 0)
    (hQrel : IsRelPrime (toGeneric f) (toGeneric Q))
    (hf : @VanishesTo GeoJets _ P hP.isPrime (toGeneric f) a)
    (hQ : @VanishesTo GeoJets _ P hP.isPrime (toGeneric Q) b) :
    ((a*b : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P hP.isPrime := by
  let := hP.isPrime
  exact cycleLength_ge_product (pair_height hfn hQrel hP) hf hQ

end Shared50Multiplicity
