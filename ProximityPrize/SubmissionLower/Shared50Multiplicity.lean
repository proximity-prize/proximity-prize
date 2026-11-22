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

/-- Convert a multiplicity product to the natural weight used by the mixed-degree ledger. -/
theorem cycleWeight_ge_product {f Q : Row 4} {P : Ideal GeoJets} {a b : ℕ}
    (hP : (intersectionIdeal f Q).IsMinimalPrime P) (hfn : toGeneric f ≠ 0)
    (hQrel : IsRelPrime (toGeneric f) (toGeneric Q))
    (hfin : cycleLength (intersectionIdeal f Q) P hP.isPrime ≠ ⊤)
    (hf : @VanishesTo GeoJets _ P hP.isPrime (toGeneric f) a)
    (hQ : @VanishesTo GeoJets _ P hP.isPrime (toGeneric Q) b) :
    a*b ≤ cycleWeight (intersectionIdeal f Q) P := by
  have h := cycleLength_ge_product_of_minimal hP hfn hQrel hf hQ
  have hp : (cycleWeight (intersectionIdeal f Q) P : ℕ∞) =
      cycleLength (intersectionIdeal f Q) P hP.isPrime := by
    simp only [cycleWeight, dite_eq_left hP.isPrime]
    exact ENat.natCast_toNat hfin
  rw [← hp] at h
  exact_mod_cast h

/-- Any selected components can use the product lower bounds in the existing
weighted projective degree sum. -/
theorem product_degree_le_cycle_budget {f Q : Row 4} (hfn : toGeneric f ≠ 0)
    (hQrel : IsRelPrime (toGeneric f) (toGeneric Q))
    (selected : Finset (Ideal GeoJets)) (a b : Ideal GeoJets → ℕ)
    (hdata : ∀ P ∈ selected, ∃ hP : (intersectionIdeal f Q).IsMinimalPrime P,
      cycleLength (intersectionIdeal f Q) P hP.isPrime ≠ ⊤ ∧
      @VanishesTo GeoJets _ P hP.isPrime (toGeneric f) (a P) ∧
      @VanishesTo GeoJets _ P hP.isPrime (toGeneric Q) (b P)) :
    (∑ P ∈ selected, ((a P*b P : ℕ) : ℚ) * MvPolynomial.affineDegree P) ≤
      ∑ P ∈ (intersectionIdeal f Q).minimalPrimesFinset,
        (cycleWeight (intersectionIdeal f Q) P : ℚ) * MvPolynomial.affineDegree P := by
  classical
  have hsubset : selected ⊆ (intersectionIdeal f Q).minimalPrimesFinset := by
    intro P hP
    obtain ⟨hp,_,_,_⟩ := hdata P hP
    exact Ideal.mem_minimalPrimesFinset.mpr hp
  calc
    _ ≤ ∑ P ∈ selected, (cycleWeight (intersectionIdeal f Q) P : ℚ) * MvPolynomial.affineDegree P := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hp,hfinite,ha,hb⟩ := hdata P hP
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (cycleWeight_ge_product hp hfn hQrel hfinite ha hb))
        (MvPolynomial.affineDegree_nonneg P)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun P _ _ => mul_nonneg (Nat.cast_nonneg _) (MvPolynomial.affineDegree_nonneg P))

#print axioms cycleLength_ge_product
#print axioms cycleLength_ge_product_of_minimal
#print axioms product_degree_le_cycle_budget
end Shared50Multiplicity
