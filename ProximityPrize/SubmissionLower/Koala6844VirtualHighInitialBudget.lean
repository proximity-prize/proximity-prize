import ProximityPrize.SubmissionLower.Koala6844VirtualHighPartnerCount


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN132 RCN137
open scoped Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {K Seed : Type} [Field K] [Field Seed]
local notation "R" => MvPolynomial (Fin 4) K
local notation "E" => RationalCoefficients K

theorem card_initialExceptional [CharP K modulus] (embed : Seed →+* E) (v : Seed → E)
    (A : Finset Seed) (hinj : Set.InjOn v (↑A : Set Seed))
    (P : R) (hP : P ≠ 0) (hy : P.degreeOf 1 ≤ 179)
    (hb : P.degreeOf 2 ≤ 3800) (hc : P.degreeOf 3 ≤ 3800) :
    (initialExceptional embed modulus v A P).card ≤ excludedBudget := by
  let factors := normalizedFactorSet P
  let S := factors.filter fun f => f.degreeOf 1 = 0
  let V := factors.filter fun f => f.degreeOf 2 = 0 ∧ f.degreeOf 3 = 0
  let T := factors.filter fun f => 0 < f.degreeOf 1
  let w (f : R) := f.degreeOf 2 + modulus * f.degreeOf 3
  let wtotal := 3800 + modulus * 3800
  have wsum (s : Finset R) (hsub : s ⊆ factors) : (∑ f ∈ s, w f) ≤ wtotal := by
    have h₂ := (family_degree_bounds P hP s hsub 2).trans hb
    have h₃ := (family_degree_bounds P hP s hsub 3).trans hc
    simpa only [w,wtotal,Finset.sum_add_distrib,← Finset.mul_sum] using
      Nat.add_le_add h₂ (Nat.mul_le_mul_left modulus h₃)
  have hone (f : R) (hf : f ∈ factors) (i : Fin 4) : f.degreeOf i ≤ P.degreeOf i :=
    coordinate_degree_le_of_dvd i f P (normalizedFactorSet_spec P f hf).2 hP
  have hS : (S.biUnion (surfaceSeeds embed modulus v A)).card ≤ wtotal := by
    apply (Finset.card_biUnion_le).trans
    apply (Finset.sum_le_sum fun f hf => ?_).trans (wsum S (Finset.filter_subset _ _))
    have hm := Finset.mem_filter.mp hf
    exact card_seed_only A f (normalizedFactorSet_spec P f hm.1).1.ne_zero hm.2
      (by decide +kernel) (((hone f hm.1 2).trans hb).trans_lt (by decide +kernel : 3800 < modulus))
  have hV : (V.biUnion (surfaceSeeds embed modulus v A)).card ≤ 179 := by
    apply (Finset.card_biUnion_le).trans
    apply (Finset.sum_le_sum fun f hf => ?_).trans
      ((family_degree_bounds P hP V (Finset.filter_subset _ _) 1).trans hy)
    have hm := Finset.mem_filter.mp hf
    exact card_seed_free A hinj f (normalizedFactorSet_spec P f hm.1).1.ne_zero hm.2.1 hm.2.2
  have hT : (T.biUnion fun f => surfaceSeeds embed modulus v A f ∩
      surfaceSeeds embed modulus v A (MvPolynomial.pderiv 1 f)).card ≤ (2*179)*wtotal := by
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun f => (2*179)*w f) (fun f hf => ?_)).trans ?_)
    · have hm := Finset.mem_filter.mp hf
      have hfy := (hone f hm.1 1).trans hy
      have hfb := (hone f hm.1 2).trans hb
      have hdig := (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hfy) hfb).trans_lt
        (by decide +kernel : 2*179*3800 < modulus)
      exact (card_singular_factor embed v A f (normalizedFactorSet_spec P f hm.1).1 hm.2
        (hfy.trans_lt (by decide +kernel)) hdig).trans (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 2 hfy))
    · rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (wsum T (Finset.filter_subset _ _))
  change ((S.biUnion (surfaceSeeds embed modulus v A)) ∪
    (V.biUnion (surfaceSeeds embed modulus v A)) ∪ (T.biUnion fun f =>
      surfaceSeeds embed modulus v A f ∩ surfaceSeeds embed modulus v A (MvPolynomial.pderiv 1 f))).card ≤ _
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add hS hV)) hT).trans
      (by decide +kernel))

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

