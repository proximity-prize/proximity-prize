import ProximityPrize.SubmissionLower.Koala6844VirtualHighPrimary


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN132 RCN137
open scoped Classical BigOperators

noncomputable section
set_option autoImplicit false

variable {K Seed : Type} [Field K] [Field Seed]
local notation "R" => MvPolynomial (Fin 4) K
local notation "E" => RationalCoefficients K

def boundedPartner (embed : Seed →+* E) (p : ℕ) (v : Seed → E)
    (A : Finset Seed) (caps : Rectangle) (F : R) : Prop :=
  ∃ H : R, ¬ F ∣ H ∧ H.degreeOf 1 ≤ caps.value ∧ H.degreeOf 2 ≤ caps.first ∧
    H.degreeOf 3 ≤ caps.second ∧
    ∀ g ∈ A, MvPolynomial.eval (seedPoint embed p v g) (rationalSurfaceMap K H) = 0

theorem family_degree_bounds (P : R) (hP : P ≠ 0)
    (family : Finset R) (hsub : family ⊆ normalizedFactorSet P) (i : Fin 4) :
    (∑ f ∈ family, f.degreeOf i) ≤ P.degreeOf i :=
  (Finset.sum_le_sum_of_subset hsub).trans (normalizedFactorSet_degree_budget P hP i)

theorem sum_degree_eq_factorRectangle (family : Finset R) (i : Fin 4)
    (hF : ∀ f ∈ family, f ≠ 0) :
    (∑ f ∈ family, f.degreeOf i) = (∏ f ∈ family, f).degreeOf i :=
  (MvPolynomial.degreeOf_prod_eq family id hF).symm

theorem card_resolved_family (embed : Seed →+* E) (p : ℕ) (v : Seed → E)
    (A : Finset Seed) (L : Finset R) (total cap : Rectangle)
    (hy : (∑ f ∈ L, f.degreeOf 1) ≤ total.value)
    (hb : (∑ f ∈ L, f.degreeOf 2) ≤ total.first)
    (hc : (∑ f ∈ L, f.degreeOf 3) ≤ total.second)
    (hgate : total.value * cap.first + cap.value * total.first < p)
    (hF : ∀ f ∈ L, Irreducible f ∧ 0 < f.degreeOf 1)
    (hH : ∀ f ∈ L, boundedPartner embed p v A cap f) :
    (L.biUnion (regularSeeds embed p v A)).card ≤ resultantCharge p total cap := by
  apply card_biUnion_le_resultantCharge p L (regularSeeds embed p v A)
    integralRectangle total cap _ hy hb hc
  intro f hf
  have yf := (Finset.single_le_sum (f := fun f : R => f.degreeOf 1)
    (fun g _ => Nat.zero_le _) hf).trans hy
  have bf := (Finset.single_le_sum (f := fun f : R => f.degreeOf 2)
    (fun g _ => Nat.zero_le _) hf).trans hb
  obtain ⟨H,hdiv,hyH,hbH,hcH,heval⟩ := hH f hf
  have hsmall := (Nat.add_le_add (Nat.mul_le_mul yf hbH) (Nat.mul_le_mul hyH bf)).trans_lt hgate
  have hcount := cardinal_resolved_integral_pair embed p f H
    (hF f hf).1 (hF f hf).2 hdiv hsmall
    (regularSeeds embed p v A f) v
    (fun g hg => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hg).1).2)
    (fun g hg => heval g (Finset.mem_filter.mp (Finset.mem_sdiff.mp hg).1).1)
  apply hcount.trans
  unfold resultantCharge integralRectangle
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ hbH) (Nat.mul_le_mul_right _ hyH))
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hcH) (Nat.mul_le_mul_right _ hyH)))

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

