import ProximityPrize.SubmissionLower.Koala6844VirtualHighExceptions
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRouting


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open RCN132 RCN137 UniqueFactorizationMonoid
open scoped Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {K Seed : Type} [Field K] [Field Seed]
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local notation "R" => MvPolynomial (Fin 4) K
local notation "E" => RationalCoefficients K

def regularSeeds (embed : Seed →+* E) (p : ℕ) (v : Seed → E) (A : Finset Seed) (F : R) :=
  surfaceSeeds embed p v A F \ surfaceSeeds embed p v A (MvPolynomial.pderiv 1 F)

def primaryFactors (P : R) :=
  (normalizedFactorSet P).filter fun f => 0 < f.degreeOf 1 ∧
    0 < f.degreeOf 2 + f.degreeOf 3

def initialExceptional (embed : Seed →+* E) (p : ℕ) (v : Seed → E) (A : Finset Seed) (P : R) :=
  let factors := normalizedFactorSet P
  let seedOnly := (factors.filter fun f => f.degreeOf 1 = 0).biUnion (surfaceSeeds embed p v A)
  let valueOnly := (factors.filter fun f => f.degreeOf 2 = 0 ∧ f.degreeOf 3 = 0).biUnion
    (surfaceSeeds embed p v A)
  let singular := (factors.filter fun f => 0 < f.degreeOf 1).biUnion fun f =>
    surfaceSeeds embed p v A f ∩ surfaceSeeds embed p v A (MvPolynomial.pderiv 1 f)
  seedOnly ∪ valueOnly ∪ singular

theorem primary_seeds_cover (embed : Seed →+* E) (p : ℕ) (v : Seed → E) (A : Finset Seed)
    (P : R) (hP : P ≠ 0)
    (hz : ∀ g ∈ A, MvPolynomial.eval (seedPoint embed p v g) (rationalSurfaceMap K P) = 0) :
    A ⊆ initialExceptional embed p v A P ∪
      (primaryFactors P).biUnion (regularSeeds embed p v A) := by
  intro g hg
  let h := (MvPolynomial.eval (seedPoint embed p v g)).comp (rationalSurfaceMap K)
  obtain ⟨f,hf,hf0⟩ := exists_normalizedFactorSet_zero h P hP (hz g hg)
  have hfa : g ∈ surfaceSeeds embed p v A f := Finset.mem_filter.mpr ⟨hg,hf0⟩
  by_cases hy : f.degreeOf 1 = 0
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨f,Finset.mem_filter.mpr ⟨hf,hy⟩,hfa⟩)))
  by_cases hseed : f.degreeOf 2 + f.degreeOf 3 = 0
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨f,Finset.mem_filter.mpr ⟨hf,by omega⟩,hfa⟩)))
  by_cases hd : g ∈ surfaceSeeds embed p v A (MvPolynomial.pderiv 1 f)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨f,Finset.mem_filter.mpr ⟨hf,Nat.pos_of_ne_zero hy⟩,
        Finset.mem_inter.mpr ⟨hfa,hd⟩⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨f,Finset.mem_filter.mpr ⟨hf,Nat.pos_of_ne_zero hy,Nat.pos_of_ne_zero hseed⟩,
        Finset.mem_sdiff.mpr ⟨hfa,hd⟩⟩)

theorem primary_nonassociate (P : R) {f g : R}
    (hf : f ∈ normalizedFactorSet P) (hg : g ∈ normalizedFactorSet P)
    (hne : f ≠ g) : ¬ f ∣ g := by
  classical
  have hf' : f ∈ normalizedFactors P := by simpa only [normalizedFactorSet, Multiset.mem_toFinset] using hf
  have hg' : g ∈ normalizedFactors P := by simpa only [normalizedFactorSet, Multiset.mem_toFinset] using hg
  have hfI := irreducible_of_normalized_factor f hf'
  have hgI := irreducible_of_normalized_factor g hg'
  intro h
  apply hne
  apply mem_normalizedFactors_eq_of_associated hf' hg'
  exact (hfI.dvd_irreducible_iff_associated hgI).mp h

theorem card_singular_factor {p : ℕ} [CharP K p]
    (embed : Seed →+* E) (v : Seed → E) (A : Finset Seed)
    (F : R) (hF : Irreducible F) (hy : 0 < F.degreeOf 1) (hc : F.degreeOf 1 < p)
    (hsmall : 2 * F.degreeOf 1 * F.degreeOf 2 < p) :
    (surfaceSeeds embed p v A F ∩ surfaceSeeds embed p v A (MvPolynomial.pderiv 1 F)).card ≤
      (2 * F.degreeOf 1) * (F.degreeOf 2 + p * F.degreeOf 3) := by
  let H := MvPolynomial.pderiv 1 F
  have hnz : H ≠ 0 := fun h => (Nat.ne_of_gt hy)
    ((RCN267.pderiv_zero_iff_degree_zero_below_char 1 F p hc).mp h)
  have hproper : ¬ F ∣ H := by
    intro h
    have hh := RCN137.coordinate_degree_le_of_dvd 1 F H h hnz
    have hcap := RCN313.pderiv_same_degree_bound 1 F (F.degreeOf 1) le_rfl
    change H.degreeOf 1 ≤ F.degreeOf 1 - 1 at hcap
    omega
  have hd (i : Fin 4) : H.degreeOf i ≤ F.degreeOf i :=
    RCN313.pderiv_degree_bound 1 i F (F.degreeOf i) le_rfl
  have hlow : F.degreeOf 1 * H.degreeOf 2 + H.degreeOf 1 * F.degreeOf 2
      ≤ 2 * F.degreeOf 1 * F.degreeOf 2 := by
    have h := Nat.add_le_add (Nat.mul_le_mul_left (F.degreeOf 1) (hd 2))
      (Nat.mul_le_mul_right (F.degreeOf 2) (hd 1))
    convert h using 1 <;> ring
  have hhigh : F.degreeOf 1 * H.degreeOf 3 + H.degreeOf 1 * F.degreeOf 3
      ≤ 2 * F.degreeOf 1 * F.degreeOf 3 := by
    have h := Nat.add_le_add (Nat.mul_le_mul_left (F.degreeOf 1) (hd 3))
      (Nat.mul_le_mul_right (F.degreeOf 3) (hd 1))
    convert h using 1 <;> ring
  apply (cardinal_resolved_integral_pair embed p F H hF hy hproper (hlow.trans_lt hsmall)
    _ v (fun g hg => (Finset.mem_filter.mp (Finset.mem_inter.mp hg).1).2)
    (fun g hg => (Finset.mem_filter.mp (Finset.mem_inter.mp hg).2).2)).trans
  change F.degreeOf 1 * H.degreeOf 2 + H.degreeOf 1 * F.degreeOf 2 +
    p*(F.degreeOf 1 * H.degreeOf 3 + H.degreeOf 1 * F.degreeOf 3) ≤ _
  refine (Nat.add_le_add hlow (Nat.mul_le_mul_left _ hhigh)).trans ?_
  apply le_of_eq
  ring

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

