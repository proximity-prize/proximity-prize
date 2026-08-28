import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpecialization
import ProximityPrize.SubmissionLower.BCHKSLambdaAvoid

namespace ProximityPrize.SubmissionLower
open Polynomial

/-- Localized lambda selection for a capped factor over the concrete IRS field. -/
theorem exists_localized_coprime_pair
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (j0 : ℕ)
    (hf0 : (localizedSwapY R).coeff j0 ≠ 0)
    (htop : Ideal.span (Set.range (localizedSwapY R).coeff) = ⊤)
    (hcdeg : ∀ j, ((localizedSwapY R).coeff j).natDegree ≤ BCHKSConcreteGS.DZ) :
    let c := (localizedSwapY R).coeff
    let f := c j0
    ∃ h : (RatFunc ProximityPrize.Benchmark.IRSProfile.Field)[X],
      h ∈ Submodule.span ProximityPrize.Benchmark.IRSProfile.Field (Set.range c) ∧
      IsCoprime f h ∧ f.natDegree ≤ BCHKSConcreteGS.DZ := by
  classical
  let c := (localizedSwapY R).coeff
  let f := c j0
  let G := (UniqueFactorizationMonoid.normalizedFactors f).toFinset
  have hwit : ∀ g ∈ G, ∃ j, ¬ g ∣ c j := by
    intro g hg
    by_contra hn
    push Not at hn
    have hle : Ideal.span (Set.range c) ≤ Ideal.span {g} :=
      Ideal.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        simpa [Ideal.mem_span_singleton] using hn j)
    have hone : (1 : (RatFunc ProximityPrize.Benchmark.IRSProfile.Field)[X]) ∈
        Ideal.span (Set.range c) := by rw [htop]; simp
    have hgd : g ∣ 1 := by simpa [Ideal.mem_span_singleton] using hle hone
    have hp : Prime g :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hf0).mp
        (by simpa [G, f, c] using hg) |>.1
    exact hp.not_unit (isUnit_iff_dvd_one.mpr hgd)
  have hirr : ∀ g ∈ G, Irreducible g := by
    intro g hg
    exact ((Polynomial.mem_normalizedFactors_iff hf0).mp
      (by simpa [G, f, c] using hg)).1
  have hnc : ∀ g ∈ G, g.degree ≠ 0 := by
    intro g hg hdegree
    have := (hirr g hg).not_unit
    apply this
    exact Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree
  have hcard : G.card < Fintype.card
      ProximityPrize.Benchmark.IRSProfile.Field := by
    calc
      G.card ≤ f.natDegree := by
        simpa [G] using normalizedFactors_toFinset_card_le_natDegree_of_field f hf0
      _ ≤ BCHKSConcreteGS.DZ := hcdeg j0
      _ < Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
        norm_num [BCHKSConcreteGS.DZ, ProximityPrize.Benchmark.IRSProfile.Field]
  obtain ⟨h, hh, hav⟩ := lambdaAvoid G c hirr hnc hwit hcard
  have hprod : IsCoprime (UniqueFactorizationMonoid.normalizedFactors f).prod h := by
    apply Multiset.induction_on (UniqueFactorizationMonoid.normalizedFactors f)
    · simp
    · intro g s ih
      rw [Multiset.prod_cons]
      apply IsCoprime.mul_left
      · exact (hirr g (by simp [G])).prime.coprime_iff_not_dvd.mpr
          (hav g (by simp [G]))
      · exact ih (fun q hq => hirr q (by simp [G, hq]))
          (fun q hq => hav q (by simp [G, hq]))
  rcases UniqueFactorizationMonoid.prod_normalizedFactors hf0 with ⟨u, hu⟩
  refine ⟨h, hh, ?_, hcdeg j0⟩
  rw [← hu]
  exact (isCoprime_mul_unit_right_left u.isUnit _ _).mpr hprod

end ProximityPrize.SubmissionLower
