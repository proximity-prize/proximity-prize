import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionLower.BCHKSLambdaAvoid

namespace ProximityPrize.SubmissionLower

open Polynomial

/-- A primitive coefficient family over a rational function field contains a
linear combination coprime to any chosen nonzero coefficient. -/
theorem exists_primitive_localized_selection
    {F J : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq J]
    (c : J → (RatFunc F)[X]) (j₀ : J) (DZ : ℕ)
    (hf : c j₀ ≠ 0)
    (hspan : Ideal.span (Set.range c) = ⊤)
    (hdeg : (c j₀).natDegree < DZ)
    (hfield : DZ < Fintype.card F) :
    ∃ h : (RatFunc F)[X],
      h ∈ Submodule.span F (Set.range c) ∧ IsCoprime (c j₀) h := by
  classical
  let f := c j₀
  have hf' : f ≠ 0 := by simpa [f] using hf
  let G := (UniqueFactorizationMonoid.normalizedFactors f).toFinset
  have hwit : ∀ g ∈ G, ∃ j, ¬ g ∣ c j := by
    intro g hg
    by_contra hn
    push Not at hn
    have hle : Ideal.span (Set.range c) ≤ Ideal.span {g} :=
      Ideal.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        simpa [Ideal.mem_span_singleton] using hn j)
    have hone : (1 : (RatFunc F)[X]) ∈ Ideal.span (Set.range c) := by
      rw [hspan]
      simp
    have hgd : g ∣ 1 := by
      simpa [Ideal.mem_span_singleton] using hle hone
    have hp : Prime g :=
      ((Polynomial.mem_normalizedFactors_iff hf').mp
        (by simpa [G, f] using hg)).1.prime
    exact hp.not_unit (isUnit_iff_dvd_one.mpr hgd)
  have hirr : ∀ g ∈ G, Irreducible g := by
    intro g hg
    exact ((Polynomial.mem_normalizedFactors_iff hf').mp
      (by simpa [G, f] using hg)).1
  have hnc : ∀ g ∈ G, g.degree ≠ 0 := by
    intro g hg hd
    exact (hirr g hg).not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hd)
  have hcard : G.card < Fintype.card F := by
    calc
      G.card ≤ f.natDegree := by
        simpa [G] using normalizedFactors_toFinset_card_le_natDegree_of_field f hf'
      _ < DZ := by simpa [f] using hdeg
      _ < Fintype.card F := hfield
  obtain ⟨h, hh, hav⟩ := lambdaAvoid G c hirr hnc hwit hcard
  have hprod : IsCoprime (UniqueFactorizationMonoid.normalizedFactors f).prod h := by
    suffices ∀ M : Multiset (RatFunc F)[X], (∀ q ∈ M, q ∈ G) → IsCoprime M.prod h by
      exact this _ (by simp [G])
    intro M hM
    induction M using Multiset.induction_on with
    | empty => exact isCoprime_one_left
    | cons g s ih =>
        rw [Multiset.prod_cons]
        apply IsCoprime.mul_left
        · exact (hirr g (hM g (by simp))).prime.coprime_iff_not_dvd.mpr
            (hav g (hM g (by simp)))
        · apply ih
          intro q hq
          exact hM q (by simp [hq])
  rcases UniqueFactorizationMonoid.prod_normalizedFactors hf' with ⟨u, hu⟩
  refine ⟨h, hh, ?_⟩
  change IsCoprime f h
  rw [← hu]
  exact (isCoprime_mul_unit_right_left u.isUnit _ _).mpr hprod

end ProximityPrize.SubmissionLower
