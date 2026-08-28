import ProximityPrize.SubmissionLower.BCHKSStagedPairAssembly
import ProximityPrize.SubmissionLower.BCHKSSingleFactorGood

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The outer integration theorem: the only missing input is a quantitative
primitive-specialization certificate for each possible first-stage factor. -/
theorem exists_concrete_staged_pair_of_certificates
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (cert : ∀ R : Polynomial (Polynomial (Polynomial F)),
      ClearedPrimitiveCertificate F R)
    (hcertDegree : ∀ R : Polynomial (Polynomial (Polynomial F)),
      (cert R).obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F)
    (hfactorXDegree : ∀ (R : Polynomial (Polynomial (Polynomial F))) (x : F),
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 519143)
    (hchar : 852 < ringChar F)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 851)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 519143)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 111624646)
    (hcard : 632176 * 519142 * 851 ^ 2 +
      (bchksErrors + 1) * 851 + 2 * 519143 * 851 < S.card) :
    ∃ R H T x₀, ∃ Bad : Finset F,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval x₀ (P z)) z = 0) ∧
      (if R.natDegree = 1 then 2 * 111624646 * 519142
        else 632176 * 519142 * R.natDegree) * H.natDegree +
        (bchksErrors + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R x₀ ∧
      R.natDegree ≤ 852 ∧ H.natDegree ≤ 852 ∧
      Polynomial.Bivariate.totalDegree H ≤ 519142 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 519142 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 111624646) ∧
      RationalFunctions.HenselNumerators.Hypotheses x₀ R H ∧
      Bad.card ≤ 2 * R.natDegree * 519143 ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let good : ∀ R : Polynomial (Polynomial (Polynomial F)),
      Irreducible R → 0 < R.natDegree → R.natDegree ≤ 852 →
      ∃ x₀ : F, ∃ Bad : Finset F,
        Bad.card ≤ 2 * R.natDegree * 519143 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).IsPrimitive ∧
        (∀ z ∉ Bad, ∀ y,
          Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
          Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
    intro R hR hp hd
    apply exists_single_factor_good R hR hp
      (lt_of_le_of_lt hd hchar) (cert R)
      R.natDegree 519143 (hcertDegree R) (hfactorXDegree R)
  let pick : Polynomial (Polynomial (Polynomial F)) → F × Finset F := fun R =>
    if h : Irreducible R ∧ 0 < R.natDegree ∧ R.natDegree ≤ 852 then
      (Classical.choose (good R h.1 h.2.1 h.2.2),
        Classical.choose (Classical.choose_spec (good R h.1 h.2.1 h.2.2)))
    else (0, ∅)
  let x₀ := fun R => (pick R).1
  let Bad := fun R => (pick R).2
  have hpick : ∀ R (hi : Irreducible R) (hp : 0 < R.natDegree) (hd : R.natDegree ≤ 852),
      (Bad R).card ≤ 2 * R.natDegree * 519143 ∧
      (triSpecializeX R (x₀ R)).natDegree = R.natDegree ∧
      triSpecializeX R (x₀ R) ≠ 0 ∧
      (triSpecializeX R (x₀ R)).IsPrimitive ∧
      (∀ z ∉ Bad R, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R (x₀ R)) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z) ≠ 0) := by
    intro R hi hp hd
    simpa [x₀, Bad, pick, hi, hp, hd] using
      Classical.choose_spec (Classical.choose_spec (good R hi hp hd))
  have hRdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.natDegree ≤ 852 := by
    intro R hRQ
    calc
      R.natDegree ≤ ∑ A ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          A.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (by simpa using hRQ)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 852 := hQY.trans (by omega)
  let G : StagedGoodFamily Q S := {
    x₀ := x₀
    Bad := Bad
    badCap := fun R => 2 * R.natDegree * 519143
    specialize_ne_zero := by
      intro R hRQ hp
      exact (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.1
    primitive := by
      intro R hRQ hp
      rw [Polynomial.Bivariate.evalX_eq_map]
      exact (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.1
    bad_card := by
      intro R hRQ hp
      exact (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).1
    bad_cap := by simp
    second_ne_zero := by
      intro R hRQ hp z hz
      intro heq
      have hs := (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.2
        z (Finset.mem_sdiff.mp hz).2 0
      have hder : triSpecializeX R.derivative (x₀ R) =
          (triSpecializeX R (x₀ R)).derivative := by
        simp [triSpecializeX, Polynomial.derivative_map]
      have hd : biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z = 0 := by
        rw [hder]
        simpa [biSpecializeZ, Polynomial.derivative_map] using
          congrArg Polynomial.derivative heq
      exact (hs (by rw [heq]; simp)) (by rw [hd]; simp)
  }
  obtain ⟨R, H, T, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
      hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp⟩ :=
    exists_staged_pair_with_setup S P Q G hQ hQeval hQz hQY hQYZ
      hQweightedX hcard
  have hg := hpick R hRi hp hRd
  exact ⟨R, H, T, x₀ R, Bad R, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
    hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp, hg.1, hg.2.2.2.2⟩


/-- Effective-obstruction overload of the concrete staged-pair theorem. -/
theorem exists_concrete_staged_pair_of_effective_obstructions
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (cert : ∀ R : Polynomial (Polynomial (Polynomial F)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q → 0 < R.natDegree →
      EffectivePrimitiveObstruction F R)
    (hcertDegree : ∀ (R : Polynomial (Polynomial (Polynomial F)))
      (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (hp : 0 < R.natDegree),
      (cert R hRQ hp).obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F)
    (hfactorXDegree : ∀ (R : Polynomial (Polynomial (Polynomial F)))
      (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (hp : 0 < R.natDegree)
      (x : F),
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 519143)
    (hchar : 852 < ringChar F)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 851)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 519143)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 111624646)
    (hcard : 632176 * 519142 * 851 ^ 2 +
      (bchksErrors + 1) * 851 + 2 * 519143 * 851 < S.card) :
    ∃ R H T x₀, ∃ Bad : Finset F,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval x₀ (P z)) z = 0) ∧
      (if R.natDegree = 1 then 2 * 111624646 * 519142
        else 632176 * 519142 * R.natDegree) * H.natDegree +
        (bchksErrors + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R x₀ ∧
      R.natDegree ≤ 852 ∧ H.natDegree ≤ 852 ∧
      Polynomial.Bivariate.totalDegree H ≤ 519142 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 519142 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 111624646) ∧
      RationalFunctions.HenselNumerators.Hypotheses x₀ R H ∧
      Bad.card ≤ 2 * R.natDegree * 519143 ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let good : ∀ R : Polynomial (Polynomial (Polynomial F)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q →
      Irreducible R → 0 < R.natDegree → R.natDegree ≤ 852 →
      ∃ x₀ : F, ∃ Bad : Finset F,
        Bad.card ≤ 2 * R.natDegree * 519143 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).IsPrimitive ∧
        (∀ z ∉ Bad, ∀ y,
          Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
          Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
    intro R hRQ hR hp hd
    apply exists_single_factor_good_effective R hR hp
      (lt_of_le_of_lt hd hchar) (cert R hRQ hp)
      R.natDegree 519143 (hcertDegree R hRQ hp) (hfactorXDegree R hRQ hp)
  let pick : Polynomial (Polynomial (Polynomial F)) → F × Finset F := fun R =>
    if h : R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        Irreducible R ∧ 0 < R.natDegree ∧ R.natDegree ≤ 852 then
      (Classical.choose (good R h.1 h.2.1 h.2.2.1 h.2.2.2),
        Classical.choose (Classical.choose_spec (good R h.1 h.2.1 h.2.2.1 h.2.2.2)))
    else (0, ∅)
  let x₀ := fun R => (pick R).1
  let Bad := fun R => (pick R).2
  have hpick : ∀ R (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
      (hi : Irreducible R) (hp : 0 < R.natDegree) (hd : R.natDegree ≤ 852),
      (Bad R).card ≤ 2 * R.natDegree * 519143 ∧
      (triSpecializeX R (x₀ R)).natDegree = R.natDegree ∧
      triSpecializeX R (x₀ R) ≠ 0 ∧
      (triSpecializeX R (x₀ R)).IsPrimitive ∧
      (∀ z ∉ Bad R, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R (x₀ R)) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z) ≠ 0) := by
    intro R hRQ hi hp hd
    simpa [x₀, Bad, pick, hRQ, hi, hp, hd] using
      Classical.choose_spec (Classical.choose_spec (good R hRQ hi hp hd))
  have hRdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.natDegree ≤ 852 := by
    intro R hRQ
    calc
      R.natDegree ≤ ∑ A ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          A.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (by simpa using hRQ)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 852 := hQY.trans (by omega)
  let G : StagedGoodFamily Q S := {
    x₀ := x₀
    Bad := Bad
    badCap := fun R => 2 * R.natDegree * 519143
    specialize_ne_zero := by
      intro R hRQ hp
      exact (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.1
    primitive := by
      intro R hRQ hp
      rw [Polynomial.Bivariate.evalX_eq_map]
      exact (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.1
    bad_card := by
      intro R hRQ hp
      exact (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).1
    bad_cap := by simp
    second_ne_zero := by
      intro R hRQ hp z hz
      intro heq
      have hs := (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.2
        z (Finset.mem_sdiff.mp hz).2 0
      have hder : triSpecializeX R.derivative (x₀ R) =
          (triSpecializeX R (x₀ R)).derivative := by
        simp [triSpecializeX, Polynomial.derivative_map]
      have hd : biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z = 0 := by
        rw [hder]
        simpa [biSpecializeZ, Polynomial.derivative_map] using
          congrArg Polynomial.derivative heq
      exact (hs (by rw [heq]; simp)) (by rw [hd]; simp)
  }
  obtain ⟨R, H, T, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
      hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp⟩ :=
    exists_staged_pair_with_setup S P Q G hQ hQeval hQz hQY hQYZ
      hQweightedX hcard
  have hg := hpick R hRQ hRi hp hRd
  exact ⟨R, H, T, x₀ R, Bad R, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
    hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp, hg.1, hg.2.2.2.2⟩

end ProximityPrize.SubmissionLower
