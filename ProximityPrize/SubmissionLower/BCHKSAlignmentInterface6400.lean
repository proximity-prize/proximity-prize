import ProximityPrize.SubmissionLower.BCHKSInterpolation6400
import ProximityPrize.SubmissionLower.BCHKSFixedFactorSelection6400
import ProximityPrize.SubmissionLower.BCHKSFixedFactorDegree1146400

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open BCHKSSubstitutionVanish
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- Exact score-64 polynomial-alignment statement remaining after concrete
interpolation. -/
def BCHKSPolynomialAlignment6400 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↥S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field))),
    bchksNumerator6400 < S.card →
    Q ≠ 0 →
    (∀ z : ↥S, (P z).natDegree ≤ 131071) →
    (∀ z : ↥S, 185364 ≤ (A z.1).card) →
    (∀ z : ↥S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) →
    (∀ z : ↥S, triEval Q z.1 (P z) = 0) →
    (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      j < 63522 ∧ a + 131071 * j < 8325809424 ∧
        ((Q.coeff j).coeff a).natDegree + j < 1898945374) →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      ∃ T : Finset IRSProfile.Field, ∃ hTS : T ⊆ S,
      bchksErrors6400 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

/-- The sole branch left after the fixed-factor universal ledger: an
already-selected irreducible factor of degree at least 115. -/
def BCHKSSelectedLargeFactorAlignment6400 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↥S → Polynomial IRSProfile.Field)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (D : ℕ),
    Irreducible R →
    115 ≤ R.natDegree →
    D ≤ 1898945373 →
    YZCap R D →
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424) →
    (∀ z : ↥S, (P z).natDegree ≤ 131071) →
    (∀ z : ↥S, 185364 ≤ (A z.1).card) →
    (∀ z : ↥S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) →
    (∀ z : ↥S, triEval R z.1 (P z) = 0) →
    144802557 * D < S.card →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      ∃ T : Finset IRSProfile.Field, ∃ hTS : T ⊆ S,
      bchksErrors6400 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

/-- The new degree-114 closure reduces the entire score-64 algebraic problem
to the explicitly isolated degree-at-least-115 selected-factor branch. -/
theorem polynomialAlignment6400_of_selectedLargeFactorAlignment
    (hlarge : BCHKSSelectedLargeFactorAlignment6400) :
    BCHKSPolynomialAlignment6400 := by
  classical
  intro U S A P Q hScard hQ hPdeg hAcard hagree hQeval hcaps
  obtain ⟨R, T, hRQ, hRpos, hTD, hTRdeg, hTsub, hQz, hRroot⟩ :=
    exists_fixed_positive_factor_factorYZ6400 S P Q hQ hcaps hQeval hScard
  let D := YZFactorCap.yzSupportDegree R 1
  have hRirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hYZ : YZCap R D := by
    simpa [D] using yzCap_yzSupportDegree_one R
  have hDcap : D ≤ 1898945373 := by
    have hsingle : YZFactorCap.yzSupportDegree R 1 ≤
        ∑ J ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          YZFactorCap.yzSupportDegree J 1 :=
      Finset.single_le_sum
        (f := fun J : Polynomial (Polynomial (Polynomial IRSProfile.Field)) =>
          YZFactorCap.yzSupportDegree J 1)
        (fun _ _ => Nat.zero_le _)
        (Multiset.mem_toFinset.mpr hRQ)
    calc
      D ≤ ∑ J ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          YZFactorCap.yzSupportDegree J 1 := by simpa [D] using hsingle
      _ ≤ YZFactorCap.yzSupportDegree Q 1 :=
        YZFactorCap.normalizedFactors_toFinset_sum_yzSupportDegree_le Q 1 hQ
      _ ≤ 1898945373 :=
        yzSupportDegree_le_1898945373_of_caps6400 Q hQ hcaps
  have hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424 :=
    WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R 131071 8325809424 hQ hRQ (fun j a h => (hcaps j a h).2.1)
  let PT : ↑T → Polynomial IRSProfile.Field := fun z =>
    P ⟨z, hTsub z.property⟩
  have hPTdeg : ∀ z : ↑T, (PT z).natDegree ≤ 131071 :=
    fun z => hPdeg ⟨z, hTsub z.property⟩
  have hTAcard : ∀ z : ↑T, 185364 ≤ (A z.1).card :=
    fun z => hAcard ⟨z, hTsub z.property⟩
  have hTagree : ∀ z : ↑T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (PT z) =
        U 0 i + z.1 * U 1 i := by
    intro z i hi
    exact hagree ⟨z, hTsub z.property⟩ i hi
  have hTRroot : ∀ z : ↑T, triEval R z.1 (PT z) = 0 := by
    intro z
    exact hRroot z z.property
  have hTD' : 144802557 * D < T.card := by simpa [D] using hTD
  by_cases hd : R.natDegree ≤ 114
  · obtain ⟨p₀, p₁, Good, hGoodT, hGoodCard, hp₀, hp₁, hline⟩ :=
      fixed_factor_degree_le_114_alignment_6400 U T A PT R hRirr hRpos hd
        D hDcap hYZ hweighted hPTdeg hTAcard hTagree hTRroot hTD'
    let hGoodS : Good ⊆ S := fun z hz => hTsub (hGoodT hz)
    refine ⟨p₀, p₁, Good, hGoodS, hGoodCard, hp₀, hp₁, ?_⟩
    intro z hz
    simpa [PT] using hline z hz
  · have hdeg115 : 115 ≤ R.natDegree := by omega
    obtain ⟨p₀, p₁, Good, hGoodT, hGoodCard, hp₀, hp₁, hline⟩ :=
      hlarge U T A PT R D hRirr hdeg115 hDcap hYZ hweighted
        hPTdeg hTAcard hTagree hTRroot hTD'
    let hGoodS : Good ⊆ S := fun z hz => hTsub (hGoodT hz)
    refine ⟨p₀, p₁, Good, hGoodS, hGoodCard, hp₀, hp₁, ?_⟩
    intro z hz
    simpa [PT] using hline z hz

private lemma degree_lt_baseDimension_of_natDegree_le_6400
    {p : Polynomial IRSProfile.Field} (hp : p.natDegree ≤ 131071) :
    p.degree < (IRSProfile.baseDimension : WithBot ℕ) := by
  by_cases hzero : p = 0
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
    norm_num [IRSProfile.baseDimension]
    omega

/-- Polynomial alignment implies the exact score-64 affine-line alignment
predicate consumed by the completed analytic reduction. -/
theorem alignmentBound6400_of_polynomialAlignment
    (halg : BCHKSPolynomialAlignment6400) :
    AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400 := by
  classical
  intro U S A hS hA hcomb
  have hA' : ∀ z ∈ S, 185364 ≤ (A z).card := by
    intro z hz
    have h := hA z hz
    norm_num [IRSProfile.Index, bchksErrors6400] at h
    exact h
  obtain ⟨P, Q, hQ, hPdeg, hPagree, hQvan, hcaps⟩ :=
    exists_bchks_interpolant_vanishing6400 U S A hA' hcomb
  obtain ⟨p₀, p₁, T, hTS, hTcard, hp₀deg, hp₁deg, hline⟩ :=
    halg U S A P Q hS hQ hPdeg (fun z => hA' z z.property)
      hPagree hQvan hcaps
  let p : Fin 2 → IRSProfile.Index → IRSProfile.Field := fun j =>
    ReedSolomon.evalOnPoints IRSProfile.domain (if j = 0 then p₀ else p₁)
  refine ⟨p, ?_, T, hTS, hTcard, ?_⟩
  · intro j
    change p j ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    fin_cases j
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le_6400 hp₀deg
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le_6400 hp₁deg
  · intro z hz x hx
    have hagree := hPagree ⟨z, hTS hz⟩ x hx
    have hpoly := congrArg (Polynomial.eval (IRSProfile.domain x))
      (hline z hz)
    simp [p, ReedSolomon.evalOnPoints] at hpoly
    rw [← hagree]
    simpa [p, ReedSolomon.evalOnPoints, mul_add, add_mul] using hpoly

end ProximityPrize.SubmissionLower
