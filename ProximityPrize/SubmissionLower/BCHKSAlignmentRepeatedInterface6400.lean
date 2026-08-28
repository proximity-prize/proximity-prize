import ProximityPrize.SubmissionLower.BCHKSAlignmentHighIdentityInterface6400
import ProximityPrize.SubmissionLower.BCHKSSimpleSetOwner6400

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open FixedFactorCover6400

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- The exact residual branch after low-identity and simple-identity closure:
131413 selected coordinates carry an affine root of the factor with vanishing
`Y` derivative. -/
def BCHKSSelectedLargeFactorRepeatedAlignment6400 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↥S → Polynomial IRSProfile.Field)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (D : ℕ)
    (Repeat : Finset IRSProfile.Index),
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
    Repeat.card = 131413 →
    (∀ i ∈ Repeat,
      directAffineObstruction R (IRSProfile.domain i) (U 0 i) (U 1 i) = 0 ∧
      (triSpecializeX R (IRSProfile.domain i)).derivative.eval
        (Polynomial.C (U 0 i) + Polynomial.X * Polynomial.C (U 1 i)) = 0) →
    144802557 * D < S.card →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      ∃ T : Finset IRSProfile.Field, ∃ hTS : T ⊆ S,
      bchksErrors6400 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

/-- The strict simple-owner theorem removes the simple half of the
high-identity dichotomy, leaving exactly the repeated-coordinate interface. -/
theorem selectedLargeFactorHighIdentityAlignment6400_of_repeated
    (hrepeated : BCHKSSelectedLargeFactorRepeatedAlignment6400) :
    BCHKSSelectedLargeFactorHighIdentityAlignment6400 := by
  classical
  intro U S A P R D hRirr hRdegree hDcap hYZ hweighted
    hPdegree hAcard hagreement hRroot hIdentityHigh hScard
  let Pfull : IRSProfile.Field → Polynomial IRSProfile.Field := fun z ↦
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let G : IRSProfile.Index → Polynomial IRSProfile.Field := fun i ↦
    directAffineObstruction R (IRSProfile.domain i) (U 0 i) (U 1 i)
  let Identity : Finset IRSProfile.Index := Finset.univ.filter fun i ↦ G i = 0
  let BI : IRSProfile.Index → Polynomial (Polynomial IRSProfile.Field) :=
    fun i ↦ triSpecializeX R (IRSProfile.domain i)
  let LI : IRSProfile.Index → Polynomial IRSProfile.Field := fun i ↦
    Polynomial.C (U 0 i) + Polynomial.X * Polynomial.C (U 1 i)
  let Simple : Finset IRSProfile.Index := Identity.filter fun i ↦
    (BI i).derivative.eval (LI i) ≠ 0
  have hIdentity : 212479 ≤ Identity.card := by
    have hh : 212478 < Identity.card := by
      simpa [Identity, G] using hIdentityHigh
    omega
  rcases large_simple_or_exists_sparse_nonsimple_coordinates_extended_6400
      Identity Simple (Finset.filter_subset _ _) hIdentity with
    hsimple | hrepeat
  · have hRdegreeD : R.natDegree ≤ D :=
      natDegree_le_of_YZCap R D hRirr.ne_zero hYZ
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    have hPfullDegree : ∀ z ∈ S, (Pfull z).natDegree ≤ 131071 := by
      intro z hz
      simpa [Pfull, hz] using hPdegree ⟨z, hz⟩
    have hPfullExact : ∀ z ∈ S,
        (triSpecializeZ R z).eval (Pfull z) = 0 := by
      intro z hz
      simpa only [← triEval_eq_eval_triSpecializeZ] using
        (show triEval R z (Pfull z) = 0 by
          simpa [Pfull, hz] using hRroot ⟨z, hz⟩)
    have hPfullAgreement : ∀ z ∈ S, ∀ i ∈ A z,
        Polynomial.eval (IRSProfile.domain i) (Pfull z) =
          U 0 i + z * U 1 i := by
      intro z hz i hi
      simpa [Pfull, hz] using hagreement ⟨z, hz⟩ i hi
    obtain ⟨Good, p₀, p₁, hGoodS, hGoodCard, hp₀, hp₁, hline⟩ :=
      simple_set_affine_owner_alignment_6400
        IRSProfile.domain hn R D (by omega) hRdegreeD hYZ
        S Pfull A (U 0) (U 1) Simple hsimple
        (by
          intro i hi
          have hiIdentity := (Finset.mem_filter.mp hi).1
          have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
          exact ⟨by simpa [G] using hGi,
            by simpa [BI, LI] using (Finset.mem_filter.mp hi).2⟩)
        hPfullDegree hPfullExact
        (fun z hz ↦ hAcard ⟨z, hz⟩) hPfullAgreement hScard
        (by
          rw [CompPoly.Extension.Ext.card_ext]
          norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize])
    refine ⟨p₀, p₁, Good, hGoodS, ?_, hp₀, hp₁, ?_⟩
    · simpa [bchksErrors6400] using hGoodCard
    · intro z hz
      simpa [Pfull, hGoodS hz] using hline z hz
  · obtain ⟨Repeat, hRepeatSub, hRepeatCard⟩ := hrepeat
    apply hrepeated U S A P R D Repeat hRirr hRdegree hDcap hYZ hweighted
      hPdegree hAcard hagreement hRroot hRepeatCard
    · intro i hi
      have hiDiff := hRepeatSub hi
      have hiIdentity : i ∈ Identity := (Finset.mem_sdiff.mp hiDiff).1
      have hiNotSimple : i ∉ Simple := (Finset.mem_sdiff.mp hiDiff).2
      have hGi : G i = 0 := (Finset.mem_filter.mp hiIdentity).2
      have hslope : (BI i).derivative.eval (LI i) = 0 := by
        by_contra hne
        exact hiNotSimple (Finset.mem_filter.mpr ⟨hiIdentity, hne⟩)
      exact ⟨by simpa [G] using hGi, by simpa [BI, LI] using hslope⟩
    · exact hScard

end ProximityPrize.SubmissionLower
