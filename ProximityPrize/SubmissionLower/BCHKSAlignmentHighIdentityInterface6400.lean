import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface6400
import ProximityPrize.SubmissionLower.BCHKSFactorYZIdentityStrict6400

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open FixedFactorCover6400

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- The exact branch remaining after both the degree-114 universal ledger and
the strict factor-specific low-identity argument: the selected irreducible
factor has degree at least 115 and at least 212479 direct affine identities. -/
def BCHKSSelectedLargeFactorHighIdentityAlignment6400 : Prop :=
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
    212478 < (Finset.univ.filter fun i : IRSProfile.Index ↦
      directAffineObstruction R (IRSProfile.domain i) (U 0 i) (U 1 i) = 0).card →
    144802557 * D < S.card →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      ∃ T : Finset IRSProfile.Field, ∃ hTS : T ⊆ S,
      bchksErrors6400 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

/-- The strict low-identity theorem removes that branch from the old
degree-at-least-115 interface. -/
theorem selectedLargeFactorAlignment6400_of_highIdentity
    (hhigh : BCHKSSelectedLargeFactorHighIdentityAlignment6400) :
    BCHKSSelectedLargeFactorAlignment6400 := by
  classical
  intro U S A P R D hRirr hRdegree hDcap hYZ hweighted
    hPdegree hAcard hagreement hRroot hScard
  let Pfull : IRSProfile.Field → Polynomial IRSProfile.Field := fun z ↦
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let Identity : Finset IRSProfile.Index := Finset.univ.filter fun i ↦
    directAffineObstruction R (IRSProfile.domain i) (U 0 i) (U 1 i) = 0
  by_cases hid : Identity.card ≤ 212478
  · have hRdegreeD : R.natDegree ≤ D :=
      natDegree_le_of_YZCap R D hRirr.ne_zero hYZ
    have hDpos : 0 < D := by omega
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    have hPfullDegree : ∀ z ∈ S, (Pfull z).natDegree ≤ 131071 := by
      intro z hz
      simpa [Pfull, hz] using hPdegree ⟨z, hz⟩
    have hPfullRoot : ∀ z ∈ S, triEval R z (Pfull z) = 0 := by
      intro z hz
      simpa [Pfull, hz] using hRroot ⟨z, hz⟩
    have hPfullAgreement : ∀ z ∈ S, ∀ i ∈ A z,
        Polynomial.eval (IRSProfile.domain i) (Pfull z) =
          U 0 i + z * U 1 i := by
      intro z hz i hi
      simpa [Pfull, hz] using hagreement ⟨z, hz⟩ i hi
    obtain ⟨Good, p₀, p₁, hGoodS, hGoodCard, hp₀, hp₁, hline⟩ :=
      fixed_factor_low_identity_alignment_factorYZ_strict_6400
        IRSProfile.domain hn R D hDpos hYZ S Pfull A (U 0) (U 1)
        hPfullDegree hPfullRoot
        (fun z hz ↦ hAcard ⟨z, hz⟩) hPfullAgreement hScard
        (by simpa [Identity] using hid)
    refine ⟨p₀, p₁, Good, hGoodS, ?_, hp₀, hp₁, ?_⟩
    · simpa [bchksErrors6400] using hGoodCard
    · intro z hz
      simpa [Pfull, hGoodS hz] using hline z hz
  · apply hhigh U S A P R D hRirr hRdegree hDcap hYZ hweighted
      hPdegree hAcard hagreement hRroot
    · simpa [Identity] using (show 212478 < Identity.card by omega)
    · exact hScard

end ProximityPrize.SubmissionLower
