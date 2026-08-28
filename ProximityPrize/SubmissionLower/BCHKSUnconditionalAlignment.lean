import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface
import ProximityPrize.SubmissionLower.BCHKSQBadRemoval
import ProximityPrize.SubmissionLower.BCHKSStagedUnconditional
import ProximityPrize.SubmissionLower.BCHKSDegreeTwoSelectedFinal
import ProximityPrize.SubmissionLower.BCHKSLinearDegreeOneFinal
import ProximityPrize.SubmissionLower.BCHKSLinearProtocolAdapter

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

/-- Outer assembly, with the degree-one conclusion supplied separately while
its resultant witness is constructed. -/
theorem bchksPolynomialAlignment_of_linear
    (hlinear : ∀
      (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
      (P : IRSProfile.Field → IRSProfile.Field[X])
      (Arow : IRSProfile.Field → Finset IRSProfile.Index)
      (R : Polynomial (Polynomial (Polynomial IRSProfile.Field))) (T : Finset IRSProfile.Field),
      (∀ z ∈ T, (P z).natDegree ≤ 131071) →
      (∀ z ∈ T, triEval R z (P z) = 0) →
      (∀ z ∈ T, 185423 ≤ (Arow z).card) →
      (∀ z ∈ T, ∀ i ∈ Arow z,
        Polynomial.eval (IRSProfile.domain i) (P z) = U (0 : Fin 2) i + z * U (1 : Fin 2) i) →
      Irreducible R → YZCap R 519142 →
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 111624646) →
      R.natDegree = 1 →
      (bchksErrors + 1) + 2 * 111624646 * 519142 < T.card →
      ∃ Tgood : Finset IRSProfile.Field, Tgood ⊆ T ∧ bchksErrors + 1 < Tgood.card ∧
        ∃ p₀ p₁ : IRSProfile.Field[X], p₀.natDegree ≤ 131071 ∧
          p₁.natDegree ≤ 131071 ∧ ∀ z ∈ Tgood,
            P z = p₀ + Polynomial.C z * p₁) :
    BCHKSPolynomialAlignment := by
  classical
  intro U S A P Q hScard hQ hPdeg hAcard hagree hQeval hcaps
  let PE : IRSProfile.Field → IRSProfile.Field[X] := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  have hQY : Q.natDegree ≤ 851 := by
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlc
    have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.mem_support_iff.mp ha
    have := (hcaps Q.natDegree a hca).1
    omega
  obtain ⟨Sgood, rfl, hSgoodS, hQz, hQevalgood, hbad, hlarge⟩ :=
    exists_bchks_Qbad_removal S PE Q hScard hQ
      (by intro z hz; simpa [PE, hz, BCHKSSubstitutionVanish.triEval, triEval,
        BCHKSSubstitutionVanish.specializeZ] using hQeval ⟨z, hz⟩)
      hQY (fun j a ha => (hcaps j a ha).2.2)
      (fun j a ha => (hcaps j a ha).2.1)
  obtain ⟨R, H, T, x₀, Bad, hRQ, hRpos, hHT, hHpos, hTS, hTbad,
      hvan, hmargin, hRi, hHi, hHdiv, hRle, hHle, hHtot, hRXtot,
      hRweighted, hHyp, hBadcard, hsimple⟩ :=
    bchks_staged_unconditional _ PE Q hQ hQevalgood hQz hQY
      (fun j a ha => (hcaps j a ha).2.2)
      (fun j a ha => (hcaps j a ha).2.1) hlarge
  have hPT : ∀ z ∈ T, (PE z).natDegree ≤ 131071 := by
    intro z hz
    have hzS : z ∈ S := hSgoodS (hTS hz)
    simpa [PE, hzS] using hPdeg ⟨z, hzS⟩
  have hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card := by
    intro z hz
    have hzS : z ∈ S := hSgoodS (hTS hz)
    norm_num
    exact hAcard ⟨z, hzS⟩
  have hagreeT : ∀ z ∈ T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (PE z) = U (0 : Fin 2) i + z * U (1 : Fin 2) i := by
    intro z hz i hi
    have hzS : z ∈ S := hSgoodS (hTS hz)
    simpa [PE, hzS] using hagree ⟨z, hzS⟩ i hi
  have hYZ : RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap R 519142 := by
    intro j a ha
    have hh := YZFactorCap.normalizedFactor_YZ_cap Q R 519143 hQ hRQ
      (fun j a ha => (hcaps j a ha).2.2) j a ha
    omega
  by_cases hdeg : R.natDegree = 1
  · obtain ⟨Tgood, hgoodT, hgoodcard, p₀, p₁, hp₀, hp₁, halign⟩ :=
      hlinear U PE A R T hPT (fun z hz => (hvan z hz).1)
        (by intro z hz; exact hAcard ⟨z, hSgoodS (hTS hz)⟩)
        hagreeT hRi hYZ hRweighted hdeg (by
          have hHp : 1 ≤ H.natDegree := hHpos
          have hm : 2 * 111624646 * 519142 ≤
              2 * 111624646 * 519142 * R.natDegree * H.natDegree := by
            rw [hdeg]
            nlinarith
          have hmargin' : (bchksErrors + 1) +
              2 * 111624646 * 519142 * R.natDegree * H.natDegree < T.card := by
            simpa [hdeg, Nat.add_comm] using hmargin
          exact lt_of_le_of_lt (Nat.add_le_add_left hm _) hmargin')
    refine ⟨p₀, p₁, Tgood, ?_, hgoodcard, hp₀, hp₁, ?_⟩
    · exact hgoodT.trans (hTS.trans hSgoodS)
    · intro z hz
      have hzS : z ∈ S := (hgoodT.trans (hTS.trans hSgoodS)) hz
      simpa [PE, hzS] using halign z hz
  · have hdeg2 : 2 ≤ R.natDegree := by omega
    obtain ⟨Tgood, hgoodT, hgoodcard, p₀, p₁, hp₀, hp₁, halign⟩ :=
      degree_two_selected_final U PE A R H T x₀ Bad hPT hvan hTbad
        (by simpa [hdeg] using hmargin)
        hRi hHi hHpos hHyp hHtot hYZ hsimple hrow hagreeT hdeg2
    refine ⟨p₀, p₁, Tgood, ?_, hgoodcard, hp₀, hp₁, ?_⟩
    · exact hgoodT.trans (hTS.trans hSgoodS)
    · intro z hz
      have hzS : z ∈ S := (hgoodT.trans (hTS.trans hSgoodS)) hz
      simpa [PE, hzS] using halign z hz


/-- The unconditional BCHKS polynomial alignment theorem. -/
theorem bchksPolynomialAlignment : BCHKSPolynomialAlignment := by
  apply bchksPolynomialAlignment_of_linear
  intro U P Arow R T hPdeg hvan hrow hagree hRi hYZ hWeighted hRdeg hmargin
  exact bchksLinearProtocolAdapter U P Arow R T hPdeg hvan hrow hagree
    hRi hYZ hWeighted hRdeg hmargin

end ProximityPrize.SubmissionLower
