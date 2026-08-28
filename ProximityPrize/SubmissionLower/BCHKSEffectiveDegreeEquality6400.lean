import ProximityPrize.SubmissionLower.BCHKSEffectiveLocatorLocalNullity6400
import ProximityPrize.SubmissionLower.BCHKSCyclicNormSpecialization6400

/-!
# Sharpness of the effective-defect rebate

The effective-defect construction initially gives only

`effective.card + deg(B) <= 22489 - L`.

If this inequality were strict, every regular retained owner would acquire
strictly more than the generic `L` locator-kernel dimensions.  A single fixed
maximal minor detects all such rank drops, and its challenge degree plus the
leading-coefficient exclusion budget is tiny compared with `ownerFloor`.
Therefore the rebate is always an equality in the low-degree direction.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSEffectiveDegreeEquality6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSEffectiveFixedRelation6400
open BCHKSRankOneEffectiveDefectProduction6400
open BCHKSEffectiveLocatorLocalNullity6400
open BCHKSCyclicNormSpecialization6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem card_le_filter_eval_ne_zero_add_natDegree
    {F : Type} [Field F] [DecidableEq F]
    (T : Finset F) (P : F[X]) (hP : P ≠ 0) :
    T.card ≤ (T.filter (fun z ↦ P.eval z ≠ 0)).card + P.natDegree := by
  have hzero :
      (T.filter (fun z ↦ P.eval z = 0)).card ≤ P.natDegree := by
    have hsubset : T.filter (fun z ↦ P.eval z = 0) ⊆
        P.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact (Finset.mem_filter.mp hz).2
    exact (Finset.card_le_card hsubset).trans
      ((Multiset.toFinset_card_le P.roots).trans
        (Polynomial.card_roots' P))
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun z ↦ P.eval z ≠ 0) (s := T)
  have hzero' :
      (T.filter (fun z ↦ ¬P.eval z ≠ 0)).card ≤ P.natDegree := by
    simpa only [not_ne_iff] using hzero
  omega

private theorem exists_score6400_agreementPolynomial_of_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    ∃ Agreement : Finset IRSProfile.Index, ∃ P : IRSProfile.Field[X],
      185364 ≤ Agreement.card ∧
      P.natDegree ≤ 131071 ∧
      ∀ i ∈ Agreement,
        P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      f₀ f₁ 185364 z := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨Agreement, P, hAgreement, hPdegree, hagree, _⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 f₀ f₁ z hbadRS
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · subst P
      norm_num
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  exact ⟨Agreement, P, hAgreement, hPnat, hagree⟩

/-- In the low-degree direction the effective-defect rebate is exact. -/
theorem Score6400RankOneEffectiveDefectData.effective_rebate_eq
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hTcard : ownerFloor ≤ T.card)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    (score6400EffectiveFixedDefect data.Fixed data.K).card +
        data.B.natDegree = locatorFrobeniusRows6400 - L := by
  let FixedEff := score6400EffectiveFixedDefect data.Fixed data.K
  have hrebate : FixedEff.card + data.B.natDegree ≤
      locatorFrobeniusRows6400 - L := by
    simpa only [FixedEff, score6400EffectiveFixedDefect] using
      data.effective_rebate
  apply le_antisymm hrebate
  by_contra hreverse
  have hstrict : FixedEff.card + data.B.natDegree <
      locatorFrobeniusRows6400 - L := by
    omega
  let room := locatorFrobeniusRows6400 - FixedEff.card -
    data.B.natDegree
  have hroomLarge : L < room := by
    dsimp only [room]
    omega
  have hroomPositive : 0 < room := by omega
  obtain ⟨Δ, hΔne, hΔdegree, hΔdrop⟩ :=
    exists_score6400_genericPivot_rankDropPolynomial
      f₀ f₁ L hkernelRank hLtwo
  have hHne : data.H ≠ 0 := by
    intro hzero
    have hpositive := data.H_positive
    rw [hzero, Polynomial.natDegree_zero] at hpositive
    omega
  have hBchallenge : data.B.leadingCoeff.natDegree ≤
      76779 * 2130706433 := by
    simpa only [Polynomial.leadingCoeff] using
      (quotient_coeff_natDegree_le
        (score6400PolynomialLocatorRelationPair data.q).2.1
        data.H data.B (76779 * 2130706433) data.B.natDegree
        data.B_factor hHne data.B_ne
        (fun n ↦
          score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
            data.q (76779 * 2130706433) n data.q_degree))
  have hBleadingNe : data.B.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr data.B_ne
  let Good : Finset IRSProfile.Field :=
    T.filter (fun z ↦ data.B.leadingCoeff.eval z ≠ 0)
  have hfilterBound : T.card ≤ Good.card +
      data.B.leadingCoeff.natDegree := by
    simpa only [Good] using
      card_le_filter_eval_ne_zero_add_natDegree
        T data.B.leadingCoeff hBleadingNe
  have hGoodLarge : Δ.natDegree < Good.card := by
    have hnumeric :
        2 * (76779 * 2130706433) < ownerFloor := by
      norm_num [ownerFloor]
    omega
  have hΔroots : ∀ z ∈ Good, Δ.eval z = 0 := by
    intro z hzGood
    have hzParts := Finset.mem_filter.mp hzGood
    have hzT : z ∈ T := hzParts.1
    have hBleading : data.B.leadingCoeff.eval z ≠ 0 := hzParts.2
    obtain ⟨Agreement, P, hAgreement, hPdegree, hagree⟩ :=
      exists_score6400_agreementPolynomial_of_mcaBad
        f₀ f₁ z (hbad z hzT)
    have hlocalLower :=
      BCHKSEffectiveLocatorLocalNullity6400.Score6400RankOneEffectiveDefectData.effectiveRoom_le_localNullity
        data hAdirection z hzT
        Agreement P hAgreement hPdegree hagree hBleading (by
          simpa only [room, FixedEff] using hroomPositive)
    apply hΔdrop z
    exact hroomLarge.trans_le (by
      simpa only [room, FixedEff] using hlocalLower)
  apply hΔne
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    Δ Good hΔroots hGoodLarge

end BCHKSEffectiveDegreeEquality6400
end ProximityPrize.SubmissionLower
