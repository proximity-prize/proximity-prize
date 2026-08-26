import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusFullRankOne6401

/-!
# Classification interface for the full symbolic rank-one branch at 64.01

The preceding determinant/rank-two fork leaves a projected rank-one
condition.  The locator-root argument upgrades it to full rank one.  Here we
package that result as the sole residual of the benchmark-facing fork and
extract an actual nontrivial kernel row which is a common rational projective
direction for every other kernel row.

The conclusion is denominator-free: one nonzero pivot component cross-
multiplies every row into the selected direction.  Polynomial primitive
descent, or an argument exploiting the challenge dependence of this one
direction, is intentionally not assumed.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusFullRankOneClassification6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusFullRankOne6401

set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000

/-- The exact full-rank-one residual for the entire balanced symbolic
kernel, rather than only three arbitrarily selected rows. -/
def FullSymbolicKernelRankOneResidual6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F) : Prop :=
  ∀ c d : SymbolicKernel sigma alpha u₀ u₁,
    ¬ SymbolicRowPairIndependent
      (coefficientRowMap c.1) (coefficientRowMap d.1)

/-- Under no projected direction, the complete determinant/rank-two
argument leaves only genuine full symbolic rank one. -/
theorem symbolicKernel_owner_card_le_mca_or_fullRankOneResidual6401
    {F : Type} [Field F] [DecidableEq F]
    (C : LinearCode (Fin n6401) F)
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hcode : ∀ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 →
      (fun i => Polynomial.eval (alpha i) Q) ∈ C)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod C (A z)) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 ∨
      FullSymbolicKernelRankOneResidual6401 sigma alpha u₀ u₁ := by
  rcases symbolicKernel_owner_card_le_mca_or_A1A2RankOneResidual6401
      C sigma alpha u₀ u₁ hsigma hfixed S A P
        hPdegree hrow howner hcode hnoDirection with hcap | hprojected
  · exact Or.inl hcap
  · exact Or.inr <|
      A1A2RankOneResidual_implies_fullSymbolicRankOne6401
        sigma alpha alpha.injective u₀ u₁ hprojected

/-- A kernel row with both homogeneous Frobenius components zero is itself
zero.  The constant component has outer degree at most `174762`, but vanishes
at all `262144` distinct locators. -/
theorem kernel_eq_zero_of_A1_eq_zero_of_A2_eq_zero
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (c : SymbolicKernel sigma alpha u₀ u₁)
    (hA1 : coefficientRowMap c.1 1 = 0)
    (hA2 : coefficientRowMap c.1 2 = 0) :
    c = 0 := by
  let roots : Finset (Polynomial F) :=
    Finset.univ.map
      ⟨fun i : Fin n6401 => Polynomial.C (alpha i),
        Polynomial.C_injective.comp alpha.injective⟩
  have hA0 : coefficientRowMap c.1 0 = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (coefficientRowMap c.1 0) roots
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
      have hc := kernel_coordinate_relation_eq_zero sigma alpha u₀ u₁ c i
      unfold symbolicCoordinateRelation at hc
      rw [hA1, hA2] at hc
      simpa [evalOuterAt] using hc
    · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
      have hdegree : (coefficientRowMap c.1 0).natDegree ≤ 174762 := by
        simpa [coefficientRowMap, a0XSlots6401] using
          (boxPolynomialMap_natDegree_le a0XSlots6401
            symbolicDepth6401 c.1.1)
      exact hdegree.trans_lt (by norm_num [n6401])
  apply Subtype.ext
  apply coefficientRowMap_injective
  have hmap : coefficientRowMap c.1 = 0 := by
    funext j
    fin_cases j
    · exact hA0
    · exact hA1
    · exact hA2
  simpa using hmap

/-- A concrete nonzero homogeneous component exists in the actual symbolic
kernel.  This rules out the vacuous full-rank-one branch consisting only of
constant-column rows. -/
theorem exists_kernel_row_with_nontrivial_homogeneous_part
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F) :
    ∃ c : SymbolicKernel sigma alpha u₀ u₁,
      coefficientRowMap c.1 1 ≠ 0 ∨
        coefficientRowMap c.1 2 ≠ 0 := by
  obtain ⟨q, hq⟩ :=
    exists_three_independent_symbolicKernel_coefficients sigma alpha u₀ u₁
  let c := q 0
  have hc : c ≠ 0 := LinearIndependent.ne_zero 0 hq
  refine ⟨c, ?_⟩
  by_contra htrivial
  push Not at htrivial
  exact hc (kernel_eq_zero_of_A1_eq_zero_of_A2_eq_zero
    sigma alpha u₀ u₁ c htrivial.1 htrivial.2)

/-- Denominator-free common rational direction data.  The selected base is
an actual kernel row with a nonzero homogeneous pivot.  Every other kernel
row is projectively proportional to it by literal cross multiplication in
`F[Z][X]`. -/
structure CommonRationalSymbolicDirection6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F) where
  base : SymbolicKernel sigma alpha u₀ u₁
  pivot : Fin 3
  pivot_homogeneous : pivot = 1 ∨ pivot = 2
  pivot_ne_zero : coefficientRowMap base.1 pivot ≠ 0
  cross : ∀ c : SymbolicKernel sigma alpha u₀ u₁, ∀ j : Fin 3,
    coefficientRowMap base.1 pivot * coefficientRowMap c.1 j =
      coefficientRowMap c.1 pivot * coefficientRowMap base.1 j

/-- Full symbolic rank one has an actual nontrivial base row and a common
rational projective direction.  This is the strongest classification that
uses only integral-domain cross products; it does not silently assume that
the associated rank-one submodule is principal over the bivariate ring. -/
theorem exists_commonRationalSymbolicDirection_of_fullRankOne
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hfull : FullSymbolicKernelRankOneResidual6401 sigma alpha u₀ u₁) :
    Nonempty (CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁) := by
  classical
  obtain ⟨base, hbase⟩ :=
    exists_kernel_row_with_nontrivial_homogeneous_part sigma alpha u₀ u₁
  rcases hbase with hbase1 | hbase2
  · refine ⟨⟨base, 1, Or.inl rfl, hbase1, ?_⟩⟩
    intro c j
    let B := coefficientRowMap base.1
    let R := coefficientRowMap c.1
    have hpair := hfull base c
    have h01 : symbolicMinor01 B R = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inl h))
    have h12 : symbolicRankTwoDenominator B R = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inr (Or.inr h)))
    fin_cases j
    · change B 1 * R 0 = R 1 * B 0
      change B 0 * R 1 - R 0 * B 1 = 0 at h01
      rw [sub_eq_zero] at h01
      calc
        B 1 * R 0 = R 0 * B 1 := mul_comm _ _
        _ = B 0 * R 1 := h01.symm
        _ = R 1 * B 0 := mul_comm _ _
    · change B 1 * R 1 = R 1 * B 1
      exact mul_comm _ _
    · change B 1 * R 2 = R 1 * B 2
      exact sub_eq_zero.mp h12
  · refine ⟨⟨base, 2, Or.inr rfl, hbase2, ?_⟩⟩
    intro c j
    let B := coefficientRowMap base.1
    let R := coefficientRowMap c.1
    have hpair := hfull base c
    have h02 : symbolicRankTwoNumerator B R = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inr (Or.inl h)))
    have h12 : symbolicRankTwoDenominator B R = 0 :=
      not_ne_iff.mp (fun h => hpair (Or.inr (Or.inr h)))
    fin_cases j
    · change B 2 * R 0 = R 2 * B 0
      change B 0 * R 2 - R 0 * B 2 = 0 at h02
      rw [sub_eq_zero] at h02
      calc
        B 2 * R 0 = R 0 * B 2 := mul_comm _ _
        _ = B 0 * R 2 := h02.symm
        _ = R 2 * B 0 := mul_comm _ _
    · change B 2 * R 1 = R 2 * B 1
      change B 1 * R 2 - R 1 * B 2 = 0 at h12
      rw [sub_eq_zero] at h12
      calc
        B 2 * R 1 = R 1 * B 2 := mul_comm _ _
        _ = B 1 * R 2 := h12.symm
        _ = R 2 * B 1 := mul_comm _ _
    · change B 2 * R 2 = R 2 * B 2
      exact mul_comm _ _

/-! ## Specialization of the common direction -/

noncomputable def CommonRationalSymbolicDirection6401.badChallenges
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 → F}
    {u₀ u₁ : Fin n6401 → F}
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (S : Finset F) : Finset F :=
  S.filter fun z =>
    specializeCoeffZ z (coefficientRowMap D.base.1 D.pivot) = 0

noncomputable def CommonRationalSymbolicDirection6401.goodChallenges
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 → F}
    {u₀ u₁ : Fin n6401 → F}
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (S : Finset F) : Finset F :=
  S.filter fun z =>
    specializeCoeffZ z (coefficientRowMap D.base.1 D.pivot) ≠ 0

/-- The selected homogeneous pivot becomes the zero polynomial at at most
`balancedDepth-2` challenges.  Thus essentially the entire remaining
problem has a nonzero specialized semilinear direction. -/
theorem CommonRationalSymbolicDirection6401.badChallenges_card_le
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 → F}
    {u₀ u₁ : Fin n6401 → F}
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (S : Finset F) :
    (D.badChallenges S).card ≤ balancedDepth6401 - 2 := by
  let B : XOverZ F := coefficientRowMap D.base.1 D.pivot
  have hswap : (Polynomial.Bivariate.swap B).natDegree ≤
      balancedDepth6401 - 2 := by
    rcases D.pivot_homogeneous with hp | hp
    · dsimp [B]
      rw [hp]
      change (Polynomial.Bivariate.swap
        (boxPolynomialMap a1XSlots6401 symbolicDepthOne6401
          D.base.1.2.1)).natDegree ≤ balancedDepth6401 - 2
      have h := swap_boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 D.base.1.2.1
      have hle : symbolicDepthOne6401 - 1 ≤
          balancedDepth6401 - 2 := by
        norm_num [symbolicDepthOne6401, balancedDepth6401,
          balancedThreshold6401, moduleIndexSum6401, a1XSlots6401, q6401]
      exact h.trans hle
    · dsimp [B]
      rw [hp]
      change (Polynomial.Bivariate.swap
        (boxPolynomialMap a2XSlots6401 symbolicDepthFrobenius6401
          D.base.1.2.2)).natDegree ≤ balancedDepth6401 - 2
      have h := swap_boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 D.base.1.2.2
      have hle : symbolicDepthFrobenius6401 - 1 ≤
          balancedDepth6401 - 2 := by
        norm_num [symbolicDepthFrobenius6401, balancedDepth6401,
          balancedThreshold6401, moduleIndexSum6401, a1XSlots6401, q6401]
      exact h.trans hle
  obtain ⟨a, _ha, hcard⟩ :=
    card_zero_specializations_le_coefficient_degree S B (by
      simpa [B] using D.pivot_ne_zero)
  exact hcard.trans <| (coeff_natDegree_le_swap_natDegree B a).trans hswap

/-- Cross multiplication survives every challenge specialization. -/
theorem CommonRationalSymbolicDirection6401.specialize_cross
    {F : Type*} [Field F]
    {sigma : F →+* F} {alpha : Fin n6401 → F}
    {u₀ u₁ : Fin n6401 → F}
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (z : F) (c : SymbolicKernel sigma alpha u₀ u₁) (j : Fin 3) :
    specializeRow z (coefficientRowMap D.base.1) D.pivot *
        specializeRow z (coefficientRowMap c.1) j =
      specializeRow z (coefficientRowMap c.1) D.pivot *
        specializeRow z (coefficientRowMap D.base.1) j := by
  simpa [specializeRow] using
    congrArg (specializeCoeffZ z) (D.cross c j)

/-- On every good challenge, the specialized common direction has a
nonzero homogeneous component. -/
theorem CommonRationalSymbolicDirection6401.specialized_homogeneous_ne_zero
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 → F}
    {u₀ u₁ : Fin n6401 → F}
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (S : Finset F) (z : F) (hz : z ∈ D.goodChallenges S) :
    specializeRow z (coefficientRowMap D.base.1) D.pivot ≠ 0 := by
  simpa [CommonRationalSymbolicDirection6401.goodChallenges,
    specializeRow] using (Finset.mem_filter.mp hz).2

/-- The common base row annihilates every owner after specialization; this
is the concrete one-row semilinear family left for the rank-one analysis. -/
theorem CommonRationalSymbolicDirection6401.base_owner_relation
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (z : F) (A : Finset (Fin n6401)) (P : Polynomial F)
    (hP : P.natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ i ∈ A,
      Polynomial.eval (alpha i) P = u₀ i + z * u₁ i)
    (hcard : a6401 ≤ A.card) :
    symbolicRelation sigma
      (specializeRow z (coefficientRowMap D.base.1)) P = 0 :=
  kernel_symbolicRelation_eq_zero_of_owner
    sigma alpha u₀ u₁ hsigma hfixed D.base z A P
      hP howner hcard

/-- Exact owner budget left after paying the one-time bad-specialization
charge of a common symbolic direction. -/
def rankOneGoodDirectionBudget6401 : ℕ :=
  BCHKSFinalConditional6401.mcaNumerator6401 -
    (balancedDepth6401 - 2)

theorem rankOneGoodDirectionBudget_exact6401 :
    rankOneGoodDirectionBudget6401 = 274949696485844468 ∧
    (balancedDepth6401 - 2) + rankOneGoodDirectionBudget6401 =
      BCHKSFinalConditional6401.mcaNumerator6401 := by
  norm_num [rankOneGoodDirectionBudget6401, balancedDepth6401,
    balancedThreshold6401, moduleIndexSum6401, a1XSlots6401, q6401,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401]

/-- Once the good specializations of the one common direction meet their
explicit budget, the full owner family meets the MCA numerator.  This makes
the remaining quantitative proposition exact rather than hiding it inside
a generic rank-one label. -/
theorem CommonRationalSymbolicDirection6401.owner_card_le_mca_of_good_card
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 → F}
    {u₀ u₁ : Fin n6401 → F}
    (D : CommonRationalSymbolicDirection6401 sigma alpha u₀ u₁)
    (S : Finset F)
    (hgood : (D.goodChallenges S).card ≤
      rankOneGoodDirectionBudget6401) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 := by
  have hbad := D.badChallenges_card_le S
  have hsplit : (D.badChallenges S).card + (D.goodChallenges S).card =
      S.card := by
    classical
    rw [CommonRationalSymbolicDirection6401.badChallenges,
      CommonRationalSymbolicDirection6401.goodChallenges]
    simpa using
      (Finset.card_filter_add_card_filter_not (s := S)
        (fun z => specializeCoeffZ z
          (coefficientRowMap D.base.1 D.pivot) = 0))
  rw [← hsplit]
  exact (Nat.add_le_add hbad hgood).trans_eq
    rankOneGoodDirectionBudget_exact6401.2

end BCHKSTwoFrobeniusFullRankOneClassification6401
end ProximityPrize.SubmissionLower
