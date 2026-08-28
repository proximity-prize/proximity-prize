import ProximityPrize.SubmissionLower.BCHKSFixedFactorUniversal6400
import ProximityPrize.SubmissionLower.BCHKSSingleFactorGood
import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffectiveResultant
import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators
import ProximityPrize.SubmissionLower.BCHKSFactorXDegree
import ProximityPrize.SubmissionLower.BCHKSUniversalFactorSums
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

namespace FixedFactorCover6400

abbrev F := IRSProfile.Field
abbrev TriPoly := Polynomial (Polynomial (Polynomial F))
abbrev BiPoly := Polynomial (Polynomial F)

local instance fixedFactorChar : CharP F 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- An actual `Z+Y` cap controls both coefficient-variable degrees after
specializing the middle variable. -/
theorem eval_Z_caps_of_YZCap
    (R : TriPoly) (x₀ : F) (D : ℕ) (hYZ : YZCap R D) :
    degreeX (triSpecializeX R x₀) ≤ D ∧
      (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff).natDegree ≤ D := by
  have hcoeffCap : ∀ j, degreeX (R.coeff j) ≤ D := by
    intro j
    unfold degreeX
    apply Finset.sup_le
    intro a ha
    have h := hYZ j a (Polynomial.mem_support_iff.mp ha)
    exact (Nat.le_add_right _ _).trans h
  have hevalCap : ∀ p : Polynomial (Polynomial F),
      degreeX p ≤ D →
      (Polynomial.eval (Polynomial.C x₀) p).natDegree ≤ D := by
    intro p hp
    have heq : (Polynomial.Bivariate.swap p).map
        (Polynomial.evalRingHom x₀) = Polynomial.eval (Polynomial.C x₀) p := by
      rw [← Polynomial.Bivariate.evalX_eq_map]
      exact (Polynomial.Bivariate.evalY_eq_evalX_swap x₀ p).symm
    rw [← heq]
    exact Polynomial.natDegree_map_le.trans (by
      rw [show (Polynomial.Bivariate.swap p).natDegree =
          Polynomial.Bivariate.natDegreeY
            (Polynomial.Bivariate.swap p) from rfl,
        Polynomial.Bivariate.natDegreeY_swap]
      exact hp)
  constructor
  · unfold degreeX
    apply Finset.sup_le
    intro j hj
    simp only [triSpecializeX, Polynomial.coeff_map]
    exact hevalCap (R.coeff j) (hcoeffCap j)
  · exact hevalCap R.leadingCoeff (by
      rw [← Polynomial.coeff_natDegree]
      exact hcoeffCap R.natDegree)

/-- Caps in the swapped orientation required by the effective primitive
obstruction, derived directly from the fixed factor's two support ledgers. -/
theorem swap_caps_of_support
    (R : TriPoly) (D DX : ℕ) (hYZ : YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < DX) :
    (∀ j, (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤ D) ∧
      (∀ j, Polynomial.Bivariate.degreeX
        (Polynomial.Bivariate.swap (R.coeff j)) ≤ DX) := by
  constructor
  · intro j
    rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
        Polynomial.Bivariate.natDegreeY
          (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
      Polynomial.Bivariate.natDegreeY_swap]
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have h := hYZ j a (Polynomial.mem_support_iff.mp ha)
    exact (Nat.le_add_right _ _).trans h
  · intro j
    rw [Polynomial.Bivariate.degreeX_swap]
    change (R.coeff j).natDegree ≤ DX
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hne : (R.coeff j).coeff (R.coeff j).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have h := hweighted j (R.coeff j).natDegree hne
      omega

/-- The weighted middle-variable support cap also gives the two rational-
function `X` caps used by the separability obstruction. -/
theorem rational_X_caps_of_weighted
    (R : TriPoly) (DX : ℕ)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < DX) :
    degreeX (mapZToRatFunc R) ≤ DX ∧ R.leadingCoeff.natDegree ≤ DX := by
  constructor
  · unfold degreeX
    apply Finset.sup_le
    intro j hj
    simp only [mapZToRatFunc, Polynomial.coeff_map]
    apply Polynomial.natDegree_map_le.trans
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hne : (R.coeff j).coeff (R.coeff j).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have h := hweighted j (R.coeff j).natDegree hne
      omega
  · by_cases hz : R.leadingCoeff = 0
    · simp [hz]
    · have hne :
        (R.coeff R.natDegree).coeff R.leadingCoeff.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have h := hweighted R.natDegree R.leadingCoeff.natDegree hne
      omega

/-- One score-64 factor of degree at most 114 admits a primitive full-degree
middle-variable specialization.  The exceptional seed set costs only
`2*d*D`, where `D` is this factor's own `Z+Y` support degree. -/
theorem exists_fixed_factor_good_6400
    (R : TriPoly) (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hd : R.natDegree ≤ 114) (D : ℕ) (hD : D ≤ 1898945373)
    (hYZ : YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424) :
    ∃ x₀ : F, ∃ Bad : Finset F,
      Bad.card ≤ 2 * R.natDegree * D ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive ∧
      Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
      (∀ z ∉ Bad, Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0) ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  obtain ⟨hZ, hXswap⟩ := swap_caps_of_support R D 8325809424 hYZ hweighted
  obtain ⟨hX, hlead⟩ := rational_X_caps_of_weighted R 8325809424 hweighted
  have hfield : D + 1 < Fintype.card F := by
    rw [CompPoly.Extension.Ext.card_ext]
    norm_num [F, IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize] at ⊢
    omega
  obtain ⟨w, hw⟩ := effectivePrimitiveObstruction_of_irreducible_bounded
    R hR hpos D 8325809424 hfield hZ hXswap
  have hfactor : (factorXObstruction R).natDegree ≤
      (2 * R.natDegree + 2) * 8325809424 :=
    factorXObstruction_natDegree_le R 8325809424 hX hlead
  have hxcap : w.obstruction.natDegree +
      (factorXObstruction R).natDegree < Fintype.card F := by
    have htotal : w.obstruction.natDegree +
        (factorXObstruction R).natDegree ≤
        2 * (1898945373 + 1) * 8325809424 +
          (2 * 114 + 2) * 8325809424 := by
      exact Nat.add_le_add (hw.trans (by gcongr)) (hfactor.trans (by gcongr))
    rw [CompPoly.Extension.Ext.card_ext]
    exact htotal.trans_lt (by
      norm_num [F, IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize])
  have hchar : R.natDegree < ringChar F := by
    rw [ringChar.eq F 2130706433]
    omega
  have hzcap : ∀ x : F,
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * D := by
    intro x
    have hc := eval_Z_caps_of_YZCap R x D hYZ
    exact factorXObstruction_eval_natDegree_le R x R.natDegree D hpos le_rfl
      hc.1 hc.2
  obtain ⟨x₀, hw, hxObs, hprim⟩ :=
    exists_single_factor_primitive_base_effective R hR hpos hchar w hxcap
  let zObs : Polynomial F :=
    Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)
  let Bad : Finset F := zObs.roots.toFinset
  have hBad : Bad.card ≤ 2 * R.natDegree * D := by
    dsimp [Bad]
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' zObs).trans (hzcap x₀))
  have hlead : Polynomial.eval (Polynomial.C x₀) R.leadingCoeff ≠ 0 := by
    intro hz
    apply hxObs
    rw [factorXObstruction, Polynomial.eval_mul, hz, zero_mul]
  have hdegEq : (triSpecializeX R x₀).natDegree = R.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom (Polynomial.C x₀)) hlead
  have hB0 : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    apply hlead
    have hc := congrArg
      (fun B : Polynomial (Polynomial F) => B.coeff R.natDegree) hz
    simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coeff_zero,
      Polynomial.coe_evalRingHom, Polynomial.leadingCoeff] using hc
  have hseed : ∀ z ∉ Bad, Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0 := by
    intro z hzBad hz
    apply hzBad
    change z ∈ zObs.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hxObs]
    exact hz
  have hsimple : ∀ z ∉ Bad, ∀ y,
      Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
      Polynomial.eval y
        (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0 := by
    intro z hzBad y hy
    have hzO := hseed z hzBad
    have hresEval : Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (rawSepResultant R)) ≠ 0 := by
      intro hzres
      apply hzO
      rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul,
        hzres, mul_zero]
    have hresX : Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) =
        Polynomial.resultant (triSpecializeX R x₀)
          (triSpecializeX R.derivative x₀)
          R.natDegree (R.natDegree - 1) := by
      simp [rawSepResultant, triSpecializeX, Polynomial.derivative_map]
    have hder : triSpecializeX R.derivative x₀ =
        (triSpecializeX R x₀).derivative := by
      simp [triSpecializeX, Polynomial.derivative_map]
    have hresB : Polynomial.eval z
        (Polynomial.resultant (triSpecializeX R x₀)
          (triSpecializeX R x₀).derivative
          (triSpecializeX R x₀).natDegree
          ((triSpecializeX R x₀).natDegree - 1)) ≠ 0 := by
      rw [hdegEq, ← hder, ← hresX]
      exact hresEval
    have hs := simple_root_of_fixed_resultant_eval_ne_zero
      (triSpecializeX R x₀) z y (by rw [hdegEq]; exact hpos) hresB hy
    rw [← hder] at hs
    exact hs
  exact ⟨x₀, Bad, hBad, hdegEq, hB0, hprim, hxObs, hseed, hsimple⟩

noncomputable def innerFactors (R : TriPoly) (x₀ : F) : Finset BiPoly :=
  (UniqueFactorizationMonoid.normalizedFactors
    (triSpecializeX R x₀)).toFinset.filter fun H => 0 < H.natDegree

def innerRel (Pz : F → Polynomial F) (x₀ z : F) (H : BiPoly) : Prop :=
  biEval H ((Pz z).eval x₀) z = 0

noncomputable def innerFiber
    (S Bad : Finset F) (Pz : F → Polynomial F) (x₀ : F) (H : BiPoly) :
    Finset F := by
  classical
  exact (S \ Bad).filter fun z => innerRel Pz x₀ z H

noncomputable def innerResultantCapacity
    (E d D : ℕ) (H : BiPoly) : ℕ :=
  H.natDegree * (E * D) + (E * d) * Bivariate.degreeX H

/-- Positivity and factor-degree additivity bound the number of candidate
inner factors by the fixed outer degree. -/
theorem innerFactors_card_le
    (R : TriPoly) (x₀ : F) (hB : triSpecializeX R x₀ ≠ 0)
    (hdeg : (triSpecializeX R x₀).natDegree = R.natDegree) :
    (innerFactors R x₀).card ≤ R.natDegree := by
  calc
    (innerFactors R x₀).card =
        ∑ H ∈ innerFactors R x₀, 1 := by simp
    _ ≤ ∑ H ∈ innerFactors R x₀, H.natDegree := by
      apply Finset.sum_le_sum
      intro H hH
      exact (Finset.mem_filter.mp hH).2
    _ ≤ (triSpecializeX R x₀).natDegree := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (by simp)).trans
          (normalizedFactors_toFinset_sum_natDegree_le _ hB)
    _ = R.natDegree := hdeg

/-- The sum of actual resultant capacities over the positive inner factors is
at most `2*E*d*D`; the local result cap retains the harmless affine `+d`
slack used by the fused arithmetic. -/
theorem innerFactors_resultantCapacity_sum_le
    (R : TriPoly) (x₀ : F) (D : ℕ)
    (hB : triSpecializeX R x₀ ≠ 0)
    (hdeg : (triSpecializeX R x₀).natDegree = R.natDegree)
    (hBZ : Bivariate.degreeX (triSpecializeX R x₀) ≤ D) :
    (∑ H ∈ innerFactors R x₀,
      innerResultantCapacity bchksUniversalExponent6399 R.natDegree D H) ≤
      bchksFixedFactorResultCap6400 R.natDegree D := by
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le
    (triSpecializeX R x₀) hB
  dsimp only at hsums
  have hsumY : (∑ H ∈ innerFactors R x₀, H.natDegree) ≤ R.natDegree := by
    exact hsums.1.trans_eq hdeg
  have hsumZ :
      (∑ H ∈ innerFactors R x₀, Bivariate.degreeX H) ≤ D :=
    hsums.2.trans hBZ
  calc
    (∑ H ∈ innerFactors R x₀,
        innerResultantCapacity bchksUniversalExponent6399 R.natDegree D H) =
      (∑ H ∈ innerFactors R x₀, H.natDegree) *
          (bchksUniversalExponent6399 * D) +
        (bchksUniversalExponent6399 * R.natDegree) *
          (∑ H ∈ innerFactors R x₀, Bivariate.degreeX H) := by
            simp only [innerResultantCapacity, Finset.sum_add_distrib,
              Finset.sum_mul, Finset.mul_sum]
    _ ≤ R.natDegree * (bchksUniversalExponent6399 * D) +
        (bchksUniversalExponent6399 * R.natDegree) * D := by
      exact Nat.add_le_add (Nat.mul_le_mul_right _ hsumY)
        (Nat.mul_le_mul_left _ hsumZ)
    _ = 2 * bchksUniversalExponent6399 * R.natDegree * D := by ring
    _ ≤ bchksFixedFactorResultCap6400 R.natDegree D := by
      simp [bchksFixedFactorResultCap6400]

/-- The fixed factor's own degree is bounded by any `YZCap` that it satisfies. -/
theorem natDegree_le_of_YZCap
    (R : TriPoly) (D : ℕ) (hR : R ≠ 0) (hYZ : YZCap R D) :
    R.natDegree ≤ D := by
  have hlead : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
  have hcoeff : (R.coeff R.natDegree).coeff a ≠ 0 :=
    Polynomial.mem_support_iff.mp ha
  exact (Nat.le_add_left _ _).trans (hYZ R.natDegree a hcoeff)

/-- Every row outside the one fixed-factor bad set has a positive inner
normalized factor through its specialized root. -/
theorem inner_factor_cover
    (S : Finset F) (Pz : F → Polynomial F) (R : TriPoly)
    (x₀ : F) (Bad : Finset F)
    (hroot : ∀ z ∈ S, triEval R z (Pz z) = 0)
    (hsimple : ∀ z ∉ Bad, ∀ y,
      Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
      Polynomial.eval y
        (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) :
    ∀ z ∈ S \ Bad, ∃ H ∈ innerFactors R x₀, innerRel Pz x₀ z H := by
  classical
  intro z hz
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hzBad := (Finset.mem_sdiff.mp hz).2
  let B := triSpecializeX R x₀
  let y := (Pz z).eval x₀
  have hpoint : Polynomial.eval y (biSpecializeZ B z) = 0 := by
    change biEval B y z = 0
    rw [← eval_triEval_eq_biEval_triSpecializeX, hroot z hzS]
    simp
  have hslope := hsimple z hzBad y hpoint
  have hBz : biSpecializeZ B z ≠ 0 := by
    intro hzero
    apply hslope
    have hder : triSpecializeX R.derivative x₀ = B.derivative := by
      simp [B, triSpecializeX, Polynomial.derivative_map]
    rw [hder]
    have hspec : biSpecializeZ B.derivative z =
        (biSpecializeZ B z).derivative := by
      simp [biSpecializeZ, Polynomial.derivative_map]
    rw [hspec, hzero]
    simp
  obtain ⟨H, hHB, hHpos, hHroot⟩ :=
    exists_positive_normalizedFactor_biEval_eq_zero B z y hBz (by
      simpa [biEval_eq_eval_biSpecializeZ] using hpoint)
  exact ⟨H, Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr hHB, hHpos⟩, hHroot⟩

/-- Fused global selection for one already-selected score-64 factor.  This is
the factor-specific replacement for the all-outer-factor 63.99 ledger. -/
theorem exists_large_fixed_inner_factor_6400
    (S : Finset F) (Pz : F → Polynomial F) (R : TriPoly)
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hd : R.natDegree ≤ 114) (D : ℕ) (hD : D ≤ 1898945373)
    (hYZ : YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424)
    (hroot : ∀ z ∈ S, triEval R z (Pz z) = 0)
    (hS : 144802557 * D < S.card) :
    ∃ x₀ : F, ∃ Bad : Finset F, ∃ H : BiPoly,
      Bad.card ≤ 2 * R.natDegree * D ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive ∧
      (∀ z ∉ Bad, Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0) ∧
      H ∈ innerFactors R x₀ ∧
      (262144 - 131071) *
          innerResultantCapacity bchksUniversalExponent6399
            R.natDegree D H /
          (262144 - bchksErrors6400 - 131071) +
          (bchksErrors6400 + 1) <
        (innerFiber S Bad Pz x₀ H).card ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  have hR0 : R ≠ 0 := hR.ne_zero
  have hdD : R.natDegree ≤ D := natDegree_le_of_YZCap R D hR0 hYZ
  obtain ⟨x₀, Bad, hBad, hBdeg, hB0, hprim, hobs, hseed, hsimple⟩ :=
    exists_fixed_factor_good_6400 R hR hpos hd D hD hYZ hweighted
  let Outer : Finset Unit := {()}
  let OuterBad : Unit → Finset F := fun _ => Bad
  let rdeg : BiPoly → ℕ :=
    innerResultantCapacity bchksUniversalExponent6399 R.natDegree D
  have hBZ := (eval_Z_caps_of_YZCap R x₀ D hYZ).1
  have hresult : (∑ H ∈ innerFactors R x₀, rdeg H) ≤
      bchksFixedFactorResultCap6400 R.natDegree D := by
    simpa [rdeg] using innerFactors_resultantCapacity_sum_le
      R x₀ D hB0 hBdeg hBZ
  have hpairs : (innerFactors R x₀).card ≤ R.natDegree :=
    innerFactors_card_le R x₀ hB0 hBdeg
  have hfused := bchks_fixed_factor_fused_incidence_6400
    R.natDegree D (by omega)
  have hlarge : 0 + 2 * R.natDegree * D +
      (bchksFixedFactorFusedCap6400 R.natDegree D +
        (bchksErrors6400 + 1) * R.natDegree) < S.card := by
    have hledger := bchks_fixed_factor_total_ledger_lt_6400
      S.card R.natDegree D hd hdD hS
    omega
  have houter : (∑ u ∈ Outer, (OuterBad u).card) ≤
      2 * R.natDegree * D := by
    simpa [Outer, OuterBad] using hBad
  have hcover : ∀ z ∈ S \ (∅ ∪ Outer.biUnion OuterBad),
      ∃ H ∈ innerFactors R x₀, innerRel Pz x₀ z H := by
    intro z hz
    apply inner_factor_cover S Pz R x₀ Bad hroot hsimple z
    simpa [Outer, OuterBad] using hz
  obtain ⟨H, hH, hfiber⟩ :=
    exists_pair_fiber_of_fused_resultant_ledger
      S ∅ Outer OuterBad (innerFactors R x₀) (innerRel Pz x₀) rdeg
      (262144 - 131071) (262144 - bchksErrors6400 - 131071)
      bchksErrors6400 0 (2 * R.natDegree * D)
      (bchksFixedFactorResultCap6400 R.natDegree D) R.natDegree
      (bchksFixedFactorFusedCap6400 R.natDegree D)
      (by simp) houter hresult hpairs hfused hcover hlarge
  refine ⟨x₀, Bad, H, hBad, hBdeg, hB0, hprim, hseed, hH, ?_, hsimple⟩
  simpa [Outer, OuterBad, rdeg, innerFiber] using hfiber

end FixedFactorCover6400

end ProximityPrize.SubmissionLower
