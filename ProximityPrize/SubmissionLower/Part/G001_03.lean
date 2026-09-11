import ProximityPrize.SubmissionLower.Part.G001_02
section Compact_PackedLocatorTail
section PackedLocator_LocatorBatchProductRoute
namespace ProximityPrize.SubmissionLower.LocatorBatchProductRoute
open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorTwoFactorAvoidance
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid



/-! ## Contact-thinned batch selector (lever S1) -/


theorem exists_batchExitStage_of_bandBudgetThin_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hw : 1 ≤ w) (hDlow : Dlow = Dhigh - delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (hA : A.Nonempty)
    (hsource :
      LocatorArbitraryPowerAvoidance.powerBandBudgetThin w Dhigh delta
          (wt (contactWeights w) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          T YS S (steps + 1) < Module.finrank K V)
    (hterminal :
      T - steps * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - steps * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - steps * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfield : A.card < ENat.card K) :
    HasBatchExitStage (steps + 1) Dlow w delta T YS S H A q := by
  classical
  let P := regularProduct H A
  have hP : P ≠ 0 := by
    simpa only [P] using regularProduct_ne_zero H A
  change LocatorArbitraryPowerAvoidance.powerBandBudgetThin w Dhigh delta
      (wt (contactWeights w) P)
      (wt residualTotalWeights P) (wt residualYSWeights P)
      (wt residualSWeights P) T YS S (steps + 1) <
    Module.finrank K V at hsource
  change
    T - steps * wt residualTotalWeights P < wt residualTotalWeights P ∨
    YS - steps * wt residualYSWeights P < wt residualYSWeights P ∨
    S - steps * wt residualSWeights P < wt residualSWeights P at hterminal
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      let bandOne := (highBandMap (K := K) w Dlow delta T
        (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S).comp q
      let lowOne := LinearMap.ker bandOne
      have hwidth : Dhigh ≤ Dlow + delta := by omega
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T
              (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank : 0 < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hfirst : delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S <
              Module.finrank K V := by
          simpa only [LocatorArbitraryPowerAvoidance.powerBandBudgetThin,
            Nat.add_zero] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          LocatorArbitraryPowerAvoidance.mem_low_of_highBandMap_cut_eq_zero
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        exfalso
        obtain ⟨v, hv⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp hlowOneRank
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        have hdivT : wt residualTotalWeights P ≤
            wt residualTotalWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualTotalWeights P
              (qOne v) (hdivP v) hqv
        have hdivY : wt residualYSWeights P ≤
            wt residualYSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualYSWeights P
              (qOne v) (hdivP v) hqv
        have hdivS : wt residualSWeights P ≤
            wt residualSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualSWeights P
              (qOne v) (hdivP v) hqv
        rcases hterminal with ht | hy | hs
        · apply (not_lt_of_ge (hdivT.trans hb.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using ht
        · apply (not_lt_of_ge (hdivY.trans hb.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hy
        · apply (not_lt_of_ge (hdivS.trans hb.2.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hs
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T
        (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S).comp q
      let lowOne := LinearMap.ker bandOne
      have hwidth : Dhigh ≤ Dlow + delta := by omega
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T
              (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          LocatorArbitraryPowerAvoidance.powerBandBudgetThin w
              (Dhigh - delta - wt (contactWeights w) P) delta
              (wt (contactWeights w) P)
              (wt residualTotalWeights P) (wt residualYSWeights P)
              (wt residualSWeights P)
              (T - wt residualTotalWeights P)
              (YS - wt residualYSWeights P)
              (S - wt residualSWeights P) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S +
                LocatorArbitraryPowerAvoidance.powerBandBudgetThin w
                  (Dhigh - delta - wt (contactWeights w) P) delta
                  (wt (contactWeights w) P)
                  (wt residualTotalWeights P) (wt residualYSWeights P)
                  (wt residualSWeights P)
                  (T - wt residualTotalWeights P)
                  (YS - wt residualYSWeights P)
                  (S - wt residualSWeights P) (steps + 1) <
              Module.finrank K V := by
          simpa only [LocatorArbitraryPowerAvoidance.powerBandBudgetThin,
            Nat.succ_eq_add_one, Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          LocatorArbitraryPowerAvoidance.mem_low_of_highBandMap_cut_eq_zero
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        let qTwo := quotientLinear qOne P hP hdivP
        obtain ⟨hqTwo, _hprodTwo, hqTwoBox⟩ :=
          quotientLinear_nested_data Dlow w T YS S qOne hqOne hqOneBox
            P hP hdivP
        let DOneHigh := Dlow - wt (contactWeights w) P
        let DOneLow := Dlow - delta - wt (contactWeights w) P
        let TOne := T - wt residualTotalWeights P
        let YOne := YS - wt residualYSWeights P
        let SOne := S - wt residualSWeights P
        have hDlowRest : DOneLow = DOneHigh - delta := by
          simp only [DOneHigh, DOneLow]
          omega
        have hterminalRest :
            TOne - steps * wt residualTotalWeights P <
                wt residualTotalWeights P ∨
            YOne - steps * wt residualYSWeights P <
                wt residualYSWeights P ∨
            SOne - steps * wt residualSWeights P <
                wt residualSWeights P := by
          rcases hterminal with ht | hy | hs
          · left
            simpa only [TOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using ht
          · right; left
            simpa only [YOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hy
          · right; right
            simpa only [SOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hs
        obtain ⟨j, child, v, J, hchild, hv, hJ, heq, hbox, havoid⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hDlowRest qTwo hqTwo
            (by simpa only [qTwo, DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [DOneHigh, TOne, YOne, SOne, hDlow] using hlowOneRank)
            hterminalRest
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, child, v.1, J, hchild, ?_, hJ, ?_, ?_, havoid⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change P ^ (j.val + 1) * J = q v.1
          calc
            P ^ (j.val + 1) * J = P * (P ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = P * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne P hdivP v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) P =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) P := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights P =
              T - (j.val + 1) * wt residualTotalWeights P := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights P =
              YS - (j.val + 1) * wt residualYSWeights P := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights P =
              S - (j.val + 1) * wt residualSWeights P := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          change J ∈ nestedCoefficientBox K
            (DOneLow - j.val * delta -
              j.val * wt (contactWeights w) P) w
            (TOne - j.val * wt residualTotalWeights P)
            (YOne - j.val * wt residualYSWeights P)
            (SOne - j.val * wt residualSWeights P) at hbox
          change J ∈ nestedCoefficientBox K
            (Dlow - (j.val + 1) * delta -
              (j.val + 1) * wt (contactWeights w) P) w
            (T - (j.val + 1) * wt residualTotalWeights P)
            (YS - (j.val + 1) * wt residualYSWeights P)
            (S - (j.val + 1) * wt residualSWeights P)
          rw [hD, hT, hY, hS] at hbox
          exact hbox
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid


/-! ## Derivative extraction has no internal-collision locus -/

/-- The retained complementary product is part of the helper passed to the
power-extraction lemma.  Hence this conclusion holds on every regular seed,
without assuming that the complementary product specializes nonzero. -/
theorem specialization_eq_zero_of_batch_power
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (P : Polynomial K) (gamma : K) (J : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F.1 = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F.1) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (regularProduct H A ^ j * J)) = 0) :
    RCN319.specialization K P gamma
      (regularCofactor H A F ^ j * J) = 0 := by
  rw [regularProduct_power_split H A F hFA j J] at hpower
  exact specialization_eq_zero_of_iteratePderivR_power_product
    j P gamma F.1 (regularCofactor H A F ^ j * J)
    hfactorial hFzero hregular hpower

/-- Kernel/contact wrapper for the collision-free batch extraction.  The
only capacity cost is the derivative order `j`; no specialization condition
on any other regular factor appears. -/
theorem batch_helper_zero_on_regularSeeds
    {I : Type} [Fintype I] [DecidableEq I]
    (j D Dlow w L S m agreements p : ℕ)
    [CharP K p] (hp : p.Prime)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
    (J : P4 K)
    (hj : 1 ≤ j) (hjchar : j < p) (hw : 1 ≤ w)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card)
    (hcapacity : Dlow ≤ (m - j) * agreements + j * (w - 1))
    (hlow : reconstruct K D w L S v.1 ∈
      globalCoefficientBox K Dlow w L S)
    (heq : regularProduct H A ^ j * J = reconstruct K D w L S v.1) :
    ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (regularCofactor H A F ^ j * J) = 0 := by
  classical
  intro gamma hgamma
  have hgammaG := regularSeeds_subset H selected Gamma F hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
  have hcard : agreements ≤ support.card := hagreement gamma hgammaG
  have hcap : Dlow ≤ (m - j) * support.card + j * (w - 1) :=
    hcapacity.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (m - j) hcard) _)
  have hvalues : ∀ i ∈ support,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
    j D Dlow w L S m nodes u0 u1 v hlow
    (selected gamma) gamma support hj hw (hdegree gamma hgammaG)
    hcap hvalues
  rw [← heq] at hder
  obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
  exact specialization_eq_zero_of_batch_power H A F hFA j
    (selected gamma) gamma J
    (factorial_ne_zero_of_lt_char p j hp hjchar)
    hFzero hregular hder

/-! ## Numerical one-split interface -/


/-! ## Abstract recursion by a phase potential

The state type below is deliberately indexed by an arbitrary well-founded
phase rank.  A state may therefore carry the current quotient space, its
post-projection linear family, the product identity, and all box receipts;
none of those data has to be compressed into a flag.  Its `factors` are
exactly the factors universal immediately after the preceding projection.

At a successor state a consumer has two choices.

* Stop, by showing that the sum of ordinary per-factor caps fits the current
  potential.
* Produce a child state on the universal subset `U`.  All factors in `A \ U`
  must receive helper bounds from the *current* post-projection family.  The
  child potential plus those helper caps must fit the parent potential.

The child may have `U = A`; the phase rank then records one fewer band of the
same source.  When `U ⊂ A`, the child may instead reset to a fresh source and
the phase rank can encode a lexicographic measure such as aggregate positive
R-weight followed by that source's remaining bands.  At rank zero `hbase` is the
terminal receipt (usually the fact that no nonempty universal subset fits the
residual box, followed by one last simultaneous-avoidance split).
-/

/-- Soundness of a recursive post-projection partition certificate.  This is
pure finite-sum bookkeeping: all algebraic obligations are localized in
`hstep`, and all numerical obligations are localized in `hbase`, the stop
alternative, and the displayed potential inequality. -/
theorem sum_count_le_of_phasePotential
    {A : Type} [DecidableEq A]
    (count ordinaryCap : A → ℕ)
    (State : ℕ → Type)
    (factors : (n : ℕ) → State n → Finset A)
    (potential : (n : ℕ) → State n → ℕ)
    (hordinary : ∀ a, count a ≤ ordinaryCap a)
    (hbase : ∀ s : State 0,
      (∑ a ∈ factors 0 s, ordinaryCap a) ≤ potential 0 s)
    (hstep : ∀ n (s : State (n + 1)),
      ((∑ a ∈ factors (n + 1) s, ordinaryCap a) ≤
          potential (n + 1) s) ∨
        ∃ (t : State n) (helperCap : A → ℕ),
          factors n t ⊆ factors (n + 1) s ∧
          (∀ a ∈ factors (n + 1) s \ factors n t,
            count a ≤ helperCap a) ∧
          potential n t +
              (∑ a ∈ factors (n + 1) s \ factors n t, helperCap a) ≤
            potential (n + 1) s)
    (n : ℕ) (s : State n) :
    (∑ a ∈ factors n s, count a) ≤ potential n s := by
  induction n with
  | zero =>
      exact (Finset.sum_le_sum fun a _ha => hordinary a).trans (hbase s)
  | succ n ih =>
      rcases hstep n s with hstop | ⟨t, helperCap, hsub, hhelper, hpot⟩
      · exact (Finset.sum_le_sum fun a _ha => hordinary a).trans hstop
      · let current := factors (n + 1) s
        let universal := factors n t
        have hsplit : current = universal ∪ (current \ universal) := by
          ext a
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · intro ha
            by_cases hau : a ∈ universal
            · exact Or.inl hau
            · exact Or.inr ⟨ha, hau⟩
          · intro ha
            exact ha.elim (fun hau => hsub hau) (fun hd => hd.1)
        have hdisjoint : Disjoint universal (current \ universal) := by
          apply Finset.disjoint_left.mpr
          intro a hau had
          exact (Finset.mem_sdiff.mp had).2 hau
        change (∑ a ∈ current, count a) ≤ potential (n + 1) s
        rw [hsplit, Finset.sum_union hdisjoint]
        exact (Nat.add_le_add (ih t)
          (Finset.sum_le_sum fun a ha => hhelper a ha)).trans hpot


/-! ## Complete descent through one source phase

The rank-indexed interface above is convenient while constructing one
particular algebraic route.  Numerical prefix certificates use a different
view: keep applying the same source while it routes the current aggregate,
and stop at the first nonrouteable strict subaggregate.  The next two lemmas
are the finite-set induction engine for that view.

Crucially, a routed step must return a *strict* child.  Thus its algebraic
implementation may restart from a fresh source on that child; no claim about
mixed powers in the preceding source family is hidden in this bookkeeping.
-/

/-- Repeatedly remove a helper-charged complement while `routeable` holds.
At the terminal subaggregate the single shared `defect` bounds what remains
above the additive charge. -/
theorem sum_count_le_charge_add_defect_of_strict_routes
    {A : Type} [DecidableEq A]
    (count charge : A → ℕ)
    (routeable : Finset A → Prop)
    (ambient : Finset A) (defect : ℕ)
    (hterminal : ∀ B, B ⊆ ambient → ¬ routeable B →
      (∑ a ∈ B, count a) ≤ (∑ a ∈ B, charge a) + defect)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧
        (∑ a ∈ B \ U, count a) ≤ (∑ a ∈ B \ U, charge a)) :
    (∑ a ∈ ambient, count a) ≤
      (∑ a ∈ ambient, charge a) + defect := by
  classical
  have aux : ∀ B : Finset A, B ⊆ ambient →
      (∑ a ∈ B, count a) ≤ (∑ a ∈ B, charge a) + defect := by
    intro B
    induction B using Finset.strongInduction with
    | H B ih =>
        intro hB
        by_cases hr : routeable B
        · obtain ⟨U, hUB, hexit⟩ := hroute B hB hr
          have hUsub : U ⊆ B := hUB.subset
          have hUambient : U ⊆ ambient := hUsub.trans hB
          have hUbound := ih U hUB hUambient
          let exited := B \ U
          have hexit' : (∑ a ∈ exited, count a) ≤
              (∑ a ∈ exited, charge a) := by
            simpa only [exited] using hexit
          have hsplit : B = U ∪ exited := by
            dsimp only [exited]
            exact (Finset.union_sdiff_of_subset hUsub).symm
          have hdisjoint : Disjoint U exited := by
            apply Finset.disjoint_left.mpr
            intro a hau had
            change a ∈ B \ U at had
            exact (Finset.mem_sdiff.mp had).2 hau
          calc
            (∑ a ∈ B, count a) =
                (∑ a ∈ U, count a) + (∑ a ∈ exited, count a) := by
              rw [hsplit, Finset.sum_union hdisjoint]
            _ ≤ ((∑ a ∈ U, charge a) + defect) +
                (∑ a ∈ exited, charge a) :=
              Nat.add_le_add hUbound hexit'
            _ = (∑ a ∈ B, charge a) + defect := by
              rw [hsplit, Finset.sum_union hdisjoint]
              omega
        · exact hterminal B hB hr
  exact aux ambient (fun _ ha => ha)

/-- One numerical phase transition.  `previous` is the already certified
bound before adding this source.  A nonrouteable terminal row bounds the
previous excess over the new additive charge, while a routeable row supplies
a strict child and helper-charged complement.  The resulting bound is the
minimum of retaining the previous certificate and using the new phase. -/
theorem sum_count_le_min_previous_onePhase
    {A : Type} [DecidableEq A]
    (count charge : A → ℕ)
    (routeable : Finset A → Prop)
    (previous : Finset A → ℕ)
    (ambient : Finset A) (defect : ℕ)
    (hprevious : ∀ B, B ⊆ ambient →
      (∑ a ∈ B, count a) ≤ previous B)
    (hterminal : ∀ B, B ⊆ ambient → ¬ routeable B →
      previous B ≤ (∑ a ∈ B, charge a) + defect)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧
        (∑ a ∈ B \ U, count a) ≤ (∑ a ∈ B \ U, charge a)) :
    (∑ a ∈ ambient, count a) ≤
      min (previous ambient) ((∑ a ∈ ambient, charge a) + defect) := by
  classical
  apply le_min
  · exact hprevious ambient (fun _ ha => ha)
  · apply sum_count_le_charge_add_defect_of_strict_routes
      count charge routeable ambient defect
    · intro B hB hnroute
      exact (hprevious B hB).trans (hterminal B hB hnroute)
    · exact hroute

end

end ProximityPrize.SubmissionLower.LocatorBatchProductRoute
end PackedLocator_LocatorBatchProductRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch. -/
section PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Unequal-pair parameters for a regular factor and an arbitrary helper
source.  Keeping the source parameters explicit lets all external locator
profiles share one factor-switch proof. -/
def helperPair (L YS S leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181363, leftY, leftR, leftZ, YS, S, L⟩

def HelperPairGates (L YS S leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair L YS S leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- For each regular irreducible factor, either it divides an entire source
kernel or one source witness is coprime to it and supplies the unequal-pair
count. -/
theorem divisor_or_helper_count
    (D L S m YS : ℕ) (hD : 0 < D) (hDa : D ≤ m * 181363)
    (hshape : D + S ≤ 131071 * (YS + 1))
    {u0 u1 : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates L YS S leftY leftR leftZ) :
    (∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        (helperPair L YS S leftY leftR leftZ).regularCountCap := by
  classical
  by_cases hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K D 131071 L S v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K D 131071 L S :=
      reconstruct_mem_globalCoefficientBox K D 131071 L S v.1
    have hQYS : wt residualYSWeights Q ≤ YS := by
      apply flag_box_ys_bound D 131071 L S YS (by decide) hshape Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      D 131071 L S hD).mp hQbox
    have hQY : Q.degreeOf 1 ≤ YS :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ S :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ L :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply regularSeeds_count_le_intersection
      (helperPair L YS S leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        exact Fintype.card_fin _)
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair, UnequalParameters.errors, (show (262144 - 181363 : ℕ) = 80781 by decide +kernel)] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_mem_ker K
      D 131071 L S m IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
    · exact hD
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · exact hDa.trans (Nat.mul_le_mul_left m
        (hagreement gamma (Finset.mem_filter.mp hgamma).1))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch
end PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericPowerRoute. -/
section PackedLocator_LocatorGenericPowerRoute

/-!
# A generic arbitrary-power locator route

This file packages the three generic ingredients needed by the replacement
grid.  A source first supplies either an immediate helper-pair bound or a
common factor.  In the common-factor branch, arbitrary many high-band
projections select an `F`-adic stage.  The arbitrary contact and product
lemmas then make its terminal quotient vanish on every regular seed, and the
same unequal-pair count charges that stage.

There is no hard-coded maximum power and no source-specific arithmetic here.
-/

namespace ProximityPrize.SubmissionLower.LocatorGenericPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open LocatorGenericHelperFactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Lower and upper cumulative-weight bounds for one factor cell. -/
structure PowerRouteBox where
  tLo : ℕ
  tHi : ℕ
  yLo : ℕ
  yHi : ℕ
  rLo : ℕ
  rHi : ℕ
  deriving DecidableEq

/-- The unequal-pair profile charged after removing `j` copies of a factor. -/
def stagePair (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) :
    UnequalParameters :=
  helperPair (L - j * b.tLo) (YS - j * b.yLo) (S - j * b.rLo)
    b.yHi b.rHi b.tHi

def stageCost (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) : ℕ :=
  (stagePair L YS S b j).regularCountCap

/-- Maximum of the initial helper cost and every power-stage cost through
`k`.  Primitive recursion avoids a large finite computation in receipts. -/
def routeCost (L YS S : ℕ) (b : PowerRouteBox) : ℕ → ℕ
  | 0 => stageCost L YS S b 0
  | k + 1 => max (routeCost L YS S b k) (stageCost L YS S b (k + 1))

theorem stageCost_le_routeCost (L YS S : ℕ) (b : PowerRouteBox)
    {j k : ℕ} (hjk : j ≤ k) :
    stageCost L YS S b j ≤ routeCost L YS S b k := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      exact le_rfl
  | succ k ih =>
      rw [routeCost]
      by_cases hj : j ≤ k
      · exact (ih hj).trans (Nat.le_max_left _ _)
      · have hjeq : j = k + 1 := by omega
        subst j
        exact Nat.le_max_right _ _

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- The generic form of `count_le_stageCost`. -/
theorem regularSeeds_count_le_stageCost
    (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (F : RegularIndex H)
    (hFY : F.1.degreeOf 1 ≤ b.yHi)
    (hFR : F.1.degreeOf 2 ≤ b.rHi)
    (hFZ : F.1.degreeOf 3 ≤ b.tHi)
    (Q : P4)
    (hQT : wt residualTotalWeights Q ≤ L - j * b.tLo)
    (hQY : wt residualYSWeights Q ≤ YS - j * b.yLo)
    (hQR : wt residualSWeights Q ≤ S - j * b.rLo)
    (hrel : IsRelPrime F.1 Q)
    (hgates : HelperPairGates (L - j * b.tLo) (YS - j * b.yLo)
      (S - j * b.rLo) b.yHi b.rHi b.tHi)
    (hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (regularSeeds H selected Gamma F).card ≤ stageCost L YS S b j := by
  have hQY' : Q.degreeOf 1 ≤ (stagePair L YS S b j).rightY := by
    simpa only [stagePair, helperPair] using (degreeY_le_ysWeight Q).trans hQY
  have hQR' : Q.degreeOf 2 ≤ (stagePair L YS S b j).rightR := by
    simpa only [stagePair, helperPair] using (degreeR_le_sWeight Q).trans hQR
  have hQZ : Q.degreeOf 3 ≤ (stagePair L YS S b j).rightZ := by
    simpa only [stagePair, helperPair] using (degreeZ_le_totalWeight Q).trans hQT
  obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
    hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
  have hcount := regularSeeds_count_le_intersection
    (stagePair L YS S b j) H Q F hrel 2130706433
    (by simpa only [stagePair, helperPair] using hFY)
    (by simpa only [stagePair, helperPair] using hFR)
    (by simpa only [stagePair, helperPair] using hFZ)
    hQY' hQR' hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      exact Fintype.card_fin _)
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    hdegree hagreement
    (by simpa only [stagePair, helperPair, UnequalParameters.errors,
      (show (262144 - 181363 : ℕ) = 80781 by decide +kernel)] using hno)
    hQzero
  simpa only [stageCost] using hcount

private theorem quotient_nested
    (D L S m YS : ℕ) (hshape : D + S ≤ 131071 * (YS + 1))
    (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F ∣ reconstruct K D 131071 L S v.1) :
    ∃ q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4,
      Function.Injective q ∧
      (∀ v, reconstruct K D 131071 L S v.1 = F * q v) ∧
      (∀ v, q v ∈ nestedCoefficientBox K
        (D - wt (contactWeights 131071) F) 131071
        (L - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F)) := by
  let recon := kernelReconstructLinear (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  have hdivK : ∀ v, F ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F hF hdivK
  have hqinj : Function.Injective q := quotientLinear_injective recon
    (kernelReconstructLinear_injective (K := K) D 131071 L S m
      IRSProfile.domain u0 u1) F hF hdivK
  have hprod (v) : recon v = F * q v :=
    recon_eq_mul_quotientPolynomial recon F hdivK v
  have hproduct : ∀ v, reconstruct K D 131071 L S v.1 = F * q v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hprod v
  have hqbox : ∀ v, q v ∈ globalCoefficientBox K
      (D - wt (contactWeights 131071) F) 131071
      (L - wt residualTotalWeights F) (S - wt residualSWeights F) :=
    quotient_box_of_full_divisor D 131071 L S m
      (wt (contactWeights 131071) F) (wt residualTotalWeights F)
      (wt residualSWeights F) IRSProfile.domain u0 u1 F hF hdivK
      le_rfl le_rfl le_rfl
  have hqNested : ∀ v, q v ∈ nestedCoefficientBox K
      (D - wt (contactWeights 131071) F) 131071
      (L - wt residualTotalWeights F)
      (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
    intro v
    have hqYS : wt residualYSWeights (q v) ≤
        YS - wt residualYSWeights F := by
      by_cases hv : v = 0
      · subst v
        simp [wt, MvPolynomial.weightedTotalDegree]
      · have hqv : q v ≠ 0 := by
          intro hz
          apply hv
          apply hqinj
          simpa only [map_zero] using hz
        have hsrc : wt residualYSWeights
            (reconstruct K D 131071 L S v.1) ≤ YS := by
          apply flag_box_ys_bound D 131071 L S YS (by decide) hshape
          exact reconstruct_mem_globalCoefficientBox K D 131071 L S v.1
        have hmul := weightedTotalDegree_mul residualYSWeights F (q v) hF hqv
        rw [← hproduct v] at hmul
        simp only [wt] at hsrc ⊢
        omega
    intro d hd
    have hb := hqbox v hd
    have hy := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hqYS
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
    simpa [residualYSWeights] using hy
  exact ⟨q, hqinj, hproduct, hqNested⟩

private theorem sub_one_then_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem sub_pair_then_mul (a x y j : ℕ) :
    a - x - y - j * x - j * y =
      a - (j + 1) * x - (j + 1) * y := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem reconstruct_mem_low_of_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (F Q : P4) (heq : reconstruct K D 131071 L S v.1 = F ^ j * Q)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) Q <
      Dlow - j * wt (contactWeights 131071) F) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [heq]
  have hmul := wt_mul_le (contactWeights 131071) (F ^ j) Q
  have hp := wt_pow_le (contactWeights 131071) F j
  omega

/-- One theorem replaces every source-specific `count_k2`, ..., `count_kN`
ladder.  The source arithmetic appears only in `hband`, `hgapLe`, capacity,
and positivity receipts. -/
theorem regularSeeds_count_le_arbitraryPowerRoute
    (D L S m YS gap delta k : ℕ) (b : PowerRouteBox)
    (hD : 0 < D) (hDa : D ≤ m * 181363)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hk : 1 ≤ k) (hkchar : k < 2130706433)
    (hband : powerBandBudget delta b.tLo b.yLo b.rLo
      (L - b.tLo) (YS - b.yLo) (S - b.rLo) k < gap)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      D - j * delta ≤ (m - j) * 181363 + j * (131071 - 1))
    (hlowpos : ∀ j, 1 ≤ j → j ≤ k → 0 < D - j * delta)
    (hterminal : L - k * b.tLo < b.tLo ∨
      YS - k * b.yLo < b.yLo ∨ S - k * b.rLo < b.rLo)
    (hgates : ∀ j, j ≤ k →
      HelperPairGates (L - j * b.tLo) (YS - j * b.yLo)
        (S - j * b.rLo) b.yHi b.rHi b.tHi)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (F : RegularIndex H)
    (hFT : b.tLo ≤ wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1 ≤ b.tHi)
    (hFY : b.yLo ≤ wt residualYSWeights F.1 ∧
      wt residualYSWeights F.1 ≤ b.yHi)
    (hFR : b.rLo ≤ wt residualSWeights F.1 ∧
      wt residualSWeights F.1 ≤ b.rHi)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost L YS S b k := by
  classical
  have hFspec := RCN167.positiveRFactors_spec H F.1 F.2
  have hF : F.1 ≠ 0 := hFspec.1.ne_zero
  have hFdegY : F.1.degreeOf 1 ≤ b.yHi :=
    (degreeY_le_ysWeight F.1).trans hFY.2
  have hFdegR : F.1.degreeOf 2 ≤ b.rHi :=
    (degreeR_le_sWeight F.1).trans hFR.2
  have hFdegZ : F.1.degreeOf 3 ≤ b.tHi :=
    (degreeZ_le_totalWeight F.1).trans hFT.2
  rcases divisor_or_helper_count D L S m YS hD hDa hshape
      selected Gamma hdegree hagreement hno F b.yHi b.rHi b.tHi
      hFdegY hFdegR hFdegZ (by
        simpa only [Nat.zero_mul, Nat.sub_zero] using
          hgates 0 (Nat.zero_le k)) with hdiv | hhelper
  · cases k with
    | zero => omega
    | succ steps =>
      obtain ⟨q, hqinj, hproduct, hqNested⟩ :=
        quotient_nested D L S m YS hshape u0 u1 F.1 hF hdiv
      have hTstart : L - wt residualTotalWeights F.1 ≤ L - b.tLo :=
        Nat.sub_le_sub_left hFT.1 L
      have hYstart : YS - wt residualYSWeights F.1 ≤ YS - b.yLo :=
        Nat.sub_le_sub_left hFY.1 YS
      have hRstart : S - wt residualSWeights F.1 ≤ S - b.rLo :=
        Nat.sub_le_sub_left hFR.1 S
      have hbudgetMono := powerBandBudget_mono delta
        (wt residualTotalWeights F.1) (wt residualYSWeights F.1)
        (wt residualSWeights F.1)
        (L - wt residualTotalWeights F.1)
        (YS - wt residualYSWeights F.1) (S - wt residualSWeights F.1)
        b.tLo b.yLo b.rLo (L - b.tLo) (YS - b.yLo) (S - b.rLo)
        (steps + 1) hTstart hYstart hRstart hFT.1 hFY.1 hFR.1
      have hsource : powerBandBudget delta
          (wt residualTotalWeights F.1) (wt residualYSWeights F.1)
          (wt residualSWeights F.1)
          (L - wt residualTotalWeights F.1)
          (YS - wt residualYSWeights F.1)
          (S - wt residualSWeights F.1) (steps + 1) <
        Module.finrank K (ConstraintKernel (K := K) D 131071 L S m
          IRSProfile.domain u0 u1) := by
        exact (hbudgetMono.trans_lt (by
          simpa only [Nat.succ_eq_add_one] using hband)).trans_le hgapLe
      have hwidth : D - wt (contactWeights 131071) F.1 ≤
          (D - delta - wt (contactWeights 131071) F.1) + delta := by
        omega
      obtain ⟨j0, v, J, _hv, hJ, heq, hJbox, hnotTerminal⟩ :=
        exists_power_stage_of_bandBudget_succ steps
          (D - wt (contactWeights 131071) F.1)
          (D - delta - wt (contactWeights 131071) F.1)
          131071 delta
          (L - wt residualTotalWeights F.1)
          (YS - wt residualYSWeights F.1)
          (S - wt residualSWeights F.1)
          hwidth q hqinj hqNested F.1 hF hsource
      let j := j0.val + 1
      have hjpos : 1 ≤ j := by simp only [j]; omega
      have hjle : j ≤ Nat.succ steps := by
        simp only [j]
        omega
      have heqOriginal : reconstruct K D 131071 L S v.1 = F.1 ^ j * J := by
        calc
          reconstruct K D 131071 L S v.1 = F.1 * q v := hproduct v
          _ = F.1 * (F.1 ^ j0.val * J) := by rw [heq]
          _ = F.1 ^ j * J := by
            simp only [j, pow_succ', mul_assoc]
      have hweights := nested_mem_weights hJbox hJ
      have hJTactual : wt residualTotalWeights J ≤
          L - j * wt residualTotalWeights F.1 := by
        simpa only [j, sub_one_then_mul] using hweights.1
      have hJYactual : wt residualYSWeights J ≤
          YS - j * wt residualYSWeights F.1 := by
        simpa only [j, sub_one_then_mul] using hweights.2.1
      have hJRactual : wt residualSWeights J ≤
          S - j * wt residualSWeights F.1 := by
        simpa only [j, sub_one_then_mul] using hweights.2.2.1
      have hJT : wt residualTotalWeights J ≤ L - j * b.tLo :=
        hJTactual.trans (Nat.sub_le_sub_left
          (Nat.mul_le_mul_left j hFT.1) L)
      have hJY : wt residualYSWeights J ≤ YS - j * b.yLo :=
        hJYactual.trans (Nat.sub_le_sub_left
          (Nat.mul_le_mul_left j hFY.1) YS)
      have hJR : wt residualSWeights J ≤ S - j * b.rLo :=
        hJRactual.trans (Nat.sub_le_sub_left
          (Nat.mul_le_mul_left j hFR.1) S)
      have hJcontact : wt (contactWeights 131071) J <
          D - j * delta - j * wt (contactWeights 131071) F.1 := by
        simpa only [j, sub_pair_then_mul] using hweights.2.2.2
      have hlow : reconstruct K D 131071 L S v.1 ∈
          globalCoefficientBox K (D - j * delta) 131071 L S :=
        reconstruct_mem_low_of_power u0 u1 v F.1 J heqOriginal hD
          (hlowpos j hjpos hjle) hJcontact
      have hrel : IsRelPrime F.1 J := by
        by_cases hjlt : j < Nat.succ steps
        · apply hFspec.1.isRelPrime_iff_not_dvd.mpr
          apply hnotTerminal
          simpa only [j, Nat.succ_eq_add_one] using hjlt
        · have hjeq : j = Nat.succ steps := by omega
          rcases hterminal with ht | hy | hr
          · apply isRelPrime_of_weight_lt residualTotalWeights F.1 J
              hFspec.1 hJ
            exact hJT.trans_lt (by rw [hjeq]; exact ht.trans_le hFT.1)
          · apply isRelPrime_of_weight_lt residualYSWeights F.1 J
              hFspec.1 hJ
            exact hJY.trans_lt (by rw [hjeq]; exact hy.trans_le hFY.1)
          · apply isRelPrime_of_weight_lt residualSWeights F.1 J
              hFspec.1 hJ
            exact hJR.trans_lt (by rw [hjeq]; exact hr.trans_le hFR.1)
      have hJzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
          RCN319.specialization K (selected gamma) gamma J = 0 := by
        intro gamma hgamma
        have hgammaG := regularSeeds_subset H selected Gamma F hgamma
        let support := (Finset.univ : Finset I).filter (fun i ↦
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)
        have hcard : 181363 ≤ support.card := hagreement gamma hgammaG
        have hcap : D - j * delta ≤
            (m - j) * support.card + j * (131071 - 1) :=
          (hcapacity j hjpos hjle).trans
            (Nat.add_le_add_right (Nat.mul_le_mul_left (m - j) hcard) _)
        have hvalues : ∀ i ∈ support,
            (selected gamma).eval (IRSProfile.domain i) =
              u0 i + gamma * u1 i := by
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
          j D (D - j * delta) 131071 L S m IRSProfile.domain u0 u1
          v hlow (selected gamma) gamma support hjpos (by decide)
          (hdegree gamma hgammaG) hcap hvalues
        rw [heqOriginal] at hder
        obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
        apply specialization_eq_zero_of_iteratePderivR_power_product
          j (selected gamma) gamma F.1 J
          (factorial_ne_zero_of_lt_char 2130706433 j
            (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
            (hjle.trans_lt hkchar))
          hFzero hregular hder
      have hstage := regularSeeds_count_le_stageCost L YS S b j u0 u1 H
        selected Gamma hdegree hagreement hno F hFdegY hFdegR hFdegZ J
        hJT hJY hJR hrel (hgates j hjle) hJzero
      exact hstage.trans (stageCost_le_routeCost L YS S b hjle)
  · have hzeroCost :
      (helperPair L YS S b.yHi b.rHi b.tHi).regularCountCap =
        stageCost L YS S b 0 := by
      simp only [stageCost, stagePair, Nat.zero_mul, Nat.sub_zero]
    rw [hzeroCost] at hhelper
    exact hhelper.trans (stageCost_le_routeCost L YS S b (Nat.zero_le k))

end

end ProximityPrize.SubmissionLower.LocatorGenericPowerRoute
end PackedLocator_LocatorGenericPowerRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Oracle. -/
section PackedLocator_LocatorPhase6800Oracle

/-!
# Compact numerical oracle for the 6800 regular-factor phases

This module contains only the small, reusable interface of the numerical
certificate.  The generated receipt rows live in separate modules.  A raw
state `⟨z,v,r⟩` represents cumulative degrees
`(total, middle, slope) = (z+v+r,v+r,r)`.

The four source phases are, in order, R1200, C, Split500 and Split390.  Three
prefixes forget `z`.  The C prefix retains 304-wide buckets (offset 64) only
on the critical rectangle `r ≤ 17, v ≤ 64`; outside that rectangle it too
forgets `z`.  This is a sound weakening of the exact prefix recurrence.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorLowQuotient LocatorArbitraryPowerAvoidance
open LocatorGenericPowerRoute LocatorGenericHelperFactorSwitch

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Coefficients of an additive potential in cumulative coordinates. -/
structure Potential where
  totalCoeff : ℕ
  middleCoeff : ℕ
  slopeCoeff : ℕ
  deriving DecidableEq, Repr

def Potential.eval (q : Potential) (p : FlagDegree) : ℕ :=
  q.totalCoeff * total p + q.middleCoeff * middle p + q.slopeCoeff * p.all

theorem Potential.eval_add (q : Potential) (p₁ p₂ : FlagDegree) :
    q.eval (p₁ + p₂) = q.eval p₁ + q.eval p₂ := by
  simp only [Potential.eval, total, middle, add_zOnly, add_yz, add_all]
  ring

def initialAPotential : Potential :=
  ⟨6028951284, 5462225136421, 25579200875807⟩

def r1200Potential : Potential :=
  ⟨36764078701232, 1763223219624231, 7905084447061489⟩

def sourceCPotential : Potential :=
  ⟨13427735141811, 664006777607640, 2980009468608277⟩

def split500Potential : Potential :=
  ⟨3401226049834, 169036896818327, 748519503389805⟩

def split1200Potential : Potential :=
  ⟨838681789895, 41479411858231, 186222646970525⟩

def split390Potential : Potential :=
  ⟨88195266130, 3190747159490, 14361692776390⟩

/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def sourceR1200 : SourceNumbers :=
  ⟨526750, 10983, 2450, 36963750380693986577⟩

def sourceC : SourceNumbers :=
  ⟨328400, 6641, 1480, 5090867013182078230⟩

def sourceSplit500 : SourceNumbers :=
  ⟨165000, 3320, 750, 315862958949324685⟩

def sourceSplit1200 : SourceNumbers :=
  ⟨82100, 1660, 370, 18278038734560710⟩

def sourceSplit390 : SourceNumbers :=
  ⟨19500, 539, 120, 91073661700890⟩

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50293 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

/-- Lever S1.  The product of the routed factors has contact weight at least
`131071 * middle p - p.all` (`contact_ge_ys` with the exact aggregate weights), and the
source's kernel degree satisfies `D + slopeCap ≤ 131071 * (middleCap + 1)`; so the level-1
contact cap of the band ladder is at most `contactCap`, and it drops by `50293 + contactDec`
per level.  `bandThin` is the ladder charged on the rows that can carry a monomial. -/
def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50293 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem SourceNumbers.bandThin_le (s : SourceNumbers) (p : FlagDegree) :
    s.bandThin p ≤ s.band p :=
  powerBandBudgetThin_le _ _ _ _ _ _ _ _ _ _ _

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

def exactRouteBox (p : FlagDegree) : PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

/-- The arithmetic interface required by the algebraic source adapter.  The
stage-cost and gate checks are deliberately separate from band thresholds. -/
structure PhaseSourceSound where
  source : SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6677 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6677 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

/-- Raw-to-cumulative flag constructor. -/
def rawFlag (r v z : ℕ) : FlagDegree := ⟨z, v, r⟩

@[simp] theorem rawFlag_all (r v z : ℕ) : (rawFlag r v z).all = r := rfl
@[simp] theorem rawFlag_middle (r v z : ℕ) : middle (rawFlag r v z) = r + v := by
  simp [rawFlag, middle, Nat.add_comm]
@[simp] theorem rawFlag_total (r v z : ℕ) : total (rawFlag r v z) = r + v + z := by
  simp [rawFlag, total, Nat.add_comm, Nat.add_left_comm]

/-- The C-prefix bucket used by the compact receipt. -/
def cBucket (z : ℕ) : ℕ := if z ≤ 64 then 0 else (z - 64 + 303) / 304


/-- Exact maximum additive A-potential available to a complementary raw flag
inside the wide cumulative box `(6677,153,33)`. -/
def initialAComplementCore (p : FlagDegree) : ℕ :=
  let t := 6677 - total p
  let y := 153 - middle p
  let r := 33 - p.all
  let nr := min t (min y r)
  let t' := t - nr
  let y' := y - nr
  let nv := min t' y'
  initialAPotential.eval (rawFlag nr nv (t' - nv))

/-- The correlated complement charge: the greedy A-potential complement plus the
derivative chains of the universal child (total slope `p.all`, Y-degree `middle p`)
and of the remaining factors (slope `33 - p.all`, Y-degree `153 - p.yz`). -/
def initialAComplement (p : FlagDegree) : ℕ :=
  initialAComplementCore p + ChainGroupMaj.chainMaj 6677 p.all (middle p) +
    ChainGroupMaj.chainMaj 6677 (33 - p.all) (153 - p.yz) +
    ChainGroupMaj.residMaj6802 p.all

/-- The greedy complement is maximal for the A potential among all raw flags
that can be added to `p` inside the wide box. -/
theorem initialAPotential_le_complementCore (p n : FlagDegree)
    (ht : total p + total n ≤ 6677)
    (hy : middle p + middle n ≤ 153)
    (hr : p.all + n.all ≤ 33) :
    initialAPotential.eval n ≤ initialAComplementCore p := by
  have hnpY : n.all ≤ middle n := by simp [middle]
  have hnpT : middle n ≤ total n := by simp [middle, total]
  have hppY : p.all ≤ middle p := by simp [middle]
  have hppT : middle p ≤ total p := by simp [middle, total]
  simp only [initialAComplementCore, Potential.eval, initialAPotential,
    rawFlag_total, rawFlag_middle, rawFlag_all]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem initialAComplementCore_le (p : FlagDegree) :
    initialAComplementCore p ≤ initialAComplement p := by
  unfold initialAComplement
  omega

theorem initialAPotential_le_complement (p n : FlagDegree)
    (ht : total p + total n ≤ 6677)
    (hy : middle p + middle n ≤ 153)
    (hr : p.all + n.all ≤ 33) :
    initialAPotential.eval n ≤ initialAComplement p :=
  (initialAPotential_le_complementCore p n ht hy hr).trans (initialAComplementCore_le p)
end ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end PackedLocator_LocatorPhase6800Oracle
end Compact_PackedLocatorTail
