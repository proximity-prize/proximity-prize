import ProximityPrize.SubmissionLower.LocatorPhase6800Audit

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchPowerRoute. -/
section PackedLocator_LocatorBatchPowerRoute

/-!
# Counting consumer for shared regular-product power routes

`LocatorBatchProductRoute` selects the first strict post-projection factor
subset.  This file turns that algebraic stage into the helper bounds used by
the numerical phase recursion.  Source-specific gaps and receipt arithmetic
remain parameters here and are instantiated in the phase bridge.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute
  LocatorBatchProductRoute

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

/-- The exact cell box of a regular factor.  With this box `stageCost` is the
actual unequal-pair charge after the displayed number of source quotients. -/
def exactRouteBox {H : P4} (F : RegularIndex H) : PowerRouteBox where
  tLo := wt residualTotalWeights F.1
  tHi := wt residualTotalWeights F.1
  yLo := wt residualYSWeights F.1
  yHi := wt residualYSWeights F.1
  rLo := wt residualSWeights F.1
  rHi := wt residualSWeights F.1

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

/-- Multiplying the low terminal quotient by the removed batch power returns
an original source row in the derivative-contact box. -/
theorem reconstruct_mem_low_of_batch_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (P J : P4)
    (heq : P ^ j * J = reconstruct K D 131071 L S v.1)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) J <
      Dlow - j * wt (contactWeights 131071) P) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have hmul := wt_mul_le (contactWeights 131071) (P ^ j) J
  have hp := wt_pow_le (contactWeights 131071) P j
  omega

/-- Convert a selected batch exit into per-factor helper charges.  The
consumer retains the complementary product in every helper, so no internal
collision locus is charged. -/
theorem counts_of_batchExitStage
    (D L S m YS delta fuel : ℕ)
    (hD : 0 < D) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181373 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (A : Finset (RegularIndex H))
    (q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4)
    (hproduct : ∀ v,
      reconstruct K D 131071 L S v.1 = regularProduct H A * q v)
    (hexit : HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) (regularProduct H A))
      131071 delta
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) H A q)
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgates : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let P := regularProduct H A
  change HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) P) 131071 delta
      (L - wt residualTotalWeights P) (YS - wt residualYSWeights P)
      (S - wt residualSWeights P) H A q at hexit
  obtain ⟨e, U, v, J, hUA, hv, hJ, heq, hbox, havoid⟩ := hexit
  let j := e.val + 1
  have hj : 1 ≤ j := by simp only [j]; omega
  have hjle : j ≤ fuel := by simp only [j]; omega
  have hjchar : j < 2130706433 := hjle.trans_lt hfuelChar
  have heqOriginal : P ^ j * J =
      reconstruct K D 131071 L S v.1 := by
    calc
      P ^ j * J = P * (P ^ e.val * J) := by
        simp only [j, pow_succ']
        ring
      _ = P * q v := by rw [heq]
      _ = reconstruct K D 131071 L S v.1 := (hproduct v).symm
  change J ∈ nestedCoefficientBox K
      (D - delta - wt (contactWeights 131071) P - e.val * delta -
        e.val * wt (contactWeights 131071) P) 131071
      (L - wt residualTotalWeights P - e.val * wt residualTotalWeights P)
      (YS - wt residualYSWeights P - e.val * wt residualYSWeights P)
      (S - wt residualSWeights P - e.val * wt residualSWeights P) at hbox
  have hweights := nested_mem_weights hbox hJ
  have hJT : wt residualTotalWeights J ≤
      L - j * wt residualTotalWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.1
  have hJY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.1
  have hJS : wt residualSWeights J ≤
      S - j * wt residualSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.2.1
  have hJcontact : wt (contactWeights 131071) J <
      D - j * delta - j * wt (contactWeights 131071) P := by
    have hc := hweights.2.2.2
    simp only [j, Nat.sub_sub, Nat.add_mul, one_mul] at hc ⊢
    omega
  have hlow : reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K (D - j * delta) 131071 L S :=
    reconstruct_mem_low_of_batch_power u0 u1 v P J heqOriginal hD
      (hlowpos j hj hjle) hJcontact
  have hPT : j * wt residualTotalWeights P ≤ L :=
    (Nat.mul_le_mul_right (wt residualTotalWeights P) hjle).trans hfeasible.1
  have hPY : j * wt residualYSWeights P ≤ YS :=
    (Nat.mul_le_mul_right (wt residualYSWeights P) hjle).trans hfeasible.2.1
  have hPS : j * wt residualSWeights P ≤ S :=
    (Nat.mul_le_mul_right (wt residualSWeights P) hjle).trans hfeasible.2.2
  refine ⟨U, hUA, ?_⟩
  intro F hFU
  have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFU)
  have hQbounds := liftedHelper_residual_bounds H A F hFA L YS S j J hJ
    hJT hJY hJS hPT hPY hPS
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma QF = 0 := by
    exact batch_helper_zero_on_regularSeeds j D (D - j * delta) 131071
      L S m 181373 2130706433
      (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
      IRSProfile.domain u0 u1 H A F hFA selected Gamma v J hj hjchar
      (by decide) hdegree hagreement (hcapacity j hj hjle) hlow
      heqOriginal
  have hstage := regularSeeds_count_le_stageCost L YS S
    (exactRouteBox F) j u0 u1 H selected Gamma hdegree hagreement hno F
    (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
    (degreeZ_le_totalWeight F.1) QF
    (by simpa only [exactRouteBox] using hQbounds.1)
    (by simpa only [exactRouteBox] using hQbounds.2.1)
    (by simpa only [exactRouteBox] using hQbounds.2.2)
    hrel (by simpa only [exactRouteBox] using hgates F hFA j hj hjle)
    hQzero
  exact hstage.trans (hcharge F hFA j hj hjle)

/-- A complete algebraic step for one fresh source.  Stage zero uses the
existing divisor-or-helper switch.  If the entire batch product divides the
source, it is removed once and the shared product-power selector finds a
later strict exit.  `hcharge` is the sole interface to the additive numerical
potential used by a phase receipt. -/
theorem exists_strict_helper_split_of_batch_source
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181373)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181373 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hband : powerBandBudget delta
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hwidth :
          D - wt (contactWeights 131071) (regularProduct H A) ≤
            (D - delta -
              wt (contactWeights 131071) (regularProduct H A)) + delta := by
        omega
      have hsource : powerBandBudget delta
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hband.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudget_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) hwidth q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))


/-! ## Contact-thinned consumer (lever S1): the band hypothesis is the thin budget. -/


theorem exists_strict_helper_split_of_batch_source_thin
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181373)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181373 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) delta
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hDlow :
          D - delta - wt (contactWeights 131071) (regularProduct H A) =
            (D - wt (contactWeights 131071) (regularProduct H A)) - delta := by
        omega
      have hsource : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (D - wt (contactWeights 131071) (regularProduct H A)) delta
          (wt (contactWeights 131071) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hbandThin.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudgetThin_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) (by decide) hDlow q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))


end

end ProximityPrize.SubmissionLower.LocatorBatchPowerRoute
end PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier18 : True := by trivial
end ProximityPrize.SubmissionLower

