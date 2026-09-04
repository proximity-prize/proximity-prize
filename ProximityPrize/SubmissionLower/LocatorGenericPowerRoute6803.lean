import ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch6803

/-! Packed from ProximityPrize.SubmissionLower.LocatorGenericPowerRoute6803. -/
section PackedLocator_LocatorGenericPowerRoute6803

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

namespace ProximityPrize.SubmissionLower.LocatorGenericPowerRoute6803

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open LocatorGenericHelperFactorSwitch6803

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
      norm_num [I, IRSProfile.Index])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    hdegree hagreement
    (by simpa only [stagePair, helperPair, UnequalParameters.errors,
      Nat.reduceSub] using hno)
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

end ProximityPrize.SubmissionLower.LocatorGenericPowerRoute6803
end PackedLocator_LocatorGenericPowerRoute6803

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803Power : True := by trivial
end ProximityPrize.SubmissionLower


