import ProximityPrize.SubmissionLower.LocatorBatchPhase6800

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound. -/
section PackedLocator_LocatorPhase6800SourceSound

/-! Analytic helper-cost and gate bounds for the four 6800 phase sources. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helperPair_regularCountCap_mono_right
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂) :
    (helperPair L₁ Y₁ S₁ leftY leftR leftZ).regularCountCap ≤
      (helperPair L₂ Y₂ S₂ leftY leftR leftZ).regularCountCap := by
  let P₁ := helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂ := helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha : vectorLE P₁.agreement P₂.agreement := by
    refine ⟨?_, ?_, ?_⟩
    · exact max_le_max le_rfl (Nat.add_le_add_left
        (Nat.mul_le_mul_left (2 * 131071) hY) 1)
    · exact max_le_max le_rfl (Nat.mul_le_mul_left 131071
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hS) 1))
    · exact max_le_max le_rfl (Nat.add_le_add_right
        (Nat.mul_le_mul_left (2 * 131071) hL) 1)
  have hm : vectorLE P₁.mixedCost P₂.mixedCost := by
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot : dot P₁.agreement P₁.mixedCost ≤
      dot P₂.agreement P₂.mixedCost := by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum : P₁.regularNumerator ≤ P₂.regularNumerator := by
    unfold UnequalParameters.regularNumerator
    exact Nat.add_le_add (Nat.mul_le_mul_left (P₁.n - P₁.w) hdot)
      (Nat.mul_le_mul_left ((P₁.errors + 1) * P₁.gap) hm.2.2)
  exact Nat.div_le_div_right hnum

theorem stageCost_le_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ) :
    stageCost L YS S (exactRouteBox p) j ≤
      stageCost L YS S (exactRouteBox p) 0 := by
  apply helperPair_regularCountCap_mono_right
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le L (j * total p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le YS (j * middle p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le S (j * p.all)

theorem helperPair_gates_of_right_le
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hgate : HelperPairGates L₂ Y₂ S₂ leftY leftR leftZ) :
    HelperPairGates L₁ Y₁ S₁ leftY leftR leftZ := by
  rcases hgate with ⟨hr, hy, hs, hz, hmy, hmr, hmz⟩
  refine ⟨hr, hy, hs, hz, ?_, ?_, ?_⟩
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
      (Nat.mul_le_mul_left leftZ hS)).trans_lt hmy
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
      (Nat.mul_le_mul_left leftZ hY)).trans_lt hmr
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
      (Nat.mul_le_mul_left leftR hY)).trans_lt hmz

theorem stageGates_of_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ)
    (hgate : HelperPairGates L YS S (middle p) p.all (total p)) :
    HelperPairGates (L - j * total p) (YS - j * middle p)
      (S - j * p.all) (middle p) p.all (total p) := by
  apply helperPair_gates_of_right_le
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact hgate

private theorem r1200_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    stageCost 328400 6642 1480 (exactRouteBox p) 0 ≤
      r1200Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 1741147165 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 387839089 := by omega
  have haz : 262142 * total p + 1 ≤ 86087432801 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, r1200Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem sourceC_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    stageCost 82100 1660 370 (exactRouteBox p) 0 ≤
      sourceCPotential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 435155721 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 96861469 := by omega
  have haz : 262142 * total p + 1 ≤ 21521858201 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, sourceCPotential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem split500_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    stageCost 42000 1383 310 (exactRouteBox p) 0 ≤
      split500Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 362542387 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 81132949 := by omega
  have haz : 262142 * total p + 1 ≤ 11009964001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split500Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem split390_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    stageCost 19500 539 120 (exactRouteBox p) 0 ≤
      split390Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 141294539 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 31325969 := by omega
  have haz : 262142 * total p + 1 ≤ 5111769001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split390Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem r1200_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    HelperPairGates 328400 6642 1480 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem sourceC_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    HelperPairGates 82100 1660 370 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem split500_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    HelperPairGates 42000 1383 310 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem split390_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 132) (ht : total p ≤ 6412) :
    HelperPairGates 19500 539 120 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def r1200Sound : PhaseSourceSound where
  source := sourceR1200
  potential := r1200Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 328400 6642 1480 p j).trans
      (r1200_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 328400 6642 1480 p j
      (r1200_stageZero_gates p hr hs hy ht)

def sourceCSound : PhaseSourceSound where
  source := sourceC
  potential := sourceCPotential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 82100 1660 370 p j).trans
      (sourceC_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 82100 1660 370 p j
      (sourceC_stageZero_gates p hr hs hy ht)

def split500Sound : PhaseSourceSound where
  source := sourceSplit500
  potential := split500Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 42000 1383 310 p j).trans
      (split500_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 42000 1383 310 p j
      (split500_stageZero_gates p hr hs hy ht)

def split390Sound : PhaseSourceSound where
  source := sourceSplit390
  potential := split390Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 19500 539 120 p j).trans
      (split390_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 19500 539 120 p j
      (split390_stageZero_gates p hr hs hy ht)

/-! The initial A split is wider than A in the middle/slope coordinates, so
its two agreement maxima are handled explicitly rather than by source
dominance. -/

private theorem initialA_highY_highR_int (t y r : ℤ)
    (ht : y ≤ t) (hylo : 132 ≤ y) (hyhi : y ≤ 153)
    (hrlo : 29 ≤ r) (hrhi : r ≤ 33) :
    996432412614 * t * y + 4535485464312 * t * r +
        8933531975160000 * y * r ≤
      302125682489247 * t + 173204606068620937 * y +
        563790857807479424 * r + 50301 := by
  have hcT : 0 ≤ 302125682489247 - 996432412614 * y -
      4535485464312 * r := by omega
  have hpT : 0 ≤ (t - y) * (302125682489247 - 996432412614 * y -
      4535485464312 * r) := mul_nonneg (by omega) hcT
  have hcR : 0 ≤ 8938067460624312 * y - 563790857807479424 := by
    omega
  have hpR : 0 ≤ (33 - r) *
      (8938067460624312 * y - 563790857807479424) :=
    mul_nonneg (by omega) hcR
  have hpY : 0 ≤ 2 * (153 - y) *
      (498216206307 * y + 60800974304311027) :=
    mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)
  nlinarith

private theorem initialA_highY_lowR_int (t y r : ℤ)
    (ht : y ≤ t) (hylo : 132 ≤ y) (hyhi : y ≤ 153)
    (hrhi : r ≤ 28) :
    996432412614 * t * y + 4466765987580000 * y * r ≤
      170596604024199 * t + 43668392428800937 * y +
        563790857807479424 * r + 50301 := by
  have hcT : 0 ≤ 170596604024199 - 996432412614 * y := by omega
  have hpT : 0 ≤ (t - y) * (170596604024199 - 996432412614 * y) :=
    mul_nonneg (by omega) hcT
  have hcR : 0 ≤ 4466765987580000 * y - 563790857807479424 := by
    omega
  have hpR : 0 ≤ (28 - r) *
      (4466765987580000 * y - 563790857807479424) :=
    mul_nonneg (by omega) hcR
  have hpY : 0 ≤ 2 * (153 - y) *
      (498216206307 * y + 40691456389272403) :=
    mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by positivity)
  nlinarith

private theorem initialA_lowY_highR_int (t y r : ℤ)
    (ht : y ≤ t) (hyr : r ≤ y) (hrlo : 29 ≤ r) (hrhi : r ≤ 33) :
    4535485464312 * t * r + 4466765987580000 * y * r +
        25822252553080576 * r ≤
      170596604024199 * t + 173204606068620937 * y + 50301 := by
  have hcT : 0 ≤ 170596604024199 - 4535485464312 * r := by omega
  have hpT : 0 ≤ (t - y) * (170596604024199 - 4535485464312 * r) :=
    mul_nonneg (by omega) hcT
  have hcY : 0 ≤ 173375202672645136 - 4471301473044312 * r := by
    omega
  have hpY : 0 ≤ (y - r) *
      (173375202672645136 - 4471301473044312 * r) :=
    mul_nonneg (by omega) hcY
  have hpR : 0 ≤ 2 * (33 - r) * (2235650736522156 * r - 754551132) :=
    mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)
  nlinarith

/- Keep the casts and the truncated predecessor `2 * r - 1` out of the main
   helper definition.  These three fixed branch lemmas elaborate much faster
   than normalizing that definition after all maxima have been split. -/
private theorem initialA_highY_highR_nat (t y r : ℕ)
    (ht : y ≤ t) (hylo : 132 ≤ y) (hyhi : y ≤ 153)
    (hrlo : 29 ≤ r) (hrhi : r ≤ 33) :
    131073 *
          ((1 + 262142 * y) * (r * 130000 + t * 29) +
            131071 * (2 * r - 1) * (y * 130000 + t * 132) +
            34078460001 * (y * 29 + r * 132)) +
        4062993144 * (y * 29 + r * 132) ≤
      (5961153504 * t + 5974067721865 * y + 22929595672934 * r) *
          50302 + 50301 := by
  have hi := initialA_highY_highR_int (t : ℤ) (y : ℤ) (r : ℤ)
    (by exact_mod_cast ht) (by exact_mod_cast hylo) (by exact_mod_cast hyhi)
    (by exact_mod_cast hrlo) (by exact_mod_cast hrhi)
  have hn :
      996432412614 * t * y + 4535485464312 * t * r +
          8933531975160000 * y * r ≤
        302125682489247 * t + 173204606068620937 * y +
          563790857807479424 * r + 50301 := by
    exact_mod_cast hi
  have hsub : 2 * r - 1 + 1 = 2 * r := by omega
  nlinarith

private theorem initialA_highY_lowR_nat (t y r : ℕ)
    (ht : y ≤ t) (hylo : 132 ≤ y) (hyhi : y ≤ 153)
    (hrhi : r ≤ 28) (hrlo : 1 ≤ r) :
    131073 *
          ((1 + 262142 * y) * (r * 130000 + t * 29) +
            7471047 * (y * 130000 + t * 132) +
            34078460001 * (y * 29 + r * 132)) +
        4062993144 * (y * 29 + r * 132) ≤
      (5961153504 * t + 5974067721865 * y + 22929595672934 * r) *
          50302 + 50301 := by
  have hi := initialA_highY_lowR_int (t : ℤ) (y : ℤ) (r : ℤ)
    (by exact_mod_cast ht) (by exact_mod_cast hylo) (by exact_mod_cast hyhi)
    (by exact_mod_cast hrhi)
  have hn :
      996432412614 * t * y + 4466765987580000 * y * r ≤
        170596604024199 * t + 43668392428800937 * y +
          563790857807479424 * r + 50301 := by
    exact_mod_cast hi
  nlinarith

private theorem initialA_lowY_highR_nat (t y r : ℕ)
    (ht : y ≤ t) (hyr : r ≤ y) (hrlo : 29 ≤ r) (hrhi : r ≤ 33) :
    131073 *
          (34602745 * (r * 130000 + t * 29) +
            131071 * (2 * r - 1) * (y * 130000 + t * 132) +
            34078460001 * (y * 29 + r * 132)) +
        4062993144 * (y * 29 + r * 132) ≤
      (5961153504 * t + 5974067721865 * y + 22929595672934 * r) *
          50302 + 50301 := by
  have hi := initialA_lowY_highR_int (t : ℤ) (y : ℤ) (r : ℤ)
    (by exact_mod_cast ht) (by exact_mod_cast hyr)
    (by exact_mod_cast hrlo) (by exact_mod_cast hrhi)
  have hn :
      4535485464312 * t * r + 4466765987580000 * y * r +
          25822252553080576 * r ≤
        170596604024199 * t + 173204606068620937 * y + 50301 := by
    exact_mod_cast hi
  have hsub : 2 * r - 1 + 1 = 2 * r := by omega
  nlinarith

theorem initialAHelperCap_le_potential (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 153) (ht : total p ≤ 6412) :
    (helperPair 130000 132 29 (middle p) p.all (total p)).regularCountCap ≤
      initialAPotential.eval p := by
  have haz : 262142 * total p + 1 ≤ 34078460001 := by omega
  have hry : p.all ≤ middle p := by simp [middle]
  have hyt : middle p ≤ total p := by simp [middle, total]
  simp only [helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, initialAPotential]
  rw [max_eq_right haz]
  by_cases hay : 34602745 ≤ 1 + 262142 * middle p
  · rw [max_eq_left hay]
    by_cases har : 7471047 ≤ 131071 * (2 * p.all - 1)
    · rw [max_eq_left har]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hrlo : 29 ≤ p.all := by omega
      have hylo : 132 ≤ middle p := by omega
      exact initialA_highY_highR_nat (total p) (middle p) p.all hyt hylo hy
        hrlo hs
    · rw [max_eq_right (Nat.le_of_not_ge har)]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hylo : 132 ≤ middle p := by omega
      have hr27 : p.all ≤ 28 := by omega
      exact initialA_highY_lowR_nat (total p) (middle p) p.all hyt hylo hy
        hr27 hr
  · rw [max_eq_right (Nat.le_of_not_ge hay)]
    by_cases har : 7471047 ≤ 131071 * (2 * p.all - 1)
    · rw [max_eq_left har]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hrlo : 29 ≤ p.all := by omega
      exact initialA_lowY_highR_nat (total p) (middle p) p.all hyt hry hrlo hs
    · rw [max_eq_right (Nat.le_of_not_ge har)]
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      ring_nf
      omega

end ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound
end PackedLocator_LocatorPhase6800SourceSound

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier44 : True := by trivial
end ProximityPrize.SubmissionLower

