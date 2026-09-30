import ProximityPrize.SubmissionLower.BalancedPhasePotential6815
import ProximityPrize.SubmissionLower.MovingFiberRouting6815
import ProximityPrize.SubmissionLower.MovingFiberKernels6815
set_option Elab.async false

namespace ProximityPrize.SubmissionLower.Lower80899.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80899.FactorSwitch Lower80899.PowerRoute
open Lower80899.Oracle
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helperPair_regularCountCap_mono_right
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂) :
    AsymmetricHelper.leftRegularCountCap (helperPair L₁ Y₁ S₁ leftY leftR leftZ) ≤
      AsymmetricHelper.leftRegularCountCap (helperPair L₂ Y₂ S₂ leftY leftR leftZ) := by
  let P₁ := helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂ := helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha : vectorLE P₁.leftAgreement P₂.leftAgreement := by
    exact ⟨le_rfl, le_rfl, le_rfl⟩
  have hm : vectorLE P₁.mixedCost P₂.mixedCost := by
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot : dot P₁.leftAgreement P₁.mixedCost ≤
      dot P₂.leftAgreement P₂.mixedCost := by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum : AsymmetricHelper.leftRegularNumerator P₁ ≤ AsymmetricHelper.leftRegularNumerator P₂ := by
    unfold AsymmetricHelper.leftRegularNumerator
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

namespace Phase00
def source : SourceNumbers := ⟨3840000,88497,19840,93828256412168595823867⟩
def potential : Potential := ⟨4806017950917,253306083227735,1156885757390133⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 3840000 88497 19840 (exactRouteBox p) 0≤potential.eval p := by
  have h := BalancedPhasePotential6815.count_le 3840000 88497 19840 39 182 11192 4806017950917 253306083227735 1156885757390133
    p.all (middle p) (total p) (by decide +kernel) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 3840000 88497 19840 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11599498755
  m := 63999
  weighted := by decide
  shape := MovingFiberKernels6815.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source00.finrank_gap u0 u1
end Phase00
namespace Phase01
def source : SourceNumbers := ⟨3200000,44249,9888,12051170488452604225288⟩
def potential : Potential := ⟨2399033815107,160155294626274,737980429949547⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 3200000 44249 9888 (exactRouteBox p) 0≤potential.eval p := by
  have h := BalancedPhasePotential6815.count_le 3200000 44249 9888 39 182 11192 2399033815107 160155294626274 737980429949547
    p.all (middle p) (total p) (by decide +kernel) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 3200000 44249 9888 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5799840000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6815.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source01.finrank_gap u0 u1
end Phase01
namespace Phase02
def source : SourceNumbers := ⟨2880000,44249,9888,10494049854430335745288⟩
def potential : Potential := ⟨2399033815107,151718415432486,698097000197501⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 2880000 44249 9888 (exactRouteBox p) 0≤potential.eval p := by
  have h := BalancedPhasePotential6815.count_le 2880000 44249 9888 39 182 11192 2399033815107 151718415432486 698097000197501
    p.all (middle p) (total p) (by decide +kernel) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 2880000 44249 9888 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5799840000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6815.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source02.finrank_gap u0 u1
end Phase02
namespace Phase03
def source : SourceNumbers := ⟨1062000,22124,4940,423032138525943634815⟩
def potential : Potential := ⟨1199005182058,65862486198238,301932366457852⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 1062000 22124 4940 (exactRouteBox p) 0≤potential.eval p := by
  have h := BalancedPhasePotential6815.count_le 1062000 22124 4940 39 182 11192 1199005182058 65862486198238 301932366457852
    p.all (middle p) (total p) (by decide +kernel) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 1062000 22124 4940 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2899920000
  m := 16000
  weighted := by decide
  shape := MovingFiberKernels6815.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source03.finrank_gap u0 u1
end Phase03
namespace Phase04
def source : SourceNumbers := ⟨531000,11062,2470,26128801782659821322⟩
def potential : Potential := ⟨445577482556,42396791527856,150966183228926⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 531000 11062 2470 (exactRouteBox p) 0≤potential.eval p := by
  have h := PhasePotential6815.half_middle_count p.all (middle p) (total p) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 531000 11062 2470 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1449960000
  m := 8000
  weighted := by decide
  shape := MovingFiberKernels6815.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source04.finrank_gap u0 u1
end Phase04
namespace Phase05
def source : SourceNumbers := ⟨88902,1382,308,8232573564822491⟩
def potential : Potential := ⟨74824573155,4704586947946,21672693353003⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 88902 1382 308 (exactRouteBox p) 0≤potential.eval p := by
  have h := BalancedPhasePotential6815.count_le 88902 1382 308 39 182 11192 74824573155 4704586947946 21672693353003
    p.all (middle p) (total p) (by decide +kernel) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 88902 1382 308 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181245000
  m := 1000
  weighted := by decide
  shape := MovingFiberKernels6815.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source05.finrank_gap u0 u1
end Phase05
namespace Phase06
def source : SourceNumbers := ⟨3640000,19359,4267,1324669961085702762641⟩
def potential : Potential := ⟨1042225434577,128673890692949,602050925398042⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 3640000 19359 4267 (exactRouteBox p) 0≤potential.eval p := by
  have h := BalancedPhasePotential6815.count_le 3640000 19359 4267 39 182 11192 1042225434577 128673890692949 602050925398042
    p.all (middle p) (total p) (by decide +kernel) hr hs hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 3640000 19359 4267 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2537430000
  m := 14000
  weighted := by decide
  shape := MovingFiberKernels6815.Source06.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source06.finrank_gap u0 u1
end Phase06
namespace PhaseFinal
def source : SourceNumbers := ⟨88902,1382,308,8232573564822491⟩
def potential : Potential := ⟨0,4690861953401,43345274666350⟩
theorem stageZero_le (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    stageCost 88902 1382 308 (exactRouteBox p) 0≤potential.eval p := by
  have h := PhasePotential6815.final_pass_count p.all (middle p) (total p) hr hy ht
  simpa only [stageCost,stagePair,exactRouteBox,helperPair,PhasePotential6815.pair,
    potential,Potential.eval,Nat.zero_mul,Nat.sub_zero,Nat.zero_add] using h
theorem stageZero_gates (p : FlagDegree) (hr : 1≤p.all) (hs : p.all≤39)
    (hy : middle p≤182) (ht : total p≤11192) :
    HelperPairGates 88902 1382 308 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  omega
def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)
noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80899.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181245000
  m := 1000
  weighted := by decide
  shape := MovingFiberKernels6815.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6815.Source05.finrank_gap u0 u1
end PhaseFinal
end ProximityPrize.SubmissionLower.Lower80899.SourceSound
