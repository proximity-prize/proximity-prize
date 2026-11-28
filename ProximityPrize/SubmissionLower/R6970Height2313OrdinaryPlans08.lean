import ProximityPrize.SubmissionLower.R6970Height2313Rescue
import ProximityPrize.SubmissionLower.R6970Height2313Sources

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1703
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases22
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,40⟩
  bank i := ![Physical.src1738.bank, Physical.src1739.bank, Physical.src1740.bank, Physical.src1741.bank, Physical.src1742.bank, Physical.src1743.bank, Physical.src1744.bank, Physical.src1745.bank, Physical.src1747.bank, Physical.src1748.bank, Physical.src1746.bank] i
  reserve i := ![0, 1, 3, 6, 13, 32, 110, 145, 190, 245, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 26

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1738
    · exact Physical.rank1739
    · exact Physical.rank1740
    · exact Physical.rank1741
    · exact Physical.rank1742
    · exact Physical.rank1743
    · exact Physical.rank1744
    · exact Physical.rank1745
    · exact Physical.rank1747
    · exact Physical.rank1748
    · exact Physical.rank1746
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1738⟩
    · exact ⟨_, Physical.cover1739⟩
    · exact ⟨_, Physical.cover1740⟩
    · exact ⟨_, Physical.cover1741⟩
    · exact ⟨_, Physical.cover1742⟩
    · exact ⟨_, Physical.cover1743⟩
    · exact ⟨_, Physical.cover1744⟩
    · exact ⟨_, Physical.cover1745⟩
    · exact ⟨_, Physical.cover1747⟩
    · exact ⟨_, Physical.cover1748⟩
    · exact ⟨_, Physical.cover1746⟩

def price : EarlyPrice := ⟨7, 40, 10, 44083624858637/61566059282432, 19357/28172, ![22961875808064, 3511089970265, 23532332544, 3529859256], 4459253244284812⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases22
end Z6969Source1703


section Z6969Source1706
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.MarkedExitCandidates2
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,56⟩
  bank i := ![Physical.src1749.bank, Physical.src1750.bank, Physical.src1751.bank, Physical.src1752.bank, Physical.src1753.bank, Physical.src1754.bank, Physical.src1755.bank, Physical.src1756.bank, Physical.src1757.bank, Physical.src1759.bank, Physical.src1758.bank] i
  reserve i := ![0, 1, 2, 4, 8, 20, 50, 145, 190, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 41

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1749
    · exact Physical.rank1750
    · exact Physical.rank1751
    · exact Physical.rank1752
    · exact Physical.rank1753
    · exact Physical.rank1754
    · exact Physical.rank1755
    · exact Physical.rank1756
    · exact Physical.rank1757
    · exact Physical.rank1759
    · exact Physical.rank1758
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1749⟩
    · exact ⟨_, Physical.cover1750⟩
    · exact ⟨_, Physical.cover1751⟩
    · exact ⟨_, Physical.cover1752⟩
    · exact ⟨_, Physical.cover1753⟩
    · exact ⟨_, Physical.cover1754⟩
    · exact ⟨_, Physical.cover1755⟩
    · exact ⟨_, Physical.cover1756⟩
    · exact ⟨_, Physical.cover1757⟩
    · exact ⟨_, Physical.cover1759⟩
    · exact ⟨_, Physical.cover1758⟩

def price : EarlyPrice := ⟨7, 56, 10, 1360503545473632727635065/2070476470749970103795712, 75725/123822, ![20077306027064, 2244664952574, 39133396016, 4192875148], 3490991259973785⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.MarkedExitCandidates2
end Z6969Source1706


end Research6970.Height2313
