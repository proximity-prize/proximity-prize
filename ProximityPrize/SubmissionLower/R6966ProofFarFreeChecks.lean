import ProximityPrize.SubmissionLower.R6966ProofFarSourceArithmetic
import ProximityPrize.SubmissionLower.R6960RescueGeometryBills

set_option Elab.async false

-- merged module R6966ProofFarSourceData
section Merged_R6966ProofFarSourceData

namespace Research6966.FarSourceData
open FarSourceArithmetic (Request)
open Lower6960

def free (i : Fin 17) : Request :=
  ⟨FreeSource.bank i, FreeSource.reserve i, (FreeSource.bank i).shape.J+1, 0, 0⟩

def helper (test : HelperSource.HelperTest) : Request :=
  ⟨HelperSource.helperBank, 10, test.slope, test.excess, test.seed⟩

def rescue (rect : Fin 4) (i : Fin 17) : Request :=
  ⟨RescueSource.bank rect i, RescueSource.reserve i, 1, RescueSource.excess rect, RescueSource.seed rect⟩

end Research6966.FarSourceData

end Merged_R6966ProofFarSourceData

-- merged module R6966ProofFarFreeChecks
section Merged_R6966ProofFarFreeChecks

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem free0_first : value (free 0) 2500 = 7268145703125 := by decide +kernel
private theorem free0_next : value (free 0) 2501 = 7376408729595 := by decide +kernel
theorem free0 : Checked (free 0) := by
  refine ⟨(Lower6960.FreeSource.checked 0).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free0_first]; decide
  · rw [free0_first, free0_next]; decide

private theorem free1_first : value (free 1) 2500 = 10566169977600 := by decide +kernel
private theorem free1_next : value (free 1) 2501 = 10729975828800 := by decide +kernel
theorem free1 : Checked (free 1) := by
  refine ⟨(Lower6960.FreeSource.checked 1).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free1_first]; decide
  · rw [free1_first, free1_next]; decide

private theorem free2_first : value (free 2) 2500 = 16430271908080 := by decide +kernel
private theorem free2_next : value (free 2) 2501 = 16681769415560 := by decide +kernel
theorem free2 : Checked (free 2) := by
  refine ⟨(Lower6960.FreeSource.checked 2).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free2_first]; decide
  · rw [free2_first, free2_next]; decide

private theorem free3_first : value (free 3) 2500 = 21236405460230 := by decide +kernel
private theorem free3_next : value (free 3) 2501 = 21587164742080 := by decide +kernel
theorem free3 : Checked (free 3) := by
  refine ⟨(Lower6960.FreeSource.checked 3).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free3_first]; decide
  · rw [free3_first, free3_next]; decide

private theorem free4_first : value (free 4) 2500 = 31093336045930 := by decide +kernel
private theorem free4_next : value (free 4) 2501 = 31597351762194 := by decide +kernel
theorem free4 : Checked (free 4) := by
  refine ⟨(Lower6960.FreeSource.checked 4).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free4_first]; decide
  · rw [free4_first, free4_next]; decide

private theorem free5_first : value (free 5) 2500 = 40406879330580 := by decide +kernel
private theorem free5_next : value (free 5) 2501 = 41084929192104 := by decide +kernel
theorem free5 : Checked (free 5) := by
  refine ⟨(Lower6960.FreeSource.checked 5).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free5_first]; decide
  · rw [free5_first, free5_next]; decide

private theorem free6_first : value (free 6) 2500 = 66001518342930 := by decide +kernel
private theorem free6_next : value (free 6) 2501 = 67189260557724 := by decide +kernel
theorem free6 : Checked (free 6) := by
  refine ⟨(Lower6960.FreeSource.checked 6).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free6_first]; decide
  · rw [free6_first, free6_next]; decide

private theorem free7_first : value (free 7) 2500 = 133303487782080 := by decide +kernel
private theorem free7_next : value (free 7) 2501 = 135808055952723 := by decide +kernel
theorem free7 : Checked (free 7) := by
  refine ⟨(Lower6960.FreeSource.checked 7).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free7_first]; decide
  · rw [free7_first, free7_next]; decide

private theorem free8_first : value (free 8) 2500 = 442419842201400 := by decide +kernel
private theorem free8_next : value (free 8) 2501 = 451256785811832 := by decide +kernel
theorem free8 : Checked (free 8) := by
  refine ⟨(Lower6960.FreeSource.checked 8).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free8_first]; decide
  · rw [free8_first, free8_next]; decide

private theorem free9_first : value (free 9) 2500 = 131679140701032 := by decide +kernel
private theorem free9_next : value (free 9) 2501 = 134149143402486 := by decide +kernel
theorem free9 : Checked (free 9) := by
  refine ⟨(Lower6960.FreeSource.checked 9).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free9_first]; decide
  · rw [free9_first, free9_next]; decide

private theorem free10_first : value (free 10) 2500 = 808001622327240 := by decide +kernel
private theorem free10_next : value (free 10) 2501 = 824969118911212 := by decide +kernel
theorem free10 : Checked (free 10) := by
  refine ⟨(Lower6960.FreeSource.checked 10).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free10_first]; decide
  · rw [free10_first, free10_next]; decide

private theorem free11_first : value (free 11) 2500 = 3532829609178400 := by decide +kernel
private theorem free11_next : value (free 11) 2501 = 3616357064951636 := by decide +kernel
theorem free11 : Checked (free 11) := by
  refine ⟨(Lower6960.FreeSource.checked 11).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free11_first]; decide
  · rw [free11_first, free11_next]; decide

private theorem free12_first : value (free 12) 2500 = 3202757854075344 := by decide +kernel
private theorem free12_next : value (free 12) 2501 = 3276935010864703 := by decide +kernel
theorem free12 : Checked (free 12) := by
  refine ⟨(Lower6960.FreeSource.checked 12).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free12_first]; decide
  · rw [free12_first, free12_next]; decide

private theorem free13_first : value (free 13) 2500 = 11097452075067252 := by decide +kernel
private theorem free13_next : value (free 13) 2501 = 11375372834708342 := by decide +kernel
theorem free13 : Checked (free 13) := by
  refine ⟨(Lower6960.FreeSource.checked 13).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free13_first]; decide
  · rw [free13_first, free13_next]; decide

private theorem free14_first : value (free 14) 2500 = 83095799901290500 := by decide +kernel
private theorem free14_next : value (free 14) 2501 = 85381953778954055 := by decide +kernel
theorem free14 : Checked (free 14) := by
  refine ⟨(Lower6960.FreeSource.checked 14).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free14_first]; decide
  · rw [free14_first, free14_next]; decide

private theorem free15_first : value (free 15) 2500 = 98068442122375360 := by decide +kernel
private theorem free15_next : value (free 15) 2501 = 100756157138732840 := by decide +kernel
theorem free15 : Checked (free 15) := by
  refine ⟨(Lower6960.FreeSource.checked 15).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free15_first]; decide
  · rw [free15_first, free15_next]; decide

private theorem free16_first : value (free 16) 2500 = 357338824773737328 := by decide +kernel
private theorem free16_next : value (free 16) 2501 = 367663243703907264 := by decide +kernel
theorem free16 : Checked (free 16) := by
  refine ⟨(Lower6960.FreeSource.checked 16).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free16_first]; decide
  · rw [free16_first, free16_next]; decide

#print axioms free16
end Research6966.FarSourceData

end Merged_R6966ProofFarFreeChecks
