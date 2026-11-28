import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

-- merged module Z6969Pack0554
section Merged_Z6969Pack0554

-- Source: Research6969.Far6970ProfileArithmetic
section Z6969Source0575
set_option autoImplicit true
namespace Research6969.Far6970ProfileArithmetic
open Research6966.FarSourceArithmetic (Request fastPhase fastPhase_eq)
open Lower6960.HelperSource (WidthGuard gain surplus gain_eq_compressed)
abbrev agreement : ℕ := 179730
abbrev firstHeight : ℕ := 2558
abbrev heightCap : ℕ := 33755

def value (q:Request) (h:ℕ) : ℤ :=
  (fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 0-
    fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 1:ℕ) -
    (P1_7.debit h q.bank:ℤ)

theorem value_eq (q:Request) (h:ℕ) (pos:0<q.slope) (narrow:q.bank.shape.J<131071-h) :
    value q h=surplus q.bank agreement h q.reserve q.slope q.excess q.seed := by
  unfold value surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ pos,fastPhase_eq _ _ _ _ _ _ _ _ narrow,fastPhase_eq _ _ _ _ _ _ _ _ narrow]

structure Checked (q:Request) : Prop where
  rank : P3_7_1.BankOK q.bank
  width : WidthGuard q.bank agreement firstHeight q.reserve
  reserve_fit : 2*q.reserve≤q.bank.shape.B
  positive_slope : 0<q.slope
  narrow : q.bank.shape.J<131071-(firstHeight+1)
  positive : 0<value q firstHeight
  increases : value q firstHeight≤value q (firstHeight+1)

theorem Checked.gain_all {q:Request} (cert:Checked q) {h:ℕ} (lo:firstHeight≤h) (hi:h≤heightCap) :
    WidthGuard q.bank agreement h q.reserve ∧
    P1_7.debit h q.bank<gain q.bank.shape agreement h q.reserve q.slope q.excess q.seed := by
  have earlier:=cert.narrow.trans_le (Nat.sub_le_sub_left (Nat.le_succ firstHeight) _)
  have pos:=cert.positive
  have next:=cert.increases
  rw [value_eq _ _ cert.positive_slope earlier] at pos
  rw [value_eq _ _ cert.positive_slope earlier,value_eq _ _ cert.positive_slope cert.narrow] at next
  exact ⟨Lower6960.HelperSource.width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width,
         Lower6960.HelperSource.surplus_positive _ _ _ _ _ _ _ _ lo (hi.trans (by decide)) pos next⟩

theorem Checked.window {q:Request} (cert:Checked q) {h:ℕ} (lo:firstHeight≤h) (hi:h≤heightCap) :
    WidthGuard q.bank agreement h q.reserve := (cert.gain_all lo hi).1
theorem Checked.gain {q:Request} (cert:Checked q) {h:ℕ} (lo:firstHeight≤h) (hi:h≤heightCap) :
    P1_7.debit h q.bank<Lower6960.HelperSource.gain q.bank.shape agreement h q.reserve q.slope q.excess q.seed :=
  (cert.gain_all lo hi).2
end Research6969.Far6970ProfileArithmetic
end Z6969Source0575

-- Source: Research6969.Far6970Sources
section Z6969Source0576
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Research6969.Far6970Sources
open Far6970ProfileArithmetic (value Checked)
open Research6966.FarSourceData (free helper rescue)
open Lower6960



private theorem free0_first : value (free 0) 2558 = 7151364242010 := by decide +kernel
private theorem free0_next : value (free 0) 2559 = 7259627268480 := by decide +kernel
theorem free0 : Checked (free 0) := by
  refine ⟨(Lower6960.FreeSource.checked 0).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free0_first]; decide
  · rw [free0_first, free0_next]; decide

private theorem free1_first : value (free 1) 2558 = 10080891534000 := by decide +kernel
private theorem free1_next : value (free 1) 2559 = 10244697385200 := by decide +kernel
theorem free1 : Checked (free 1) := by
  refine ⟨(Lower6960.FreeSource.checked 1).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free1_first]; decide
  · rw [free1_first, free1_next]; decide

private theorem free2_first : value (free 2) 2558 = 15833949011600 := by decide +kernel
private theorem free2_next : value (free 2) 2559 = 16085446519080 := by decide +kernel
theorem free2 : Checked (free 2) := by
  refine ⟨(Lower6960.FreeSource.checked 2).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free2_first]; decide
  · rw [free2_first, free2_next]; decide

private theorem free3_first : value (free 3) 2558 = 19088273867290 := by decide +kernel
private theorem free3_next : value (free 3) 2559 = 19439033149140 := by decide +kernel
theorem free3 : Checked (free 3) := by
  refine ⟨(Lower6960.FreeSource.checked 3).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free3_first]; decide
  · rw [free3_first, free3_next]; decide

private theorem free4_first : value (free 4) 2558 = 28507382741472 := by decide +kernel
private theorem free4_next : value (free 4) 2559 = 29011398457736 := by decide +kernel
theorem free4 : Checked (free 4) := by
  refine ⟨(Lower6960.FreeSource.checked 4).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free4_first]; decide
  · rw [free4_first, free4_next]; decide

private theorem free5_first : value (free 5) 2558 = 35785232948892 := by decide +kernel
private theorem free5_next : value (free 5) 2559 = 36463282810416 := by decide +kernel
theorem free5 : Checked (free 5) := by
  refine ⟨(Lower6960.FreeSource.checked 5).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free5_first]; decide
  · rw [free5_first, free5_next]; decide

private theorem free6_first : value (free 6) 2558 = 53891996541102 := by decide +kernel
private theorem free6_next : value (free 6) 2559 = 55079738755896 := by decide +kernel
theorem free6 : Checked (free 6) := by
  refine ⟨(Lower6960.FreeSource.checked 6).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free6_first]; decide
  · rw [free6_first, free6_next]; decide

private theorem free7_first : value (free 7) 2558 = 103420601782344 := by decide +kernel
private theorem free7_next : value (free 7) 2559 = 105925169952987 := by decide +kernel
theorem free7 : Checked (free 7) := by
  refine ⟨(Lower6960.FreeSource.checked 7).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free7_first]; decide
  · rw [free7_first, free7_next]; decide

private theorem free8_first : value (free 8) 2558 = 315227853635016 := by decide +kernel
private theorem free8_next : value (free 8) 2559 = 324064797245448 := by decide +kernel
theorem free8 : Checked (free 8) := by
  refine ⟨(Lower6960.FreeSource.checked 8).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free8_first]; decide
  · rw [free8_first, free8_next]; decide

private theorem free9_first : value (free 9) 2558 = 102211467990516 := by decide +kernel
private theorem free9_next : value (free 9) 2559 = 104681470691970 := by decide +kernel
theorem free9 : Checked (free 9) := by
  refine ⟨(Lower6960.FreeSource.checked 9).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free9_first]; decide
  · rw [free9_first, free9_next]; decide

private theorem free10_first : value (free 10) 2558 = 530107733826616 := by decide +kernel
private theorem free10_next : value (free 10) 2559 = 547075230410588 := by decide +kernel
theorem free10 : Checked (free 10) := by
  refine ⟨(Lower6960.FreeSource.checked 10).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free10_first]; decide
  · rw [free10_first, free10_next]; decide

private theorem free11_first : value (free 11) 2558 = 1807621470344288 := by decide +kernel
private theorem free11_next : value (free 11) 2559 = 1891148926117524 := by decide +kernel
theorem free11 : Checked (free 11) := by
  refine ⟨(Lower6960.FreeSource.checked 11).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free11_first]; decide
  · rw [free11_first, free11_next]; decide

private theorem free12_first : value (free 12) 2558 = 1725163463766541 := by decide +kernel
private theorem free12_next : value (free 12) 2559 = 1799340620555900 := by decide +kernel
theorem free12 : Checked (free 12) := by
  refine ⟨(Lower6960.FreeSource.checked 12).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free12_first]; decide
  · rw [free12_first, free12_next]; decide

private theorem free13_first : value (free 13) 2558 = 4848138409279712 := by decide +kernel
private theorem free13_next : value (free 13) 2559 = 5126059168920802 := by decide +kernel
theorem free13 : Checked (free 13) := by
  refine ⟨(Lower6960.FreeSource.checked 13).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free13_first]; decide
  · rw [free13_first, free13_next]; decide

private theorem free14_first : value (free 14) 2558 = 25173163661240885 := by decide +kernel
private theorem free14_next : value (free 14) 2559 = 27459317538904440 := by decide +kernel
theorem free14 : Checked (free 14) := by
  refine ⟨(Lower6960.FreeSource.checked 14).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free14_first]; decide
  · rw [free14_first, free14_next]; decide

private theorem free15_first : value (free 15) 2558 = 30294287973510200 := by decide +kernel
private theorem free15_next : value (free 15) 2559 = 32982002989867680 := by decide +kernel
theorem free15 : Checked (free 15) := by
  refine ⟨(Lower6960.FreeSource.checked 15).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free15_first]; decide
  · rw [free15_first, free15_next]; decide

private theorem free16_first : value (free 16) 2558 = 81712083231003048 := by decide +kernel
private theorem free16_next : value (free 16) 2559 = 92036502161172984 := by decide +kernel
theorem free16 : Checked (free 16) := by
  refine ⟨(Lower6960.FreeSource.checked 16).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free16_first]; decide
  · rw [free16_first, free16_next]; decide



private theorem helper_twoSlopes_first : value (helper .twoSlopes) 2558 = 3635218438386960 := by decide +kernel
private theorem helper_twoSlopes_next : value (helper .twoSlopes) 2559 = 3769545359946690 := by decide +kernel
theorem helper_twoSlopes : Checked (helper .twoSlopes) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_twoSlopes_first]; decide
  · rw [helper_twoSlopes_first, helper_twoSlopes_next]; decide

private theorem helper_seedBoundary_first : value (helper .seedBoundary) 2558 = 4664794084236574 := by decide +kernel
private theorem helper_seedBoundary_next : value (helper .seedBoundary) 2559 = 4799518914495192 := by decide +kernel
theorem helper_seedBoundary : Checked (helper .seedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_seedBoundary_first]; decide
  · rw [helper_seedBoundary_first, helper_seedBoundary_next]; decide

private theorem helper_mixedBoundary_first : value (helper .mixedBoundary) 2558 = 4464150262565352 := by decide +kernel
private theorem helper_mixedBoundary_next : value (helper .mixedBoundary) 2559 = 4598801238786606 := by decide +kernel
theorem helper_mixedBoundary : Checked (helper .mixedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_mixedBoundary_first]; decide
  · rw [helper_mixedBoundary_first, helper_mixedBoundary_next]; decide

private theorem helper_jetBoundary_first : value (helper .jetBoundary) 2558 = 11062154576063436 := by decide +kernel
private theorem helper_jetBoundary_next : value (helper .jetBoundary) 2559 = 11199384912845088 := by decide +kernel
theorem helper_jetBoundary : Checked (helper .jetBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_jetBoundary_first]; decide
  · rw [helper_jetBoundary_first, helper_jetBoundary_next]; decide



private theorem rescue0_0_first : value (rescue 0 0) 2558 = 3295059944239048620 := by decide +kernel
private theorem rescue0_0_next : value (rescue 0 0) 2559 = 3582650864003778886 := by decide +kernel
theorem rescue0_0 : Checked (rescue 0 0) := by
  refine ⟨(Lower6960.RescueSource.checked 0 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_0_first]; decide
  · rw [rescue0_0_first, rescue0_0_next]; decide

private theorem rescue0_1_first : value (rescue 0 1) 2558 = 4692484528628170917 := by decide +kernel
private theorem rescue0_1_next : value (rescue 0 1) 2559 = 5122392251659011268 := by decide +kernel
theorem rescue0_1 : Checked (rescue 0 1) := by
  refine ⟨(Lower6960.RescueSource.checked 0 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_1_first]; decide
  · rw [rescue0_1_first, rescue0_1_next]; decide

private theorem rescue0_2_first : value (rescue 0 2) 2558 = 6819031795604523403 := by decide +kernel
private theorem rescue0_2_next : value (rescue 0 2) 2559 = 7427627538650003144 := by decide +kernel
theorem rescue0_2 : Checked (rescue 0 2) := by
  refine ⟨(Lower6960.RescueSource.checked 0 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_2_first]; decide
  · rw [rescue0_2_first, rescue0_2_next]; decide

private theorem rescue0_3_first : value (rescue 0 3) 2558 = 9986769873672557849 := by decide +kernel
private theorem rescue0_3_next : value (rescue 0 3) 2559 = 10904976048201012448 := by decide +kernel
theorem rescue0_3 : Checked (rescue 0 3) := by
  refine ⟨(Lower6960.RescueSource.checked 0 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_3_first]; decide
  · rw [rescue0_3_first, rescue0_3_next]; decide

private theorem rescue0_4_first : value (rescue 0 4) 2558 = 15921983194168527663 := by decide +kernel
private theorem rescue0_4_next : value (rescue 0 4) 2559 = 17294589022753069442 := by decide +kernel
theorem rescue0_4 : Checked (rescue 0 4) := by
  refine ⟨(Lower6960.RescueSource.checked 0 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_4_first]; decide
  · rw [rescue0_4_first, rescue0_4_next]; decide

private theorem rescue0_5_first : value (rescue 0 5) 2558 = 17476421844972291313 := by decide +kernel
private theorem rescue0_5_next : value (rescue 0 5) 2559 = 19296397996223835842 := by decide +kernel
theorem rescue0_5 : Checked (rescue 0 5) := by
  refine ⟨(Lower6960.RescueSource.checked 0 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_5_first]; decide
  · rw [rescue0_5_first, rescue0_5_next]; decide

private theorem rescue0_6_first : value (rescue 0 6) 2558 = 31627427366443332829 := by decide +kernel
private theorem rescue0_6_next : value (rescue 0 6) 2559 = 34915293445872034044 := by decide +kernel
theorem rescue0_6 : Checked (rescue 0 6) := by
  refine ⟨(Lower6960.RescueSource.checked 0 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_6_first]; decide
  · rw [rescue0_6_first, rescue0_6_next]; decide

private theorem rescue0_7_first : value (rescue 0 7) 2558 = 58099393897275141796 := by decide +kernel
private theorem rescue0_7_next : value (rescue 0 7) 2559 = 65616189266205385016 := by decide +kernel
theorem rescue0_7 : Checked (rescue 0 7) := by
  refine ⟨(Lower6960.RescueSource.checked 0 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_7_first]; decide
  · rw [rescue0_7_first, rescue0_7_next]; decide



private theorem rescue0_8_first : value (rescue 0 8) 2558 = 184398041507796454545 := by decide +kernel
private theorem rescue0_8_next : value (rescue 0 8) 2559 = 211223421220268595974 := by decide +kernel
theorem rescue0_8 : Checked (rescue 0 8) := by
  refine ⟨(Lower6960.RescueSource.checked 0 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_8_first]; decide
  · rw [rescue0_8_first, rescue0_8_next]; decide

private theorem rescue0_9_first : value (rescue 0 9) 2558 = 64471993526770102583 := by decide +kernel
private theorem rescue0_9_next : value (rescue 0 9) 2559 = 71804049722084513248 := by decide +kernel
theorem rescue0_9 : Checked (rescue 0 9) := by
  refine ⟨(Lower6960.RescueSource.checked 0 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_9_first]; decide
  · rw [rescue0_9_first, rescue0_9_next]; decide

private theorem rescue0_10_first : value (rescue 0 10) 2558 = 241856543595487405106 := by decide +kernel
private theorem rescue0_10_next : value (rescue 0 10) 2559 = 315264903057342987554 := by decide +kernel
theorem rescue0_10 : Checked (rescue 0 10) := by
  refine ⟨(Lower6960.RescueSource.checked 0 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_10_first]; decide
  · rw [rescue0_10_first, rescue0_10_next]; decide

private theorem rescue0_11_first : value (rescue 0 11) 2558 = 848487169092660272876 := by decide +kernel
private theorem rescue0_11_next : value (rescue 0 11) 2559 = 1231771668888702471836 := by decide +kernel
theorem rescue0_11 : Checked (rescue 0 11) := by
  refine ⟨(Lower6960.RescueSource.checked 0 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_11_first]; decide
  · rw [rescue0_11_first, rescue0_11_next]; decide

private theorem rescue0_12_first : value (rescue 0 12) 2558 = 1470811691724044969259 := by decide +kernel
private theorem rescue0_12_next : value (rescue 0 12) 2559 = 1722848498789219008749 := by decide +kernel
theorem rescue0_12 : Checked (rescue 0 12) := by
  refine ⟨(Lower6960.RescueSource.checked 0 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_12_first]; decide
  · rw [rescue0_12_first, rescue0_12_next]; decide

private theorem rescue0_13_first : value (rescue 0 13) 2558 = 4416524845416804857385 := by decide +kernel
private theorem rescue0_13_next : value (rescue 0 13) 2559 = 5413276584878357068029 := by decide +kernel
theorem rescue0_13 : Checked (rescue 0 13) := by
  refine ⟨(Lower6960.RescueSource.checked 0 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_13_first]; decide
  · rw [rescue0_13_first, rescue0_13_next]; decide

private theorem rescue0_14_first : value (rescue 0 14) 2558 = 31223976727403176395716 := by decide +kernel
private theorem rescue0_14_next : value (rescue 0 14) 2559 = 39710859281628247212508 := by decide +kernel
theorem rescue0_14 : Checked (rescue 0 14) := by
  refine ⟨(Lower6960.RescueSource.checked 0 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_14_first]; decide
  · rw [rescue0_14_first, rescue0_14_next]; decide

private theorem rescue0_15_first : value (rescue 0 15) 2558 = 36868549626138717046785 := by decide +kernel
private theorem rescue0_15_next : value (rescue 0 15) 2559 = 46871258881466535884433 := by decide +kernel
theorem rescue0_15 : Checked (rescue 0 15) := by
  refine ⟨(Lower6960.RescueSource.checked 0 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_15_first]; decide
  · rw [rescue0_15_first, rescue0_15_next]; decide



private theorem rescue0_16_first : value (rescue 0 16) 2558 = 130873267675626196434458 := by decide +kernel
private theorem rescue0_16_next : value (rescue 0 16) 2559 = 170526473745090853980726 := by decide +kernel
theorem rescue0_16 : Checked (rescue 0 16) := by
  refine ⟨(Lower6960.RescueSource.checked 0 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_16_first]; decide
  · rw [rescue0_16_first, rescue0_16_next]; decide

private theorem rescue1_0_first : value (rescue 1 0) 2558 = 2963638845484467172 := by decide +kernel
private theorem rescue1_0_next : value (rescue 1 0) 2559 = 3222220059053170273 := by decide +kernel
theorem rescue1_0 : Checked (rescue 1 0) := by
  refine ⟨(Lower6960.RescueSource.checked 1 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_0_first]; decide
  · rw [rescue1_0_first, rescue1_0_next]; decide

private theorem rescue1_1_first : value (rescue 1 1) 2558 = 4219648485013772094 := by decide +kernel
private theorem rescue1_1_next : value (rescue 1 1) 2559 = 4606134499895094775 := by decide +kernel
theorem rescue1_1 : Checked (rescue 1 1) := by
  refine ⟨(Lower6960.RescueSource.checked 1 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_1_first]; decide
  · rw [rescue1_1_first, rescue1_1_next]; decide

private theorem rescue1_2_first : value (rescue 1 2) 2558 = 6137058875156071252 := by decide +kernel
private theorem rescue1_2_next : value (rescue 1 2) 2559 = 6684751728391910796 := by decide +kernel
theorem rescue1_2 : Checked (rescue 1 2) := by
  refine ⟨(Lower6960.RescueSource.checked 1 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_2_first]; decide
  · rw [rescue1_2_first, rescue1_2_next]; decide

private theorem rescue1_3_first : value (rescue 1 3) 2558 = 8976123960973587103 := by decide +kernel
private theorem rescue1_3_next : value (rescue 1 3) 2559 = 9801269724588327447 := by decide +kernel
theorem rescue1_3 : Checked (rescue 1 3) := by
  refine ⟨(Lower6960.RescueSource.checked 1 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_3_first]; decide
  · rw [rescue1_3_first, rescue1_3_next]; decide

private theorem rescue1_4_first : value (rescue 1 4) 2558 = 14354336982871183971 := by decide +kernel
private theorem rescue1_4_next : value (rescue 1 4) 2559 = 15591596049789223464 := by decide +kernel
theorem rescue1_4 : Checked (rescue 1 4) := by
  refine ⟨(Lower6960.RescueSource.checked 1 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_4_first]; decide
  · rw [rescue1_4_first, rescue1_4_next]; decide

private theorem rescue1_5_first : value (rescue 1 5) 2558 = 15737405711079255955 := by decide +kernel
private theorem rescue1_5_next : value (rescue 1 5) 2559 = 17376164520470100584 := by decide +kernel
theorem rescue1_5 : Checked (rescue 1 5) := by
  refine ⟨(Lower6960.RescueSource.checked 1 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_5_first]; decide
  · rw [rescue1_5_first, rescue1_5_next]; decide

private theorem rescue1_6_first : value (rescue 1 6) 2558 = 28520566565211130555 := by decide +kernel
private theorem rescue1_6_next : value (rescue 1 6) 2559 = 31484673709831157307 := by decide +kernel
theorem rescue1_6 : Checked (rescue 1 6) := by
  refine ⟨(Lower6960.RescueSource.checked 1 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_6_first]; decide
  · rw [rescue1_6_first, rescue1_6_next]; decide



private theorem rescue1_7_first : value (rescue 1 7) 2558 = 52313382604281707505 := by decide +kernel
private theorem rescue1_7_next : value (rescue 1 7) 2559 = 59081251344513563604 := by decide +kernel
theorem rescue1_7 : Checked (rescue 1 7) := by
  refine ⟨(Lower6960.RescueSource.checked 1 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_7_first]; decide
  · rw [rescue1_7_first, rescue1_7_next]; decide

private theorem rescue1_8_first : value (rescue 1 8) 2558 = 166004458361939678066 := by decide +kernel
private theorem rescue1_8_next : value (rescue 1 8) 2559 = 190152420096122258058 := by decide +kernel
theorem rescue1_8 : Checked (rescue 1 8) := by
  refine ⟨(Lower6960.RescueSource.checked 1 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_8_first]; decide
  · rw [rescue1_8_first, rescue1_8_next]; decide

private theorem rescue1_9_first : value (rescue 1 9) 2558 = 58144167531554552693 := by decide +kernel
private theorem rescue1_9_next : value (rescue 1 9) 2559 = 64754965791429119841 := by decide +kernel
theorem rescue1_9 : Checked (rescue 1 9) := by
  refine ⟨(Lower6960.RescueSource.checked 1 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_9_first]; decide
  · rw [rescue1_9_first, rescue1_9_next]; decide

private theorem rescue1_10_first : value (rescue 1 10) 2558 = 215859924691018661559 := by decide +kernel
private theorem rescue1_10_next : value (rescue 1 10) 2559 = 281365554944426842304 := by decide +kernel
theorem rescue1_10 : Checked (rescue 1 10) := by
  refine ⟨(Lower6960.RescueSource.checked 1 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_10_first]; decide
  · rw [rescue1_10_first, rescue1_10_next]; decide

private theorem rescue1_11_first : value (rescue 1 11) 2558 = 757509646223449665534 := by decide +kernel
private theorem rescue1_11_next : value (rescue 1 11) 2559 = 1099598499861469081929 := by decide +kernel
theorem rescue1_11 : Checked (rescue 1 11) := by
  refine ⟨(Lower6960.RescueSource.checked 1 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_11_first]; decide
  · rw [rescue1_11_first, rescue1_11_next]; decide

private theorem rescue1_12_first : value (rescue 1 12) 2558 = 1326814889306817553328 := by decide +kernel
private theorem rescue1_12_next : value (rescue 1 12) 2559 = 1554083552148093742965 := by decide +kernel
theorem rescue1_12 : Checked (rescue 1 12) := by
  refine ⟨(Lower6960.RescueSource.checked 1 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_12_first]; decide
  · rw [rescue1_12_first, rescue1_12_next]; decide

private theorem rescue1_13_first : value (rescue 1 13) 2558 = 3977501850038839784150 := by decide +kernel
private theorem rescue1_13_next : value (rescue 1 13) 2559 = 4875055120645303003933 := by decide +kernel
theorem rescue1_13 : Checked (rescue 1 13) := by
  refine ⟨(Lower6960.RescueSource.checked 1 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_13_first]; decide
  · rw [rescue1_13_first, rescue1_13_next]; decide

private theorem rescue1_14_first : value (rescue 1 14) 2558 = 28120674693828811474851 := by decide +kernel
private theorem rescue1_14_next : value (rescue 1 14) 2559 = 35763024368859202417204 := by decide +kernel
theorem rescue1_14 : Checked (rescue 1 14) := by
  refine ⟨(Lower6960.RescueSource.checked 1 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_14_first]; decide
  · rw [rescue1_14_first, rescue1_14_next]; decide



private theorem rescue1_15_first : value (rescue 1 15) 2558 = 33203722373407493098416 := by decide +kernel
private theorem rescue1_15_next : value (rescue 1 15) 2559 = 42211066447711548500551 := by decide +kernel
theorem rescue1_15 : Checked (rescue 1 15) := by
  refine ⟨(Lower6960.RescueSource.checked 1 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_15_first]; decide
  · rw [rescue1_15_first, rescue1_15_next]; decide

private theorem rescue1_16_first : value (rescue 1 16) 2558 = 117866323533143514719330 := by decide +kernel
private theorem rescue1_16_next : value (rescue 1 16) 2559 = 153573575236720113704229 := by decide +kernel
theorem rescue1_16 : Checked (rescue 1 16) := by
  refine ⟨(Lower6960.RescueSource.checked 1 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_16_first]; decide
  · rw [rescue1_16_first, rescue1_16_next]; decide

private theorem rescue2_0_first : value (rescue 2 0) 2558 = 1581084047985823818 := by decide +kernel
private theorem rescue2_0_next : value (rescue 2 0) 2559 = 1718752325480809084 := by decide +kernel
theorem rescue2_0 : Checked (rescue 2 0) := by
  refine ⟨(Lower6960.RescueSource.checked 2 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_0_first]; decide
  · rw [rescue2_0_first, rescue2_0_next]; decide

private theorem rescue2_1_first : value (rescue 2 1) 2558 = 2248352856428782529 := by decide +kernel
private theorem rescue2_1_next : value (rescue 2 1) 2559 = 2453838914458836955 := by decide +kernel
theorem rescue2_1 : Checked (rescue 2 1) := by
  refine ⟨(Lower6960.RescueSource.checked 2 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_1_first]; decide
  · rw [rescue2_1_first, rescue2_1_next]; decide

private theorem rescue2_2_first : value (rescue 2 2) 2558 = 3284459529305383639 := by decide +kernel
private theorem rescue2_2_next : value (rescue 2 2) 2559 = 3577484377480376940 := by decide +kernel
theorem rescue2_2 : Checked (rescue 2 2) := by
  refine ⟨(Lower6960.RescueSource.checked 2 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_2_first]; decide
  · rw [rescue2_2_first, rescue2_2_next]; decide

private theorem rescue2_3_first : value (rescue 2 3) 2558 = 4755361444791161940 := by decide +kernel
private theorem rescue2_3_next : value (rescue 2 3) 2559 = 5191897095587347020 := by decide +kernel
theorem rescue2_3 : Checked (rescue 2 3) := by
  refine ⟨(Lower6960.RescueSource.checked 2 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_3_first]; decide
  · rw [rescue2_3_first, rescue2_3_next]; decide

private theorem rescue2_4_first : value (rescue 2 4) 2558 = 7764633437294240814 := by decide +kernel
private theorem rescue2_4_next : value (rescue 2 4) 2559 = 8433213186193437426 := by decide +kernel
theorem rescue2_4 : Checked (rescue 2 4) := by
  refine ⟨(Lower6960.RescueSource.checked 2 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_4_first]; decide
  · rw [rescue2_4_first, rescue2_4_next]; decide

private theorem rescue2_5_first : value (rescue 2 5) 2558 = 8459152811750925318 := by decide +kernel
private theorem rescue2_5_next : value (rescue 2 5) 2559 = 9339592170723273907 := by decide +kernel
theorem rescue2_5 : Checked (rescue 2 5) := by
  refine ⟨(Lower6960.RescueSource.checked 2 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_5_first]; decide
  · rw [rescue2_5_first, rescue2_5_next]; decide



private theorem rescue2_6_first : value (rescue 2 6) 2558 = 14545143643550145705 := by decide +kernel
private theorem rescue2_6_next : value (rescue 2 6) 2559 = 16150286398396787378 := by decide +kernel
theorem rescue2_6 : Checked (rescue 2 6) := by
  refine ⟨(Lower6960.RescueSource.checked 2 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_6_first]; decide
  · rw [rescue2_6_first, rescue2_6_next]; decide

private theorem rescue2_7_first : value (rescue 2 7) 2558 = 28116049774734449989 := by decide +kernel
private theorem rescue2_7_next : value (rescue 2 7) 2559 = 31751289584784700621 := by decide +kernel
theorem rescue2_7 : Checked (rescue 2 7) := by
  refine ⟨(Lower6960.RescueSource.checked 2 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_7_first]; decide
  · rw [rescue2_7_first, rescue2_7_next]; decide

private theorem rescue2_8_first : value (rescue 2 8) 2558 = 88961660499465465623 := by decide +kernel
private theorem rescue2_8_next : value (rescue 2 8) 2559 = 101896484433133273572 := by decide +kernel
theorem rescue2_8 : Checked (rescue 2 8) := by
  refine ⟨(Lower6960.RescueSource.checked 2 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_8_first]; decide
  · rw [rescue2_8_first, rescue2_8_next]; decide

private theorem rescue2_9_first : value (rescue 2 9) 2558 = 31561786305895233446 := by decide +kernel
private theorem rescue2_9_next : value (rescue 2 9) 2559 = 35143887652822976787 := by decide +kernel
theorem rescue2_9 : Checked (rescue 2 9) := by
  refine ⟨(Lower6960.RescueSource.checked 2 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_9_first]; decide
  · rw [rescue2_9_first, rescue2_9_next]; decide

private theorem rescue2_10_first : value (rescue 2 10) 2558 = 108774085789394721283 := by decide +kernel
private theorem rescue2_10_next : value (rescue 2 10) 2559 = 141737477493257987298 := by decide +kernel
theorem rescue2_10 : Checked (rescue 2 10) := by
  refine ⟨(Lower6960.RescueSource.checked 2 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_10_first]; decide
  · rw [rescue2_10_first, rescue2_10_next]; decide

private theorem rescue2_11_first : value (rescue 2 11) 2558 = 382578414765916072204 := by decide +kernel
private theorem rescue2_11_next : value (rescue 2 11) 2559 = 555012258125699384836 := by decide +kernel
theorem rescue2_11 : Checked (rescue 2 11) := by
  refine ⟨(Lower6960.RescueSource.checked 2 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_11_first]; decide
  · rw [rescue2_11_first, rescue2_11_next]; decide

private theorem rescue2_12_first : value (rescue 2 12) 2558 = 645401814656588800731 := by decide +kernel
private theorem rescue2_12_next : value (rescue 2 12) 2559 = 768613507570758488774 := by decide +kernel
theorem rescue2_12 : Checked (rescue 2 12) := by
  refine ⟨(Lower6960.RescueSource.checked 2 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_12_first]; decide
  · rw [rescue2_12_first, rescue2_12_next]; decide

private theorem rescue2_13_first : value (rescue 2 13) 2558 = 2139178986782225409325 := by decide +kernel
private theorem rescue2_13_next : value (rescue 2 13) 2559 = 2621499274980537495099 := by decide +kernel
theorem rescue2_13 : Checked (rescue 2 13) := by
  refine ⟨(Lower6960.RescueSource.checked 2 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_13_first]; decide
  · rw [rescue2_13_first, rescue2_13_next]; decide



private theorem rescue2_14_first : value (rescue 2 14) 2558 = 15128967837626944770411 := by decide +kernel
private theorem rescue2_14_next : value (rescue 2 14) 2559 = 19236602729633055727690 := by decide +kernel
theorem rescue2_14 : Checked (rescue 2 14) := by
  refine ⟨(Lower6960.RescueSource.checked 2 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_14_first]; decide
  · rw [rescue2_14_first, rescue2_14_next]; decide

private theorem rescue2_15_first : value (rescue 2 15) 2558 = 17853298667077555377281 := by decide +kernel
private theorem rescue2_15_next : value (rescue 2 15) 2559 = 22692378701912488744604 := by decide +kernel
theorem rescue2_15 : Checked (rescue 2 15) := by
  refine ⟨(Lower6960.RescueSource.checked 2 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_15_first]; decide
  · rw [rescue2_15_first, rescue2_15_next]; decide

private theorem rescue2_16_first : value (rescue 2 16) 2558 = 63421397675301897973460 := by decide +kernel
private theorem rescue2_16_next : value (rescue 2 16) 2559 = 82614966073727706189234 := by decide +kernel
theorem rescue2_16 : Checked (rescue 2 16) := by
  refine ⟨(Lower6960.RescueSource.checked 2 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_16_first]; decide
  · rw [rescue2_16_first, rescue2_16_next]; decide

private theorem rescue3_0_first : value (rescue 3 0) 2558 = 231117123793746664 := by decide +kernel
private theorem rescue3_0_next : value (rescue 3 0) 2559 = 245767282156921856 := by decide +kernel
theorem rescue3_0 : Checked (rescue 3 0) := by
  refine ⟨(Lower6960.RescueSource.checked 3 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_0_first]; decide
  · rw [rescue3_0_first, rescue3_0_next]; decide

private theorem rescue3_1_first : value (rescue 3 1) 2558 = 330564520749253912 := by decide +kernel
private theorem rescue3_1_next : value (rescue 3 1) 2559 = 352723379676272924 := by decide +kernel
theorem rescue3_1 : Checked (rescue 3 1) := by
  refine ⟨(Lower6960.RescueSource.checked 3 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_1_first]; decide
  · rw [rescue3_1_first, rescue3_1_next]; decide

private theorem rescue3_2_first : value (rescue 3 2) 2558 = 460822893061145468 := by decide +kernel
private theorem rescue3_2_next : value (rescue 3 2) 2559 = 493346414742533247 := by decide +kernel
theorem rescue3_2 : Checked (rescue 3 2) := by
  refine ⟨(Lower6960.RescueSource.checked 3 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_2_first]; decide
  · rw [rescue3_2_first, rescue3_2_next]; decide

private theorem rescue3_3_first : value (rescue 3 3) 2558 = 628271733164761589 := by decide +kernel
private theorem rescue3_3_next : value (rescue 3 3) 2559 = 674778512580337941 := by decide +kernel
theorem rescue3_3 : Checked (rescue 3 3) := by
  refine ⟨(Lower6960.RescueSource.checked 3 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_3_first]; decide
  · rw [rescue3_3_first, rescue3_3_next]; decide

private theorem rescue3_4_first : value (rescue 3 4) 2558 = 845102587229854616 := by decide +kernel
private theorem rescue3_4_next : value (rescue 3 4) 2559 = 941256298873371468 := by decide +kernel
theorem rescue3_4 : Checked (rescue 3 4) := by
  refine ⟨(Lower6960.RescueSource.checked 3 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_4_first]; decide
  · rw [rescue3_4_first, rescue3_4_next]; decide



private theorem rescue3_5_first : value (rescue 3 5) 2558 = 1522887591637551073 := by decide +kernel
private theorem rescue3_5_next : value (rescue 3 5) 2559 = 1734416027693665536 := by decide +kernel
theorem rescue3_5 : Checked (rescue 3 5) := by
  refine ⟨(Lower6960.RescueSource.checked 3 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_5_first]; decide
  · rw [rescue3_5_first, rescue3_5_next]; decide

private theorem rescue3_6_first : value (rescue 3 6) 2558 = 2098115071251066308 := by decide +kernel
private theorem rescue3_6_next : value (rescue 3 6) 2559 = 2416390906162606464 := by decide +kernel
theorem rescue3_6 : Checked (rescue 3 6) := by
  refine ⟨(Lower6960.RescueSource.checked 3 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_6_first]; decide
  · rw [rescue3_6_first, rescue3_6_next]; decide

private theorem rescue3_7_first : value (rescue 3 7) 2558 = 4806782935631794435 := by decide +kernel
private theorem rescue3_7_next : value (rescue 3 7) 2559 = 5709184254285410385 := by decide +kernel
theorem rescue3_7 : Checked (rescue 3 7) := by
  refine ⟨(Lower6960.RescueSource.checked 3 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_7_first]; decide
  · rw [rescue3_7_first, rescue3_7_next]; decide

private theorem rescue3_8_first : value (rescue 3 8) 2558 = 10367495929805643053 := by decide +kernel
private theorem rescue3_8_next : value (rescue 3 8) 2559 = 12684705437047549314 := by decide +kernel
theorem rescue3_8 : Checked (rescue 3 8) := by
  refine ⟨(Lower6960.RescueSource.checked 3 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_8_first]; decide
  · rw [rescue3_8_first, rescue3_8_next]; decide

private theorem rescue3_9_first : value (rescue 3 9) 2558 = 3799491651473018522 := by decide +kernel
private theorem rescue3_9_next : value (rescue 3 9) 2559 = 4464371711285747256 := by decide +kernel
theorem rescue3_9 : Checked (rescue 3 9) := by
  refine ⟨(Lower6960.RescueSource.checked 3 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_9_first]; decide
  · rw [rescue3_9_first, rescue3_9_next]; decide

private theorem rescue3_10_first : value (rescue 3 10) 2558 = 29241485754274717666 := by decide +kernel
private theorem rescue3_10_next : value (rescue 3 10) 2559 = 32698973256459793518 := by decide +kernel
theorem rescue3_10 : Checked (rescue 3 10) := by
  refine ⟨(Lower6960.RescueSource.checked 3 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_10_first]; decide
  · rw [rescue3_10_first, rescue3_10_next]; decide

private theorem rescue3_11_first : value (rescue 3 11) 2558 = 139529696227090607352 := by decide +kernel
private theorem rescue3_11_next : value (rescue 3 11) 2559 = 158758304558952513636 := by decide +kernel
theorem rescue3_11 : Checked (rescue 3 11) := by
  refine ⟨(Lower6960.RescueSource.checked 3 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_11_first]; decide
  · rw [rescue3_11_first, rescue3_11_next]; decide

private theorem rescue3_12_first : value (rescue 3 12) 2558 = 59888774590987925752 := by decide +kernel
private theorem rescue3_12_next : value (rescue 3 12) 2559 = 82300507594802270196 := by decide +kernel
theorem rescue3_12 : Checked (rescue 3 12) := by
  refine ⟨(Lower6960.RescueSource.checked 3 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_12_first]; decide
  · rw [rescue3_12_first, rescue3_12_next]; decide



private theorem rescue3_13_first : value (rescue 3 13) 2558 = 204594698647833924293 := by decide +kernel
private theorem rescue3_13_next : value (rescue 3 13) 2559 = 314299481849217711359 := by decide +kernel
theorem rescue3_13 : Checked (rescue 3 13) := by
  refine ⟨(Lower6960.RescueSource.checked 3 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_13_first]; decide
  · rw [rescue3_13_first, rescue3_13_next]; decide

private theorem rescue3_14_first : value (rescue 3 14) 2558 = 1026925967187471239832 := by decide +kernel
private theorem rescue3_14_next : value (rescue 3 14) 2559 = 1983013669170773357076 := by decide +kernel
theorem rescue3_14 : Checked (rescue 3 14) := by
  refine ⟨(Lower6960.RescueSource.checked 3 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_14_first]; decide
  · rw [rescue3_14_first, rescue3_14_next]; decide

private theorem rescue3_15_first : value (rescue 3 15) 2558 = 1076309171024379434832 := by decide +kernel
private theorem rescue3_15_next : value (rescue 3 15) 2559 = 2083845837594211799832 := by decide +kernel
theorem rescue3_15 : Checked (rescue 3 15) := by
  refine ⟨(Lower6960.RescueSource.checked 3 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_15_first]; decide
  · rw [rescue3_15_first, rescue3_15_next]; decide

private theorem rescue3_16_first : value (rescue 3 16) 2558 = 3081982895656107703790 := by decide +kernel
private theorem rescue3_16_next : value (rescue 3 16) 2559 = 7632821896443632717670 := by decide +kernel
theorem rescue3_16 : Checked (rescue 3 16) := by
  refine ⟨(Lower6960.RescueSource.checked 3 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_16_first]; decide
  · rw [rescue3_16_first, rescue3_16_next]; decide



theorem free_checked (i : Fin 17) : Checked (free i) := by
  fin_cases i
  · exact free0
  · exact free1
  · exact free2
  · exact free3
  · exact free4
  · exact free5
  · exact free6
  · exact free7
  · exact free8
  · exact free9
  · exact free10
  · exact free11
  · exact free12
  · exact free13
  · exact free14
  · exact free15
  · exact free16

theorem helper_checked (test : HelperSource.HelperTest) : Checked (helper test) := by
  cases test
  · exact helper_twoSlopes
  · exact helper_seedBoundary
  · exact helper_mixedBoundary
  · exact helper_jetBoundary

theorem rescue_checked (rect : Fin 4) (i : Fin 17) : Checked (rescue rect i) := by
  fin_cases rect <;> fin_cases i
  · exact rescue0_0
  · exact rescue0_1
  · exact rescue0_2
  · exact rescue0_3
  · exact rescue0_4
  · exact rescue0_5
  · exact rescue0_6
  · exact rescue0_7
  · exact rescue0_8
  · exact rescue0_9
  · exact rescue0_10
  · exact rescue0_11
  · exact rescue0_12
  · exact rescue0_13
  · exact rescue0_14
  · exact rescue0_15
  · exact rescue0_16
  · exact rescue1_0
  · exact rescue1_1
  · exact rescue1_2
  · exact rescue1_3
  · exact rescue1_4
  · exact rescue1_5
  · exact rescue1_6
  · exact rescue1_7
  · exact rescue1_8
  · exact rescue1_9
  · exact rescue1_10
  · exact rescue1_11
  · exact rescue1_12
  · exact rescue1_13
  · exact rescue1_14
  · exact rescue1_15
  · exact rescue1_16
  · exact rescue2_0
  · exact rescue2_1
  · exact rescue2_2
  · exact rescue2_3
  · exact rescue2_4
  · exact rescue2_5
  · exact rescue2_6
  · exact rescue2_7
  · exact rescue2_8
  · exact rescue2_9
  · exact rescue2_10
  · exact rescue2_11
  · exact rescue2_12
  · exact rescue2_13
  · exact rescue2_14
  · exact rescue2_15
  · exact rescue2_16
  · exact rescue3_0
  · exact rescue3_1
  · exact rescue3_2
  · exact rescue3_3
  · exact rescue3_4
  · exact rescue3_5
  · exact rescue3_6
  · exact rescue3_7
  · exact rescue3_8
  · exact rescue3_9
  · exact rescue3_10
  · exact rescue3_11
  · exact rescue3_12
  · exact rescue3_13
  · exact rescue3_14
  · exact rescue3_15
  · exact rescue3_16

end Research6969.Far6970Sources
end Z6969Source0576

-- Source: Research6969.FarSourceRows
section Z6969Source0577
set_option autoImplicit true
set_option Elab.async false

namespace Lower6960.Far6970FreeSource
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (debit)
open HelperSource (WidthGuard cutoffCount)
open Research6966.FarSourceData (free)
open Research6969.Far6970Sources (free_checked)
open Research6969.Far6970ProfileArithmetic (agreement)

abbrev bank := FreeSource.bank
abbrev reserve := FreeSource.reserve
def cutoff (h : ℕ) (i : Fin 17) : ℕ := cutoffCount (bank i).shape agreement h (reserve i)-1

theorem shape_guards (i : Fin 17) :
    0<(bank i).shape.J ∧ (bank i).shape.J≤(bank i).shape.B ∧
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*agreement<K1.p := by
  fin_cases i <;> decide +kernel

theorem cutoff_fit {h : ℕ} (lo : 2558≤h) (hi : h≤33755) (i : Fin 17) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*agreement :=
  FreeSource.buffered_fit _ _ _ _ ((free_checked i).window lo hi)

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) (i : Fin 17) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have cert := free_checked i
  have positive := cert.gain lo hi
  change debit h (bank i)<HelperSource.gain (bank i).shape agreement h (reserve i)
    ((bank i).shape.J+1) 0 0 at positive
  rw [FreeSource.gain_eq_raw _ _ _ _ (by omega)] at positive
  exact FreeSource.nonzero_row Crt word (bank i) agreement (reserve i) (by omega) (by omega)
    cert.rank (cert.window lo hi) positive

end Lower6960.Far6970FreeSource

namespace Lower6960.Far6970HelperSource
open Polynomial
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open HelperSource (HelperTest cutoffCount WidthGuard)
open Research6969.Far6970Sources (helper_checked)
open Research6969.Far6970ProfileArithmetic (agreement)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev helperBank := HelperSource.helperBank
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape agreement h 10-1

theorem helper_width {h : ℕ} (lo : 2558≤h) (hi : h≤33755) : WidthGuard helperBank agreement h 10 :=
  (helper_checked .twoSlopes).window lo hi

theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬G∣Q := by
  have cert := helper_checked test
  exact HelperSource.crt_avoiding_row Crt word helperBank agreement 10 test.slope test.excess test.seed
    (by omega) (by omega) cert.positive_slope cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2
    (by decide) (cert.window lo hi) (cert.gain lo hi) irr seeded slope seed excess

theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have cert := helper_checked .twoSlopes
  have sup := HelperSource.crt_supply Crt word helperBank agreement 10 2 0 1 (by omega) (by omega)
    (by decide) cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2 (cert.window lo hi) (cert.gain lo hi)
  exact HelperSource.nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)

private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega

theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤85 ∧ (2≤jetDegree G → seedDegree G≤78) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperSource.HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 86≤seedDegree G; omega)
      (by simpa [HelperSource.HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 79≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)

theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have cert := helper_checked .twoSlopes
  have supply := HelperSource.crt_supply Crt word helperBank agreement 10 2 0 1 (by omega) (by omega) (by decide)
    cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2 (cert.window lo hi) (cert.gain lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape agreement h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH

end Lower6960.Far6970HelperSource

namespace Lower6960.Far6970RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (cutoffCount)
open Research6969.Far6970Sources (rescue_checked)
open Research6969.Far6970ProfileArithmetic (agreement)

abbrev bank := RescueSource.bank
abbrev reserve := RescueSource.reserve
abbrev excess := RescueSource.excess
abbrev seed := RescueSource.seed
abbrev jetCap := RescueSource.jetCap
abbrev seedCap := RescueSource.seedCap
def cutoff (h : ℕ) (rect : Fin 4) (i : Fin 17) : ℕ := cutoffCount (bank rect i).shape agreement h (reserve i)-1

theorem shape_guards (rect : Fin 4) (i : Fin 17) :
    0<(bank rect i).shape.J ∧ (bank rect i).shape.J≤(bank rect i).shape.B ∧
      (bank rect i).shape.B<K1.p ∧ (bank rect i).shape.U<K1.p ∧ (bank rect i).shape.m*agreement<K1.p := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem cutoff_fit {h : ℕ} (lo : 2558≤h) (hi : h≤33755) (rect : Fin 4) (i : Fin 17) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*agreement :=
  FreeSource.buffered_fit _ _ _ _ ((rescue_checked rect i).window lo hi)

theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) (rect : Fin 4) (i : Fin 17) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬G∣Q := by
  have cert := rescue_checked rect i
  exact HelperSource.crt_avoiding_row Crt word (bank rect i) agreement (reserve i) 1 (excess rect) (seed rect)
    (by omega) (by omega) (by decide) cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2
    (shape_guards rect i).2.2.2.1 (cert.window lo hi) (cert.gain lo hi) irr seeded slope hs hj

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤85) (mixed : 2≤j → u≤78) :
    ∃ rect : Fin 4, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect := by
  by_cases hJ : 2≤j
  · refine ⟨3,?_⟩
    change 2≤j ∧ j≤7 ∧ 1≤u ∧ u≤78
    exact ⟨hJ,hiJ,loU,mixed hJ⟩
  · by_cases hU : u≤1
    · refine ⟨0,?_⟩
      change 1≤j ∧ j≤1 ∧ 1≤u ∧ u≤1
      omega
    · by_cases hU' : u≤6
      · refine ⟨1,?_⟩
        change 1≤j ∧ j≤1 ∧ 2≤u ∧ u≤6
        omega
      · refine ⟨2,?_⟩
        change 1≤j ∧ j≤1 ∧ 7≤u ∧ u≤85
        omega

theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2558≤h) (hi : h≤33755) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word Far6970HelperSource.helperBank.shape (Far6970HelperSource.helperCutoff h), G∣P) :
    ∃ rect : Fin 4, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      ∀ i : Fin 17, ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := Far6970HelperSource.helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,fun i => ?_⟩
  exact rescue_row Crt word lo hi rect i irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

end Lower6960.Far6970RescueSource
end Z6969Source0577

-- Source: Research6969.FarRescueGeometry
section Z6969Source0578
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960RescueGeometry
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Far6970RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (FiniteSections residualBudget ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open Far6970RescueSource (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)
abbrev Model (u : P1.Words) (deleted : Finset I) := P1.ModelAt 33755 u deleted
abbrev Family {u deleted} (M : Model u deleted) (Γ : Finset K) := P1.FamilyAt 179730 M Γ
def word {u deleted} (M : Model u deleted) : I→L := fun i => algebraMap K L (M.word i)
def OnMark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (A : Ideal Ambient) (γ : K) : Prop := OnJet A (M.label γ) (F.scalar γ)
theorem label_injective {u deleted} (M : Model u deleted) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def primeShape (rect : Fin 4) : Shape := ⟨0,jetCap rect,1,seedCap rect⟩
def initialCap (rect : Fin 4) : Fin 4 → ℕ := pairCap (primeShape rect) (bank rect 0).shape
theorem prime_shape_fit (rect : Fin 4) : (primeShape rect).J≤(primeShape rect).B := by
  fin_cases rect <;> decide
theorem initial_small (rect : Fin 4) (k : Fin 4) : initialCap rect k<K1.p := by
  fin_cases rect <;> fin_cases k <;> decide +kernel
theorem reserve_small (i : Fin 17) : reserve i<K1.p := by
  fin_cases i <;> decide +kernel
theorem contact_at_mark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {s : Shape} {W r : ℕ} {P : Jet} (inside : P∈evaluated Crt (word M) s W)
    (width : W+2*M.overhead.toNat*r<s.m*179730)
    (γ : K) (hγ : γ∈Γ) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (r+1) P := by
  let B := F.mark γ hγ
  have degree : (liftPoly (F.scalar γ)).natDegree≤131071+M.overhead.toNat := by
    rw [liftPoly, Polynomial.natDegree_map]
    rcases B.scalar_degree with hzero | hd
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at hd
      omega
  refine PrefixRows.contact_of_crt Crt (word M) s P inside width noPole
    (M.label γ) (F.scalar γ) (residues γ hγ) degree B.bad.support B.bad.agreement ?_
  intro i hit
  rw [word,liftPoly,nodeL,Polynomial.eval_map,Polynomial.eval₂_hom]
  exact congrArg (algebraMap K L) (B.scalar_hits i hit)
theorem zero_of_contact {z : K} {S : (Polynomial K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r+1) P) : jetAt P z S=0 := by
  have test := contact [] (by simp)
  change toJet P∈RingHom.ker (jetMarkHom z S) at test
  rwa [RingHom.mem_ker,K1_14_2.eval_toJet] at test
private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 4) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ
private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (initialCap rect))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))
theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (bank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (Far6970RescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))
end Lower6960.Far6970RescueGeometry

end
end Merged_R6960RescueGeometry

section Merged_R6960RescueGeometryHistory
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Far6970RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open Far6970RescueSource (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {rect : Fin 4} (irr : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (Q : Fin 17→Jet) (init : Initial F G (Q 0) rect) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (bank rect i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (reserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (Q i)) ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
        (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c) ∧
      ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) (prime_shape_fit rect)
      (Far6970RescueSource.shape_guards rect i).2.1 init.parents on (reserve i) (reserve_small i)
  let selected (i : Fin 17) := if i = 0 then init.parents else S i
  have first : selected 0=init.parents := by simp [selected]
  have rzero : reserve 0=0 := by decide
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (reserve 0+1) (Q 0) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin 17) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (reserve i+1) (Q i) := by
    by_cases zi : i = 0
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin 17) (c : Fin 4) :
      (reserve i+1)*mass (selected i) c≤pairCap (primeShape rect) (bank rect i).shape c := by
    by_cases zi : i = 0
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin 17,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin 17,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = 0 := Fin.ext (by omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ 0 := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩
structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) where
  rect : Fin 4
  row : Fin 17→Jet
  row_mem : ∀ i,row i∈evaluated Crt (word M) (bank rect i).shape (cutoff M.overhead.toNat rect i)
  avoids : ∀ i,¬G∣row i
  initial : Initial F G (row 0) rect
  kept : ℕ→Finset (Ideal Ambient)
  start : kept 0=initial.parents
  intro_pass : kept 1=initial.parents
  antitone : Antitone kept
  passed : ∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (row i)
  cap : ∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
    (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c
  cut : ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
    ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0
theorem prepare {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2558≤M.overhead.toNat) (hi : M.overhead.toNat≤33755)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (evaluated Crt (word M) Far6970HelperSource.helperBank.shape (Far6970HelperSource.helperCutoff M.overhead.toNat)) G) :
    Nonempty (Run F Crt G) := by
  obtain ⟨rect,linear,jCap,uCap,rows⟩ := Far6970RescueSource.exceptional_rows Crt (word M) lo hi
    common.1 common.2.2.1 common.2.1 common.2.2.2
  choose Q inside avoid using rows
  have capsG : RowCaps G (primeShape rect) :=
    (rowCaps_iff G _).mpr ⟨jCap,linear.le,uCap⟩
  have caps (i : Fin 17) : RowCaps (Q i) (bank rect i).shape :=
    evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin 17) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i) (Far6970RescueSource.cutoff_fit lo hi rect i) γ hγ
  obtain ⟨ini⟩ := initial_cover F common.1 (avoid 0) capsG (caps 0)
    (fun γ hγ=>zero_of_contact (contact 0 γ hγ))
  obtain ⟨kept,start,intro_pass,anti,passed,cap,cut⟩ :=
    history_from_initial common.1 capsG Q ini avoid caps contact
  exact ⟨⟨rect,Q,inside,avoid,ini,kept,start,intro_pass,anti,passed,cap,cut⟩⟩
theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)
end Lower6960.Far6970RescueGeometry

end
end Merged_R6960RescueGeometryHistory

section Merged_R6960RescueGeometryCuts
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Far6970RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt atX seedEmbedding)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom eval_toJet CoordinateRing)
open K1_14_2_2 (RowCaps Active dual mass sectionDegree CutCover weight dot emptyCut joinCuts
  joinCuts_cost sum_dot)
open K1_14_2_2_3 K1_14_2_2_7
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open Far6970RescueSource (bank reserve)
open scoped Classical
open HighCore82258_3 (envelope_caps)
open K1_14_2_2_7 (seed_value_eq)
def terminalShape : Shape := ⟨4500,6286,1329,748778⟩
def terminalCutoff : ℕ := terminalShape.m*179730-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179730-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179730-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def Run.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    Finset (Ideal Ambient) :=
  (R.kept 17).filter (TerminalPass Crt (word M))
def Run.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  if n<17 then R.kept (n+1) else R.final
def Run.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  R.live n \ R.live (n+1)
theorem Run.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) : R.live (i+1)⊆R.live i := by
  by_cases hn : i+1<17
  · simp only [Run.live,ite_eq_left hi,ite_eq_left hn]
    exact R.antitone (by omega)
  · have eq : i+1=17 := by omega
    rw [Run.live,Run.live,ite_eq_right hn,ite_eq_left hi,eq]
    exact filter_subset _ _
theorem Run.live_active {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.live i) : Active J := by
  rw [Run.live,ite_eq_left hi] at mem
  exact (R.parent_geom mem).1
theorem Run.live_start {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    R.live 0=R.initial.parents := by
  rw [Run.live,ite_eq_left (by decide : 0<17)]
  exact R.intro_pass
def rescueStage (rect : Fin 4) (i : Fin 17) : P1_7.Stage :=
  ⟨reserve i,⟨HelperPrefix.timesShape (reserve i+1) (primeShape rect),0,0⟩,bank rect i⟩
def cutShape (rect : Fin 4) (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (rescueStage rect ⟨i+1,hi⟩) else terminalShape
theorem cutShape_fit (rect : Fin 4) (i : ℕ) : (cutShape rect i).J≤(cutShape rect i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide
theorem Run.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.lost i) :
    ∃ C : Jet, RowCaps C (cutShape R.rect i) ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Run.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    rw [Run.live,ite_eq_left hn] at lost
    obtain ⟨C,cap,proper,zero⟩ := R.cut j J prev lost
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    apply envelope_caps (s:=rescueStage R.rect j)
    · exact Nat.mul_le_mul_left _ (prime_shape_fit R.rect)
    · exact (Far6970RescueSource.shape_guards R.rect j).2.1
    · exact Or.inr cap
  · have eq : i+1=17 := by omega
    rw [Run.live,ite_eq_right hn] at lost
    have hf : ¬ TerminalPass Crt (word M) J := fun pass =>
      lost (mem_filter.mpr ⟨eq ▸ prev,pass⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    rw [cutShape,dite_eq_right hn]
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ
    apply zero_of_contact (r:=0)
    exact contact_at_mark F Crt noPole residues inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179730)) (by decide : 0<1)) γ hγ
private theorem mark_on_cut {J : Ideal Ambient} {P : Jet} {z : K} {S : (Polynomial K)}
    (on : OnJet J z S) (zero : jetAt P z S=0) :
    ∃ Q∈cutComponents J P,OnJet Q z S := by
  let e := jetMarkHom z S
  have incl : J ⊔ Ideal.span {toJet P} ≤ RingHom.ker e :=
    sup_le on ((Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans zero)))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q,minimal,mark⟩ := Ideal.exists_minimalPrimes_le incl
  exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr minimal,mark⟩
theorem proper_cut {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (s : Shape) {J : Ideal Ambient} {P : Jet} (sl : s.J≤s.B) (act : Active J)
    (cap : RowCaps P s) (proper : toJet P∉J) (zero : ∀ γ∈Γ,jetAt P (M.label γ) (F.scalar γ)=0) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight s fee) (sectionDegree J)) ∧
      ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnMark F Q)
  let direct := (constantComponents J P).biUnion marked
  have card : direct.card≤(constantComponents J P).card := by
    have single (Q : Ideal Ambient) (mem : Q∈constantComponents J P) : (marked Q).card≤1 := by
      obtain ⟨comp,seed⟩ := mem_filter.mp mem
      let _ : Q.IsPrime := (cutComponent_curve act proper comp).1
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply label_injective M
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq seed (mem_filter.mp hγ).2).trans (seed_value_eq seed (mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈constantComponents J P,(marked Q).card := card_biUnion_le
      _ ≤ ∑ _∈constantComponents J P,1 := sum_le_sum single
      _ = _ := by simp
  let C : CutCover := ⟨direct,movingComponents J P,by
    intro Q hQ
    obtain ⟨comp,moving⟩ := mem_filter.mp hQ
    obtain ⟨prime,dim⟩ := cutComponent_curve act proper comp
    exact ⟨prime,dim,K1_14_2_2_7_1.proof Q prime dim moving⟩⟩
  refine ⟨C,?_,?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s J P sl act cap proper
    · exact P0_10R.Bridge.cut_ordinate_mass s J P sl act cap proper
    · exact card.trans (P0_10R.Bridge.cut_constant_count s J P sl act cap proper)
  · intro γ hγ on
    obtain ⟨Q,comp,mark⟩ := mark_on_cut on (zero γ hγ)
    by_cases c : ConstantSeed Q
    · exact Or.inl (mem_biUnion.mpr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mem_filter.mpr ⟨hγ,mark⟩⟩)
    · exact Or.inr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mark⟩
theorem Run.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := R.marked_cutter noPole residues hi mem
    exact proper_cut F _ (cutShape_fit _ _) (R.live_active hi (mem_sdiff.mp mem).1) cap proper zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark F Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩
theorem Run.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.final ∨ ∃ i<17,J∈R.lost i := by
  by_cases h : ∃ i<17,J∈R.lost i
  · exact Or.inr h
  · have live : ∀ n≤17,J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Run.live] using live 17 le_rfl)
def OnSurface {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (q : Surface) (γ : K) : Prop :=
  ∀ P∈q.asIdeal,jetAt P (M.label γ) (F.scalar γ)=0
def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179730-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
theorem Run.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈R.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  let getGeom (J : R.final) := R.parent_geom (mem_filter.mp J.property).1
  let surface (J : R.final) := surfaceOf J.val (getGeom J).1.prime
  let S := R.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : R.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Run.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=R.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩
end Lower6960.Far6970RescueGeometry

end
end Merged_R6960RescueGeometryCuts

section Merged_R6960RescueGeometryBills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Far6970RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open Far6970RescueSource (bank reserve)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical
def initialMass (rect : Fin 4) : Mass := fun k => initialCap rect k
def history (rect : Fin 4) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<17 then
      let i : Fin 17 := ⟨n+1,hn⟩
      min (history rect n k)
        ((pairCap (primeShape rect) (bank rect i).shape k : ℚ)/(reserve i+1))
    else history rect n k
theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by
    simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))
theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<17) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 17 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (bank R.rect j).shape k : ℚ) / (reserve j+1)
    have pos : (0 : ℚ)<reserve j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound
    unfold massQ
    exact_mod_cast bound
theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]
  exact R.history_cap hi (Nat.lt_succ_self _) k
theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]
  exact R.initial_cap _ k
def cutWeight (rect : Fin 4) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k
def seedLimit (rect : Fin 4) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)
def pointLimit (rect : Fin 4) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)
def initialSeedLimit (rect : Fin 4) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3
theorem seed_limit_small (rect : Fin 4) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)
theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)
theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)
structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<17,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ
theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩
theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound
theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_history hi))
def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct
theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_initial hi)
def beforeCuts (first : Mass) (rest : ℕ → Mass) : ℕ → Mass
  | 0 => first
  | i+1 => rest i
private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i
private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i
theorem Run.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ R.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : R.jointLive 18 = R.final := by simp [Run.jointLive,Run.live]
    simpa only [beforeCuts,Run.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using
        (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]
      exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) R.final)).trans
    (R.joint_bill_with_final rank cut)

theorem inventory {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2558≤M.overhead.toNat) (hi : M.overhead.toNat≤33755)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (K1_14_1.evaluated Crt (word M) Far6970HelperSource.helperBank.shape (Far6970HelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (R : Run F Crt G) (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
        γ∈R.initial.seedMarks ∨ γ∈R.initial.ordinateMarks ∨
        (∃ J∈R.initial.rankExit,OnMark F J γ) ∨ γ∈C.pointMarks ∨
        (∃ i<17,∃ Q∈(C.cover i).curves,OnMark F Q γ) ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := prepare F Crt lo hi noPole residues common
  obtain ⟨C⟩ := R.cutBooks noPole residues
  obtain ⟨S,geom,pass⟩ := R.terminal_surfaces
  refine ⟨R,C,S,geom,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_filter.mpr ⟨hγ,seed⟩)
  · exact Or.inr (Or.inl (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pass γ hγ ⟨J,final,on⟩)))))
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | curve
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,hi,curve⟩))))
end Lower6960.Far6970RescueGeometry

end
end Merged_R6960RescueGeometryBills
end Z6969Source0578

