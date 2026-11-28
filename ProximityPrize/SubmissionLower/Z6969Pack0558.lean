import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

-- merged module Z6969Pack0554
section Merged_Z6969Pack0554

-- Source: Research6969.FarProfileArithmetic
section Z6969Source0575
set_option autoImplicit true
namespace Research6969.FarProfileArithmetic
open Research6966.FarSourceArithmetic (Request fastPhase fastPhase_eq)
open Lower6960.HelperSource (WidthGuard gain surplus gain_eq_compressed)
abbrev agreement : ℕ := 179740
abbrev firstHeight : ℕ := 2535
abbrev heightCap : ℕ := 33735

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
end Research6969.FarProfileArithmetic
end Z6969Source0575

-- Source: Research6969.FarSources
section Z6969Source0576
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Research6969.FarSources
open FarProfileArithmetic (value Checked)
open Research6966.FarSourceData (free helper rescue)
open Lower6960



private theorem free0_first : value (free 0) 2535 = 6301324119450 := by decide +kernel
private theorem free0_next : value (free 0) 2536 = 6409587145920 := by decide +kernel
theorem free0 : Checked (free 0) := by
  refine ⟨(Lower6960.FreeSource.checked 0).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free0_first]; decide
  · rw [free0_first, free0_next]; decide

private theorem free1_first : value (free 1) 2535 = 8873874344400 := by decide +kernel
private theorem free1_next : value (free 1) 2536 = 9037680195600 := by decide +kernel
theorem free1 : Checked (free 1) := by
  refine ⟨(Lower6960.FreeSource.checked 1).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free1_first]; decide
  · rw [free1_first, free1_next]; decide

private theorem free2_first : value (free 2) 2535 = 13942628988360 := by decide +kernel
private theorem free2_next : value (free 2) 2536 = 14194126495840 := by decide +kernel
theorem free2 : Checked (free 2) := by
  refine ⟨(Lower6960.FreeSource.checked 2).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free2_first]; decide
  · rw [free2_first, free2_next]; decide

private theorem free3_first : value (free 3) 2535 = 16788033446340 := by decide +kernel
private theorem free3_next : value (free 3) 2536 = 17138792728190 := by decide +kernel
theorem free3 : Checked (free 3) := by
  refine ⟨(Lower6960.FreeSource.checked 3).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free3_first]; decide
  · rw [free3_first, free3_next]; decide

private theorem free4_first : value (free 4) 2535 = 25073704561700 := by decide +kernel
private theorem free4_next : value (free 4) 2536 = 25577720277964 := by decide +kernel
theorem free4 : Checked (free 4) := by
  refine ⟨(Lower6960.FreeSource.checked 4).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free4_first]; decide
  · rw [free4_first, free4_next]; decide

private theorem free5_first : value (free 5) 2535 = 31458942121040 := by decide +kernel
private theorem free5_next : value (free 5) 2536 = 32136991982564 := by decide +kernel
theorem free5 : Checked (free 5) := by
  refine ⟨(Lower6960.FreeSource.checked 5).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free5_first]; decide
  · rw [free5_first, free5_next]; decide

private theorem free6_first : value (free 6) 2535 = 47342789770040 := by decide +kernel
private theorem free6_next : value (free 6) 2536 = 48530531984834 := by decide +kernel
theorem free6 : Checked (free 6) := by
  refine ⟨(Lower6960.FreeSource.checked 6).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free6_first]; decide
  · rw [free6_first, free6_next]; decide

private theorem free7_first : value (free 7) 2535 = 90725236395255 := by decide +kernel
private theorem free7_next : value (free 7) 2536 = 93229804565898 := by decide +kernel
theorem free7 : Checked (free 7) := by
  refine ⟨(Lower6960.FreeSource.checked 7).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free7_first]; decide
  · rw [free7_first, free7_next]; decide

private theorem free8_first : value (free 8) 2535 = 276012693664680 := by decide +kernel
private theorem free8_next : value (free 8) 2536 = 284849637275112 := by decide +kernel
theorem free8 : Checked (free 8) := by
  refine ⟨(Lower6960.FreeSource.checked 8).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free8_first]; decide
  · rw [free8_first, free8_next]; decide

private theorem free9_first : value (free 9) 2535 = 89690592881394 := by decide +kernel
private theorem free9_next : value (free 9) 2536 = 92160595582848 := by decide +kernel
theorem free9 : Checked (free 9) := by
  refine ⟨(Lower6960.FreeSource.checked 9).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free9_first]; decide
  · rw [free9_first, free9_next]; decide

private theorem free10_first : value (free 10) 2535 = 463447284285260 := by decide +kernel
private theorem free10_next : value (free 10) 2536 = 480414780869232 := by decide +kernel
theorem free10 : Checked (free 10) := by
  refine ⟨(Lower6960.FreeSource.checked 10).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free10_first]; decide
  · rw [free10_first, free10_next]; decide

private theorem free11_first : value (free 11) 2535 = 1571054237221860 := by decide +kernel
private theorem free11_next : value (free 11) 2536 = 1654581692995096 := by decide +kernel
theorem free11 : Checked (free 11) := by
  refine ⟨(Lower6960.FreeSource.checked 11).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free11_first]; decide
  · rw [free11_first, free11_next]; decide

private theorem free12_first : value (free 12) 2535 = 1501106674045034 := by decide +kernel
private theorem free12_next : value (free 12) 2536 = 1575283830834393 := by decide +kernel
theorem free12 : Checked (free 12) := by
  refine ⟨(Lower6960.FreeSource.checked 12).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free12_first]; decide
  · rw [free12_first, free12_next]; decide

private theorem free13_first : value (free 13) 2535 = 4191529584963042 := by decide +kernel
private theorem free13_next : value (free 13) 2536 = 4469450344604132 := by decide +kernel
theorem free13 : Checked (free 13) := by
  refine ⟨(Lower6960.FreeSource.checked 13).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free13_first]; decide
  · rw [free13_first, free13_next]; decide

private theorem free14_first : value (free 14) 2535 = 21442793999219070 := by decide +kernel
private theorem free14_next : value (free 14) 2536 = 23728947876882625 := by decide +kernel
theorem free14 : Checked (free 14) := by
  refine ⟨(Lower6960.FreeSource.checked 14).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free14_first]; decide
  · rw [free14_first, free14_next]; decide

private theorem free15_first : value (free 15) 2535 = 25825977237698160 := by decide +kernel
private theorem free15_next : value (free 15) 2536 = 28513692254055640 := by decide +kernel
theorem free15 : Checked (free 15) := by
  refine ⟨(Lower6960.FreeSource.checked 15).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free15_first]; decide
  · rw [free15_first, free15_next]; decide

private theorem free16_first : value (free 16) 2535 = 68466611809553640 := by decide +kernel
private theorem free16_next : value (free 16) 2536 = 78791030739723576 := by decide +kernel
theorem free16 : Checked (free 16) := by
  refine ⟨(Lower6960.FreeSource.checked 16).debit_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [free16_first]; decide
  · rw [free16_first, free16_next]; decide



private theorem helper_twoSlopes_first : value (helper .twoSlopes) 2535 = 3170375913978270 := by decide +kernel
private theorem helper_twoSlopes_next : value (helper .twoSlopes) 2536 = 3304702835538000 := by decide +kernel
theorem helper_twoSlopes : Checked (helper .twoSlopes) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_twoSlopes_first]; decide
  · rw [helper_twoSlopes_first, helper_twoSlopes_next]; decide

private theorem helper_seedBoundary_first : value (helper .seedBoundary) 2535 = 4190745481257060 := by decide +kernel
private theorem helper_seedBoundary_next : value (helper .seedBoundary) 2536 = 4325470311515678 := by decide +kernel
theorem helper_seedBoundary : Checked (helper .seedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_seedBoundary_first]; decide
  · rw [helper_seedBoundary_first, helper_seedBoundary_next]; decide

private theorem helper_mixedBoundary_first : value (helper .mixedBoundary) 2535 = 3991854480941610 := by decide +kernel
private theorem helper_mixedBoundary_next : value (helper .mixedBoundary) 2536 = 4126505457162864 := by decide +kernel
theorem helper_mixedBoundary : Checked (helper .mixedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_mixedBoundary_first]; decide
  · rw [helper_mixedBoundary_first, helper_mixedBoundary_next]; decide

private theorem helper_jetBoundary_first : value (helper .jetBoundary) 2535 = 10530533501550540 := by decide +kernel
private theorem helper_jetBoundary_next : value (helper .jetBoundary) 2536 = 10667763838332192 := by decide +kernel
theorem helper_jetBoundary : Checked (helper .jetBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_jetBoundary_first]; decide
  · rw [helper_jetBoundary_first, helper_jetBoundary_next]; decide



private theorem rescue0_0_first : value (rescue 0 0) 2535 = 2806488209325225423 := by decide +kernel
private theorem rescue0_0_next : value (rescue 0 0) 2536 = 3094024358550922717 := by decide +kernel
theorem rescue0_0 : Checked (rescue 0 0) := by
  refine ⟨(Lower6960.RescueSource.checked 0 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_0_first]; decide
  · rw [rescue0_0_first, rescue0_0_next]; decide

private theorem rescue0_1_first : value (rescue 0 1) 2535 = 3988550173101799125 := by decide +kernel
private theorem rescue0_1_next : value (rescue 0 1) 2536 = 4418374195716599600 := by decide +kernel
theorem rescue0_1 : Checked (rescue 0 1) := by
  refine ⟨(Lower6960.RescueSource.checked 0 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_1_first]; decide
  · rw [rescue0_1_first, rescue0_1_next]; decide

private theorem rescue0_2_first : value (rescue 0 2) 2535 = 5808008440272227792 := by decide +kernel
private theorem rescue0_2_next : value (rescue 0 2) 2536 = 6416584246449523989 := by decide +kernel
theorem rescue0_2 : Checked (rescue 0 2) := by
  refine ⟨(Lower6960.RescueSource.checked 0 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_2_first]; decide
  · rw [rescue0_2_first, rescue0_2_next]; decide

private theorem rescue0_3_first : value (rescue 0 3) 2535 = 8489045120340175173 := by decide +kernel
private theorem rescue0_3_next : value (rescue 0 3) 2536 = 9407103543708372224 := by decide +kernel
theorem rescue0_3 : Checked (rescue 0 3) := by
  refine ⟨(Lower6960.RescueSource.checked 0 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_3_first]; decide
  · rw [rescue0_3_first, rescue0_3_next]; decide

private theorem rescue0_4_first : value (rescue 0 4) 2535 = 13572274201713286703 := by decide +kernel
private theorem rescue0_4_next : value (rescue 0 4) 2536 = 14944684734727145861 := by decide +kernel
theorem rescue0_4 : Checked (rescue 0 4) := by
  refine ⟨(Lower6960.RescueSource.checked 0 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_4_first]; decide
  · rw [rescue0_4_first, rescue0_4_next]; decide

private theorem rescue0_5_first : value (rescue 0 5) 2535 = 14783673254026831786 := by decide +kernel
private theorem rescue0_5_next : value (rescue 0 5) 2536 = 16603570987916046272 := by decide +kernel
theorem rescue0_5 : Checked (rescue 0 5) := by
  refine ⟨(Lower6960.RescueSource.checked 0 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_5_first]; decide
  · rw [rescue0_5_first, rescue0_5_next]; decide

private theorem rescue0_6_first : value (rescue 0 6) 2535 = 26735594966985136446 := by decide +kernel
private theorem rescue0_6_next : value (rescue 0 6) 2536 = 30022946402345039897 := by decide +kernel
theorem rescue0_6 : Checked (rescue 0 6) := by
  refine ⟨(Lower6960.RescueSource.checked 0 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_6_first]; decide
  · rw [rescue0_6_first, rescue0_6_next]; decide

private theorem rescue0_7_first : value (rescue 0 7) 2535 = 48579946846921207096 := by decide +kernel
private theorem rescue0_7_next : value (rescue 0 7) 2536 = 56096448853854133258 := by decide +kernel
theorem rescue0_7 : Checked (rescue 0 7) := by
  refine ⟨(Lower6960.RescueSource.checked 0 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_7_first]; decide
  · rw [rescue0_7_first, rescue0_7_next]; decide



private theorem rescue0_8_first : value (rescue 0 8) 2535 = 153034211525830684404 := by decide +kernel
private theorem rescue0_8_next : value (rescue 0 8) 2536 = 179858597339678581744 := by decide +kernel
theorem rescue0_8 : Checked (rescue 0 8) := by
  refine ⟨(Lower6960.RescueSource.checked 0 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_8_first]; decide
  · rw [rescue0_8_first, rescue0_8_next]; decide

private theorem rescue0_9_first : value (rescue 0 9) 2535 = 54253719284231312496 := by decide +kernel
private theorem rescue0_9_next : value (rescue 0 9) 2536 = 61584668855443151272 := by decide +kernel
theorem rescue0_9 : Checked (rescue 0 9) := by
  refine ⟨(Lower6960.RescueSource.checked 0 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_9_first]; decide
  · rw [rescue0_9_first, rescue0_9_next]; decide

private theorem rescue0_10_first : value (rescue 0 10) 2535 = 185887726839312169752 := by decide +kernel
private theorem rescue0_10_next : value (rescue 0 10) 2536 = 259293432041413643638 := by decide +kernel
theorem rescue0_10 : Checked (rescue 0 10) := by
  refine ⟨(Lower6960.RescueSource.checked 0 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_10_first]; decide
  · rw [rescue0_10_first, rescue0_10_next]; decide

private theorem rescue0_11_first : value (rescue 0 11) 2535 = 603383417641961764212 := by decide +kernel
private theorem rescue0_11_next : value (rescue 0 11) 2536 = 986654937017292568818 := by decide +kernel
theorem rescue0_11 : Checked (rescue 0 11) := by
  refine ⟨(Lower6960.RescueSource.checked 0 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_11_first]; decide
  · rw [rescue0_11_first, rescue0_11_next]; decide

private theorem rescue0_12_first : value (rescue 0 12) 2535 = 1204012020110467588419 := by decide +kernel
private theorem rescue0_12_next : value (rescue 0 12) 2536 = 1456006585969947043902 := by decide +kernel
theorem rescue0_12 : Checked (rescue 0 12) := by
  refine ⟨(Lower6960.RescueSource.checked 0 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_12_first]; decide
  · rw [rescue0_12_first, rescue0_12_next]; decide

private theorem rescue0_13_first : value (rescue 0 13) 2535 = 3527985143629091656719 := by decide +kernel
private theorem rescue0_13_next : value (rescue 0 13) 2536 = 4524703403506384345793 := by decide +kernel
theorem rescue0_13 : Checked (rescue 0 13) := by
  refine ⟨(Lower6960.RescueSource.checked 0 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_13_first]; decide
  · rw [rescue0_13_first, rescue0_13_next]; decide

private theorem rescue0_14_first : value (rescue 0 14) 2535 = 24384091339451557572831 := by decide +kernel
private theorem rescue0_14_next : value (rescue 0 14) 2536 = 32870699470858721439420 := by decide +kernel
theorem rescue0_14 : Checked (rescue 0 14) := by
  refine ⟨(Lower6960.RescueSource.checked 0 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_14_first]; decide
  · rw [rescue0_14_first, rescue0_14_next]; decide

private theorem rescue0_15_first : value (rescue 0 15) 2535 = 28799639768483285624199 := by decide +kernel
private theorem rescue0_15_next : value (rescue 0 15) 2536 = 38802028925443336592988 := by decide +kernel
theorem rescue0_15 : Checked (rescue 0 15) := by
  refine ⟨(Lower6960.RescueSource.checked 0 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_15_first]; decide
  · rw [rescue0_15_first, rescue0_15_next]; decide



private theorem rescue0_16_first : value (rescue 0 16) 2535 = 100623371791455975137226 := by decide +kernel
private theorem rescue0_16_next : value (rescue 0 16) 2536 = 140275338676778466146149 := by decide +kernel
theorem rescue0_16 : Checked (rescue 0 16) := by
  refine ⟨(Lower6960.RescueSource.checked 0 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_16_first]; decide
  · rw [rescue0_16_first, rescue0_16_next]; decide

private theorem rescue1_0_first : value (rescue 1 0) 2535 = 2524244788829024961 := by decide +kernel
private theorem rescue1_0_next : value (rescue 1 0) 2536 = 2782776717089927073 := by decide +kernel
theorem rescue1_0 : Checked (rescue 1 0) := by
  refine ⟨(Lower6960.RescueSource.checked 1 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_0_first]; decide
  · rw [rescue1_0_first, rescue1_0_next]; decide

private theorem rescue1_1_first : value (rescue 1 1) 2535 = 3586665148066055304 := by decide +kernel
private theorem rescue1_1_next : value (rescue 1 1) 2536 = 3973075860143930507 := by decide +kernel
theorem rescue1_1 : Checked (rescue 1 1) := by
  refine ⟨(Lower6960.RescueSource.checked 1 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_1_first]; decide
  · rw [rescue1_1_first, rescue1_1_next]; decide

private theorem rescue1_2_first : value (rescue 1 2) 2535 = 5227181608208552780 := by decide +kernel
private theorem rescue1_2_next : value (rescue 1 2) 2536 = 5774856605280971611 := by decide +kernel
theorem rescue1_2 : Checked (rescue 1 2) := by
  refine ⟨(Lower6960.RescueSource.checked 1 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_2_first]; decide
  · rw [rescue1_2_first, rescue1_2_next]; decide

private theorem rescue1_3_first : value (rescue 1 3) 2535 = 7629995639410116839 := by decide +kernel
private theorem rescue1_3_next : value (rescue 1 3) 2536 = 8455008646787738813 := by decide +kernel
theorem rescue1_3 : Checked (rescue 1 3) := by
  refine ⟨(Lower6960.RescueSource.checked 1 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_3_first]; decide
  · rw [rescue1_3_first, rescue1_3_next]; decide

private theorem rescue1_4_first : value (rescue 1 4) 2535 = 12236088259186578657 := by decide +kernel
private theorem rescue1_4_next : value (rescue 1 4) 2536 = 13473171384980890699 := by decide +kernel
theorem rescue1_4 : Checked (rescue 1 4) := by
  refine ⟨(Lower6960.RescueSource.checked 1 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_4_first]; decide
  · rw [rescue1_4_first, rescue1_4_next]; decide

private theorem rescue1_5_first : value (rescue 1 5) 2535 = 13312666626709547422 := by decide +kernel
private theorem rescue1_5_next : value (rescue 1 5) 2536 = 14951355166615389476 := by decide +kernel
theorem rescue1_5 : Checked (rescue 1 5) := by
  refine ⟨(Lower6960.RescueSource.checked 1 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_5_first]; decide
  · rw [rescue1_5_first, rescue1_5_next]; decide

private theorem rescue1_6_first : value (rescue 1 6) 2535 = 24109646670454946184 := by decide +kernel
private theorem rescue1_6_next : value (rescue 1 6) 2536 = 27073289964527028587 := by decide +kernel
theorem rescue1_6 : Checked (rescue 1 6) := by
  refine ⟨(Lower6960.RescueSource.checked 1 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_6_first]; decide
  · rw [rescue1_6_first, rescue1_6_next]; decide



private theorem rescue1_7_first : value (rescue 1 7) 2535 = 43741992495855253002 := by decide +kernel
private theorem rescue1_7_next : value (rescue 1 7) 2536 = 50509598441825801532 := by decide +kernel
theorem rescue1_7 : Checked (rescue 1 7) := by
  refine ⟨(Lower6960.RescueSource.checked 1 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_7_first]; decide
  · rw [rescue1_7_first, rescue1_7_next]; decide

private theorem rescue1_8_first : value (rescue 1 8) 2535 = 137769942605978798208 := by decide +kernel
private theorem rescue1_8_next : value (rescue 1 8) 2536 = 161917013302689978340 := by decide +kernel
theorem rescue1_8 : Checked (rescue 1 8) := by
  refine ⟨(Lower6960.RescueSource.checked 1 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_8_first]; decide
  · rw [rescue1_8_first, rescue1_8_next]; decide

private theorem rescue1_9_first : value (rescue 1 9) 2535 = 48929425267418573999 := by decide +kernel
private theorem rescue1_9_next : value (rescue 1 9) 2536 = 55539226281585114480 := by decide +kernel
theorem rescue1_9 : Checked (rescue 1 9) := by
  refine ⟨(Lower6960.RescueSource.checked 1 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_9_first]; decide
  · rw [rescue1_9_first, rescue1_9_next]; decide

private theorem rescue1_10_first : value (rescue 1 10) 2535 = 165912357044068086450 := by decide +kernel
private theorem rescue1_10_next : value (rescue 1 10) 2536 = 231415629583719685482 := by decide +kernel
theorem rescue1_10 : Checked (rescue 1 10) := by
  refine ⟨(Lower6960.RescueSource.checked 1 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_10_first]; decide
  · rw [rescue1_10_first, rescue1_10_next]; decide

private theorem rescue1_11_first : value (rescue 1 11) 2535 = 538729632194716555749 := by decide +kernel
private theorem rescue1_11_next : value (rescue 1 11) 2536 = 880806957038313472128 := by decide +kernel
theorem rescue1_11 : Checked (rescue 1 11) := by
  refine ⟨(Lower6960.RescueSource.checked 1 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_11_first]; decide
  · rw [rescue1_11_first, rescue1_11_next]; decide

private theorem rescue1_12_first : value (rescue 1 12) 2535 = 1086172195904440503700 := by decide +kernel
private theorem rescue1_12_next : value (rescue 1 12) 2536 = 1313402766638740771765 := by decide +kernel
theorem rescue1_12 : Checked (rescue 1 12) := by
  refine ⟨(Lower6960.RescueSource.checked 1 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_12_first]; decide
  · rw [rescue1_12_first, rescue1_12_next]; decide

private theorem rescue1_13_first : value (rescue 1 13) 2535 = 3177345812538269311581 := by decide +kernel
private theorem rescue1_13_next : value (rescue 1 13) 2536 = 4074869082281229672313 := by decide +kernel
theorem rescue1_13 : Checked (rescue 1 13) := by
  refine ⟨(Lower6960.RescueSource.checked 1 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_13_first]; decide
  · rw [rescue1_13_first, rescue1_13_next]; decide

private theorem rescue1_14_first : value (rescue 1 14) 2535 = 21961058083711182117420 := by decide +kernel
private theorem rescue1_14_next : value (rescue 1 14) 2536 = 29603161883608865700717 := by decide +kernel
theorem rescue1_14 : Checked (rescue 1 14) := by
  refine ⟨(Lower6960.RescueSource.checked 1 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_14_first]; decide
  · rw [rescue1_14_first, rescue1_14_next]; decide



private theorem rescue1_15_first : value (rescue 1 15) 2535 = 25937355565120174010616 := by decide +kernel
private theorem rescue1_15_next : value (rescue 1 15) 2536 = 34944412739660806915129 := by decide +kernel
theorem rescue1_15 : Checked (rescue 1 15) := by
  refine ⟨(Lower6960.RescueSource.checked 1 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_15_first]; decide
  · rw [rescue1_15_first, rescue1_15_next]; decide

private theorem rescue1_16_first : value (rescue 1 16) 2535 = 90624969067233859733103 := by decide +kernel
private theorem rescue1_16_next : value (rescue 1 16) 2536 = 126331110637110433447429 := by decide +kernel
theorem rescue1_16 : Checked (rescue 1 16) := by
  refine ⟨(Lower6960.RescueSource.checked 1 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_16_first]; decide
  · rw [rescue1_16_first, rescue1_16_next]; decide

private theorem rescue2_0_first : value (rescue 2 0) 2535 = 1346753513339089455 := by decide +kernel
private theorem rescue2_0_next : value (rescue 2 0) 2536 = 1484395402841923741 := by decide +kernel
theorem rescue2_0 : Checked (rescue 2 0) := by
  refine ⟨(Lower6960.RescueSource.checked 2 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_0_first]; decide
  · rw [rescue2_0_first, rescue2_0_next]; decide

private theorem rescue2_1_first : value (rescue 2 1) 2535 = 1911240405180781089 := by decide +kernel
private theorem rescue2_1_next : value (rescue 2 1) 2536 = 2116686214393180707 := by decide +kernel
theorem rescue2_1 : Checked (rescue 2 1) := by
  refine ⟨(Lower6960.RescueSource.checked 2 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_1_first]; decide
  · rw [rescue2_1_first, rescue2_1_next]; decide

private theorem rescue2_2_first : value (rescue 2 2) 2535 = 2797557201988916924 := by decide +kernel
private theorem rescue2_2_next : value (rescue 2 2) 2536 = 3090572823396384799 := by decide +kernel
theorem rescue2_2 : Checked (rescue 2 2) := by
  refine ⟨(Lower6960.RescueSource.checked 2 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_2_first]; decide
  · rw [rescue2_2_first, rescue2_2_next]; decide

private theorem rescue2_3_first : value (rescue 2 3) 2535 = 4042441770998222472 := by decide +kernel
private theorem rescue2_3_next : value (rescue 2 3) 2536 = 4478907269374424472 := by decide +kernel
theorem rescue2_3 : Checked (rescue 2 3) := by
  refine ⟨(Lower6960.RescueSource.checked 2 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_3_first]; decide
  · rw [rescue2_3_first, rescue2_3_next]; decide

private theorem rescue2_4_first : value (rescue 2 4) 2535 = 6619098970745690847 := by decide +kernel
private theorem rescue2_4_next : value (rescue 2 4) 2536 = 7287584024187973294 := by decide +kernel
theorem rescue2_4 : Checked (rescue 2 4) := by
  refine ⟨(Lower6960.RescueSource.checked 2 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_4_first]; decide
  · rw [rescue2_4_first, rescue2_4_next]; decide

private theorem rescue2_5_first : value (rescue 2 5) 2535 = 7156016882344874786 := by decide +kernel
private theorem rescue2_5_next : value (rescue 2 5) 2536 = 8036419786525919804 := by decide +kernel
theorem rescue2_5 : Checked (rescue 2 5) := by
  refine ⟨(Lower6960.RescueSource.checked 2 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_5_first]; decide
  · rw [rescue2_5_first, rescue2_5_next]; decide



private theorem rescue2_6_first : value (rescue 2 6) 2535 = 12269935385630792207 := by decide +kernel
private theorem rescue2_6_next : value (rescue 2 6) 2536 = 13875028065872667954 := by decide +kernel
theorem rescue2_6 : Checked (rescue 2 6) := by
  refine ⟨(Lower6960.RescueSource.checked 2 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_6_first]; decide
  · rw [rescue2_6_first, rescue2_6_next]; decide

private theorem rescue2_7_first : value (rescue 2 7) 2535 = 23510493197956205964 := by decide +kernel
private theorem rescue2_7_next : value (rescue 2 7) 2536 = 27145596966086196335 := by decide +kernel
theorem rescue2_7 : Checked (rescue 2 7) := by
  refine ⟨(Lower6960.RescueSource.checked 2 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_7_first]; decide
  · rw [rescue2_7_first, rescue2_7_next]; decide

private theorem rescue2_8_first : value (rescue 2 8) 2535 = 73833751442565593787 := by decide +kernel
private theorem rescue2_8_next : value (rescue 2 8) 2536 = 86768112085822107058 := by decide +kernel
theorem rescue2_8 : Checked (rescue 2 8) := by
  refine ⟨(Lower6960.RescueSource.checked 2 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_8_first]; decide
  · rw [rescue2_8_first, rescue2_8_next]; decide

private theorem rescue2_9_first : value (rescue 2 9) 2535 = 26562384751911392619 := by decide +kernel
private theorem rescue2_9_next : value (rescue 2 9) 2536 = 30143947763233293486 := by decide +kernel
theorem rescue2_9 : Checked (rescue 2 9) := by
  refine ⟨(Lower6960.RescueSource.checked 2 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_9_first]; decide
  · rw [rescue2_9_first, rescue2_9_next]; decide

private theorem rescue2_10_first : value (rescue 2 10) 2535 = 83624763405930682206 := by decide +kernel
private theorem rescue2_10_next : value (rescue 2 10) 2536 = 116587008818282640548 := by decide +kernel
theorem rescue2_10 : Checked (rescue 2 10) := by
  refine ⟨(Lower6960.RescueSource.checked 2 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_10_first]; decide
  · rw [rescue2_10_first, rescue2_10_next]; decide

private theorem rescue2_11_first : value (rescue 2 11) 2535 = 272225621525380604396 := by decide +kernel
private theorem rescue2_11_next : value (rescue 2 11) 2536 = 444653863552899542194 := by decide +kernel
theorem rescue2_11 : Checked (rescue 2 11) := by
  refine ⟨(Lower6960.RescueSource.checked 2 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_11_first]; decide
  · rw [rescue2_11_first, rescue2_11_next]; decide

private theorem rescue2_12_first : value (rescue 2 12) 2535 = 524283603335062474467 := by decide +kernel
private theorem rescue2_12_next : value (rescue 2 12) 2536 = 647491514205131992526 := by decide +kernel
theorem rescue2_12 : Checked (rescue 2 12) := by
  refine ⟨(Lower6960.RescueSource.checked 2 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_12_first]; decide
  · rw [rescue2_12_first, rescue2_12_next]; decide

private theorem rescue2_13_first : value (rescue 2 13) 2535 = 1709025959689053772437 := by decide +kernel
private theorem rescue2_13_next : value (rescue 2 13) 2536 = 2191330687131706183817 := by decide +kernel
theorem rescue2_13 : Checked (rescue 2 13) := by
  refine ⟨(Lower6960.RescueSource.checked 2 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_13_first]; decide
  · rw [rescue2_13_first, rescue2_13_next]; decide



private theorem rescue2_14_first : value (rescue 2 14) 2535 = 11816862639819501958341 := by decide +kernel
private theorem rescue2_14_next : value (rescue 2 14) 2536 = 15924370114595595779703 := by decide +kernel
theorem rescue2_14 : Checked (rescue 2 14) := by
  refine ⟨(Lower6960.RescueSource.checked 2 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_14_first]; decide
  · rw [rescue2_14_first, rescue2_14_next]; decide

private theorem rescue2_15_first : value (rescue 2 15) 2535 = 13948045937816889788649 := by decide +kernel
private theorem rescue2_15_next : value (rescue 2 15) 2536 = 18786976983599504289723 := by decide +kernel
theorem rescue2_15 : Checked (rescue 2 15) := by
  refine ⟨(Lower6960.RescueSource.checked 2 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_15_first]; decide
  · rw [rescue2_15_first, rescue2_15_next]; decide

private theorem rescue2_16_first : value (rescue 2 16) 2535 = 48772062216992824522953 := by decide +kernel
private theorem rescue2_16_next : value (rescue 2 16) 2536 = 67965055803998907308839 := by decide +kernel
theorem rescue2_16 : Checked (rescue 2 16) := by
  refine ⟨(Lower6960.RescueSource.checked 2 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_16_first]; decide
  · rw [rescue2_16_first, rescue2_16_next]; decide

private theorem rescue3_0_first : value (rescue 3 0) 2535 = 199201080109429248 := by decide +kernel
private theorem rescue3_0_next : value (rescue 3 0) 2536 = 213851238472604440 := by decide +kernel
theorem rescue3_0 : Checked (rescue 3 0) := by
  refine ⟨(Lower6960.RescueSource.checked 3 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_0_first]; decide
  · rw [rescue3_0_first, rescue3_0_next]; decide

private theorem rescue3_1_first : value (rescue 3 1) 2535 = 284451339916808636 := by decide +kernel
private theorem rescue3_1_next : value (rescue 3 1) 2536 = 306610198843827648 := by decide +kernel
theorem rescue3_1 : Checked (rescue 3 1) := by
  refine ⟨(Lower6960.RescueSource.checked 3 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_1_first]; decide
  · rw [rescue3_1_first, rescue3_1_next]; decide

private theorem rescue3_2_first : value (rescue 3 2) 2535 = 395906079347109051 := by decide +kernel
private theorem rescue3_2_next : value (rescue 3 2) 2536 = 428429601028496830 := by decide +kernel
theorem rescue3_2 : Checked (rescue 3 2) := by
  refine ⟨(Lower6960.RescueSource.checked 3 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_2_first]; decide
  · rw [rescue3_2_first, rescue3_2_next]; decide

private theorem rescue3_3_first : value (rescue 3 3) 2535 = 538922937553649493 := by decide +kernel
private theorem rescue3_3_next : value (rescue 3 3) 2536 = 585429716969225845 := by decide +kernel
theorem rescue3_3 : Checked (rescue 3 3) := by
  refine ⟨(Lower6960.RescueSource.checked 3 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_3_first]; decide
  · rw [rescue3_3_first, rescue3_3_next]; decide

private theorem rescue3_4_first : value (rescue 3 4) 2535 = 711956149847775420 := by decide +kernel
private theorem rescue3_4_next : value (rescue 3 4) 2536 = 808109861491292272 := by decide +kernel
theorem rescue3_4 : Checked (rescue 3 4) := by
  refine ⟨(Lower6960.RescueSource.checked 3 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_4_first]; decide
  · rw [rescue3_4_first, rescue3_4_next]; decide



private theorem rescue3_5_first : value (rescue 3 5) 2535 = 1268164149885940824 := by decide +kernel
private theorem rescue3_5_next : value (rescue 3 5) 2536 = 1479692585942055287 := by decide +kernel
theorem rescue3_5 : Checked (rescue 3 5) := by
  refine ⟨(Lower6960.RescueSource.checked 3 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_5_first]; decide
  · rw [rescue3_5_first, rescue3_5_next]; decide

private theorem rescue3_6_first : value (rescue 3 6) 2535 = 1736847570179112720 := by decide +kernel
private theorem rescue3_6_next : value (rescue 3 6) 2536 = 2055123405090652876 := by decide +kernel
theorem rescue3_6 : Checked (rescue 3 6) := by
  refine ⟨(Lower6960.RescueSource.checked 3 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_6_first]; decide
  · rw [rescue3_6_first, rescue3_6_next]; decide

private theorem rescue3_7_first : value (rescue 3 7) 2535 = 3912172787082469785 := by decide +kernel
private theorem rescue3_7_next : value (rescue 3 7) 2536 = 4814574105736085735 := by decide +kernel
theorem rescue3_7 : Checked (rescue 3 7) := by
  refine ⟨(Lower6960.RescueSource.checked 3 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_7_first]; decide
  · rw [rescue3_7_first, rescue3_7_next]; decide

private theorem rescue3_8_first : value (rescue 3 8) 2535 = 8294738011508656500 := by decide +kernel
private theorem rescue3_8_next : value (rescue 3 8) 2536 = 10611947518750562761 := by decide +kernel
theorem rescue3_8 : Checked (rescue 3 8) := by
  refine ⟨(Lower6960.RescueSource.checked 3 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_8_first]; decide
  · rw [rescue3_8_first, rescue3_8_next]; decide

private theorem rescue3_9_first : value (rescue 3 9) 2535 = 3110872169018663640 := by decide +kernel
private theorem rescue3_9_next : value (rescue 3 9) 2536 = 3775752228831392374 := by decide +kernel
theorem rescue3_9 : Checked (rescue 3 9) := by
  refine ⟨(Lower6960.RescueSource.checked 3 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_9_first]; decide
  · rw [rescue3_9_first, rescue3_9_next]; decide

private theorem rescue3_10_first : value (rescue 3 10) 2535 = 24582832142961093570 := by decide +kernel
private theorem rescue3_10_next : value (rescue 3 10) 2536 = 28040319645146169422 := by decide +kernel
theorem rescue3_10 : Checked (rescue 3 10) := by
  refine ⟨(Lower6960.RescueSource.checked 3 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_10_first]; decide
  · rw [rescue3_10_first, rescue3_10_next]; decide

private theorem rescue3_11_first : value (rescue 3 11) 2535 = 116245463383395028620 := by decide +kernel
private theorem rescue3_11_next : value (rescue 3 11) 2536 = 135474071715256934904 := by decide +kernel
theorem rescue3_11 : Checked (rescue 3 11) := by
  refine ⟨(Lower6960.RescueSource.checked 3 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_11_first]; decide
  · rw [rescue3_11_first, rescue3_11_next]; decide

private theorem rescue3_12_first : value (rescue 3 12) 2535 = 44424604493832243540 := by decide +kernel
private theorem rescue3_12_next : value (rescue 3 12) 2536 = 66836337497646587984 := by decide +kernel
theorem rescue3_12 : Checked (rescue 3 12) := by
  refine ⟨(Lower6960.RescueSource.checked 3 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_12_first]; decide
  · rw [rescue3_12_first, rescue3_12_next]; decide



private theorem rescue3_13_first : value (rescue 3 13) 2535 = 138970249236960637325 := by decide +kernel
private theorem rescue3_13_next : value (rescue 3 13) 2536 = 248675032438344424391 := by decide +kernel
theorem rescue3_13 : Checked (rescue 3 13) := by
  refine ⟨(Lower6960.RescueSource.checked 3 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_13_first]; decide
  · rw [rescue3_13_first, rescue3_13_next]; decide

private theorem rescue3_14_first : value (rescue 3 14) 2535 = 540920948931183457620 := by decide +kernel
private theorem rescue3_14_next : value (rescue 3 14) 2536 = 1497008650914485574864 := by decide +kernel
theorem rescue3_14 : Checked (rescue 3 14) := by
  refine ⟨(Lower6960.RescueSource.checked 3 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_14_first]; decide
  · rw [rescue3_14_first, rescue3_14_next]; decide

private theorem rescue3_15_first : value (rescue 3 15) 2535 = 564754655422033808472 := by decide +kernel
private theorem rescue3_15_next : value (rescue 3 15) 2536 = 1572291321991866173472 := by decide +kernel
theorem rescue3_15 : Checked (rescue 3 15) := by
  refine ⟨(Lower6960.RescueSource.checked 3 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_15_first]; decide
  · rw [rescue3_15_first, rescue3_15_next]; decide

private theorem rescue3_16_first : value (rescue 3 16) 2535 = 973638855581067565800 := by decide +kernel
private theorem rescue3_16_next : value (rescue 3 16) 2536 = 5524477856368592579680 := by decide +kernel
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

end Research6969.FarSources
end Z6969Source0576

-- Source: Research6969.FarSourceRows
section Z6969Source0577
set_option autoImplicit true
set_option Elab.async false

namespace Lower6960.Far6969FreeSource
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (debit)
open HelperSource (WidthGuard cutoffCount)
open Research6966.FarSourceData (free)
open Research6969.FarSources (free_checked)
open Research6969.FarProfileArithmetic (agreement)

abbrev bank := FreeSource.bank
abbrev reserve := FreeSource.reserve
def cutoff (h : ℕ) (i : Fin 17) : ℕ := cutoffCount (bank i).shape agreement h (reserve i)-1

theorem shape_guards (i : Fin 17) :
    0<(bank i).shape.J ∧ (bank i).shape.J≤(bank i).shape.B ∧
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*agreement<K1.p := by
  fin_cases i <;> decide +kernel

theorem cutoff_fit {h : ℕ} (lo : 2535≤h) (hi : h≤33735) (i : Fin 17) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*agreement :=
  FreeSource.buffered_fit _ _ _ _ ((free_checked i).window lo hi)

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2535≤h) (hi : h≤33735) (i : Fin 17) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have cert := free_checked i
  have positive := cert.gain lo hi
  change debit h (bank i)<HelperSource.gain (bank i).shape agreement h (reserve i)
    ((bank i).shape.J+1) 0 0 at positive
  rw [FreeSource.gain_eq_raw _ _ _ _ (by omega)] at positive
  exact FreeSource.nonzero_row Crt word (bank i) agreement (reserve i) (by omega) (by omega)
    cert.rank (cert.window lo hi) positive

end Lower6960.Far6969FreeSource

namespace Lower6960.Far6969HelperSource
open Polynomial
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open HelperSource (HelperTest cutoffCount WidthGuard)
open Research6969.FarSources (helper_checked)
open Research6969.FarProfileArithmetic (agreement)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev helperBank := HelperSource.helperBank
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape agreement h 10-1

theorem helper_width {h : ℕ} (lo : 2535≤h) (hi : h≤33735) : WidthGuard helperBank agreement h 10 :=
  (helper_checked .twoSlopes).window lo hi

theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2535≤h) (hi : h≤33735) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬G∣Q := by
  have cert := helper_checked test
  exact HelperSource.crt_avoiding_row Crt word helperBank agreement 10 test.slope test.excess test.seed
    (by omega) (by omega) cert.positive_slope cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2
    (by decide) (cert.window lo hi) (cert.gain lo hi) irr seeded slope seed excess

theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2535≤h) (hi : h≤33735) :
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
    (lo : 2535≤h) (hi : h≤33735) {G : Jet} (irr : Irreducible G)
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
    (lo : 2535≤h) (hi : h≤33735) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
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

end Lower6960.Far6969HelperSource

namespace Lower6960.Far6969RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (cutoffCount)
open Research6969.FarSources (rescue_checked)
open Research6969.FarProfileArithmetic (agreement)

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

theorem cutoff_fit {h : ℕ} (lo : 2535≤h) (hi : h≤33735) (rect : Fin 4) (i : Fin 17) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*agreement :=
  FreeSource.buffered_fit _ _ _ _ ((rescue_checked rect i).window lo hi)




end Lower6960.Far6969RescueSource
end Z6969Source0577

namespace Research6969.TransitionArithmetic
open Research6966.FarSourceArithmetic (Request fastPhase fastPhase_eq)
open Lower6960.HelperSource (gain surplus gain_eq_compressed)
abbrev agreement : ℕ := 179730
def value (q:Request) (h:ℕ) : ℤ :=
  (fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 0-
    fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 1:ℕ) -
    (P1_7.debit h q.bank:ℤ)

theorem value_eq (q:Request) (h:ℕ) (pos:0<q.slope) (narrow:q.bank.shape.J<131071-h) :
    value q h=surplus q.bank agreement h q.reserve q.slope q.excess q.seed := by
  unfold value surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ pos,fastPhase_eq _ _ _ _ _ _ _ _ narrow,fastPhase_eq _ _ _ _ _ _ _ _ narrow]

end Research6969.TransitionArithmetic

-- Source: Research6969.FarRescueGeometry
section Z6969Source0578
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960RescueGeometry
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Far6969RescueGeometry
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
open Far6969RescueSource (bank reserve cutoff jetCap seedCap)
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
    (Far6969RescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))
end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometry

section Merged_R6960RescueGeometryHistory
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Far6969RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open Far6969RescueSource (bank reserve cutoff jetCap seedCap)
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
      (Far6969RescueSource.shape_guards rect i).2.1 init.parents on (reserve i) (reserve_small i)
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
theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)
end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometryHistory

section Merged_R6960RescueGeometryCuts
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Far6969RescueGeometry
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
open Far6969RescueSource (bank reserve)
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
    · exact (Far6969RescueSource.shape_guards R.rect j).2.1
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
end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometryCuts

section Merged_R6960RescueGeometryBills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Far6969RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open Far6969RescueSource (bank reserve)
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

end Lower6960.Far6969RescueGeometry

end
end Merged_R6960RescueGeometryBills
end Z6969Source0578

-- Source: Research6969.PrefixRates
section Z6969Source0579
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960RescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Rates
open Far6969RescueGeometry (Model Family label_injective OnMark)
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179730
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 133482

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133482) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179730 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 133482 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 133482) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2411) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤133482
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2411) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133482)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 133482) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2411) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound


end Lower6960.Prefix6969Rates

end
end Merged_R6960RescueGeometryTariffs

section Merged_R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Rates
open Far6969RescueGeometry (Model Family label_injective OnMark)
open Finset Polynomial
open K1 (K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

end Lower6960.Prefix6969Rates

end
end Merged_R6960RescueGeometryRates
end Z6969Source0579

-- Source: Research6969.TransitionSources
section Z6969Source0580
set_option autoImplicit true
namespace Research6969.TransitionSources
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open Lower6960
open TransitionArithmetic (agreement value value_eq)
open Research6966.FarSourceArithmetic (Request)

def request (r:ℕ) (b:P1_7.Bank):Request:=⟨b,r,b.shape.J+1,0,0⟩

structure Free (first r:ℕ) (b:P1_7.Bank) : Prop where
  rank:P3_7_1.BankOK b
  reserve_fit:2*r≤b.shape.B
  narrow:b.shape.J<131071-(first+1)
  width:HelperSource.WidthGuard b agreement first r
  positive:0<value (request r b) first
  grows:value (request r b) first≤value (request r b) (first+1)

/-- Each verified row supplies an actual nonzero interpolation polynomial
at every height in its interval. -/
theorem Free.row {first r:ℕ} {b:P1_7.Bank} (cert:Free first r b)
    {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (hh:0<h) (lo:first≤h) (hi:h≤131070) :
    ∃ P∈evaluated Crt word b.shape (HelperSource.cutoffCount b.shape agreement h r-1),P≠0 := by
  let q:=request r b
  have width:=HelperSource.width_at_height _ _ _ _ _ lo (by omega) cert.reserve_fit cert.width
  have before:=cert.narrow.trans_le (Nat.sub_le_sub_left (Nat.le_succ first) _)
  have pos:=cert.positive
  have grow:=cert.grows
  rw [value_eq _ _ (Nat.succ_pos _) before] at pos
  rw [value_eq _ _ (Nat.succ_pos _) before,value_eq _ _ (Nat.succ_pos _) cert.narrow] at grow
  have gain:=HelperSource.surplus_positive b agreement first h r (b.shape.J+1) 0 0 lo hi pos grow
  rw [FreeSource.gain_eq_raw _ _ _ _ (by omega)] at gain
  exact FreeSource.nonzero_row Crt word b agreement r hh hi cert.rank width gain

end Research6969.TransitionSources
end Z6969Source0580

-- Source: Research6969.PhysicalWindow
section Z6969Source0581
set_option autoImplicit true
namespace Research6969.PhysicalWindow
open K1_14 (L Jet Shape shapeSum triangle)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Research6966
open HelperAvoidance (debitAt triSlots rectSlots)
open HelperWindowIntervals (bound cutoff slotLimit box axis)
open HelperWindowPrefix (volume)
open Finset
set_option maxHeartbeats 1000000

/-- An interpolation witness specifies both the native slope valuation and
the physical weight certified for this particular factor. -/
structure Request where
  bank : P1_7.Bank
  reserve : ℕ
  jet : ℕ
  slope : ℕ
  weight : ℕ
  seed : ℕ

abbrev agreement : ℕ := 179730
abbrev Request.shape (b:Request) := b.bank.shape
abbrev Request.top (b:Request) (h:ℕ) := cutoff b.shape agreement h b.reserve
abbrev Request.limit (b:Request) (width:ℕ) := slotLimit b.shape width b.seed

def Triangular (b:Request) (lo hi:ℕ) : Prop :=
  triangle b.shape.U*b.bank.nodeRows+hi*(2*(b.shape.U+1))*b.bank.poleMoment+
    bound b.shape agreement b.reserve lo hi b.jet b.slope b.weight (b.limit b.shape.U) (triSlots b.shape.U b.seed) <
  triangle b.shape.U*volume (b.top hi) b.shape.B b.shape.J (131071-lo)

instance (b:Request) (lo hi:ℕ) : Decidable (Triangular b lo hi) := by unfold Triangular;infer_instance

def Rectangle (b:Request) (width lo hi:ℕ) : Prop :=
  let U:=box b.shape.U width
  KoalaRect.area U*b.bank.nodeRows+hi*(U 0+U 1+2)*b.bank.poleMoment+
    bound b.shape agreement b.reserve lo hi b.jet b.slope b.weight (b.limit width) (rectSlots U (axis b.seed)) <
  KoalaRect.area U*volume (b.top hi) b.shape.B b.shape.J (131071-lo)

instance (b:Request) (width lo hi:ℕ) : Decidable (Rectangle b width lo hi) := by unfold Rectangle;infer_instance

/-- A subdivision only chooses which pair of endpoints proves a uniform
source inequality. Every height in the covered interval is admitted. -/
def Cover (test:ℕ→ℕ→Prop) (last:ℕ) : ℕ→List ℕ→Prop
  | lo,[] => lo=last+1
  | lo,hi::ends => lo≤hi ∧ hi≤last ∧ test lo hi ∧ Cover test last (hi+1) ends

theorem covered {test:ℕ→ℕ→Prop} {first last h:ℕ} {ends:List ℕ}
    (cert:Cover test last first ends) (lo:first≤h) (hi:h≤last) :
    ∃ left right,left≤h ∧ h≤right ∧ right≤last ∧ test left right := by
  induction ends generalizing first with
  | nil => change first=last+1 at cert;omega
  | cons right rest ih =>
    obtain ⟨_,stop,ok,tail⟩:=cert
    by_cases earlier:h≤right
    · exact ⟨_,right,lo,earlier,stop,ok⟩
    · exact ih tail (by omega)

theorem covered_from {test:ℕ→ℕ→Prop} {first last h:ℕ} {ends:List ℕ}
    (cert:Cover test last first ends) (lo:first≤h) (hi:h≤last) :
    ∃ left right,first≤left ∧ left≤h ∧ h≤right ∧ right≤last ∧ test left right := by
  induction ends generalizing first with
  | nil => change first=last+1 at cert;omega
  | cons right rest ih =>
    obtain ⟨start,stop,ok,tail⟩:=cert
    by_cases early:h≤right
    · exact ⟨_,right,le_rfl,lo,early,stop,ok⟩
    · obtain ⟨l,r,ll,lh,hr,rs,p⟩:=ih tail (by omega)
      exact ⟨l,r,by omega,lh,hr,rs,p⟩

private theorem slope_tail {s:Shape} {a b k:ℕ} {slots:ℕ→ℕ} (positive:0<b)
    (h:slots k=0 ∨ s.B<k*a ∨ s.J<k*1) : slots k=0 ∨ s.B<k*a ∨ s.J<k*b := by
  exact h.imp_right (fun h=>h.imp_right fun h=>h.trans_le (Nat.mul_le_mul_left k positive))

theorem triangle_positive (b:Request) {lo hi h:ℕ} (hh:0<h) (low:lo≤h) (high:h≤hi)
    (narrow:b.shape.J<131071-hi) (slope:0<b.slope) (checked:Triangular b lo hi) :
    P1_7.debit h b.bank+
      (∑ W∈range (b.top h), debitAt b.shape h (b.top h) W b.jet b.slope b.weight (triSlots b.shape.U b.seed)) <
    triangle b.shape.U * shapeSum b.shape (fun q j=>b.top h+j-q*(131071-h)) := by
  have tail:=HelperWindowIntervals.triangle_tail b.shape b.jet b.shape.U b.seed
  have pos:=HelperWindowIntervals.positive b.shape agreement b.reserve lo hi h b.jet b.slope b.weight (b.limit b.shape.U)
    (triangle b.shape.U) (2*(b.shape.U+1)) b.bank.nodeRows b.bank.poleMoment _ hh low high narrow
    (fun k large=>slope_tail slope (tail k large)) checked
  simpa only [P1_7.debit,Nat.mul_left_comm h 2,Nat.mul_assoc] using pos

theorem rectangle_positive (b:Request) (width:ℕ) {lo hi h:ℕ} (hh:0<h) (low:lo≤h) (high:h≤hi)
    (narrow:b.shape.J<131071-hi) (slope:0<b.slope) (checked:Rectangle b width lo hi) :
    KoalaRect.rectDebit h b.bank.nodeRows b.bank.poleMoment (box b.shape.U width)+
      (∑ W∈range (b.top h),debitAt b.shape h (b.top h) W b.jet b.slope b.weight
        (rectSlots (box b.shape.U width) (axis b.seed))) <
    KoalaRect.area (box b.shape.U width)*shapeSum b.shape (fun q j=>b.top h+j-q*(131071-h)) := by
  have tail:=HelperWindowIntervals.rectangle_tail b.shape b.jet b.shape.U width b.seed
  exact HelperWindowIntervals.positive b.shape agreement b.reserve lo hi h b.jet b.slope b.weight (b.limit width)
    _ _ b.bank.nodeRows b.bank.poleMoment _ hh low high narrow (fun k large=>slope_tail slope (tail k large)) checked


end Research6969.PhysicalWindow
end Z6969Source0581

end Merged_Z6969Pack0554

-- merged module Z6969Pack0558
section Merged_Z6969Pack0558

-- Source: Research6969.TransitionBanks
section Z6969Source0587
set_option autoImplicit true
namespace Research6969.TransitionBanks
abbrev bank0 (u : ℕ) : P1_7.Bank := ⟨⟨102,141,31,u⟩,33533460480,11621252⟩
abbrev bank1 (u : ℕ) : P1_7.Bank := ⟨⟨104,144,32,u⟩,35837181952,12729182⟩
abbrev bank2 (u : ℕ) : P1_7.Bank := ⟨⟨106,147,32,u⟩,37385666560,13594640⟩
abbrev bank3 (u : ℕ) : P1_7.Bank := ⟨⟨107,148,33,u⟩,39047397376,14217978⟩
abbrev bank4 (u : ℕ) : P1_7.Bank := ⟨⟨108,150,33,u⟩,39862927360,14840297⟩
abbrev bank5 (u : ℕ) : P1_7.Bank := ⟨⟨109,151,33,u⟩,40687370240,15158299⟩
abbrev bank6 (u : ℕ) : P1_7.Bank := ⟨⟨111,154,34,u⟩,43306188800,16508386⟩
abbrev bank7 (u : ℕ) : P1_7.Bank := ⟨⟨113,157,35,u⟩,46031437824,17945628⟩
abbrev bank8 (u : ℕ) : P1_7.Bank := ⟨⟨114,158,35,u⟩,46942126080,18313194⟩
abbrev bank9 (u : ℕ) : P1_7.Bank := ⟨⟨117,162,36,u⟩,50775982080,20261980⟩
abbrev bank10 (u : ℕ) : P1_7.Bank := ⟨⟨119,165,36,u⟩,52725547008,21484793⟩
abbrev bank11 (u : ℕ) : P1_7.Bank := ⟨⟨119,165,37,u⟩,53801910272,21934618⟩
abbrev bank12 (u : ℕ) : P1_7.Bank := ⟨⟨120,166,37,u⟩,54812999680,22362213⟩
abbrev bank13 (u : ℕ) : P1_7.Bank := ⟨⟨121,168,37,u⟩,55834050560,23234370⟩
abbrev bank14 (u : ℕ) : P1_7.Bank := ⟨⟨124,172,38,u⟩,60131901440,25559185⟩
abbrev bank15 (u : ℕ) : P1_7.Bank := ⟨⟨126,175,38,u⟩,62309531648,27010804⟩
abbrev bank16 (u : ℕ) : P1_7.Bank := ⟨⟨126,175,39,u⟩,63517491200,27547813⟩
abbrev bank17 (u : ℕ) : P1_7.Bank := ⟨⟨127,176,39,u⟩,64644710400,28054113⟩
abbrev bank18 (u : ℕ) : P1_7.Bank := ⟨⟨130,180,40,u⟩,69377720320,30727249⟩
abbrev bank19 (u : ℕ) : P1_7.Bank := ⟨⟨133,184,41,u⟩,74336174080,33586892⟩
abbrev bank20 (u : ℕ) : P1_7.Bank := ⟨⟨134,186,41,u⟩,75585814528,34768135⟩
abbrev bank21 (u : ℕ) : P1_7.Bank := ⟨⟨135,187,41,u⟩,76846465024,35369225⟩
abbrev bank22 (u : ℕ) : P1_7.Bank := ⟨⟨135,187,42,u⟩,78229012480,36021740⟩
abbrev bank23 (u : ℕ) : P1_7.Bank := ⟨⟨137,190,42,u⟩,80832888832,37902732⟩
abbrev bank24 (u : ℕ) : P1_7.Bank := ⟨⟨140,194,43,u⟩,86317203456,41244492⟩
abbrev bank25 (u : ℕ) : P1_7.Bank := ⟨⟨143,198,44,u⟩,92044001280,44802338⟩
abbrev bank26 (u : ℕ) : P1_7.Bank := ⟨⟨145,201,44,u⟩,94934138880,47009993⟩
abbrev bank27 (u : ℕ) : P1_7.Bank := ⟨⟨148,205,45,u⟩,101033181184,50931776⟩
abbrev bank28 (u : ℕ) : P1_7.Bank := ⟨⟨148,205,46,u⟩,102693601280,51790020⟩
abbrev bank29 (u : ℕ) : P1_7.Bank := ⟨⟨150,208,46,u⟩,105810755584,54254747⟩
abbrev bank30 (u : ℕ) : P1_7.Bank := ⟨⟨151,209,47,u⟩,109114818560,56002200⟩
abbrev bank31 (u : ℕ) : P1_7.Bank := ⟨⟨153,212,47,u⟩,112361209856,58616088⟩
abbrev bank32 (u : ℕ) : P1_7.Bank := ⟨⟨155,215,47,u⟩,115657932800,61311840⟩
abbrev bank33 (u : ℕ) : P1_7.Bank := ⟨⟨156,216,48,u⟩,119176429568,63235028⟩
abbrev bank34 (u : ℕ) : P1_7.Bank := ⟨⟨159,220,49,u⟩,126261657600,68121522⟩
abbrev bank35 (u : ℕ) : P1_7.Bank := ⟨⟨163,226,50,u⟩,135467106304,75401397⟩
abbrev bank36 (u : ℕ) : P1_7.Bank := ⟨⟨164,227,50,u⟩,137325445120,76474675⟩
abbrev bank37 (u : ℕ) : P1_7.Bank := ⟨⟨164,227,51,u⟩,139361517568,77637159⟩
abbrev bank38 (u : ℕ) : P1_7.Bank := ⟨⟨166,230,51,u⟩,143178334208,80971087⟩
abbrev bank39 (u : ℕ) : P1_7.Bank := ⟨⟨168,233,52,u⟩,149189820416,85660533⟩
abbrev bank40 (u : ℕ) : P1_7.Bank := ⟨⟨171,237,53,u⟩,157407510528,91783289⟩
abbrev bank41 (u : ℕ) : P1_7.Bank := ⟨⟨174,241,53,u⟩,163628974080,96837455⟩
abbrev bank42 (u : ℕ) : P1_7.Bank := ⟨⟨174,241,54,u⟩,165921423360,98228328⟩
abbrev bank43 (u : ℕ) : P1_7.Bank := ⟨⟨176,244,54,u⟩,170203545600,102199273⟩
abbrev bank44 (u : ℕ) : P1_7.Bank := ⟨⟨178,247,55,u⟩,176946151424,107778015⟩
abbrev bank45 (u : ℕ) : P1_7.Bank := ⟨⟨183,254,57,u⟩,193292926976,121131076⟩
abbrev bank46 (u : ℕ) : P1_7.Bank := ⟨⟨189,262,58,u⟩,210421678080,135575420⟩
abbrev bank47 (u : ℕ) : P1_7.Bank := ⟨⟨190,263,59,u⟩,215642275840,139044661⟩
abbrev bank48 (u : ℕ) : P1_7.Bank := ⟨⟨192,266,59,u⟩,220738355200,144192301⟩
abbrev bank49 (u : ℕ) : P1_7.Bank := ⟨⟨193,268,59,u⟩,223309987840,147695211⟩
abbrev bank50 (u : ℕ) : P1_7.Bank := ⟨⟨193,268,60,u⟩,226125676544,149605064⟩
abbrev bank51 (u : ℕ) : P1_7.Bank := ⟨⟨194,269,59,u⟩,225897349120,149468191⟩
abbrev bank52 (u : ℕ) : P1_7.Bank := ⟨⟨204,283,63,u⟩,265373614080,184912224⟩
abbrev bank53 (u : ℕ) : P1_7.Bank := ⟨⟨205,284,64,u⟩,271454044160,189280842⟩
abbrev bank54 (u : ℕ) : P1_7.Bank := ⟨⟨212,294,65,u⟩,295979712512,214017359⟩
abbrev bank55 (u : ℕ) : P1_7.Bank := ⟨⟨215,298,67,u⟩,312397004800,228740750⟩
abbrev bank56 (u : ℕ) : P1_7.Bank := ⟨⟨222,308,69,u⟩,343008870400,260075583⟩
abbrev bank57 (u : ℕ) : P1_7.Bank := ⟨⟨224,311,70,u⟩,353725317120,271261163⟩
abbrev bank58 (u : ℕ) : P1_7.Bank := ⟨⟨225,312,70,u⟩,357261639680,274069426⟩
abbrev bank59 (u : ℕ) : P1_7.Bank := ⟨⟨225,314,68,u⟩,349597597696,273591980⟩
abbrev bank60 (u : ℕ) : P1_7.Bank := ⟨⟨225,314,69,u⟩,353440890880,276676118⟩
abbrev bank61 (u : ℕ) : P1_7.Bank := ⟨⟨227,315,71,u⟩,368270376960,285699863⟩
abbrev bank62 (u : ℕ) : P1_7.Bank := ⟨⟨237,328,74,u⟩,418217984000,335760609⟩
abbrev bank63 (u : ℕ) : P1_7.Bank := ⟨⟨239,332,74,u⟩,426141286400,349077659⟩
abbrev bank64 (u : ℕ) : P1_7.Bank := ⟨⟨243,337,74,u⟩,442223820800,366224034⟩
abbrev bank65 (u : ℕ) : P1_7.Bank := ⟨⟨252,350,78,u⟩,498909577216,430562752⟩
abbrev bank66 (u : ℕ) : P1_7.Bank := ⟨⟨256,355,79,u⟩,521718988800,455042366⟩
abbrev bank67 (u : ℕ) : P1_7.Bank := ⟨⟨256,355,80,u⟩,526651490304,459454565⟩
abbrev bank68 (u : ℕ) : P1_7.Bank := ⟨⟨259,359,80,u⟩,540538306560,476279615⟩
abbrev bank69 (u : ℕ) : P1_7.Bank := ⟨⟨260,360,82,u⟩,555371724800,489737381⟩
abbrev bank70 (u : ℕ) : P1_7.Bank := ⟨⟨260,361,79,u⟩,540090040320,480182166⟩
abbrev bank71 (u : ℕ) : P1_7.Bank := ⟨⟨262,363,82,u⟩,564966981632,502963348⟩
abbrev bank72 (u : ℕ) : P1_7.Bank := ⟨⟨266,369,83,u⟩,589745881088,535097333⟩
abbrev bank73 (u : ℕ) : P1_7.Bank := ⟨⟨269,373,83,u⟩,604708536320,553942033⟩
abbrev bank74 (u : ℕ) : P1_7.Bank := ⟨⟨269,373,84,u⟩,610154577920,559058208⟩
abbrev bank75 (u : ℕ) : P1_7.Bank := ⟨⟨272,377,84,u⟩,625462476800,578534598⟩
abbrev bank76 (u : ℕ) : P1_7.Bank := ⟨⟨272,377,85,u⟩,631028580352,583814440⟩
abbrev bank77 (u : ℕ) : P1_7.Bank := ⟨⟨275,382,83,u⟩,635228389376,597984703⟩
abbrev bank78 (u : ℕ) : P1_7.Bank := ⟨⟨275,383,83,u⟩,635228389376,603020643⟩
abbrev bank79 (u : ℕ) : P1_7.Bank := ⟨⟨275,383,84,u⟩,640970915840,608607683⟩
abbrev bank80 (u : ℕ) : P1_7.Bank := ⟨⟨275,383,87,u⟩,658033868800,625236061⟩
abbrev bank81 (u : ℕ) : P1_7.Bank := ⟨⟨276,383,83,u⟩,640392101888,603020643⟩
abbrev bank82 (u : ℕ) : P1_7.Bank := ⟨⟨277,384,86,u⟩,663023779840,624925184⟩
abbrev bank83 (u : ℕ) : P1_7.Bank := ⟨⟨281,390,87,u⟩,690560696320,662678389⟩
abbrev bank84 (u : ℕ) : P1_7.Bank := ⟨⟨282,391,87,u⟩,696062574592,668148909⟩
abbrev bank85 (u : ℕ) : P1_7.Bank := ⟨⟨285,395,89,u⟩,724956610560,702503867⟩
abbrev bank86 (u : ℕ) : P1_7.Bank := ⟨⟨287,398,89,u⟩,736375603200,719781707⟩
abbrev bank87 (u : ℕ) : P1_7.Bank := ⟨⟨287,398,90,u⟩,742561677312,725984075⟩
abbrev bank88 (u : ℕ) : P1_7.Bank := ⟨⟨295,409,92,u⟩,802732113920,805907535⟩
abbrev bank89 (u : ℕ) : P1_7.Bank := ⟨⟨296,411,92,u⟩,808826961920,818632570⟩
abbrev bank90 (u : ℕ) : P1_7.Bank := ⟨⟨300,416,94,u⟩,846999060480,865230227⟩
abbrev bank91 (u : ℕ) : P1_7.Bank := ⟨⟨302,419,95,u⟩,866513846272,892659430⟩
abbrev bank92 (u : ℕ) : P1_7.Bank := ⟨⟨310,430,95,u⟩,918657433600,970134630⟩
abbrev bank93 (u : ℕ) : P1_7.Bank := ⟨⟨313,433,97,u⟩,953437126656,1008070710⟩
abbrev bank94 (u : ℕ) : P1_7.Bank := ⟨⟨313,434,97,u⟩,953437126656,1015567563⟩
abbrev bank95 (u : ℕ) : P1_7.Bank := ⟨⟨313,434,98,u⟩,960795770880,1023606650⟩
abbrev bank96 (u : ℕ) : P1_7.Bank := ⟨⟨314,435,98,u⟩,967673118720,1031203184⟩
abbrev bank97 (u : ℕ) : P1_7.Bank := ⟨⟨316,438,99,u⟩,989003776000,1062483026⟩
abbrev bank98 (u : ℕ) : P1_7.Bank := ⟨⟨319,442,100,u⟩,1017758351360,1102455756⟩
abbrev bank99 (u : ℕ) : P1_7.Bank := ⟨⟨322,446,101,u⟩,1047064739840,1143545315⟩
abbrev bank100 (u : ℕ) : P1_7.Bank := ⟨⟨325,453,98,u⟩,1045036793856,1174588250⟩
abbrev bank101 (u : ℕ) : P1_7.Bank := ⟨⟨325,453,100,u⟩,1061047500800,1193036697⟩
abbrev bank102 (u : ℕ) : P1_7.Bank := ⟨⟨325,453,102,u⟩,1076928184320,1211360939⟩
abbrev bank103 (u : ℕ) : P1_7.Bank := ⟨⟨330,458,103,u⟩,1122512142336,1264296353⟩
abbrev bank104 (u : ℕ) : P1_7.Bank := ⟨⟨332,460,104,u⟩,1146054246400,1291682639⟩
abbrev bank105 (u : ℕ) : P1_7.Bank := ⟨⟨342,474,107,u⟩,1251092201472,1453763546⟩
abbrev bank106 (u : ℕ) : P1_7.Bank := ⟨⟨344,477,107,u⟩,1267512901632,1483537364⟩
abbrev bank107 (u : ℕ) : P1_7.Bank := ⟨⟨348,482,108,u⟩,1309818224640,1545109193⟩
abbrev bank108 (u : ℕ) : P1_7.Bank := ⟨⟨348,483,108,u⟩,1309818224640,1555432583⟩
abbrev bank109 (u : ℕ) : P1_7.Bank := ⟨⟨349,484,109,u⟩,1327400222720,1576951631⟩
abbrev bank110 (u : ℕ) : P1_7.Bank := ⟨⟨354,491,109,u⟩,1370293534720,1651411016⟩
abbrev bank111 (u : ℕ) : P1_7.Bank := ⟨⟨357,495,111,u⟩,1415598571520,1718934918⟩
abbrev bank112 (u : ℕ) : P1_7.Bank := ⟨⟨365,506,113,u⟩,1507599056896,1870272531⟩
abbrev bank113 (u : ℕ) : P1_7.Bank := ⟨⟨365,506,114,u⟩,1517607976960,1883005203⟩
abbrev bank114 (u : ℕ) : P1_7.Bank := ⟨⟨367,509,114,u⟩,1536268697600,1919120263⟩
abbrev bank115 (u : ℕ) : P1_7.Bank := ⟨⟨368,510,115,u⟩,1555815727104,1944295055⟩
abbrev bank116 (u : ℕ) : P1_7.Bank := ⟨⟨378,524,118,u⟩,1684225392640,2163592004⟩
abbrev bank117 (u : ℕ) : P1_7.Bank := ⟨⟨380,526,119,u⟩,1715056148480,2204525073⟩
abbrev bank118 (u : ℕ) : P1_7.Bank := ⟨⟨380,527,118,u⟩,1704221474816,2203657519⟩
abbrev bank119 (u : ℕ) : P1_7.Bank := ⟨⟨382,529,120,u⟩,1746249449472,2259708309⟩
abbrev bank120 (u : ℕ) : P1_7.Bank := ⟨⟨384,532,120,u⟩,1766771916800,2301165208⟩
abbrev bank121 (u : ℕ) : P1_7.Bank := ⟨⟨386,535,121,u⟩,1798595411968,2358160566⟩
abbrev bank122 (u : ℕ) : P1_7.Bank := ⟨⟨387,535,123,u⟩,1831412432896,2388083183⟩
abbrev bank123 (u : ℕ) : P1_7.Bank := ⟨⟨387,536,120,u⟩,1797793513472,2357242900⟩
abbrev bank124 (u : ℕ) : P1_7.Bank := ⟨⟨387,537,123,u⟩,1831412432896,2416913989⟩
abbrev bank125 (u : ℕ) : P1_7.Bank := ⟨⟨388,538,122,u⟩,1830787219456,2416196542⟩
abbrev bank126 (u : ℕ) : P1_7.Bank := ⟨⟨390,541,122,u⟩,1851971338240,2459779870⟩
abbrev bank127 (u : ℕ) : P1_7.Bank := ⟨⟨391,542,122,u⟩,1862611763200,2474425808⟩
abbrev bank128 (u : ℕ) : P1_7.Bank := ⟨⟨391,542,123,u⟩,1874060115968,2490027179⟩
abbrev bank129 (u : ℕ) : P1_7.Bank := ⟨⟨392,544,123,u⟩,1884803301376,2519689529⟩
abbrev bank130 (u : ℕ) : P1_7.Bank := ⟨⟨395,547,124,u⟩,1928921088000,2580674858⟩
abbrev bank131 (u : ℕ) : P1_7.Bank := ⟨⟨397,550,124,u⟩,1950842880000,2626456108⟩
abbrev bank132 (u : ℕ) : P1_7.Bank := ⟨⟨399,553,124,u⟩,1972895744000,2672787483⟩
abbrev bank133 (u : ℕ) : P1_7.Bank := ⟨⟨400,558,120,u⟩,1935519252480,2682384904⟩
abbrev bank134 (u : ℕ) : P1_7.Bank := ⟨⟨400,558,123,u⟩,1971918995456,2734096379⟩
abbrev bank135 (u : ℕ) : P1_7.Bank := ⟨⟨400,558,126,u⟩,2007957766144,2785382344⟩
abbrev bank136 (u : ℕ) : P1_7.Bank := ⟨⟨409,566,127,u⟩,2123022467072,2933627832⟩
abbrev bank137 (u : ℕ) : P1_7.Bank := ⟨⟨411,570,128,u⟩,2159008022528,3018995326⟩
abbrev bank138 (u : ℕ) : P1_7.Bank := ⟨⟨416,577,130,u⟩,2244209803264,3177562648⟩
abbrev bank139 (u : ℕ) : P1_7.Bank := ⟨⟨455,630,142,u⟩,2930701762560,4512018338⟩
abbrev bank140 (u : ℕ) : P1_7.Bank := ⟨⟨455,631,142,u⟩,2930701762560,4535089958⟩
abbrev bank141 (u : ℕ) : P1_7.Bank := ⟨⟨470,655,141,u⟩,3134317133824,5085275599⟩
abbrev bank142 (u : ℕ) : P1_7.Bank := ⟨⟨470,655,144,u⟩,3184589537280,5168862572⟩
abbrev bank143 (u : ℕ) : P1_7.Bank := ⟨⟨470,655,148,u⟩,3250957582336,5279398867⟩
abbrev bank144 (u : ℕ) : P1_7.Bank := ⟨⟨480,665,149,u⟩,3425114521600,5571898574⟩
abbrev bank145 (u : ℕ) : P1_7.Bank := ⟨⟨483,670,149,u⟩,3473185177600,5707728199⟩
abbrev bank146 (u : ℕ) : P1_7.Bank := ⟨⟨506,701,157,u⟩,4009024552960,6873381450⟩
abbrev bank147 (u : ℕ) : P1_7.Bank := ⟨⟨534,740,166,u⟩,4716471779328,8540674317⟩
abbrev bank148 (u : ℕ) : P1_7.Bank := ⟨⟨534,741,166,u⟩,4716471779328,8577852024⟩
abbrev bank149 (u : ℕ) : P1_7.Bank := ⟨⟨542,751,169,u⟩,4942312243200,9080555850⟩
abbrev bank150 (u : ℕ) : P1_7.Bank := ⟨⟨544,755,169,u⟩,4983222435840,9237048500⟩
abbrev bank151 (u : ℕ) : P1_7.Bank := ⟨⟨552,765,172,u⟩,5217441021952,9768274947⟩
abbrev bank152 (u : ℕ) : P1_7.Bank := ⟨⟨555,769,173,u⟩,5304235851776,9978111377⟩
abbrev bank153 (u : ℕ) : P1_7.Bank := ⟨⟨555,769,174,u⟩,5327303475200,10022613078⟩
abbrev bank154 (u : ℕ) : P1_7.Bank := ⟨⟨556,772,170,u⟩,5255817068544,9968090926⟩
abbrev bank155 (u : ℕ) : P1_7.Bank := ⟨⟨560,781,169,u⟩,5316921262080,10299257375⟩
abbrev bank156 (u : ℕ) : P1_7.Bank := ⟨⟨560,781,172,u⟩,5388141854720,10440670587⟩
abbrev bank157 (u : ℕ) : P1_7.Bank := ⟨⟨560,781,176,u⟩,5482316038144,10627925923⟩
abbrev bank158 (u : ℕ) : P1_7.Bank := ⟨⟨563,780,179,u⟩,5619261112320,10723114255⟩
abbrev bank159 (u : ℕ) : P1_7.Bank := ⟨⟨563,781,175,u⟩,5524531707904,10581248240⟩
abbrev bank160 (u : ℕ) : P1_7.Bank := ⟨⟨568,786,178,u⟩,5707573493760,10943454095⟩
abbrev bank161 (u : ℕ) : P1_7.Bank := ⟨⟨568,787,177,u⟩,5683410108416,10940615189⟩
abbrev bank162 (u : ℕ) : P1_7.Bank := ⟨⟨570,789,179,u⟩,5776980049920,11126431075⟩
abbrev bank163 (u : ℕ) : P1_7.Bank := ⟨⟨570,792,174,u⟩,5654852403200,11019070253⟩
abbrev bank164 (u : ℕ) : P1_7.Bank := ⟨⟨580,804,181,u⟩,6056834760704,11923349975⟩
abbrev bank165 (u : ℕ) : P1_7.Bank := ⟨⟨580,804,182,u⟩,6082014740480,11974188965⟩
abbrev bank166 (u : ℕ) : P1_7.Bank := ⟨⟨590,818,185,u⟩,6397599416320,12818954657⟩
abbrev bank167 (u : ℕ) : P1_7.Bank := ⟨⟨594,823,185,u⟩,6495116984320,13072778317⟩
abbrev bank168 (u : ℕ) : P1_7.Bank := ⟨⟨594,824,185,u⟩,6495116984320,13123950482⟩
abbrev bank169 (u : ℕ) : P1_7.Bank := ⟨⟨626,867,191,u⟩,7482311180288,15843358730⟩
abbrev bank170 (u : ℕ) : P1_7.Bank := ⟨⟨626,870,191,u⟩,7482311180288,16020316298⟩
abbrev bank171 (u : ℕ) : P1_7.Bank := ⟨⟨627,869,188,u⟩,7419528216576,15766391116⟩
abbrev bank172 (u : ℕ) : P1_7.Bank := ⟨⟨627,869,199,u⟩,7745044480000,16475620761⟩
abbrev bank173 (u : ℕ) : P1_7.Bank := ⟨⟨630,872,192,u⟩,7619678044160,16204478458⟩
abbrev bank174 (u : ℕ) : P1_7.Bank := ⟨⟨630,876,192,u⟩,7619678044160,16444710190⟩
abbrev bank175 (u : ℕ) : P1_7.Bank := ⟨⟨634,878,193,u⟩,7758708736000,16632572003⟩
abbrev bank176 (u : ℕ) : P1_7.Bank := ⟨⟨636,882,194,u⟩,7844154572800,16945191716⟩
abbrev bank177 (u : ℕ) : P1_7.Bank := ⟨⟨638,885,194,u⟩,7899413217280,17131221716⟩
abbrev bank178 (u : ℕ) : P1_7.Bank := ⟨⟨640,888,195,u⟩,7985899765760,17387809020⟩
abbrev bank179 (u : ℕ) : P1_7.Bank := ⟨⟨642,891,195,u⟩,8041801449472,17577396586⟩
abbrev bank180 (u : ℕ) : P1_7.Bank := ⟨⟨646,896,197,u⟩,8217479086080,18038668599⟩
abbrev bank181 (u : ℕ) : P1_7.Bank := ⟨⟨646,897,197,u⟩,8217479086080,18103487397⟩
abbrev bank182 (u : ℕ) : P1_7.Bank := ⟨⟨650,900,198,u⟩,8363671289856,18370859424⟩
abbrev bank183 (u : ℕ) : P1_7.Bank := ⟨⟨650,903,198,u⟩,8363671289856,18568500055⟩
abbrev bank184 (u : ℕ) : P1_7.Bank := ⟨⟨654,906,199,u⟩,8511579750400,18841034461⟩
abbrev bank185 (u : ℕ) : P1_7.Bank := ⟨⟨656,908,200,u⟩,8602464026624,19048970063⟩
abbrev bank186 (u : ℕ) : P1_7.Bank := ⟨⟨656,910,200,u⟩,8602464026624,19184229663⟩
abbrev bank187 (u : ℕ) : P1_7.Bank := ⟨⟨662,918,206,u⟩,8977766154240,20188806092⟩
abbrev bank188 (u : ℕ) : P1_7.Bank := ⟨⟨664,920,202,u⟩,8905622290432,20024299600⟩
abbrev bank189 (u : ℕ) : P1_7.Bank := ⟨⟨666,924,203,u⟩,8999288700928,20383503144⟩
abbrev bank190 (u : ℕ) : P1_7.Bank := ⟨⟨668,927,203,u⟩,9059825090560,20597080434⟩
abbrev bank191 (u : ℕ) : P1_7.Bank := ⟨⟨670,930,204,u⟩,9154580971520,20891646965⟩
abbrev bank192 (u : ℕ) : P1_7.Bank := ⟨⟨690,962,208,u⟩,9921631092736,23645774460⟩
abbrev bank193 (u : ℕ) : P1_7.Bank := ⟨⟨690,962,212,u⟩,10065769922560,23997864317⟩
abbrev bank194 (u : ℕ) : P1_7.Bank := ⟨⟨690,962,217,u⟩,10244384358400,24434817260⟩
abbrev bank195 (u : ℕ) : P1_7.Bank := ⟨⟨690,963,208,u⟩,9921631092736,23724874690⟩
abbrev bank196 (u : ℕ) : P1_7.Bank := ⟨⟨690,963,212,u⟩,10065769922560,24078187611⟩
abbrev bank197 (u : ℕ) : P1_7.Bank := ⟨⟨690,963,217,u⟩,10244384358400,24516657294⟩
abbrev bank198 (u : ℕ) : P1_7.Bank := ⟨⟨777,1079,242,u⟩,14510937341952,38464827595⟩
abbrev bank199 (u : ℕ) : P1_7.Bank := ⟨⟨820,1139,255,u⟩,17030719733760,47675541672⟩
abbrev bank200 (u : ℕ) : P1_7.Bank := ⟨⟨825,1150,248,u⟩,16903818182656,48121815022⟩
abbrev bank201 (u : ℕ) : P1_7.Bank := ⟨⟨825,1150,253,u⟩,17161575202816,48873782027⟩
abbrev bank202 (u : ℕ) : P1_7.Bank := ⟨⟨825,1150,260,u⟩,17518948515840,49918096074⟩
abbrev bank203 (u : ℕ) : P1_7.Bank := ⟨⟨825,1151,248,u⟩,16903818182656,48256472894⟩
abbrev bank204 (u : ℕ) : P1_7.Bank := ⟨⟨825,1151,253,u⟩,17161575202816,49010625289⟩
abbrev bank205 (u : ℕ) : P1_7.Bank := ⟨⟨825,1151,260,u⟩,17518948515840,50057971890⟩
abbrev bank206 (u : ℕ) : P1_7.Bank := ⟨⟨865,1201,269,u⟩,19985667194880,58933082332⟩
abbrev bank207 (u : ℕ) : P1_7.Bank := ⟨⟨877,1217,272,u⟩,20785262231552,62028176139⟩
abbrev bank208 (u : ℕ) : P1_7.Bank := ⟨⟨886,1229,274,u⟩,21383938048000,64382650838⟩
abbrev bank209 (u : ℕ) : P1_7.Bank := ⟨⟨886,1229,276,u⟩,21501770989568,64746366769⟩
abbrev bank210 (u : ℕ) : P1_7.Bank := ⟨⟨901,1250,280,u⟩,22569516007424,69141668633⟩
abbrev bank211 (u : ℕ) : P1_7.Bank := ⟨⟨912,1267,284,u⟩,23441086873600,73012155113⟩
abbrev bank212 (u : ℕ) : P1_7.Bank := ⟨⟨919,1275,287,u⟩,24035953999872,75115353358⟩
abbrev bank213 (u : ℕ) : P1_7.Bank := ⟨⟨928,1288,286,u⟩,24501513093120,77398939333⟩
abbrev bank214 (u : ℕ) : P1_7.Bank := ⟨⟨949,1317,296,u⟩,26438419611648,85393696802⟩
abbrev bank215 (u : ℕ) : P1_7.Bank := ⟨⟨962,1337,299,u⟩,27464892416000,90341964896⟩
abbrev bank216 (u : ℕ) : P1_7.Bank := ⟨⟨967,1342,302,u⟩,27995979907072,92143933560⟩
abbrev bank217 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1393,307,u⟩,30557599170560,105228376929⟩
abbrev bank218 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1394,307,u⟩,30557599170560,105471636407⟩
abbrev bank219 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1394,315,u⟩,31157463285760,107596110457⟩
abbrev bank220 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1395,296,u⟩,29722184515584,102755930405⟩
abbrev bank221 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1395,301,u⟩,30103476895744,104105680031⟩
abbrev bank222 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1395,307,u⟩,30557599170560,105715278267⟩
abbrev bank223 (u : ℕ) : P1_7.Bank := ⟨⟨1000,1395,315,u⟩,31157463285760,107844841957⟩
abbrev bank224 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1673,368,u⟩,52718727069696,218387554859⟩
abbrev bank225 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1673,378,u⟩,53798525730816,222977190790⟩
abbrev bank226 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1674,355,u⟩,51296765214720,212765123946⟩
abbrev bank227 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1674,361,u⟩,51955677528064,215563369662⟩
abbrev bank228 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1674,368,u⟩,52718727069696,218807905514⟩
abbrev bank229 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1674,378,u⟩,53798525730816,223406703910⟩
abbrev bank230 (u : ℕ) : P1_7.Bank := ⟨⟨1258,1749,391,u⟩,61347730554880,264101254943⟩
abbrev bank231 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2021,445,u⟩,92998964346880,465028319332⟩
abbrev bank232 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2022,436,u⟩,91566841790464,458421718666⟩
abbrev bank233 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2022,445,u⟩,92998964346880,465769321795⟩
abbrev bank234 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2022,457,u⟩,94890063298560,475487789910⟩
abbrev bank235 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2023,429,u⟩,90444517867520,453391020534⟩
abbrev bank236 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2023,436,u⟩,91566841790464,459151377566⟩
abbrev bank237 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2023,445,u⟩,92998964346880,466511127281⟩
abbrev bank238 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2023,457,u⟩,94890063298560,476245648464⟩
abbrev bank239 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2439,537,u⟩,163381988556800,985665319192⟩
abbrev bank240 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2440,537,u⟩,163381988556800,986966790957⟩
abbrev bank241 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2441,527,u⟩,161065121873920,973912060302⟩
abbrev bank242 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2441,537,u⟩,163381988556800,988269431527⟩
abbrev bank243 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2441,551,u⟩,166595992223744,1008217465165⟩
abbrev bank244 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2442,518,u⟩,158964379549696,962176592398⟩
abbrev bank245 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2442,527,u⟩,161065121873920,975196209190⟩
abbrev bank246 (u : ℕ) : P1_7.Bank := ⟨⟨1750,2442,537,u⟩,163381988556800,989573241440⟩
abbrev bank247 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2928,645,u⟩,282396798484480,2046887686018⟩
abbrev bank248 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2928,662,u⟩,288013660979200,2088662039796⟩
abbrev bank249 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2929,645,u⟩,282396798484480,2049139102608⟩
abbrev bank250 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2929,662,u⟩,288013660979200,2090961110089⟩
abbrev bank251 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2930,622,u⟩,274699477319680,1994139134137⟩
abbrev bank252 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2930,632,u⟩,278060332482560,2019119590628⟩
abbrev bank253 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2930,645,u⟩,282396798484480,2051392203643⟩
abbrev bank254 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2930,662,u⟩,288013660979200,2093261903519⟩
abbrev bank255 (u : ℕ) : P1_7.Bank := ⟨⟨2100,2931,632,u⟩,278060332482560,2021337557218⟩
abbrev bank256 (u : ℕ) : P1_7.Bank := ⟨⟨2387,3322,747,u⟩,420533089861632,3445098204118⟩
abbrev bank257 (u : ℕ) : P1_7.Bank := ⟨⟨2546,3544,792,u⟩,507920948920320,4440399084942⟩
abbrev bank258 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3623,798,u⟩,535425056505856,4795161706555⟩
abbrev bank259 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3623,819,u⟩,546063062138880,4892906717079⟩
abbrev bank260 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3624,798,u⟩,535425056505856,4799424311630⟩
abbrev bank261 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3625,783,u⟩,527755772952576,4733203574232⟩
abbrev bank262 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3625,798,u⟩,535425056505856,4803689494279⟩
abbrev bank263 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3625,819,u⟩,546063062138880,4901614794409⟩
abbrev bank264 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3626,798,u⟩,535425056505856,4807957255301⟩
abbrev bank265 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3626,819,u⟩,546063062138880,4905972788959⟩
abbrev bank266 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3627,783,u⟩,527755772952576,4741611634368⟩
abbrev bank267 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3627,798,u⟩,535425056505856,4812227595495⟩
abbrev bank268 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3627,819,u⟩,546063062138880,4910333421859⟩
abbrev bank269 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3628,770,u⟩,521059839508480,4684185417862⟩
abbrev bank270 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3628,783,u⟩,527755772952576,4745819470168⟩
abbrev bank271 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3628,798,u⟩,535425056505856,4816500515660⟩
abbrev bank272 (u : ℕ) : P1_7.Bank := ⟨⟨2652,3691,830,u⟩,576642060910592,5249056297887⟩
abbrev bank273 (u : ℕ) : P1_7.Bank := ⟨⟨2705,3767,814,u⟩,593924919132160,5520825894692⟩
abbrev bank274 (u : ℕ) : P1_7.Bank := ⟨⟨2717,3782,845,u⟩,617112204214272,5756976302970⟩
abbrev bank275 (u : ℕ) : P1_7.Bank := ⟨⟨2767,3852,861,u⟩,652050240634880,6196939591060⟩
abbrev bank276 (u : ℕ) : P1_7.Bank := ⟨⟨2767,3852,866,u⟩,654914606858240,6224865038545⟩
abbrev bank277 (u : ℕ) : P1_7.Bank := ⟨⟨2811,3913,874,u⟩,683226234880000,6594957993633⟩
abbrev bank278 (u : ℕ) : P1_7.Bank := ⟨⟨2811,3913,880,u⟩,686774022569984,6630087774248⟩
abbrev bank279 (u : ℕ) : P1_7.Bank := ⟨⟨2817,3923,851,u⟩,672733997301760,6512804695549⟩
abbrev bank280 (u : ℕ) : P1_7.Bank := ⟨⟨2864,3987,891,u⟩,722903184703488,7110809743963⟩
abbrev bank281 (u : ℕ) : P1_7.Bank := ⟨⟨2864,3989,885,u⟩,719210963271680,7085003902524⟩
abbrev bank282 (u : ℕ) : P1_7.Bank := ⟨⟨2867,3991,892,u⟩,725217086799872,7140033494115⟩
abbrev bank283 (u : ℕ) : P1_7.Bank := ⟨⟨2899,4037,875,u⟩,732681548595200,7298293490304⟩
abbrev bank284 (u : ℕ) : P1_7.Bank := ⟨⟨2899,4038,864,u⟩,725650419220480,7232363502162⟩
abbrev bank285 (u : ℕ) : P1_7.Bank := ⟨⟨2899,4038,875,u⟩,732681548595200,7304113170170⟩
abbrev bank286 (u : ℕ) : P1_7.Bank := ⟨⟨2917,4063,890,u⟩,752568113037312,7550005185904⟩
abbrev bank287 (u : ℕ) : P1_7.Bank := ⟨⟨2917,4063,892,u⟩,753852707766272,7563211302447⟩
abbrev bank288 (u : ℕ) : P1_7.Bank := ⟨⟨2917,4063,893,u⟩,754494559748096,7569810562400⟩
abbrev bank289 (u : ℕ) : P1_7.Bank := ⟨⟨2917,4064,890,u⟩,752568113037312,7555988947369⟩
abbrev bank290 (u : ℕ) : P1_7.Bank := ⟨⟨2956,4117,893,u⟩,777257512337408,7898464820375⟩
abbrev bank291 (u : ℕ) : P1_7.Bank := ⟨⟨2967,4133,896,u⟩,785746572083200,8018620391390⟩
abbrev bank292 (u : ℕ) : P1_7.Bank := ⟨⟨2970,4137,897,u⟩,788194070364160,8050621479572⟩
abbrev bank293 (u : ℕ) : P1_7.Bank := ⟨⟨3013,4182,898,u⟩,814632873492480,8343071159337⟩
abbrev bank294 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4459,1008,u⟩,1017717693874176,11221829825062⟩
abbrev bank295 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4461,982,u⟩,997767489781760,11012145571636⟩
abbrev bank296 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4462,982,u⟩,997767489781760,11020095796464⟩
abbrev bank297 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4463,982,u⟩,997767489781760,11028049925768⟩
abbrev bank298 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4463,1008,u⟩,1017717693874176,11254299374432⟩
abbrev bank299 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4464,963,u⟩,983050615259136,10869251283552⟩
abbrev bank300 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4464,982,u⟩,997767489781760,11036007960531⟩
abbrev bank301 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4464,1008,u⟩,1017717693874176,11262426748352⟩
abbrev bank302 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4465,947,u⟩,970564165959680,10735676910569⟩
abbrev bank303 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4465,963,u⟩,983050615259136,10877088344236⟩
abbrev bank304 (u : ℕ) : P1_7.Bank := ⟨⟨3200,4465,982,u⟩,997767489781760,11043969901736⟩
abbrev bank305 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5504,1244,u⟩,1913299978158080,26038250013848⟩
abbrev bank306 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5507,1213,u⟩,1877062482395136,25577387039299⟩
abbrev bank307 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5507,1244,u⟩,1913299978158080,26084011577468⟩
abbrev bank308 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5509,1213,u⟩,1877062482395136,25607310424524⟩
abbrev bank309 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5510,1189,u⟩,1848744952463360,25226292539926⟩
abbrev bank310 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5510,1213,u⟩,1877062482395136,25622281045803⟩
abbrev bank311 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5510,1244,u⟩,1913299978158080,26129827888718⟩
abbrev bank312 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5511,1189,u⟩,1848744952463360,25241028863276⟩
abbrev bank313 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5511,1213,u⟩,1877062482395136,25637257621145⟩
abbrev bank314 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5512,1169,u⟩,1824966114017280,24923274283249⟩
abbrev bank315 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5512,1189,u⟩,1848744952463360,25255771038451⟩
abbrev bank316 (u : ℕ) : P1_7.Bank := ⟨⟨3950,5512,1213,u⟩,1877062482395136,25652240151764⟩
abbrev bank317 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6690,1474,u⟩,3367547627110400,55703383755931⟩
abbrev bank318 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6690,1512,u⟩,3433136573644800,56816483122989⟩
abbrev bank319 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6692,1474,u⟩,3367547627110400,55757027345056⟩
abbrev bank320 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6692,1512,u⟩,3433136573644800,56871238465897⟩
abbrev bank321 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6694,1445,u⟩,3317023033262080,54952917346103⟩
abbrev bank322 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6694,1474,u⟩,3367547627110400,55810706074581⟩
abbrev bank323 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6694,1512,u⟩,3433136573644800,56926029739529⟩
abbrev bank324 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6695,1474,u⟩,3367547627110400,55837558620681⟩
abbrev bank325 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6695,1512,u⟩,3433136573644800,56953438854149⟩
abbrev bank326 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6696,1474,u⟩,3367547627110400,55864419956306⟩
abbrev bank327 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6696,1512,u⟩,3433136573644800,56980856955989⟩
abbrev bank328 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6697,1445,u⟩,3317023033262080,55032215749682⟩
abbrev bank329 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6697,1474,u⟩,3367547627110400,55891290082931⟩
abbrev bank330 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6697,1512,u⟩,3433136573644800,57008284046562⟩
abbrev bank331 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6698,1421,u⟩,3274891856707584,54342858960622⟩
abbrev bank332 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6698,1445,u⟩,3317023033262080,55058665830093⟩
abbrev bank333 (u : ℕ) : P1_7.Bank := ⟨⟨4800,6698,1474,u⟩,3367547627110400,55918169002031⟩
abbrev bank334 (u : ℕ) : P1_7.Bank := ⟨⟨5620,7835,1720,u⟩,5390441861611520,104477286568219⟩
abbrev bank335 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7946,1796,u⟩,5749327563587584,113058766636997⟩
abbrev bank336 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7948,1750,u⟩,5637370734182400,110890906752819⟩
abbrev bank337 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7948,1796,u⟩,5749327563587584,113150499898987⟩
abbrev bank338 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7950,1750,u⟩,5637370734182400,110980791054694⟩
abbrev bank339 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7950,1796,u⟩,5749327563587584,113242283843565⟩
abbrev bank340 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7951,1750,u⟩,5637370734182400,111025751789870⟩
abbrev bank341 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7951,1796,u⟩,5749327563587584,113288194826317⟩
abbrev bank342 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7952,1716,u⟩,5553838907981824,109384694947514⟩
abbrev bank343 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7952,1750,u⟩,5637370734182400,111070724916873⟩
abbrev bank344 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7952,1796,u⟩,5749327563587584,113334118485107⟩
abbrev bank345 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7953,1716,u⟩,5553838907981824,109428971647179⟩
abbrev bank346 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7953,1750,u⟩,5637370734182400,111115710437454⟩
abbrev bank347 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7954,1716,u⟩,5553838907981824,109473260530676⟩
abbrev bank348 (u : ℕ) : P1_7.Bank := ⟨⟨5700,7954,1750,u⟩,5637370734182400,111160708353364⟩
abbrev bank349 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9621,2118,u⟩,9997036108906496,238016971510476⟩
abbrev bank350 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9621,2174,u⟩,10196763128627200,242895948111878⟩
abbrev bank351 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9623,2118,u⟩,9997036108906496,238176347849000⟩
abbrev bank352 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9623,2174,u⟩,10196763128627200,243058712908678⟩
abbrev bank353 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9625,2118,u⟩,9997036108906496,238335796784464⟩
abbrev bank354 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9625,2174,u⟩,10196763128627200,243221551977378⟩
abbrev bank355 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9626,2077,u⟩,9849424459857920,234809190715807⟩
abbrev bank356 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9626,2118,u⟩,9997036108906496,238415548481346⟩
abbrev bank357 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9627,2118,u⟩,9997036108906496,238495318333820⟩
abbrev bank358 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9628,2042,u⟩,9722458861731840,231866079487253⟩
abbrev bank359 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9628,2077,u⟩,9849424459857920,234966243278304⟩
abbrev bank360 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9628,2118,u⟩,9997036108906496,238575106344005⟩
abbrev bank361 (u : ℕ) : P1_7.Bank := ⟨⟨6900,9629,2077,u⟩,9849424459857920,235044796335102⟩
abbrev bank362 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11575,2548,u⟩,17399709518790656,498569901356632⟩
abbrev bank363 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11575,2615,u⟩,17745461310914560,508734991702659⟩
abbrev bank364 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11577,2498,u⟩,17139238515245056,491197457313663⟩
abbrev bank365 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11577,2548,u⟩,17399709518790656,498847383098023⟩
abbrev bank366 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11577,2615,u⟩,17745461310914560,509018341309343⟩
abbrev bank367 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11579,2498,u⟩,17139238515245056,491470625461013⟩
abbrev bank368 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11579,2548,u⟩,17399709518790656,499124969898998⟩
abbrev bank369 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11579,2615,u⟩,17745461310914560,509301798386539⟩
abbrev bank370 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11580,2548,u⟩,17399709518790656,499263802703202⟩
abbrev bank371 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11581,2498,u⟩,17139238515245056,491743896877039⟩
abbrev bank372 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11581,2548,u⟩,17399709518790656,499402661779949⟩
abbrev bank373 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11582,2498,u⟩,17139238515245056,491880571317053⟩
abbrev bank374 (u : ℕ) : P1_7.Bank := ⟨⟨8300,11582,2548,u⟩,17399709518790656,499541547131788⟩
abbrev bank375 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13948,3070,u⟩,30428373265940480,1050983571587703⟩
abbrev bank376 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13948,3150,u⟩,31027650042265600,1072221490229155⟩
abbrev bank377 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13950,3070,u⟩,30428373265940480,1051468979452278⟩
abbrev bank378 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13950,3150,u⟩,31027650042265600,1072717072025530⟩
abbrev bank379 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13952,3010,u⟩,29974681586237440,1035886358306578⟩
abbrev bank380 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13952,3070,u⟩,30428373265940480,1051954539834997⟩
abbrev bank381 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13952,3150,u⟩,31027650042265600,1073212809809009⟩
abbrev bank382 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13953,3010,u⟩,29974681586237440,1036125345444439⟩
abbrev bank383 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13953,3070,u⟩,30428373265940480,1052197377228338⟩
abbrev bank384 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13954,3010,u⟩,29974681586237440,1036364370066239⟩
abbrev bank385 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13954,3070,u⟩,30428373265940480,1052440252760428⟩
abbrev bank386 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13955,3010,u⟩,29974681586237440,1036603432174989⟩
abbrev bank387 (u : ℕ) : P1_7.Bank := ⟨⟨10000,13955,3070,u⟩,30428373265940480,1052683166434338⟩
end Research6969.TransitionBanks
end Z6969Source0587

-- Source: Research6969.TransitionBankChecks00
section Z6969Source0588
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole0 : momentEstimate 141 31 = 11621252 := by
  refine moment_from_blocks [(128,10677580),(44,943672)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank0 (u : ℕ) : P3_7_1.BankOK (bank0 u) :=
  P3_7_1.checked (bank0 u) (m:=102) (B:=141) (J:=31) (N:=33533460480) (M:=11621252) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole0
private theorem pole1 : momentEstimate 144 32 = 12729182 := by
  refine moment_from_blocks [(128,11505698),(48,1223484)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank1 (u : ℕ) : P3_7_1.BankOK (bank1 u) :=
  P3_7_1.checked (bank1 u) (m:=104) (B:=144) (J:=32) (N:=35837181952) (M:=12729182) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole1
theorem free1_0 : TransitionSources.Free 2314 0 (bank1 1559) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank1 1559)) 2314 = 2490028451040 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank1 1559)) 2315 = 2863150948320 := by decide +kernel
  refine ⟨rank1 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free1_1 : TransitionSources.Free 2412 0 (bank1 1128) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank1 1128)) 2412 = 1319784191448 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank1 1128)) 2413 = 1507325538132 := by decide +kernel
  refine ⟨rank1 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole2 : momentEstimate 147 32 = 13594640 := by
  refine moment_from_blocks [(128,12120161),(51,1474479)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank2 (u : ℕ) : P3_7_1.BankOK (bank2 u) :=
  P3_7_1.checked (bank2 u) (m:=106) (B:=147) (J:=32) (N:=37385666560) (M:=13594640) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole2
theorem free2_0 : TransitionSources.Free 2314 0 (bank2 1529) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank2 1529)) 2314 = 2465275534470 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank2 1529)) 2315 = 2837721520440 := by decide +kernel
  refine ⟨rank2 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free2_1 : TransitionSources.Free 2412 0 (bank2 1121) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank2 1121)) 2412 = 1350596227266 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank2 1121)) 2413 = 1542807255660 := by decide +kernel
  refine ⟨rank2 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole3 : momentEstimate 148 33 = 14217978 := by
  refine moment_from_blocks [(128,12568920),(53,1649058)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank3 (u : ℕ) : P3_7_1.BankOK (bank3 u) :=
  P3_7_1.checked (bank3 u) (m:=107) (B:=148) (J:=33) (N:=39047397376) (M:=14217978) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole3
theorem free3_0 : TransitionSources.Free 2314 0 (bank3 1490) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank3 1490)) 2314 = 2404879494780 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank3 1490)) 2315 = 2772803789784 := by decide +kernel
  refine ⟨rank3 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free3_1 : TransitionSources.Free 2412 0 (bank3 1102) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank3 1102)) 2412 = 1379892813888 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank3 1102)) 2413 = 1573134932820 := by decide +kernel
  refine ⟨rank3 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free3_2 : TransitionSources.Free 2412 0 (bank3 1490) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank3 1490)) 2412 = 38461460405172 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank3 1490)) 2413 = 38829384700176 := by decide +kernel
  refine ⟨rank3 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole4 : momentEstimate 150 33 = 14840297 := by
  refine moment_from_blocks [(128,12991155),(55,1849142)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank4 (u : ℕ) : P3_7_1.BankOK (bank4 u) :=
  P3_7_1.checked (bank4 u) (m:=108) (B:=150) (J:=33) (N:=39862927360) (M:=14840297) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole4
theorem free4_0 : TransitionSources.Free 2314 0 (bank4 1470) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank4 1470)) 2314 = 2380486885044 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank4 1470)) 2315 = 2747224810566 := by decide +kernel
  refine ⟨rank4 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free4_1 : TransitionSources.Free 2412 0 (bank4 1096) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank4 1096)) 2412 = 1363296776328 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank4 1096)) 2413 = 1559030800408 := by decide +kernel
  refine ⟨rank4 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole5 : momentEstimate 151 33 = 15158299 := by
  refine moment_from_blocks [(128,13203145),(56,1955154)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank5 (u : ℕ) : P3_7_1.BankOK (bank5 u) :=
  P3_7_1.checked (bank5 u) (m:=109) (B:=151) (J:=33) (N:=40687370240) (M:=15158299) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole5
theorem free5_0 : TransitionSources.Free 2314 0 (bank5 1462) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank5 1462)) 2314 = 2336949828752 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank5 1462)) 2315 = 2704042573078 := by decide +kernel
  refine ⟨rank5 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free5_1 : TransitionSources.Free 2412 0 (bank5 1094) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank5 1094)) 2412 = 1340176399860 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank5 1094)) 2413 = 1537522777050 := by decide +kernel
  refine ⟨rank5 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole6 : momentEstimate 154 34 = 16508386 := by
  refine moment_from_blocks [(128,14102380),(60,2406006)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank6 (u : ℕ) : P3_7_1.BankOK (bank6 u) :=
  P3_7_1.checked (bank6 u) (m:=111) (B:=154) (J:=34) (N:=43306188800) (M:=16508386) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole6
theorem free6_0 : TransitionSources.Free 2314 0 (bank6 1414) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank6 1414)) 2314 = 2324854384280 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank6 1414)) 2315 = 2690063999500 := by decide +kernel
  refine ⟨rank6 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free6_1 : TransitionSources.Free 2412 0 (bank6 1073) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank6 1073)) 2412 = 1365933805764 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank6 1073)) 2413 = 1567837727136 := by decide +kernel
  refine ⟨rank6 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole7 : momentEstimate 157 35 = 17945628 := by
  refine moment_from_blocks [(128,15022913),(64,2922715)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank7 (u : ℕ) : P3_7_1.BankOK (bank7 u) :=
  P3_7_1.checked (bank7 u) (m:=113) (B:=157) (J:=35) (N:=46031437824) (M:=17945628) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole7
private theorem pole8 : momentEstimate 158 35 = 18313194 := by
  refine moment_from_blocks [(128,15245787),(65,3067407)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank8 (u : ℕ) : P3_7_1.BankOK (bank8 u) :=
  P3_7_1.checked (bank8 u) (m:=114) (B:=158) (J:=35) (N:=46942126080) (M:=18313194) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole8
theorem free8_0 : TransitionSources.Free 2314 1 (bank8 1694) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank8 1694)) 2314 = 3521986083720 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank8 1694)) 2315 = 4084966224540 := by decide +kernel
  refine ⟨rank8 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free8_1 : TransitionSources.Free 2412 1 (bank8 1238) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank8 1238)) 2412 = 1938913756416 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank8 1238)) 2413 = 2227590561924 := by decide +kernel
  refine ⟨rank8 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole9 : momentEstimate 162 36 = 20261980 := by
  refine moment_from_blocks [(128,16419027),(70,3842953)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank9 (u : ℕ) : P3_7_1.BankOK (bank9 u) :=
  P3_7_1.checked (bank9 u) (m:=117) (B:=162) (J:=36) (N:=50775982080) (M:=20261980) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole9
theorem free9_0 : TransitionSources.Free 2314 1 (bank9 1624) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank9 1624)) 2314 = 3422382445625 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank9 1624)) 2315 = 3977474293000 := by decide +kernel
  refine ⟨rank9 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free9_1 : TransitionSources.Free 2412 1 (bank9 1210) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank9 1210)) 2412 = 1981040190318 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank9 1210)) 2413 = 2276890767284 := by decide +kernel
  refine ⟨rank9 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole10 : momentEstimate 165 36 = 21484793 := by
  refine moment_from_blocks [(128,17102917),(73,4381876)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank10 (u : ℕ) : P3_7_1.BankOK (bank10 u) :=
  P3_7_1.checked (bank10 u) (m:=119) (B:=165) (J:=36) (N:=52725547008) (M:=21484793) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole10
theorem free10_0 : TransitionSources.Free 2314 1 (bank10 1603) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank10 1603)) 2314 = 3368417834074 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank10 1603)) 2315 = 3927644087660 := by decide +kernel
  refine ⟨rank10 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free10_1 : TransitionSources.Free 2412 1 (bank10 1206) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank10 1206)) 2412 = 2003883488100 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank10 1206)) 2413 = 2307779758602 := by decide +kernel
  refine ⟨rank10 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free10_2 : TransitionSources.Free 2412 1 (bank10 1603) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank10 1603)) 2412 = 58172590685502 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank10 1603)) 2413 = 58731816939088 := by decide +kernel
  refine ⟨rank10 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole11 : momentEstimate 165 37 = 21934618 := by
  refine moment_from_blocks [(128,17387565),(74,4547053)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank11 (u : ℕ) : P3_7_1.BankOK (bank11 u) :=
  P3_7_1.checked (bank11 u) (m:=119) (B:=165) (J:=37) (N:=53801910272) (M:=21934618) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole11
theorem free11_0 : TransitionSources.Free 2314 1 (bank11 1580) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank11 1580)) 2314 = 3362038885029 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank11 1580)) 2315 = 3918922559157 := by decide +kernel
  refine ⟨rank11 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free11_1 : TransitionSources.Free 2412 1 (bank11 1192) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank11 1192)) 2412 = 2035729620339 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank11 1192)) 2413 = 2340048258635 := by decide +kernel
  refine ⟨rank11 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole12 : momentEstimate 166 37 = 22362213 := by
  refine moment_from_blocks [(128,17619745),(75,4742468)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank12 (u : ℕ) : P3_7_1.BankOK (bank12 u) :=
  P3_7_1.checked (bank12 u) (m:=120) (B:=166) (J:=37) (N:=54812999680) (M:=22362213) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole12
theorem free12_0 : TransitionSources.Free 2314 1 (bank12 1569) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank12 1569)) 2314 = 3406484656500 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank12 1569)) 2315 = 3961512519740 := by decide +kernel
  refine ⟨rank12 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free12_1 : TransitionSources.Free 2412 1 (bank12 1187) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank12 1187)) 2412 = 1939223567160 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank12 1187)) 2413 = 2244164986008 := by decide +kernel
  refine ⟨rank12 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole13 : momentEstimate 168 37 = 23234370 := by
  refine moment_from_blocks [(128,18084105),(77,5150265)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank13 (u : ℕ) : P3_7_1.BankOK (bank13 u) :=
  P3_7_1.checked (bank13 u) (m:=121) (B:=168) (J:=37) (N:=55834050560) (M:=23234370) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole13
theorem free13_0 : TransitionSources.Free 2314 1 (bank13 1553) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank13 1553)) 2314 = 3323604454170 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank13 1553)) 2315 = 3879159524100 := by decide +kernel
  refine ⟨rank13 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free13_1 : TransitionSources.Free 2412 1 (bank13 1183) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank13 1183)) 2412 = 1964698916640 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank13 1183)) 2413 = 2274171480960 := by decide +kernel
  refine ⟨rank13 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole14 : momentEstimate 172 38 = 25559185 := by
  refine moment_from_blocks [(128,19318585),(82,6240600)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank14 (u : ℕ) : P3_7_1.BankOK (bank14 u) :=
  P3_7_1.checked (bank14 u) (m:=124) (B:=172) (J:=38) (N:=60131901440) (M:=25559185) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole14
theorem free14_0 : TransitionSources.Free 2314 2 (bank14 1831) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank14 1831)) 2314 = 4838163324956 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank14 1831)) 2315 = 5663075430328 := by decide +kernel
  refine ⟨rank14 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free14_1 : TransitionSources.Free 2412 2 (bank14 1349) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank14 1349)) 2412 = 2765247767325 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank14 1349)) 2413 = 3195132984900 := by decide +kernel
  refine ⟨rank14 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole15 : momentEstimate 175 38 = 27010804 := by
  refine moment_from_blocks [(128,20027410),(85,6983394)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank15 (u : ℕ) : P3_7_1.BankOK (bank15 u) :=
  P3_7_1.checked (bank15 u) (m:=126) (B:=175) (J:=38) (N:=62309531648) (M:=27010804) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole15
private theorem pole16 : momentEstimate 175 39 = 27547813 := by
  refine moment_from_blocks [(128,20337130),(86,7210683)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank16 (u : ℕ) : P3_7_1.BankOK (bank16 u) :=
  P3_7_1.checked (bank16 u) (m:=126) (B:=175) (J:=39) (N:=63517491200) (M:=27547813) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole16
theorem free16_0 : TransitionSources.Free 2314 2 (bank16 1778) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank16 1778)) 2314 = 4870756186044 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank16 1778)) 2315 = 5692770842190 := by decide +kernel
  refine ⟨rank16 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free16_1 : TransitionSources.Free 2412 2 (bank16 1326) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank16 1326)) 2412 = 2761683406616 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank16 1326)) 2413 = 3200577369154 := by decide +kernel
  refine ⟨rank16 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free16_2 : TransitionSources.Free 2412 2 (bank16 1778) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank16 1778)) 2412 = 85428192488352 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank16 1778)) 2413 = 86250207144498 := by decide +kernel
  refine ⟨rank16 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole17 : momentEstimate 176 39 = 28054113 := by
  refine moment_from_blocks [(128,20577410),(87,7476703)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank17 (u : ℕ) : P3_7_1.BankOK (bank17 u) :=
  P3_7_1.checked (bank17 u) (m:=127) (B:=176) (J:=39) (N:=64644710400) (M:=28054113) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole17
theorem free17_0 : TransitionSources.Free 2314 2 (bank17 1760) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank17 1760)) 2314 = 4737382741596 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank17 1760)) 2315 = 5550761405970 := by decide +kernel
  refine ⟨rank17 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free17_1 : TransitionSources.Free 2412 2 (bank17 1319) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank17 1319)) 2412 = 2746743552960 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank17 1319)) 2413 = 3185299500240 := by decide +kernel
  refine ⟨rank17 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0588

-- Source: Research6969.TransitionBankChecks01
section Z6969Source0589
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole18 : momentEstimate 180 40 = 30727249 := by
  refine moment_from_blocks [(128,21859642),(92,8867607)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank18 (u : ℕ) : P3_7_1.BankOK (bank18 u) :=
  P3_7_1.checked (bank18 u) (m:=130) (B:=180) (J:=40) (N:=69377720320) (M:=30727249) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole18
theorem free18_0 : TransitionSources.Free 2314 2 (bank18 1703) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank18 1703)) 2314 = 4704699292152 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank18 1703)) 2315 = 5516356524720 := by decide +kernel
  refine ⟨rank18 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free18_1 : TransitionSources.Free 2412 2 (bank18 1295) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank18 1295)) 2412 = 2772588995856 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank18 1295)) 2413 = 3223125463104 := by decide +kernel
  refine ⟨rank18 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole19 : momentEstimate 184 41 = 33586892 := by
  refine moment_from_blocks [(128,23164358),(97,10422534)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank19 (u : ℕ) : P3_7_1.BankOK (bank19 u) :=
  P3_7_1.checked (bank19 u) (m:=133) (B:=184) (J:=41) (N:=74336174080) (M:=33586892) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole19
theorem free19_0 : TransitionSources.Free 2314 2 (bank19 1656) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank19 1656)) 2314 = 4591833584778 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank19 1656)) 2315 = 5408736924462 := by decide +kernel
  refine ⟨rank19 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free19_1 : TransitionSources.Free 2412 2 (bank19 1276) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank19 1276)) 2412 = 2863795283550 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank19 1276)) 2413 = 3329407172554 := by decide +kernel
  refine ⟨rank19 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole20 : momentEstimate 186 41 = 34768135 := by
  refine moment_from_blocks [(128,23660406),(99,11107729)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank20 (u : ℕ) : P3_7_1.BankOK (bank20 u) :=
  P3_7_1.checked (bank20 u) (m:=134) (B:=186) (J:=41) (N:=75585814528) (M:=34768135) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole20
theorem free20_0 : TransitionSources.Free 2314 3 (bank20 1970) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank20 1970)) 2314 = 6565604115492 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank20 1970)) 2315 = 7744202894826 := by decide +kernel
  refine ⟨rank20 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free20_1 : TransitionSources.Free 2412 3 (bank20 1460) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank20 1460)) 2412 = 3709442948364 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank20 1460)) 2413 = 4330863277038 := by decide +kernel
  refine ⟨rank20 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole21 : momentEstimate 187 41 = 35369225 := by
  refine moment_from_blocks [(128,23908430),(100,11460795)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank21 (u : ℕ) : P3_7_1.BankOK (bank21 u) :=
  P3_7_1.checked (bank21 u) (m:=135) (B:=187) (J:=41) (N:=76846465024) (M:=35369225) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole21
theorem free21_0 : TransitionSources.Free 2314 3 (bank21 1963) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank21 1963)) 2314 = 6553817687230 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank21 1963)) 2315 = 7735885054610 := by decide +kernel
  refine ⟨rank21 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free21_1 : TransitionSources.Free 2412 3 (bank21 1459) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank21 1459)) 2412 = 3756932830170 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank21 1459)) 2413 = 4383786199750 := by decide +kernel
  refine ⟨rank21 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole22 : momentEstimate 187 42 = 36021740 := by
  refine moment_from_blocks [(128,24238885),(101,11782855)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank22 (u : ℕ) : P3_7_1.BankOK (bank22 u) :=
  P3_7_1.checked (bank22 u) (m:=135) (B:=187) (J:=42) (N:=78229012480) (M:=36021740) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole22
theorem free22_0 : TransitionSources.Free 2314 3 (bank22 1937) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank22 1937)) 2314 = 6626320855104 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank22 1937)) 2315 = 7802726577321 := by decide +kernel
  refine ⟨rank22 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free22_1 : TransitionSources.Free 2412 3 (bank22 1443) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank22 1443)) 2412 = 3767526848060 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank22 1443)) 2413 = 4394244547770 := by decide +kernel
  refine ⟨rank22 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole23 : momentEstimate 190 42 = 37902732 := by
  refine moment_from_blocks [(128,24994180),(104,12908552)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank23 (u : ℕ) : P3_7_1.BankOK (bank23 u) :=
  P3_7_1.checked (bank23 u) (m:=137) (B:=190) (J:=42) (N:=80832888832) (M:=37902732) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole23
theorem free23_0 : TransitionSources.Free 2314 3 (bank23 1898) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank23 1898)) 2314 = 6485932721196 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank23 1898)) 2315 = 7648171682760 := by decide +kernel
  refine ⟨rank23 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free23_1 : TransitionSources.Free 2412 3 (bank23 1429) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank23 1429)) 2412 = 3735807113610 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank23 1429)) 2413 = 4368211547700 := by decide +kernel
  refine ⟨rank23 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole24 : momentEstimate 194 43 = 41244492 := by
  refine moment_from_blocks [(128,26348465),(109,14896027)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank24 (u : ℕ) : P3_7_1.BankOK (bank24 u) :=
  P3_7_1.checked (bank24 u) (m:=140) (B:=194) (J:=43) (N:=86317203456) (M:=41244492) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole24
theorem free24_0 : TransitionSources.Free 2314 3 (bank24 1838) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank24 1838)) 2314 = 6221186319696 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank24 1838)) 2315 = 7377670996680 := by decide +kernel
  refine ⟨rank24 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free24_1 : TransitionSources.Free 2412 3 (bank24 1404) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank24 1404)) 2412 = 3861039693180 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank24 1404)) 2413 = 4508855761240 := by decide +kernel
  refine ⟨rank24 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free24_2 : TransitionSources.Free 2412 3 (bank24 1838) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank24 1838)) 2412 = 119556684664128 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank24 1838)) 2413 = 120713169341112 := by decide +kernel
  refine ⟨rank24 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole25 : momentEstimate 198 44 = 44802338 := by
  refine moment_from_blocks [(128,27722385),(114,17079953)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank25 (u : ℕ) : P3_7_1.BankOK (bank25 u) :=
  P3_7_1.checked (bank25 u) (m:=143) (B:=198) (J:=44) (N:=92044001280) (M:=44802338) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole25
theorem free25_0 : TransitionSources.Free 2314 4 (bank25 2129) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank25 2129)) 2314 = 8800971193605 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank25 2129)) 2315 = 10445322495750 := by decide +kernel
  refine ⟨rank25 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free25_1 : TransitionSources.Free 2412 4 (bank25 1577) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank25 1577)) 2412 = 4948495449939 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank25 1577)) 2413 = 5814521821896 := by decide +kernel
  refine ⟨rank25 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole26 : momentEstimate 201 44 = 47009993 := by
  refine moment_from_blocks [(128,28499355),(117,18510638)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank26 (u : ℕ) : P3_7_1.BankOK (bank26 u) :=
  P3_7_1.checked (bank26 u) (m:=145) (B:=201) (J:=44) (N:=94934138880) (M:=47009993) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole26
theorem free26_0 : TransitionSources.Free 2314 4 (bank26 2102) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank26 2102)) 2314 = 8649371363808 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank26 2102)) 2315 = 10297980094830 := by decide +kernel
  refine ⟨rank26 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free26_1 : TransitionSources.Free 2412 4 (bank26 1570) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank26 1570)) 2412 = 4920502672638 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank26 1570)) 2413 = 5803310795962 := by decide +kernel
  refine ⟨rank26 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole27 : momentEstimate 205 45 = 50931776 := by
  refine moment_from_blocks [(128,29902507),(122,21029269)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank27 (u : ℕ) : P3_7_1.BankOK (bank27 u) :=
  P3_7_1.checked (bank27 u) (m:=148) (B:=205) (J:=45) (N:=101033181184) (M:=50931776) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole27
private theorem pole28 : momentEstimate 205 46 = 51790020 := by
  refine moment_from_blocks [(128,30259822),(123,21530198)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank28 (u : ℕ) : P3_7_1.BankOK (bank28 u) :=
  P3_7_1.checked (bank28 u) (m:=148) (B:=205) (J:=46) (N:=102693601280) (M:=51790020) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole28
theorem free28_0 : TransitionSources.Free 2314 4 (bank28 2005) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank28 2005)) 2314 = 8386546015893 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank28 2005)) 2315 = 10005343476675 := by decide +kernel
  refine ⟨rank28 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free28_1 : TransitionSources.Free 2412 4 (bank28 1523) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank28 1523)) 2412 = 4979728113930 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank28 1523)) 2413 = 5876295386070 := by decide +kernel
  refine ⟨rank28 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole29 : momentEstimate 208 46 = 54254747 := by
  refine moment_from_blocks [(128,31057459),(126,23197288)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank29 (u : ℕ) : P3_7_1.BankOK (bank29 u) :=
  P3_7_1.checked (bank29 u) (m:=150) (B:=208) (J:=46) (N:=105810755584) (M:=54254747) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole29
theorem free29_0 : TransitionSources.Free 2314 4 (bank29 1976) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank29 1976)) 2314 = 8493328280541 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank29 1976)) 2315 = 10107828832476 := by decide +kernel
  refine ⟨rank29 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free29_1 : TransitionSources.Free 2412 4 (bank29 1513) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank29 1513)) 2412 = 5033937077553 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank29 1513)) 2413 = 5942468891692 := by decide +kernel
  refine ⟨rank29 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole30 : momentEstimate 209 47 = 56002200 := by
  refine moment_from_blocks [(128,31684220),(128,24317980)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,True.intro⟩
theorem rank30 (u : ℕ) : P3_7_1.BankOK (bank30 u) :=
  P3_7_1.checked (bank30 u) (m:=151) (B:=209) (J:=47) (N:=109114818560) (M:=56002200) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole30
theorem free30_0 : TransitionSources.Free 2314 4 (bank30 1953) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank30 1953)) 2314 = 8430451752680 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank30 1953)) 2315 = 10053724590760 := by decide +kernel
  refine ⟨rank30 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free30_1 : TransitionSources.Free 2314 5 (bank30 2315) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank30 2315)) 2314 = 11829923663952 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank30 2315)) 2315 = 14110180428336 := by decide +kernel
  refine ⟨rank30 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free30_2 : TransitionSources.Free 2412 4 (bank30 1501) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank30 1501)) 2412 = 5176930765176 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank30 1501)) 2413 = 6097323729720 := by decide +kernel
  refine ⟨rank30 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free30_3 : TransitionSources.Free 2412 5 (bank30 1706) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank30 1706)) 2412 = 6631210512432 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank30 1706)) 2413 = 7819870020864 := by decide +kernel
  refine ⟨rank30 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole31 : momentEstimate 212 47 = 58616088 := by
  refine moment_from_blocks [(128,32491820),(128,26122790),(3,1478)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank31 (u : ℕ) : P3_7_1.BankOK (bank31 u) :=
  P3_7_1.checked (bank31 u) (m:=153) (B:=212) (J:=47) (N:=112361209856) (M:=58616088) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole31
theorem free31_0 : TransitionSources.Free 2314 4 (bank31 1925) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank31 1925)) 2314 = 8344605658176 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank31 1925)) 2315 = 9962789456880 := by decide +kernel
  refine ⟨rank31 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free31_1 : TransitionSources.Free 2314 5 (bank31 2263) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank31 2263)) 2314 = 11321773563264 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank31 2263)) 2315 = 13557491639040 := by decide +kernel
  refine ⟨rank31 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free31_2 : TransitionSources.Free 2412 4 (bank31 1491) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank31 1491)) 2412 = 5171195919936 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank31 1491)) 2413 = 6103024436384 := by decide +kernel
  refine ⟨rank31 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free31_3 : TransitionSources.Free 2412 5 (bank31 1686) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank31 1686)) 2412 = 6438165633984 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank31 1686)) 2413 = 7629322081136 := by decide +kernel
  refine ⟨rank31 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole32 : momentEstimate 215 47 = 61311840 := by
  refine moment_from_blocks [(128,33299420),(128,28005185),(6,7235)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank32 (u : ℕ) : P3_7_1.BankOK (bank32 u) :=
  P3_7_1.checked (bank32 u) (m:=155) (B:=215) (J:=47) (N:=115657932800) (M:=61311840) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole32
theorem free32_0 : TransitionSources.Free 2314 5 (bank32 2243) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank32 2243)) 2314 = 11490296038320 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank32 2243)) 2315 = 13746270381360 := by decide +kernel
  refine ⟨rank32 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free32_1 : TransitionSources.Free 2412 5 (bank32 1683) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank32 1683)) 2412 = 6757652703600 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank32 1683)) 2413 = 7976825323760 := by decide +kernel
  refine ⟨rank32 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole33 : momentEstimate 216 48 = 63235028 := by
  refine moment_from_blocks [(128,33942300),(128,29277828),(8,14900)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank33 (u : ℕ) : P3_7_1.BankOK (bank33 u) :=
  P3_7_1.checked (bank33 u) (m:=156) (B:=216) (J:=48) (N:=119176429568) (M:=63235028) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole33
theorem free33_0 : TransitionSources.Free 2314 4 (bank33 1882) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank33 1882)) 2314 = 8151595591384 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank33 1882)) 2315 = 9783526675160 := by decide +kernel
  refine ⟨rank33 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free33_1 : TransitionSources.Free 2314 5 (bank33 2191) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank33 2191)) 2314 = 11063381769472 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank33 2191)) 2315 = 13274700192080 := by decide +kernel
  refine ⟨rank33 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free33_2 : TransitionSources.Free 2412 4 (bank33 1472) := by
  have left : TransitionArithmetic.value (TransitionSources.request 4 (bank33 1472)) 2412 = 5084983901772 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 4 (bank33 1472)) 2413 = 6043225273968 := by decide +kernel
  refine ⟨rank33 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free33_3 : TransitionSources.Free 2412 5 (bank33 1655) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank33 1655)) 2412 = 6551315738928 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank33 1655)) 2413 = 7762404824712 := by decide +kernel
  refine ⟨rank33 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free33_4 : TransitionSources.Free 2412 5 (bank33 2191) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank33 2191)) 2412 = 227772587185056 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank33 2191)) 2413 = 229983905607664 := by decide +kernel
  refine ⟨rank33 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole34 : momentEstimate 220 49 = 68121522 := by
  refine moment_from_blocks [(128,35408100),(128,32659360),(13,54062)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank34 (u : ℕ) : P3_7_1.BankOK (bank34 u) :=
  P3_7_1.checked (bank34 u) (m:=159) (B:=220) (J:=49) (N:=126261657600) (M:=68121522) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole34
theorem free34_0 : TransitionSources.Free 2314 5 (bank34 2131) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank34 2131)) 2314 = 10982819783988 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank34 2131)) 2315 = 13188162035880 := by decide +kernel
  refine ⟨rank34 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free34_1 : TransitionSources.Free 2412 5 (bank34 1629) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank34 1629)) 2412 = 6703517294110 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank34 1629)) 2413 = 7940508859640 := by decide +kernel
  refine ⟨rank34 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole35 : momentEstimate 226 50 = 75401397 := by
  refine moment_from_blocks [(128,37445798),(128,37776354),(20,179245)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank35 (u : ℕ) : P3_7_1.BankOK (bank35 u) :=
  P3_7_1.checked (bank35 u) (m:=163) (B:=226) (J:=50) (N:=135467106304) (M:=75401397) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole35
theorem free35_0 : TransitionSources.Free 2314 5 (bank35 2061) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank35 2061)) 2314 = 10779580291000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank35 2061)) 2315 = 12987694477040 := by decide +kernel
  refine ⟨rank35 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free35_1 : TransitionSources.Free 2412 5 (bank35 1600) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank35 1600)) 2412 = 6839501817024 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank35 1600)) 2413 = 8116885862586 := by decide +kernel
  refine ⟨rank35 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0589

-- Source: Research6969.TransitionBankChecks02
section Z6969Source0590
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole36 : momentEstimate 227 50 = 76474675 := by
  refine moment_from_blocks [(128,37724479),(128,38544159),(21,206037)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank36 (u : ℕ) : P3_7_1.BankOK (bank36 u) :=
  P3_7_1.checked (bank36 u) (m:=164) (B:=227) (J:=50) (N:=137325445120) (M:=76474675) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole36
theorem free36_0 : TransitionSources.Free 2314 5 (bank36 2062) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank36 2062)) 2314 = 10903947855884 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank36 2062)) 2315 = 13133488040602 := by decide +kernel
  refine ⟨rank36 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free36_1 : TransitionSources.Free 2412 5 (bank36 1602) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank36 1602)) 2412 = 6725157360768 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank36 1602)) 2413 = 8016822534056 := by decide +kernel
  refine ⟨rank36 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole37 : momentEstimate 227 51 = 77637159 := by
  refine moment_from_blocks [(128,38100855),(128,39302019),(22,234285)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank37 (u : ℕ) : P3_7_1.BankOK (bank37 u) :=
  P3_7_1.checked (bank37 u) (m:=164) (B:=227) (J:=51) (N:=139361517568) (M:=77637159) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole37
theorem free37_0 : TransitionSources.Free 2314 5 (bank37 2039) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank37 2039)) 2314 = 10866587052360 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank37 2039)) 2315 = 13086017149560 := by decide +kernel
  refine ⟨rank37 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free37_1 : TransitionSources.Free 2412 5 (bank37 1587) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank37 1587)) 2412 = 6690532887372 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank37 1587)) 2413 = 7980989444884 := by decide +kernel
  refine ⟨rank37 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole38 : momentEstimate 230 51 = 80971087 := by
  refine moment_from_blocks [(128,38945907),(128,41686499),(25,338681)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank38 (u : ℕ) : P3_7_1.BankOK (bank38 u) :=
  P3_7_1.checked (bank38 u) (m:=166) (B:=230) (J:=51) (N:=143178334208) (M:=80971087) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole38
theorem free38_0 : TransitionSources.Free 2314 6 (bank38 2327) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank38 2327)) 2314 = 14416548568656 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank38 2327)) 2315 = 17376864149472 := by decide +kernel
  refine ⟨rank38 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free38_1 : TransitionSources.Free 2412 6 (bank38 1764) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank38 1764)) 2412 = 8413097353940 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank38 1764)) 2413 = 10045851569590 := by decide +kernel
  refine ⟨rank38 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole39 : momentEstimate 233 52 = 85660533 := by
  refine moment_from_blocks [(128,40174265),(128,44966936),(29,519332)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank39 (u : ℕ) : P3_7_1.BankOK (bank39 u) :=
  P3_7_1.checked (bank39 u) (m:=168) (B:=233) (J:=52) (N:=149189820416) (M:=85660533) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole39
theorem free39_0 : TransitionSources.Free 2314 5 (bank39 1983) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank39 1983)) 2314 = 10901078027424 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank39 1983)) 2315 = 13143022195520 := by decide +kernel
  refine ⟨rank39 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free39_1 : TransitionSources.Free 2412 5 (bank39 1564) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank39 1564)) 2412 = 7003648823355 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank39 1564)) 2413 = 8342228841030 := by decide +kernel
  refine ⟨rank39 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole40 : momentEstimate 237 53 = 91783289 := by
  refine moment_from_blocks [(128,41696505),(128,49261334),(34,825450)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank40 (u : ℕ) : P3_7_1.BankOK (bank40 u) :=
  P3_7_1.checked (bank40 u) (m:=171) (B:=237) (J:=53) (N:=157407510528) (M:=91783289) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole40
theorem free40_0 : TransitionSources.Free 2314 6 (bank40 2218) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank40 2218)) 2314 = 14052108805882 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank40 2218)) 2315 = 16997301146840 := by decide +kernel
  refine ⟨rank40 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free40_1 : TransitionSources.Free 2412 6 (bank40 1714) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank40 1714)) 2412 = 8433855112410 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank40 1714)) 2413 = 10121865076960 := by decide +kernel
  refine ⟨rank40 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole41 : momentEstimate 241 53 = 96837455 := by
  refine moment_from_blocks [(128,42846345),(128,52842795),(38,1148315)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank41 (u : ℕ) : P3_7_1.BankOK (bank41 u) :=
  P3_7_1.checked (bank41 u) (m:=174) (B:=241) (J:=53) (N:=163628974080) (M:=96837455) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole41
theorem free41_0 : TransitionSources.Free 2314 8 (bank41 2989) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank41 2989)) 2314 = 25689261300625 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank41 2989)) 2315 = 31208010293135 := by decide +kernel
  refine ⟨rank41 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free41_1 : TransitionSources.Free 2412 8 (bank41 2155) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank41 2155)) 2412 = 13765666177494 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank41 2155)) 2413 = 16519036391242 := by decide +kernel
  refine ⟨rank41 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole42 : momentEstimate 241 54 = 98228328 := by
  refine moment_from_blocks [(128,43230220),(128,53762848),(39,1235260)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank42 (u : ℕ) : P3_7_1.BankOK (bank42 u) :=
  P3_7_1.checked (bank42 u) (m:=174) (B:=241) (J:=54) (N:=165921423360) (M:=98228328) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole42
theorem free42_0 : TransitionSources.Free 2314 6 (bank42 2171) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank42 2171)) 2314 = 14065433719722 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank42 2171)) 2315 = 17026853905050 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free42_1 : TransitionSources.Free 2314 7 (bank42 2497) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank42 2497)) 2314 = 18154516030233 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank42 2497)) 2315 = 22071192203115 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free42_2 : TransitionSources.Free 2314 10 (bank42 4552) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank42 4552)) 2314 = 60287709794763 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank42 4552)) 2315 = 73296876422715 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free42_3 : TransitionSources.Free 2412 6 (bank42 1693) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank42 1693)) 2412 = 8542285589607 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank42 1693)) 2413 = 10270700968143 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free42_4 : TransitionSources.Free 2412 7 (bank42 1886) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank42 1886)) 2412 = 10798356986736 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank42 1886)) 2413 = 12943003105824 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free42_5 : TransitionSources.Free 2412 7 (bank42 2497) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank42 2497)) 2412 = 401988780972669 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank42 2497)) 2413 = 405905457145551 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free42_6 : TransitionSources.Free 2412 10 (bank42 2862) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank42 2862)) 2412 = 24560869427864 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank42 2862)) 2413 = 29496759255656 := by decide +kernel
  refine ⟨rank42 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole43 : momentEstimate 244 54 = 102199273 := by
  refine moment_from_blocks [(128,44100925),(128,56556632),(42,1541716)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank43 (u : ℕ) : P3_7_1.BankOK (bank43 u) :=
  P3_7_1.checked (bank43 u) (m:=176) (B:=244) (J:=54) (N:=170203545600) (M:=102199273) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole43
theorem free43_0 : TransitionSources.Free 2314 6 (bank43 2152) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank43 2152)) 2314 = 13838920928063 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank43 2152)) 2315 = 16816351453660 := by decide +kernel
  refine ⟨rank43 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free43_1 : TransitionSources.Free 2412 6 (bank43 1688) := by
  have left : TransitionArithmetic.value (TransitionSources.request 6 (bank43 1688)) 2412 = 8739881957697 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 6 (bank43 1688)) 2413 = 10498117494678 := by decide +kernel
  refine ⟨rank43 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole44 : momentEstimate 247 55 = 107778015 := by
  refine moment_from_blocks [(128,45360574),(128,60399763),(46,2017678)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank44 (u : ℕ) : P3_7_1.BankOK (bank44 u) :=
  P3_7_1.checked (bank44 u) (m:=178) (B:=247) (J:=55) (N:=176946151424) (M:=107778015) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole44
theorem free44_0 : TransitionSources.Free 2314 7 (bank44 2409) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank44 2409)) 2314 = 17760545094260 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank44 2409)) 2315 = 21641284558840 := by decide +kernel
  refine ⟨rank44 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free44_1 : TransitionSources.Free 2412 7 (bank44 1848) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank44 1848)) 2412 = 10659133948860 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank44 1848)) 2413 = 12850988046590 := by decide +kernel
  refine ⟨rank44 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole45 : momentEstimate 254 57 = 121131076 := by
  refine moment_from_blocks [(128,48191330),(128,69501528),(55,3438218)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank45 (u : ℕ) : P3_7_1.BankOK (bank45 u) :=
  P3_7_1.checked (bank45 u) (m:=183) (B:=254) (J:=57) (N:=193292926976) (M:=121131076) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole45
theorem free45_0 : TransitionSources.Free 2314 7 (bank45 2316) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank45 2316)) 2314 = 17798146201626 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank45 2316)) 2315 = 21704143068510 := by decide +kernel
  refine ⟨rank45 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free45_1 : TransitionSources.Free 2412 7 (bank45 1806) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank45 1806)) 2412 = 11360693683248 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank45 1806)) 2413 = 13640391280152 := by decide +kernel
  refine ⟨rank45 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole46 : momentEstimate 262 58 = 135575420 := by
  refine moment_from_blocks [(128,50968920),(128,79162439),(64,5444061)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank46 (u : ℕ) : P3_7_1.BankOK (bank46 u) :=
  P3_7_1.checked (bank46 u) (m:=189) (B:=262) (J:=58) (N:=210421678080) (M:=135575420) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole46
theorem free46_0 : TransitionSources.Free 2314 7 (bank46 2247) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank46 2247)) 2314 = 17699335960072 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank46 2247)) 2315 = 21657493963936 := by decide +kernel
  refine ⟨rank46 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free46_1 : TransitionSources.Free 2412 7 (bank46 1778) := by
  have left : TransitionArithmetic.value (TransitionSources.request 7 (bank46 1778)) 2412 = 11411059589220 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 7 (bank46 1778)) 2413 = 13789618916400 := by decide +kernel
  refine ⟨rank46 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole47 : momentEstimate 263 59 = 139044661 := by
  refine moment_from_blocks [(128,51652705),(128,81432887),(66,5959069)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank47 (u : ℕ) : P3_7_1.BankOK (bank47 u) :=
  P3_7_1.checked (bank47 u) (m:=190) (B:=263) (J:=59) (N:=215642275840) (M:=139044661) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole47
theorem free47_0 : TransitionSources.Free 2314 10 (bank47 3362) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank47 3362)) 2314 = 39454358822496 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank47 3362)) 2315 = 48516219787050 := by decide +kernel
  refine ⟨rank47 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free47_1 : TransitionSources.Free 2412 10 (bank47 2413) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank47 2413)) 2412 = 21179790522954 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank47 2413)) 2413 = 25660111102346 := by decide +kernel
  refine ⟨rank47 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole48 : momentEstimate 266 59 = 144192301 := by
  refine moment_from_blocks [(128,52561765),(128,84798061),(69,6832475)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank48 (u : ℕ) : P3_7_1.BankOK (bank48 u) :=
  P3_7_1.checked (bank48 u) (m:=192) (B:=266) (J:=59) (N:=220738355200) (M:=144192301) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole48
theorem free48_0 : TransitionSources.Free 2314 8 (bank48 2482) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank48 2482)) 2314 = 21938236552076 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank48 2482)) 2315 = 26984233543150 := by decide +kernel
  refine ⟨rank48 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free48_1 : TransitionSources.Free 2412 8 (bank48 1930) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank48 1930)) 2412 = 13899288751776 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank48 1930)) 2413 = 16827705165554 := by decide +kernel
  refine ⟨rank48 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole49 : momentEstimate 268 59 = 147695211 := by
  refine moment_from_blocks [(128,53167805),(128,87066329),(71,7461077)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank49 (u : ℕ) : P3_7_1.BankOK (bank49 u) :=
  P3_7_1.checked (bank49 u) (m:=193) (B:=268) (J:=59) (N:=223309987840) (M:=147695211) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole49
theorem free49_0 : TransitionSources.Free 2314 9 (bank49 2815) := by
  have left : TransitionArithmetic.value (TransitionSources.request 9 (bank49 2815)) 2314 = 28326006162432 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 9 (bank49 2815)) 2315 = 34910759093760 := by decide +kernel
  refine ⟨rank49 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free49_1 : TransitionSources.Free 2412 9 (bank49 2130) := by
  have left : TransitionArithmetic.value (TransitionSources.request 9 (bank49 2130)) 2412 = 16610905765416 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 9 (bank49 2130)) 2413 = 20229134198614 := by decide +kernel
  refine ⟨rank49 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole50 : momentEstimate 268 60 = 149605064 := by
  refine moment_from_blocks [(128,53550985),(128,88295282),(72,7758797)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank50 (u : ℕ) : P3_7_1.BankOK (bank50 u) :=
  P3_7_1.checked (bank50 u) (m:=193) (B:=268) (J:=60) (N:=226125676544) (M:=149605064) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole50
theorem free50_0 : TransitionSources.Free 2314 8 (bank50 2450) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank50 2450)) 2314 = 21866261879676 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank50 2450)) 2315 = 26931058829100 := by decide +kernel
  refine ⟨rank50 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free50_1 : TransitionSources.Free 2412 8 (bank50 1914) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank50 1914)) 2412 = 14270789263540 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank50 1914)) 2413 = 17237700081060 := by decide +kernel
  refine ⟨rank50 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole51 : momentEstimate 269 59 = 149468191 := by
  refine moment_from_blocks [(128,53470825),(128,88207645),(72,7789721)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank51 (u : ℕ) : P3_7_1.BankOK (bank51 u) :=
  P3_7_1.checked (bank51 u) (m:=194) (B:=269) (J:=59) (N:=225897349120) (M:=149468191) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole51
theorem free51_0 : TransitionSources.Free 2314 9 (bank51 2810) := by
  have left : TransitionArithmetic.value (TransitionSources.request 9 (bank51 2810)) 2314 = 28548983615472 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 9 (bank51 2810)) 2315 = 35158457719710 := by decide +kernel
  refine ⟨rank51 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free51_1 : TransitionSources.Free 2412 9 (bank51 2130) := by
  have left : TransitionArithmetic.value (TransitionSources.request 9 (bank51 2130)) 2412 = 17140774866516 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 9 (bank51 2130)) 2413 = 20785657847714 := by decide +kernel
  refine ⟨rank51 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole52 : momentEstimate 283 63 = 184912224 := by
  refine moment_from_blocks [(128,59310160),(128,110289399),(90,15312665)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank52 (u : ℕ) : P3_7_1.BankOK (bank52 u) :=
  P3_7_1.checked (bank52 u) (m:=204) (B:=283) (J:=63) (N:=265373614080) (M:=184912224) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole52
theorem free52_0 : TransitionSources.Free 2314 10 (bank52 2900) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank52 2900)) 2314 = 34524160366368 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank52 2900)) 2315 = 42741505673760 := by decide +kernel
  refine ⟨rank52 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free52_1 : TransitionSources.Free 2412 10 (bank52 2212) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank52 2212)) 2412 = 20767862525472 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank52 2212)) 2413 = 25356227750688 := by decide +kernel
  refine ⟨rank52 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free52_2 : TransitionSources.Free 2412 10 (bank52 2900) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank52 2900)) 2412 = 839824000490784 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank52 2900)) 2413 = 848041345798176 := by decide +kernel
  refine ⟨rank52 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole53 : momentEstimate 284 64 = 189280842 := by
  refine moment_from_blocks [(128,59992400),(128,112951047),(92,16337395)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank53 (u : ℕ) : P3_7_1.BankOK (bank53 u) :=
  P3_7_1.checked (bank53 u) (m:=205) (B:=284) (J:=64) (N:=271454044160) (M:=189280842) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole53
theorem free53_0 : TransitionSources.Free 2314 10 (bank53 2871) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank53 2871)) 2314 = 33927054366608 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank53 2871)) 2315 = 42155369465320 := by decide +kernel
  refine ⟨rank53 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free53_1 : TransitionSources.Free 2412 10 (bank53 2196) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank53 2196)) 2412 = 20466495950784 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank53 2196)) 2413 = 25086671269946 := by decide +kernel
  refine ⟨rank53 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0590

-- Source: Research6969.TransitionBankChecks03
section Z6969Source0591
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole54 : momentEstimate 294 65 = 214017359 := by
  refine moment_from_blocks [(128,63511536),(128,127348149),(103,23157674)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank54 (u : ℕ) : P3_7_1.BankOK (bank54 u) :=
  P3_7_1.checked (bank54 u) (m:=212) (B:=294) (J:=65) (N:=295979712512) (M:=214017359) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole54
theorem free54_0 : TransitionSources.Free 2314 10 (bank54 2755) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank54 2755)) 2314 = 32772254149336 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank54 2755)) 2315 = 40975835231708 := by decide +kernel
  refine ⟨rank54 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free54_1 : TransitionSources.Free 2412 10 (bank54 2149) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank54 2149)) 2412 = 21366248173200 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank54 2149)) 2413 = 26157023184250 := by decide +kernel
  refine ⟨rank54 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole55 : momentEstimate 298 67 = 228740750 := by
  refine moment_from_blocks [(128,65510775),(128,135769786),(109,27460189)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank55 (u : ℕ) : P3_7_1.BankOK (bank55 u) :=
  P3_7_1.checked (bank55 u) (m:=215) (B:=298) (J:=67) (N:=312397004800) (M:=228740750) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole55
theorem free55_0 : TransitionSources.Free 2314 9 (bank55 2427) := by
  have left : TransitionArithmetic.value (TransitionSources.request 9 (bank55 2427)) 2314 = 27376669694640 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 9 (bank55 2427)) 2315 = 34093156282920 := by decide +kernel
  refine ⟨rank55 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free55_1 : TransitionSources.Free 2412 9 (bank55 1948) := by
  have left : TransitionArithmetic.value (TransitionSources.request 9 (bank55 1948)) 2412 = 17708341140000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 9 (bank55 1948)) 2413 = 21860761651000 := by decide +kernel
  refine ⟨rank55 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole56 : momentEstimate 308 69 = 260075583 := by
  refine moment_from_blocks [(128,69431985),(128,152777862),(121,37865736)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank56 (u : ℕ) : P3_7_1.BankOK (bank56 u) :=
  P3_7_1.checked (bank56 u) (m:=222) (B:=308) (J:=69) (N:=343008870400) (M:=260075583) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole56
theorem free56_0 : TransitionSources.Free 2314 10 (bank56 2591) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank56 2591)) 2314 = 32913517957632 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank56 2591)) 2315 = 41283865900800 := by decide +kernel
  refine ⟨rank56 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free56_1 : TransitionSources.Free 2412 10 (bank56 2069) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank56 2069)) 2412 = 21399828017760 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank56 2069)) 2413 = 26522030854440 := by decide +kernel
  refine ⟨rank56 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole57 : momentEstimate 311 70 = 271261163 := by
  refine moment_from_blocks [(128,70749938),(128,158697864),(125,41813361)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank57 (u : ℕ) : P3_7_1.BankOK (bank57 u) :=
  P3_7_1.checked (bank57 u) (m:=224) (B:=311) (J:=70) (N:=353725317120) (M:=271261163) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole57
theorem free57_0 : TransitionSources.Free 2314 11 (bank57 2831) := by
  have left : TransitionArithmetic.value (TransitionSources.request 11 (bank57 2831)) 2314 = 39938273072928 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 11 (bank57 2831)) 2315 = 50255140860792 := by decide +kernel
  refine ⟨rank57 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free57_1 : TransitionSources.Free 2412 11 (bank57 2225) := by
  have left : TransitionArithmetic.value (TransitionSources.request 11 (bank57 2225)) 2412 = 26305307108766 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 11 (bank57 2225)) 2413 = 32421587736447 := by decide +kernel
  refine ⟨rank57 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole58 : momentEstimate 312 70 = 274069426 := by
  refine moment_from_blocks [(128,71075189),(128,160118696),(126,42875541)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank58 (u : ℕ) : P3_7_1.BankOK (bank58 u) :=
  P3_7_1.checked (bank58 u) (m:=225) (B:=312) (J:=70) (N:=357261639680) (M:=274069426) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole58
theorem free58_0 : TransitionSources.Free 2314 10 (bank58 2557) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank58 2557)) 2314 = 32819637499025 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank58 2557)) 2315 = 41285060064562 := by decide +kernel
  refine ⟨rank58 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free58_1 : TransitionSources.Free 2412 10 (bank58 2054) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank58 2054)) 2412 = 22613589365700 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank58 2054)) 2413 = 27856203832260 := by decide +kernel
  refine ⟨rank58 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole59 : momentEstimate 314 68 = 273591980 := by
  refine moment_from_blocks [(128,71008015),(128,159444372),(126,43139593)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank59 (u : ℕ) : P3_7_1.BankOK (bank59 u) :=
  P3_7_1.checked (bank59 u) (m:=225) (B:=314) (J:=68) (N:=349597597696) (M:=273591980) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole59
private theorem pole60 : momentEstimate 314 69 = 276676118 := by
  refine moment_from_blocks [(128,71373225),(128,161211655),(127,44091238)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank60 (u : ℕ) : P3_7_1.BankOK (bank60 u) :=
  P3_7_1.checked (bank60 u) (m:=225) (B:=314) (J:=69) (N:=353440890880) (M:=276676118) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole60
private theorem pole61 : momentEstimate 315 71 = 285699863 := by
  refine moment_from_blocks [(128,72392562),(128,166141448),(128,47164909),(2,944)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank61 (u : ℕ) : P3_7_1.BankOK (bank61 u) :=
  P3_7_1.checked (bank61 u) (m:=227) (B:=315) (J:=71) (N:=368270376960) (M:=285699863) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole61
theorem free61_0 : TransitionSources.Free 2314 10 (bank61 2536) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank61 2536)) 2314 = 33903610636072 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank61 2536)) 2315 = 42498276556850 := by decide +kernel
  refine ⟨rank61 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free61_1 : TransitionSources.Free 2412 10 (bank61 2044) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank61 2044)) 2412 = 22985120544660 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank61 2044)) 2413 = 28343506260790 := by decide +kernel
  refine ⟨rank61 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole62 : momentEstimate 328 74 = 335760609 := by
  refine moment_from_blocks [(128,77654350),(128,190660982),(128,67248352),(18,196925)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank62 (u : ℕ) : P3_7_1.BankOK (bank62 u) :=
  P3_7_1.checked (bank62 u) (m:=237) (B:=328) (J:=74) (N:=418217984000) (M:=335760609) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole62
theorem free62_0 : TransitionSources.Free 2314 14 (bank62 3617) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank62 3617)) 2314 = 72566444384289 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank62 3617)) 2315 = 92173148134290 := by decide +kernel
  refine ⟨rank62 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free62_1 : TransitionSources.Free 2412 14 (bank62 2724) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank62 2724)) 2412 = 42171245600775 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank62 2724)) 2413 = 52843170477350 := by decide +kernel
  refine ⟨rank62 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole63 : momentEstimate 332 74 = 349077659 := by
  refine moment_from_blocks [(128,78980450),(128,196632000),(128,73117734),(22,347475)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank63 (u : ℕ) : P3_7_1.BankOK (bank63 u) :=
  P3_7_1.checked (bank63 u) (m:=239) (B:=332) (J:=74) (N:=426141286400) (M:=349077659) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole63
theorem free63_0 : TransitionSources.Free 2314 12 (bank63 2899) := by
  have left : TransitionArithmetic.value (TransitionSources.request 12 (bank63 2899)) 2314 = 47815117960450 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 12 (bank63 2899)) 2315 = 60704541174500 := by decide +kernel
  refine ⟨rank63 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free63_1 : TransitionSources.Free 2412 12 (bank63 2304) := by
  have left : TransitionArithmetic.value (TransitionSources.request 12 (bank63 2304)) 2412 = 32182113712995 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 12 (bank63 2304)) 2413 = 39995683404130 := by decide +kernel
  refine ⟨rank63 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole64 : momentEstimate 337 74 = 366224034 := by
  refine moment_from_blocks [(128,80638075),(128,204096000),(128,80864348),(27,625611)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank64 (u : ℕ) : P3_7_1.BankOK (bank64 u) :=
  P3_7_1.checked (bank64 u) (m:=243) (B:=337) (J:=74) (N:=442223820800) (M:=366224034) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole64
theorem free64_0 : TransitionSources.Free 2314 14 (bank64 3514) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank64 3514)) 2314 = 71468830991970 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank64 3514)) 2315 = 90966058767450 := by decide +kernel
  refine ⟨rank64 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free64_1 : TransitionSources.Free 2412 14 (bank64 2688) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank64 2688)) 2412 = 44123591551101 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank64 2688)) 2413 = 55072366450499 := by decide +kernel
  refine ⟨rank64 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole65 : momentEstimate 350 78 = 430562752 := by
  refine moment_from_blocks [(128,86245485),(128,232217024),(128,109511800),(44,2588443)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank65 (u : ℕ) : P3_7_1.BankOK (bank65 u) :=
  P3_7_1.checked (bank65 u) (m:=252) (B:=350) (J:=78) (N:=498909577216) (M:=430562752) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole65
theorem free65_0 : TransitionSources.Free 2314 15 (bank65 3612) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank65 3612)) 2314 = 83228843676056 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank65 3612)) 2315 = 106454702330800 := by decide +kernel
  refine ⟨rank65 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free65_1 : TransitionSources.Free 2412 15 (bank65 2772) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank65 2772)) 2412 = 51231941168808 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank65 2772)) 2413 = 64359628664672 := by decide +kernel
  refine ⟨rank65 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free65_2 : TransitionSources.Free 2412 15 (bank65 3612) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank65 3612)) 2412 = 2359362991840968 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank65 3612)) 2413 = 2382588850495712 := by decide +kernel
  refine ⟨rank65 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole66 : momentEstimate 355 79 = 455042366 := by
  refine moment_from_blocks [(128,88229060),(128,242178560),(128,120855724),(50,3779022)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank66 (u : ℕ) : P3_7_1.BankOK (bank66 u) :=
  P3_7_1.checked (bank66 u) (m:=256) (B:=355) (J:=79) (N:=521718988800) (M:=455042366) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole66
theorem free66_0 : TransitionSources.Free 2314 15 (bank66 3528) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank66 3528)) 2314 = 80098945157408 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank66 3528)) 2315 = 103131446664580 := by decide +kernel
  refine ⟨rank66 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free66_1 : TransitionSources.Free 2412 15 (bank66 2733) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank66 2733)) 2412 = 51340223562744 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank66 2733)) 2413 = 64605029638256 := by decide +kernel
  refine ⟨rank66 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole67 : momentEstimate 355 80 = 459454565 := by
  refine moment_from_blocks [(128,88515612),(128,244358208),(128,122582790),(51,3997955)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank67 (u : ℕ) : P3_7_1.BankOK (bank67 u) :=
  P3_7_1.checked (bank67 u) (m:=256) (B:=355) (J:=80) (N:=526651490304) (M:=459454565) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole67
theorem free67_0 : TransitionSources.Free 2314 16 (bank67 3891) := by
  have left : TransitionArithmetic.value (TransitionSources.request 16 (bank67 3891)) 2314 = 100360775039924 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 16 (bank67 3891)) 2315 = 128708694046408 := by decide +kernel
  refine ⟨rank67 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free67_1 : TransitionSources.Free 2412 16 (bank67 2944) := by
  have left : TransitionArithmetic.value (TransitionSources.request 16 (bank67 2944)) 2412 = 60422211617670 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 16 (bank67 2944)) 2413 = 75996284343850 := by decide +kernel
  refine ⟨rank67 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole68 : momentEstimate 359 80 = 476279615 := by
  refine moment_from_blocks [(128,89872956),(128,250682688),(128,130708443),(55,5015528)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank68 (u : ℕ) : P3_7_1.BankOK (bank68 u) :=
  P3_7_1.checked (bank68 u) (m:=259) (B:=359) (J:=80) (N:=540538306560) (M:=476279615) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole68
theorem free68_0 : TransitionSources.Free 2314 14 (bank68 3168) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank68 3168)) 2314 = 67798845614120 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank68 3168)) 2315 = 86997020510350 := by decide +kernel
  refine ⟨rank68 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free68_1 : TransitionSources.Free 2412 14 (bank68 2518) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank68 2518)) 2412 = 44979852539160 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank68 2518)) 2413 = 56619136810390 := by decide +kernel
  refine ⟨rank68 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole69 : momentEstimate 360 82 = 489737381 := by
  refine moment_from_blocks [(128,90760500),(128,256702400),(128,136423691),(58,5850790)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank69 (u : ℕ) : P3_7_1.BankOK (bank69 u) :=
  P3_7_1.checked (bank69 u) (m:=260) (B:=360) (J:=82) (N:=555371724800) (M:=489737381) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole69
theorem free69_0 : TransitionSources.Free 2314 18 (bank69 4787) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank69 4787)) 2314 = 157615888308606 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank69 4787)) 2315 = 202744433913084 := by decide +kernel
  refine ⟨rank69 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free69_1 : TransitionSources.Free 2412 18 (bank69 3442) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank69 3442)) 2412 = 84105953567790 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank69 3442)) 2413 = 106496230557178 := by decide +kernel
  refine ⟨rank69 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole70 : momentEstimate 361 79 = 480182166 := by
  refine moment_from_blocks [(128,90258020),(128,251578880),(128,133034380),(56,5310886)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank70 (u : ℕ) : P3_7_1.BankOK (bank70 u) :=
  P3_7_1.checked (bank70 u) (m:=260) (B:=361) (J:=79) (N:=540090040320) (M:=480182166) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole70
theorem free70_0 : TransitionSources.Free 2314 15 (bank70 3511) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank70 3511)) 2314 = 82338255504864 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank70 3511)) 2315 = 105930143418240 := by decide +kernel
  refine ⟨rank70 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free70_1 : TransitionSources.Free 2412 15 (bank70 2735) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank70 2735)) 2412 = 53312943479616 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank70 2735)) 2413 = 67051804109184 := by decide +kernel
  refine ⟨rank70 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole71 : momentEstimate 363 82 = 502963348 := by
  refine moment_from_blocks [(128,91785135),(128,261531008),(128,142833277),(61,6813928)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank71 (u : ℕ) : P3_7_1.BankOK (bank71 u) :=
  P3_7_1.checked (bank71 u) (m:=262) (B:=363) (J:=82) (N:=564966981632) (M:=502963348) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole71
theorem free71_0 : TransitionSources.Free 2314 12 (bank71 2671) := by
  have left : TransitionArithmetic.value (TransitionSources.request 12 (bank71 2671)) 2314 = 48825598815728 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 12 (bank71 2671)) 2315 = 63094124802184 := by decide +kernel
  refine ⟨rank71 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free71_1 : TransitionSources.Free 2412 12 (bank71 2198) := by
  have left : TransitionArithmetic.value (TransitionSources.request 12 (bank71 2198)) 2412 = 36091244174352 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 12 (bank71 2198)) 2413 = 45364586390748 := by decide +kernel
  refine ⟨rank71 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0591

-- Source: Research6969.TransitionBankChecks04
section Z6969Source0592
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole72 : momentEstimate 369 83 = 535097333 := by
  refine moment_from_blocks [(128,94100055),(128,273501312),(128,158049746),(68,9446220)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank72 (u : ℕ) : P3_7_1.BankOK (bank72 u) :=
  P3_7_1.checked (bank72 u) (m:=266) (B:=369) (J:=83) (N:=589745881088) (M:=535097333) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole72
theorem free72_0 : TransitionSources.Free 2314 13 (bank72 2841) := by
  have left : TransitionArithmetic.value (TransitionSources.request 13 (bank72 2841)) 2314 = 57409090324642 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 13 (bank72 2841)) 2315 = 74250108975266 := by decide +kernel
  refine ⟨rank72 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free72_1 : TransitionSources.Free 2412 13 (bank72 2320) := by
  have left : TransitionArithmetic.value (TransitionSources.request 13 (bank72 2320)) 2412 = 41216027536134 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 13 (bank72 2320)) 2413 = 51994064487640 := by decide +kernel
  refine ⟨rank72 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole73 : momentEstimate 373 83 = 553942033 := by
  refine moment_from_blocks [(128,95470375),(128,279995520),(128,167232504),(72,11243634)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank73 (u : ℕ) : P3_7_1.BankOK (bank73 u) :=
  P3_7_1.checked (bank73 u) (m:=269) (B:=373) (J:=83) (N:=604708536320) (M:=553942033) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole73
theorem free73_0 : TransitionSources.Free 2314 20 (bank73 5660) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank73 5660)) 2314 = 228517281679626 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank73 5660)) 2315 = 296713313742600 := by decide +kernel
  refine ⟨rank73 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free73_1 : TransitionSources.Free 2412 20 (bank73 3927) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank73 3927)) 2412 = 115240756820664 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank73 3927)) 2413 = 146744737319016 := by decide +kernel
  refine ⟨rank73 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole74 : momentEstimate 373 84 = 559058208 := by
  refine moment_from_blocks [(128,95728105),(128,282341440),(128,169295835),(73,11692828)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank74 (u : ℕ) : P3_7_1.BankOK (bank74 u) :=
  P3_7_1.checked (bank74 u) (m:=269) (B:=373) (J:=84) (N:=610154577920) (M:=559058208) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole74
theorem free74_0 : TransitionSources.Free 2314 13 (bank74 2818) := by
  have left : TransitionArithmetic.value (TransitionSources.request 13 (bank74 2818)) 2314 = 59027850126294 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 13 (bank74 2818)) 2315 = 76132781092140 := by decide +kernel
  refine ⟨rank74 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free74_1 : TransitionSources.Free 2314 16 (bank74 3583) := by
  have left : TransitionArithmetic.value (TransitionSources.request 16 (bank74 3583)) 2314 = 93851512790784 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 16 (bank74 3583)) 2315 = 121496968803840 := by decide +kernel
  refine ⟨rank74 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free74_2 : TransitionSources.Free 2314 21 (bank74 6544) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank74 6544)) 2314 = 310796611424145 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank74 6544)) 2315 = 402978981994050 := by decide +kernel
  refine ⟨rank74 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free74_3 : TransitionSources.Free 2412 13 (bank74 2309) := by
  have left : TransitionArithmetic.value (TransitionSources.request 13 (bank74 2309)) 2412 = 40857171594855 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 13 (bank74 2309)) 2413 = 51877512229620 := by decide +kernel
  refine ⟨rank74 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free74_4 : TransitionSources.Free 2412 16 (bank74 2799) := by
  have left : TransitionArithmetic.value (TransitionSources.request 16 (bank74 2799)) 2412 = 59625355231400 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 16 (bank74 2799)) 2413 = 75815465101600 := by decide +kernel
  refine ⟨rank74 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free74_5 : TransitionSources.Free 2412 21 (bank74 4330) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank74 4330)) 2412 = 141662866177158 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank74 4330)) 2413 = 180393156483912 := by decide +kernel
  refine ⟨rank74 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole75 : momentEstimate 377 84 = 578534598 := by
  refine moment_from_blocks [(128,97102385),(128,288891200),(128,178775763),(77,13765250)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank75 (u : ℕ) : P3_7_1.BankOK (bank75 u) :=
  P3_7_1.checked (bank75 u) (m:=272) (B:=377) (J:=84) (N:=625462476800) (M:=578534598) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole75
theorem free75_0 : TransitionSources.Free 2314 20 (bank75 5459) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank75 5459)) 2314 = 218437655891910 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank75 5459)) 2315 = 283909624389300 := by decide +kernel
  refine ⟨rank75 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free75_1 : TransitionSources.Free 2412 20 (bank75 3842) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank75 3842)) 2412 = 111335585350374 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank75 3842)) 2413 = 142456217312556 := by decide +kernel
  refine ⟨rank75 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole76 : momentEstimate 377 85 = 583814440 := by
  refine moment_from_blocks [(128,97352129),(128,291268928),(128,180914893),(78,14278490)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank76 (u : ℕ) : P3_7_1.BankOK (bank76 u) :=
  P3_7_1.checked (bank76 u) (m:=272) (B:=377) (J:=85) (N:=631028580352) (M:=583814440) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole76
theorem free76_0 : TransitionSources.Free 2314 18 (bank76 4276) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank76 4276)) 2314 = 137553739536395 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank76 4276)) 2315 = 178180722211765 := by decide +kernel
  refine ⟨rank76 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free76_1 : TransitionSources.Free 2412 18 (bank76 3214) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank76 3214)) 2412 = 79857207660600 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank76 3214)) 2413 = 101883175232600 := by decide +kernel
  refine ⟨rank76 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole77 : momentEstimate 382 83 = 597984703 := by
  refine moment_from_blocks [(128,98553595),(128,294607488),(128,188698448),(81,16125172)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank77 (u : ℕ) : P3_7_1.BankOK (bank77 u) :=
  P3_7_1.checked (bank77 u) (m:=275) (B:=382) (J:=83) (N:=635228389376) (M:=597984703) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole77
theorem free77_0 : TransitionSources.Free 2314 20 (bank77 5503) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank77 5503)) 2314 = 226840618678784 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank77 5503)) 2315 = 294524065757440 := by decide +kernel
  refine ⟨rank77 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free77_1 : TransitionSources.Free 2412 20 (bank77 3883) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank77 3883)) 2412 = 119113664542272 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank77 3883)) 2413 = 151453457427128 := by decide +kernel
  refine ⟨rank77 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole78 : momentEstimate 383 83 = 603020643 := by
  refine moment_from_blocks [(128,98896175),(128,296231040),(128,191148910),(82,16744518)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank78 (u : ℕ) : P3_7_1.BankOK (bank78 u) :=
  P3_7_1.checked (bank78 u) (m:=275) (B:=383) (J:=83) (N:=635228389376) (M:=603020643) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole78
private theorem pole79 : momentEstimate 383 84 = 608607683 := by
  refine moment_from_blocks [(128,99163805),(128,298715840),(128,193398103),(83,17329935)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank79 (u : ℕ) : P3_7_1.BankOK (bank79 u) :=
  P3_7_1.checked (bank79 u) (m:=275) (B:=383) (J:=84) (N:=640970915840) (M:=608607683) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole79
private theorem pole80 : momentEstimate 383 87 = 625236061 := by
  refine moment_from_blocks [(128,99894630),(128,306023168),(128,200154426),(86,19163837)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank80 (u : ℕ) : P3_7_1.BankOK (bank80 u) :=
  P3_7_1.checked (bank80 u) (m:=275) (B:=383) (J:=87) (N:=658033868800) (M:=625236061) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole80
private theorem pole81 : momentEstimate 383 83 = 603020643 := by
  refine moment_from_blocks [(128,98896175),(128,296231040),(128,191148910),(82,16744518)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank81 (u : ℕ) : P3_7_1.BankOK (bank81 u) :=
  P3_7_1.checked (bank81 u) (m:=276) (B:=383) (J:=83) (N:=640392101888) (M:=603020643) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole81
theorem free81_0 : TransitionSources.Free 2314 20 (bank81 5502) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank81 5502)) 2314 = 228110369757500 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank81 5502)) 2315 = 296148942241282 := by decide +kernel
  refine ⟨rank81 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free81_1 : TransitionSources.Free 2412 20 (bank81 3885) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank81 3885)) 2412 = 117942633380550 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank81 3885)) 2413 = 150496590367694 := by decide +kernel
  refine ⟨rank81 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole82 : momentEstimate 384 86 = 624925184 := by
  refine moment_from_blocks [(128,100008153),(128,305276736),(128,200420644),(86,19219651)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank82 (u : ℕ) : P3_7_1.BankOK (bank82 u) :=
  P3_7_1.checked (bank82 u) (m:=277) (B:=384) (J:=86) (N:=663023779840) (M:=624925184) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole82
theorem free82_0 : TransitionSources.Free 2314 14 (bank82 2965) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank82 2965)) 2314 = 67740246808849 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank82 2965)) 2315 = 88198030825274 := by decide +kernel
  refine ⟨rank82 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free82_1 : TransitionSources.Free 2412 14 (bank82 2422) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank82 2422)) 2412 = 46476642310812 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank82 2422)) 2413 = 59576282703856 := by decide +kernel
  refine ⟨rank82 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole83 : momentEstimate 390 87 = 662678389 := by
  refine moment_from_blocks [(128,102318590),(128,317771520),(128,218189305),(93,24398974)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank83 (u : ℕ) : P3_7_1.BankOK (bank83 u) :=
  P3_7_1.checked (bank83 u) (m:=281) (B:=390) (J:=87) (N:=690560696320) (M:=662678389) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole83
theorem free83_0 : TransitionSources.Free 2314 13 (bank83 2752) := by
  have left : TransitionArithmetic.value (TransitionSources.request 13 (bank83 2752)) 2314 = 61803701965964 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 13 (bank83 2752)) 2315 = 80160088495594 := by decide +kernel
  refine ⟨rank83 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free83_1 : TransitionSources.Free 2314 21 (bank83 5597) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank83 5597)) 2314 = 247868072410104 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank83 5597)) 2315 = 323750556104724 := by decide +kernel
  refine ⟨rank83 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free83_2 : TransitionSources.Free 2412 13 (bank83 2285) := by
  have left : TransitionArithmetic.value (TransitionSources.request 13 (bank83 2285)) 2412 = 43891298700336 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 13 (bank83 2285)) 2413 = 56035371916332 := by decide +kernel
  refine ⟨rank83 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free83_3 : TransitionSources.Free 2412 21 (bank83 3955) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank83 3955)) 2412 = 129071111805216 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank83 3955)) 2413 = 165431850084392 := by decide +kernel
  refine ⟨rank83 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free83_4 : TransitionSources.Free 2412 21 (bank83 5597) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank83 5597)) 2412 = 7684351474482864 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank83 5597)) 2413 = 7760233958177484 := by decide +kernel
  refine ⟨rank83 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole84 : momentEstimate 391 87 = 668148909 := by
  refine moment_from_blocks [(128,102664870),(128,319449856),(128,220815505),(94,25218678)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank84 (u : ℕ) : P3_7_1.BankOK (bank84 u) :=
  P3_7_1.checked (bank84 u) (m:=282) (B:=391) (J:=87) (N:=696062574592) (M:=668148909) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole84
theorem free84_0 : TransitionSources.Free 2314 21 (bank84 5564) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank84 5564)) 2314 = 245464229313240 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank84 5564)) 2315 = 320826071407590 := by decide +kernel
  refine ⟨rank84 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free84_1 : TransitionSources.Free 2412 21 (bank84 3942) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank84 3942)) 2412 = 127656853867496 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank84 3942)) 2413 = 163957536292018 := by decide +kernel
  refine ⟨rank84 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole85 : momentEstimate 395 89 = 702503867 := by
  refine moment_from_blocks [(128,104499330),(128,331231680),(128,236402695),(100,30370162)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank85 (u : ℕ) : P3_7_1.BankOK (bank85 u) :=
  P3_7_1.checked (bank85 u) (m:=285) (B:=395) (J:=89) (N:=724956610560) (M:=702503867) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole85
theorem free85_0 : TransitionSources.Free 2314 14 (bank85 2903) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank85 2903)) 2314 = 70078855044396 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank85 2903)) 2315 = 91457404243260 := by decide +kernel
  refine ⟨rank85 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free85_1 : TransitionSources.Free 2412 14 (bank85 2394) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank85 2394)) 2412 = 50687136851490 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank85 2394)) 2413 = 64639661972960 := by decide +kernel
  refine ⟨rank85 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole86 : momentEstimate 398 89 = 719781707 := by
  refine moment_from_blocks [(128,105542970),(128,336346560),(128,244608950),(103,33283227)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank86 (u : ℕ) : P3_7_1.BankOK (bank86 u) :=
  P3_7_1.checked (bank86 u) (m:=287) (B:=398) (J:=89) (N:=736375603200) (M:=719781707) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole86
theorem free86_0 : TransitionSources.Free 2314 18 (bank86 3897) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank86 3897)) 2314 = 125123355014582 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank86 3897)) 2315 = 164195172681340 := by decide +kernel
  refine ⟨rank86 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free86_1 : TransitionSources.Free 2314 20 (bank86 4712) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank86 4712)) 2314 = 184092010069062 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank86 4712)) 2315 = 241208230032690 := by decide +kernel
  refine ⟨rank86 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free86_2 : TransitionSources.Free 2412 18 (bank86 3038) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank86 3038)) 2412 = 78844603198248 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank86 3038)) 2413 = 101631274961502 := by decide +kernel
  refine ⟨rank86 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free86_3 : TransitionSources.Free 2412 20 (bank86 3512) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank86 3512)) 2412 = 107301215548206 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank86 3512)) 2413 = 137749865366634 := by decide +kernel
  refine ⟨rank86 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole87 : momentEstimate 398 90 = 725984075 := by
  refine moment_from_blocks [(128,105752920),(128,338881088),(128,247147643),(104,34202424)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank87 (u : ℕ) : P3_7_1.BankOK (bank87 u) :=
  P3_7_1.checked (bank87 u) (m:=287) (B:=398) (J:=90) (N:=742561677312) (M:=725984075) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole87
theorem free87_0 : TransitionSources.Free 2314 18 (bank87 3887) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank87 3887)) 2314 = 126674214610320 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank87 3887)) 2315 = 165969169532352 := by decide +kernel
  refine ⟨rank87 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free87_1 : TransitionSources.Free 2314 20 (bank87 4698) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank87 4698)) 2314 = 184777240427000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank87 4698)) 2315 = 242172376862050 := by decide +kernel
  refine ⟨rank87 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free87_2 : TransitionSources.Free 2412 18 (bank87 3031) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank87 3031)) 2412 = 81894836013048 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank87 3031)) 2413 = 104824535618704 := by decide +kernel
  refine ⟨rank87 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free87_3 : TransitionSources.Free 2412 20 (bank87 3502) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank87 3502)) 2412 = 106969554575064 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank87 3502)) 2413 = 137574191001790 := by decide +kernel
  refine ⟨rank87 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole88 : momentEstimate 409 92 = 805907535 := by
  refine moment_from_blocks [(128,109990015),(128,363054144),(128,283804970),(117,49058406)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank88 (u : ℕ) : P3_7_1.BankOK (bank88 u) :=
  P3_7_1.checked (bank88 u) (m:=295) (B:=409) (J:=92) (N:=802732113920) (M:=805907535) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole88
theorem free88_0 : TransitionSources.Free 2314 14 (bank88 2848) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank88 2848)) 2314 = 73861325839455 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank88 2848)) 2315 = 96551138491500 := by decide +kernel
  refine ⟨rank88 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free88_1 : TransitionSources.Free 2412 14 (bank88 2372) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank88 2372)) 2412 = 53183381318487 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank88 2372)) 2413 = 68287006657590 := by decide +kernel
  refine ⟨rank88 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole89 : momentEstimate 411 92 = 818632570 := by
  refine moment_from_blocks [(128,110689995),(128,366542016),(128,289683297),(119,51717262)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank89 (u : ℕ) : P3_7_1.BankOK (bank89 u) :=
  P3_7_1.checked (bank89 u) (m:=296) (B:=411) (J:=92) (N:=808826961920) (M:=818632570) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole89
theorem free89_0 : TransitionSources.Free 2314 18 (bank89 3732) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank89 3732)) 2314 = 123656006027310 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank89 3732)) 2315 = 162976971444534 := by decide +kernel
  refine ⟨rank89 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free89_1 : TransitionSources.Free 2314 21 (bank89 4866) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank89 4866)) 2314 = 211753232423124 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank89 4866)) 2315 = 278588885734872 := by decide +kernel
  refine ⟨rank89 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free89_2 : TransitionSources.Free 2314 25 (bank89 8176) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank89 8176)) 2314 = 594043830787706 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank89 8176)) 2315 = 782683827888742 := by decide +kernel
  refine ⟨rank89 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free89_3 : TransitionSources.Free 2412 18 (bank89 2959) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank89 2959)) 2412 = 80845861718160 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank89 2959)) 2413 = 104566781296880 := by decide +kernel
  refine ⟨rank89 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free89_4 : TransitionSources.Free 2412 21 (bank89 3630) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank89 3630)) 2412 = 122933199337536 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank89 3630)) 2413 = 158625947042292 := by decide +kernel
  refine ⟨rank89 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free89_5 : TransitionSources.Free 2412 25 (bank89 5201) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank89 5201)) 2412 = 249672979417734 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank89 5201)) 2413 = 322926011262270 := by decide +kernel
  refine ⟨rank89 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0592

-- Source: Research6969.TransitionBankChecks05
section Z6969Source0593
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole90 : momentEstimate 416 94 = 865230227 := by
  refine moment_from_blocks [(128,112807655),(128,380601920),(128,310327642),(126,61493010)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank90 (u : ℕ) : P3_7_1.BankOK (bank90 u) :=
  P3_7_1.checked (bank90 u) (m:=300) (B:=416) (J:=94) (N:=846999060480) (M:=865230227) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole90
theorem free90_0 : TransitionSources.Free 2314 18 (bank90 3666) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank90 3666)) 2314 = 123701216714258 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank90 3666)) 2315 = 163330324791630 := by decide +kernel
  refine ⟨rank90 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free90_1 : TransitionSources.Free 2412 18 (bank90 2925) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank90 2925)) 2412 = 84423507640087 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank90 2925)) 2413 = 108633756018788 := by decide +kernel
  refine ⟨rank90 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole91 : momentEstimate 419 95 = 892659430 := by
  refine moment_from_blocks [(128,114031096),(128,388574208),(128,322425894),(128,67626976),(2,1256)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank91 (u : ℕ) : P3_7_1.BankOK (bank91 u) :=
  P3_7_1.checked (bank91 u) (m:=302) (B:=419) (J:=95) (N:=866513846272) (M:=892659430) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole91
theorem free91_0 : TransitionSources.Free 2314 20 (bank91 4262) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank91 4262)) 2314 = 173679541104888 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank91 4262)) 2315 = 228542379296868 := by decide +kernel
  refine ⟨rank91 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free91_1 : TransitionSources.Free 2412 20 (bank91 3297) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank91 3297)) 2412 = 108035639605008 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank91 3297)) 2413 = 139541262966488 := by decide +kernel
  refine ⟨rank91 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole92 : momentEstimate 430 95 = 970134630 := by
  refine moment_from_blocks [(128,117900632),(128,408173568),(128,356871523),(128,87081925),(13,106982)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank92 (u : ℕ) : P3_7_1.BankOK (bank92 u) :=
  P3_7_1.checked (bank92 u) (m:=310) (B:=430) (J:=95) (N:=918657433600) (M:=970134630) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole92
theorem free92_0 : TransitionSources.Free 2314 23 (bank92 5432) := by
  have left : TransitionArithmetic.value (TransitionSources.request 23 (bank92 5432)) 2314 = 285650364156456 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 23 (bank92 5432)) 2315 = 379316293325340 := by decide +kernel
  refine ⟨rank92 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free92_1 : TransitionSources.Free 2412 23 (bank92 3992) := by
  have left : TransitionArithmetic.value (TransitionSources.request 23 (bank92 3992)) 2412 = 160858494445968 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 23 (bank92 3992)) 2413 = 209402994514692 := by decide +kernel
  refine ⟨rank92 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole93 : momentEstimate 433 97 = 1008070710 := by
  refine moment_from_blocks [(128,119279720),(128,419104448),(128,372899362),(128,96525680),(18,261500)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank93 (u : ℕ) : P3_7_1.BankOK (bank93 u) :=
  P3_7_1.checked (bank93 u) (m:=313) (B:=433) (J:=97) (N:=953437126656) (M:=1008070710) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole93
theorem free93_0 : TransitionSources.Free 2314 15 (bank93 2947) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank93 2947)) 2314 = 87775934600442 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank93 2947)) 2315 = 116271000206394 := by decide +kernel
  refine ⟨rank93 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free93_1 : TransitionSources.Free 2412 15 (bank93 2467) := by
  have left : TransitionArithmetic.value (TransitionSources.request 15 (bank93 2467)) 2412 = 65349540188298 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 15 (bank93 2467)) 2413 = 84512194258890 := by decide +kernel
  refine ⟨rank93 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole94 : momentEstimate 434 97 = 1015567563 := by
  refine moment_from_blocks [(128,119632520),(128,420910784),(128,376143104),(128,98576755),(19,304400)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank94 (u : ℕ) : P3_7_1.BankOK (bank94 u) :=
  P3_7_1.checked (bank94 u) (m:=313) (B:=434) (J:=97) (N:=953437126656) (M:=1015567563) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole94
theorem free94_0 : TransitionSources.Free 2314 30 (bank94 16634) := by
  have left : TransitionArithmetic.value (TransitionSources.request 30 (bank94 16634)) 2314 = 2725323194518440 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 30 (bank94 16634)) 2315 = 3636047573657850 := by decide +kernel
  refine ⟨rank94 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free94_1 : TransitionSources.Free 2412 30 (bank94 7943) := by
  have left : TransitionArithmetic.value (TransitionSources.request 30 (bank94 7943)) 2412 = 644894802522792 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 30 (bank94 7943)) 2413 = 844171043776608 := by decide +kernel
  refine ⟨rank94 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole95 : momentEstimate 434 98 = 1023606650 := by
  refine moment_from_blocks [(128,119779770),(128,423669312),(128,379388205),(128,100418518),(20,350845)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank95 (u : ℕ) : P3_7_1.BankOK (bank95 u) :=
  P3_7_1.checked (bank95 u) (m:=313) (B:=434) (J:=98) (N:=960795770880) (M:=1023606650) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole95
theorem free95_0 : TransitionSources.Free 2314 16 (bank95 3103) := by
  have left : TransitionArithmetic.value (TransitionSources.request 16 (bank95 3103)) 2314 = 96368485861120 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 16 (bank95 3103)) 2315 = 128398918313600 := by decide +kernel
  refine ⟨rank95 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free95_1 : TransitionSources.Free 2412 16 (bank95 2576) := by
  have left : TransitionArithmetic.value (TransitionSources.request 16 (bank95 2576)) 2412 = 70405094211408 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 16 (bank95 2576)) 2413 = 91588543457532 := by decide +kernel
  refine ⟨rank95 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole96 : momentEstimate 435 98 = 1031203184 := by
  refine moment_from_blocks [(128,120133035),(128,425487744),(128,382660988),(128,102518612),(21,402805)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank96 (u : ℕ) : P3_7_1.BankOK (bank96 u) :=
  P3_7_1.checked (bank96 u) (m:=314) (B:=435) (J:=98) (N:=967673118720) (M:=1031203184) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole96
theorem free96_0 : TransitionSources.Free 2314 17 (bank96 3290) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank96 3290)) 2314 = 110249268711780 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank96 3290)) 2315 = 146411432496186 := by decide +kernel
  refine ⟨rank96 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free96_1 : TransitionSources.Free 2412 17 (bank96 2705) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank96 2705)) 2412 = 78585732980568 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank96 2705)) 2413 = 102044211122469 := by decide +kernel
  refine ⟨rank96 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole97 : momentEstimate 438 99 = 1062483026 := by
  refine moment_from_blocks [(128,121332175),(128,433718400),(128,395844997),(128,110926997),(25,660457)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank97 (u : ℕ) : P3_7_1.BankOK (bank97 u) :=
  P3_7_1.checked (bank97 u) (m:=316) (B:=438) (J:=99) (N:=989003776000) (M:=1062483026) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole97
theorem free97_0 : TransitionSources.Free 2314 17 (bank97 3273) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank97 3273)) 2314 = 112074878567628 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank97 3273)) 2315 = 148693906230880 := by decide +kernel
  refine ⟨rank97 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free97_1 : TransitionSources.Free 2412 17 (bank97 2697) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank97 2697)) 2412 = 81188895426548 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank97 2697)) 2413 = 105049750841352 := by decide +kernel
  refine ⟨rank97 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole98 : momentEstimate 442 100 = 1102455756 := by
  refine moment_from_blocks [(128,122878519),(128,443831168),(128,412575637),(128,122056100),(30,1114332)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank98 (u : ℕ) : P3_7_1.BankOK (bank98 u) :=
  P3_7_1.checked (bank98 u) (m:=319) (B:=442) (J:=100) (N:=1017758351360) (M:=1102455756) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole98
theorem free98_0 : TransitionSources.Free 2314 17 (bank98 3253) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank98 3253)) 2314 = 111172807529913 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank98 3253)) 2315 = 148335127026900 := by decide +kernel
  refine ⟨rank98 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free98_1 : TransitionSources.Free 2412 17 (bank98 2688) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank98 2688)) 2412 = 80767214908779 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank98 2688)) 2413 = 105117229562666 := by decide +kernel
  refine ⟨rank98 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole99 : momentEstimate 446 101 = 1143545315 := by
  refine moment_from_blocks [(128,124418801),(128,454006080),(128,429573945),(128,133805277),(35,1741212)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank99 (u : ℕ) : P3_7_1.BankOK (bank99 u) :=
  P3_7_1.checked (bank99 u) (m:=322) (B:=446) (J:=101) (N:=1047064739840) (M:=1143545315) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole99
theorem free99_0 : TransitionSources.Free 2314 17 (bank99 3235) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank99 3235)) 2314 = 111357641949424 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank99 3235)) 2315 = 149107239816944 := by decide +kernel
  refine ⟨rank99 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free99_1 : TransitionSources.Free 2412 17 (bank99 2680) := by
  have left : TransitionArithmetic.value (TransitionSources.request 17 (bank99 2680)) 2412 = 80151031183104 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 17 (bank99 2680)) 2413 = 105012662878774 := by decide +kernel
  refine ⟨rank99 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole100 : momentEstimate 453 98 = 1174588250 := by
  refine moment_from_blocks [(128,126491805),(128,458219520),(128,442616253),(128,144853052),(39,2407620)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank100 (u : ℕ) : P3_7_1.BankOK (bank100 u) :=
  P3_7_1.checked (bank100 u) (m:=325) (B:=453) (J:=98) (N:=1045036793856) (M:=1174588250) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole100
private theorem pole101 : momentEstimate 453 100 = 1193036697 := by
  refine moment_from_blocks [(128,126773685),(128,464095808),(128,449949269),(128,149441447),(41,2776488)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank101 (u : ℕ) : P3_7_1.BankOK (bank101 u) :=
  P3_7_1.checked (bank101 u) (m:=325) (B:=453) (J:=100) (N:=1061047500800) (M:=1193036697) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole101
private theorem pole102 : momentEstimate 453 102 = 1211360939 := by
  refine moment_from_blocks [(128,127017540),(128,469838208),(128,457230201),(128,154094395),(43,3180595)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank102 (u : ℕ) : P3_7_1.BankOK (bank102 u) :=
  P3_7_1.checked (bank102 u) (m:=325) (B:=453) (J:=102) (N:=1076928184320) (M:=1211360939) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole102
private theorem pole103 : momentEstimate 458 103 = 1264296353 := by
  refine moment_from_blocks [(128,128901890),(128,482044160),(128,478390594),(128,170286937),(49,4672772)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank103 (u : ℕ) : P3_7_1.BankOK (bank103 u) :=
  P3_7_1.checked (bank103 u) (m:=330) (B:=458) (J:=103) (N:=1122512142336) (M:=1264296353) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole103
theorem free103_0 : TransitionSources.Free 2314 18 (bank103 3373) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank103 3373)) 2314 = 127894435125184 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank103 3373)) 2315 = 171879593865140 := by decide +kernel
  refine ⟨rank103 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free103_1 : TransitionSources.Free 2314 25 (bank103 5586) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank103 5586)) 2314 = 354155499352564 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank103 5586)) 2315 = 474750093478462 := by decide +kernel
  refine ⟨rank103 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free103_2 : TransitionSources.Free 2412 18 (bank103 2789) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank103 2789)) 2412 = 90699740325000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank103 2789)) 2413 = 119557168928460 := by decide +kernel
  refine ⟨rank103 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free103_3 : TransitionSources.Free 2412 25 (bank103 4148) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank103 4148)) 2412 = 201446176804272 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank103 4148)) 2413 = 265256013954078 := by decide +kernel
  refine ⟨rank103 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole104 : momentEstimate 460 104 = 1291682639 := by
  refine moment_from_blocks [(128,129714410),(128,488664960),(128,489209505),(128,178529829),(52,5563935)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank104 (u : ℕ) : P3_7_1.BankOK (bank104 u) :=
  P3_7_1.checked (bank104 u) (m:=332) (B:=460) (J:=104) (N:=1146054246400) (M:=1291682639) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole104
theorem free104_0 : TransitionSources.Free 2314 18 (bank104 3359) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank104 3359)) 2314 = 127516938336480 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank104 3359)) 2315 = 171911879664000 := by decide +kernel
  refine ⟨rank104 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free104_1 : TransitionSources.Free 2412 18 (bank104 2782) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank104 2782)) 2412 = 95384339464392 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank104 2782)) 2413 = 124608553896838 := by decide +kernel
  refine ⟨rank104 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole105 : momentEstimate 474 107 = 1453763546 := by
  refine moment_from_blocks [(128,134959905),(128,523960704),(128,551511264),(128,230420396),(69,12911277)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank105 (u : ℕ) : P3_7_1.BankOK (bank105 u) :=
  P3_7_1.checked (bank105 u) (m:=342) (B:=474) (J:=107) (N:=1251092201472) (M:=1453763546) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole105
theorem free105_0 : TransitionSources.Free 2314 18 (bank105 3304) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank105 3304)) 2314 = 134552679281140 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank105 3304)) 2315 = 181296679618160 := by decide +kernel
  refine ⟨rank105 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free105_1 : TransitionSources.Free 2412 18 (bank105 2759) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank105 2759)) 2412 = 97879682804400 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank105 2759)) 2413 = 129157493877840 := by decide +kernel
  refine ⟨rank105 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole106 : momentEstimate 477 107 = 1483537364 := by
  refine moment_from_blocks [(128,136028565),(128,529725312),(128,562530684),(128,240569057),(72,14683746)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank106 (u : ℕ) : P3_7_1.BankOK (bank106 u) :=
  P3_7_1.checked (bank106 u) (m:=344) (B:=477) (J:=107) (N:=1267512901632) (M:=1483537364) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole106
theorem free106_0 : TransitionSources.Free 2314 19 (bank106 3476) := by
  have left : TransitionArithmetic.value (TransitionSources.request 19 (bank106 3476)) 2314 = 149558101298718 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 19 (bank106 3476)) 2315 = 201919753497522 := by decide +kernel
  refine ⟨rank106 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free106_1 : TransitionSources.Free 2412 19 (bank106 2882) := by
  have left : TransitionArithmetic.value (TransitionSources.request 19 (bank106 2882)) 2412 = 107194874000796 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 19 (bank106 2882)) 2413 = 141735307381692 := by decide +kernel
  refine ⟨rank106 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole107 : momentEstimate 482 108 = 1545109193 := by
  refine moment_from_blocks [(128,137885545),(128,542300288),(128,585187132),(128,261062438),(78,18673790)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank107 (u : ℕ) : P3_7_1.BankOK (bank107 u) :=
  P3_7_1.checked (bank107 u) (m:=348) (B:=482) (J:=108) (N:=1309818224640) (M:=1545109193) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole107
theorem free107_1 : TransitionSources.Free 2412 18 (bank107 3286) := by
  have left : TransitionArithmetic.value (TransitionSources.request 18 (bank107 3286)) 2412 = 4859621395257276 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 18 (bank107 3286)) 2413 = 4907795992939810 := by decide +kernel
  refine ⟨rank107 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0593

-- Source: Research6969.TransitionBankChecks06
section Z6969Source0594
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole108 : momentEstimate 483 108 = 1555432583 := by
  refine moment_from_blocks [(128,138241975),(128,544232640),(128,588898410),(128,264648918),(79,19410640)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank108 (u : ℕ) : P3_7_1.BankOK (bank108 u) :=
  P3_7_1.checked (bank108 u) (m:=348) (B:=483) (J:=108) (N:=1309818224640) (M:=1555432583) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole108
theorem free108_0 : TransitionSources.Free 2314 21 (bank108 3859) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank108 3859)) 2314 = 189487867720060 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank108 3859)) 2315 = 256185845612300 := by decide +kernel
  refine ⟨rank108 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free108_1 : TransitionSources.Free 2314 30 (bank108 8100) := by
  have left : TransitionArithmetic.value (TransitionSources.request 30 (bank108 8100)) 2314 = 822690989991926 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 30 (bank108 8100)) 2315 = 1116421384246600 := by decide +kernel
  refine ⟨rank108 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free108_2 : TransitionSources.Free 2412 21 (bank108 3149) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank108 3149)) 2412 = 133039022611950 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank108 3149)) 2413 = 175657651271550 := by decide +kernel
  refine ⟨rank108 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free108_3 : TransitionSources.Free 2412 30 (bank108 5498) := by
  have left : TransitionArithmetic.value (TransitionSources.request 30 (bank108 5498)) 2412 = 392324296931892 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 30 (bank108 5498)) 2413 = 522182328674058 := by decide +kernel
  refine ⟨rank108 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole109 : momentEstimate 484 109 = 1576951631 := by
  refine moment_from_blocks [(128,138667375),(128,549116480),(128,596895140),(128,271375802),(81,20896834)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank109 (u : ℕ) : P3_7_1.BankOK (bank109 u) :=
  P3_7_1.checked (bank109 u) (m:=349) (B:=484) (J:=109) (N:=1327400222720) (M:=1576951631) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole109
theorem free109_0 : TransitionSources.Free 2314 20 (bank109 3631) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank109 3631)) 2314 = 168590367758704 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank109 3631)) 2315 = 228393179830160 := by decide +kernel
  refine ⟨rank109 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free109_1 : TransitionSources.Free 2412 20 (bank109 2996) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank109 2996)) 2412 = 120621750924582 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank109 2996)) 2413 = 159691590150408 := by decide +kernel
  refine ⟨rank109 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole110 : momentEstimate 491 109 = 1651411016 := by
  refine moment_from_blocks [(128,141163715),(128,562717760),(128,623093075),(128,297533216),(88,26903250)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank110 (u : ℕ) : P3_7_1.BankOK (bank110 u) :=
  P3_7_1.checked (bank110 u) (m:=354) (B:=491) (J:=109) (N:=1370293534720) (M:=1651411016) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole110
theorem free110_0 : TransitionSources.Free 2314 21 (bank110 3824) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank110 3824)) 2314 = 186358026260025 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank110 3824)) 2315 = 254575604730375 := by decide +kernel
  refine ⟨rank110 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free110_1 : TransitionSources.Free 2412 21 (bank110 3137) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank110 3137)) 2412 = 136434966915783 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank110 3137)) 2413 = 180489962623857 := by decide +kernel
  refine ⟨rank110 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole111 : momentEstimate 495 111 = 1718934918 := by
  refine moment_from_blocks [(128,142711212),(128,576511488),(128,647159296),(128,319781038),(94,32771884)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank111 (u : ℕ) : P3_7_1.BankOK (bank111 u) :=
  P3_7_1.checked (bank111 u) (m:=357) (B:=495) (J:=111) (N:=1415598571520) (M:=1718934918) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole111
theorem free111_0 : TransitionSources.Free 2314 20 (bank111 3583) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank111 3583)) 2314 = 168056081700864 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank111 3583)) 2315 = 229921261731840 := by decide +kernel
  refine ⟨rank111 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free111_1 : TransitionSources.Free 2412 20 (bank111 2977) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank111 2977)) 2412 = 127927789227144 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank111 2977)) 2413 = 168912569868096 := by decide +kernel
  refine ⟨rank111 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole112 : momentEstimate 506 113 = 1870272531 := by
  refine moment_from_blocks [(128,146735860),(128,604207296),(128,698529984),(128,372215375),(107,48584016)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank112 (u : ℕ) : P3_7_1.BankOK (bank112 u) :=
  P3_7_1.checked (bank112 u) (m:=365) (B:=506) (J:=113) (N:=1507599056896) (M:=1870272531) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole112
theorem free112_0 : TransitionSources.Free 2314 20 (bank112 3547) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank112 3547)) 2314 = 172918665997428 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank112 3547)) 2315 = 237264332234352 := by decide +kernel
  refine ⟨rank112 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free112_1 : TransitionSources.Free 2412 20 (bank112 2964) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank112 2964)) 2412 = 130411970979030 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank112 2964)) 2413 = 173529301594450 := by decide +kernel
  refine ⟨rank112 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole113 : momentEstimate 506 114 = 1883005203 := by
  refine moment_from_blocks [(128,146776110),(128,607192640),(128,703284800),(128,375863078),(108,49888575)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank113 (u : ℕ) : P3_7_1.BankOK (bank113 u) :=
  P3_7_1.checked (bank113 u) (m:=365) (B:=506) (J:=114) (N:=1517607976960) (M:=1883005203) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole113
theorem free113_0 : TransitionSources.Free 2314 21 (bank113 3716) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank113 3716)) 2314 = 190979598183192 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank113 3716)) 2315 = 262185693020370 := by decide +kernel
  refine ⟨rank113 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free113_1 : TransitionSources.Free 2412 21 (bank113 3080) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank113 3080)) 2412 = 138585270957588 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank113 3080)) 2413 = 185526434170662 := by decide +kernel
  refine ⟨rank113 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole114 : momentEstimate 509 114 = 1919120263 := by
  refine moment_from_blocks [(128,147848025),(128,613176320),(128,714920960),(128,388883014),(111,54291944)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank114 (u : ℕ) : P3_7_1.BankOK (bank114 u) :=
  P3_7_1.checked (bank114 u) (m:=367) (B:=509) (J:=114) (N:=1536268697600) (M:=1919120263) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole114
theorem free114_0 : TransitionSources.Free 2314 21 (bank114 3710) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank114 3710)) 2314 = 195563405386956 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank114 3710)) 2315 = 267356556687450 := by decide +kernel
  refine ⟨rank114 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free114_1 : TransitionSources.Free 2412 21 (bank114 3080) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank114 3080)) 2412 = 143741000998803 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank114 3080)) 2413 = 191222930394327 := by decide +kernel
  refine ⟨rank114 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole115 : momentEstimate 510 115 = 1944295055 := by
  refine moment_from_blocks [(128,148240547),(128,618155648),(128,723635840),(128,397015628),(113,57247392)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank115 (u : ℕ) : P3_7_1.BankOK (bank115 u) :=
  P3_7_1.checked (bank115 u) (m:=368) (B:=510) (J:=115) (N:=1555815727104) (M:=1944295055) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole115
theorem free115_0 : TransitionSources.Free 2314 20 (bank115 3521) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank115 3521)) 2314 = 173539124546268 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank115 3521)) 2315 = 238992195171888 := by decide +kernel
  refine ⟨rank115 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free115_1 : TransitionSources.Free 2412 20 (bank115 2949) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank115 2949)) 2412 = 129731697051100 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank115 2949)) 2413 = 173791028904600 := by decide +kernel
  refine ⟨rank115 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole116 : momentEstimate 524 118 = 2163592004 := by
  refine moment_from_blocks [(128,153323765),(128,655333952),(128,793762368),(128,473343210),(128,87827138),(2,1571)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank116 (u : ℕ) : P3_7_1.BankOK (bank116 u) :=
  P3_7_1.checked (bank116 u) (m:=378) (B:=524) (J:=118) (N:=1684225392640) (M:=2163592004) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole116
theorem free116_0 : TransitionSources.Free 2314 20 (bank116 3482) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank116 3482)) 2314 = 188011184013198 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank116 3482)) 2315 = 257133507988140 := by decide +kernel
  refine ⟨rank116 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free116_1 : TransitionSources.Free 2314 21 (bank116 3644) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank116 3644)) 2314 = 197649996801705 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank116 3644)) 2315 = 273347305909650 := by decide +kernel
  refine ⟨rank116 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free116_2 : TransitionSources.Free 2412 20 (bank116 2935) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank116 2935)) 2412 = 136093666042236 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank116 2935)) 2413 = 183217680534784 := by decide +kernel
  refine ⟨rank116 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free116_3 : TransitionSources.Free 2412 21 (bank116 3050) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank116 3050)) 2412 = 148344492050370 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank116 3050)) 2413 = 199232319762000 := by decide +kernel
  refine ⟨rank116 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole117 : momentEstimate 526 119 = 2204525073 := by
  refine moment_from_blocks [(128,154057030),(128,662373120),(128,806880000),(128,487129687),(128,94073703),(5,11533)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank117 (u : ℕ) : P3_7_1.BankOK (bank117 u) :=
  P3_7_1.checked (bank117 u) (m:=380) (B:=526) (J:=119) (N:=1715056148480) (M:=2204525073) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole117
theorem free117_0 : TransitionSources.Free 2314 41 (bank117 49199) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank117 49199)) 2314 = 36110229595987200 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank117 49199)) 2315 = 50116160550972000 := by decide +kernel
  refine ⟨rank117 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free117_1 : TransitionSources.Free 2412 41 (bank117 13588) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank117 13588)) 2412 = 2871942854164272 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank117 13588)) 2413 = 3897090742215678 := by decide +kernel
  refine ⟨rank117 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole118 : momentEstimate 527 118 = 2203657519 := by
  refine moment_from_blocks [(128,154396550),(128,661434368),(128,805711872),(128,487834896),(128,94268278),(5,11555)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank118 (u : ℕ) : P3_7_1.BankOK (bank118 u) :=
  P3_7_1.checked (bank118 u) (m:=380) (B:=527) (J:=118) (N:=1704221474816) (M:=2203657519) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole118
theorem free118_0 : TransitionSources.Free 2314 21 (bank118 3641) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank118 3641)) 2314 = 199595423953968 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank118 3641)) 2315 = 276009651099525 := by decide +kernel
  refine ⟨rank118 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free118_1 : TransitionSources.Free 2412 21 (bank118 3051) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank118 3051)) 2412 = 144817521613044 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank118 3051)) 2413 = 196303472947246 := by decide +kernel
  refine ⟨rank118 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole119 : momentEstimate 529 120 = 2259708309 := by
  refine moment_from_blocks [(128,155144506),(128,671459008),(128,824108736),(128,506040929),(128,102905218),(9,49912)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank119 (u : ℕ) : P3_7_1.BankOK (bank119 u) :=
  P3_7_1.checked (bank119 u) (m:=382) (B:=529) (J:=120) (N:=1746249449472) (M:=2259708309) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole119
theorem free119_0 : TransitionSources.Free 2314 41 (bank119 41691) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank119 41691)) 2314 = 26461924475149730 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank119 41691)) 2315 = 36712705242168144 := by decide +kernel
  refine ⟨rank119 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free119_1 : TransitionSources.Free 2412 41 (bank119 12995) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank119 12995)) 2412 = 2681938909036962 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank119 12995)) 2413 = 3637593131778324 := by decide +kernel
  refine ⟨rank119 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole120 : momentEstimate 532 120 = 2301165208 := by
  refine moment_from_blocks [(128,156217534),(128,677615488),(128,836212608),(128,520984652),(128,110027945),(12,106981)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank120 (u : ℕ) : P3_7_1.BankOK (bank120 u) :=
  P3_7_1.checked (bank120 u) (m:=384) (B:=532) (J:=120) (N:=1766771916800) (M:=2301165208) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole120
theorem free120_0 : TransitionSources.Free 2314 41 (bank120 36262) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank120 36262)) 2314 = 20090088263902568 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank120 36262)) 2315 = 27927885343688392 := by decide +kernel
  refine ⟨rank120 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free120_1 : TransitionSources.Free 2412 41 (bank120 12477) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank120 12477)) 2412 = 2478876375286430 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank120 12477)) 2413 = 3369277344586594 := by decide +kernel
  refine ⟨rank120 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole121 : momentEstimate 535 121 = 2358160566 := by
  refine moment_from_blocks [(128,157302042),(128,686740928),(128,853644736),(128,540481589),(128,119756779),(16,234492)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank121 (u : ℕ) : P3_7_1.BankOK (bank121 u) :=
  P3_7_1.checked (bank121 u) (m:=386) (B:=535) (J:=121) (N:=1798595411968) (M:=2358160566) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole121
theorem free121_0 : TransitionSources.Free 2314 41 (bank121 32187) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank121 32187)) 2314 = 16150689360995410 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank121 32187)) 2315 = 22443532440287582 := by decide +kernel
  refine ⟨rank121 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free121_1 : TransitionSources.Free 2412 41 (bank121 11999) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank121 11999)) 2412 = 2347910552970000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank121 11999)) 2413 = 3187085036694000 := by decide +kernel
  refine ⟨rank121 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole122 : momentEstimate 535 123 = 2388083183 := by
  refine moment_from_blocks [(128,157316785),(128,692546944),(128,864218496),(128,549241117),(128,124435611),(18,324230)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank122 (u : ℕ) : P3_7_1.BankOK (bank122 u) :=
  P3_7_1.checked (bank122 u) (m:=387) (B:=535) (J:=123) (N:=1831412432896) (M:=2388083183) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole122
theorem free122_0 : TransitionSources.Free 2314 40 (bank122 24063) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank122 24063)) 2314 = 9265365638633984 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank122 24063)) 2315 = 12845657351959040 := by decide +kernel
  refine ⟨rank122 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free122_1 : TransitionSources.Free 2412 40 (bank122 10626) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank122 10626)) 2412 = 1880937002478572 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank122 10626)) 2413 = 2550872304780458 := by decide +kernel
  refine ⟨rank122 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free122_2 : TransitionSources.Free 2412 40 (bank122 24063) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank122 24063)) 2412 = 360133953544489472 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank122 24063)) 2413 = 363714245257814528 := by decide +kernel
  refine ⟨rank122 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole123 : momentEstimate 536 120 = 2357242900 := by
  refine moment_from_blocks [(128,157648238),(128,685824128),(128,852351104),(128,541187438),(128,119997056),(16,234936)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank123 (u : ℕ) : P3_7_1.BankOK (bank123 u) :=
  P3_7_1.checked (bank123 u) (m:=387) (B:=536) (J:=120) (N:=1797793513472) (M:=2357242900) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole123
theorem free123_0 : TransitionSources.Free 2314 21 (bank123 3616) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank123 3616)) 2314 = 205136357676530 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank123 3616)) 2315 = 284279809810456 := by decide +kernel
  refine ⟨rank123 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free123_1 : TransitionSources.Free 2412 21 (bank123 3043) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank123 3043)) 2412 = 156841631939340 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank123 3043)) 2413 = 210625813445720 := by decide +kernel
  refine ⟨rank123 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole124 : momentEstimate 537 123 = 2416913989 := by
  refine moment_from_blocks [(128,158032265),(128,696705408),(128,872440192),(128,559567820),(128,129732484),(20,435820)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank124 (u : ℕ) : P3_7_1.BankOK (bank124 u) :=
  P3_7_1.checked (bank124 u) (m:=387) (B:=537) (J:=123) (N:=1831412432896) (M:=2416913989) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole124
theorem free124_0 : TransitionSources.Free 2314 40 (bank124 22589) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank124 22589)) 2314 = 8357064711233310 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank124 22589)) 2315 = 11533165221863250 := by decide +kernel
  refine ⟨rank124 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free124_1 : TransitionSources.Free 2412 40 (bank124 10359) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank124 10359)) 2412 = 1834732372849320 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank124 10359)) 2413 = 2475663924053880 := by decide +kernel
  refine ⟨rank124 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole125 : momentEstimate 538 122 = 2416196542 := by
  refine moment_from_blocks [(128,158383820),(128,695876928),(128,871202112),(128,560305300),(128,129991737),(20,436645)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank125 (u : ℕ) : P3_7_1.BankOK (bank125 u) :=
  P3_7_1.checked (bank125 u) (m:=388) (B:=538) (J:=122) (N:=1830787219456) (M:=2416196542) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole125
theorem free125_0 : TransitionSources.Free 2314 41 (bank125 29117) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank125 29117)) 2314 = 13501734545406492 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank125 29117)) 2315 = 18749416602234024 := by decide +kernel
  refine ⟨rank125 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free125_1 : TransitionSources.Free 2412 41 (bank125 11583) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank125 11583)) 2412 = 2232075307479168 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank125 11583)) 2413 = 3028952937646592 := by decide +kernel
  refine ⟨rank125 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0594

-- Source: Research6969.TransitionBankChecks07
section Z6969Source0595
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole126 : momentEstimate 541 122 = 2459779870 := by
  refine moment_from_blocks [(128,159456995),(128,702087936),(128,883458816),(128,575922715),(128,138204692),(23,648716)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank126 (u : ℕ) : P3_7_1.BankOK (bank126 u) :=
  P3_7_1.checked (bank126 u) (m:=390) (B:=541) (J:=122) (N:=1851971338240) (M:=2459779870) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole126
theorem free126_0 : TransitionSources.Free 2314 41 (bank126 26574) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank126 26574)) 2314 = 11292950936742800 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank126 26574)) 2315 = 15710215495399900 := by decide +kernel
  refine ⟨rank126 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free126_1 : TransitionSources.Free 2412 41 (bank126 11206) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank126 11206)) 2412 = 2099421768867948 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank126 11206)) 2413 = 2853151764942416 := by decide +kernel
  refine ⟨rank126 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole127 : momentEstimate 542 122 = 2474425808 := by
  refine moment_from_blocks [(128,159814720),(128,704158272),(128,887544384),(128,581165840),(128,141010328),(24,732264)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank127 (u : ℕ) : P3_7_1.BankOK (bank127 u) :=
  P3_7_1.checked (bank127 u) (m:=391) (B:=542) (J:=122) (N:=1862611763200) (M:=2474425808) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole127
theorem free127_0 : TransitionSources.Free 2314 21 (bank127 3592) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank127 3592)) 2314 = 214358182550278 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank127 3592)) 2315 = 295409657272496 := by decide +kernel
  refine ⟨rank127 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free127_1 : TransitionSources.Free 2412 21 (bank127 3031) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank127 3031)) 2412 = 159911207383320 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank127 3031)) 2413 = 215289159112816 := by decide +kernel
  refine ⟨rank127 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole128 : momentEstimate 542 123 = 2490027179 := by
  refine moment_from_blocks [(128,159820965),(128,707101568),(128,892994432),(128,585720831),(128,143568038),(25,821345)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank128 (u : ℕ) : P3_7_1.BankOK (bank128 u) :=
  P3_7_1.checked (bank128 u) (m:=391) (B:=542) (J:=123) (N:=1874060115968) (M:=2490027179) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole128
theorem free128_0 : TransitionSources.Free 2314 41 (bank128 25826) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank128 25826)) 2314 = 10782920365670172 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank128 25826)) 2315 = 15003848965449474 := by decide +kernel
  refine ⟨rank128 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free128_1 : TransitionSources.Free 2412 41 (bank128 11074) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank128 11074)) 2412 = 2067050278453800 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank128 11074)) 2413 = 2811741695121550 := by decide +kernel
  refine ⟨rank128 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole129 : momentEstimate 544 123 = 2519689529 := by
  refine moment_from_blocks [(128,160536445),(128,711260032),(128,901216128),(128,596312574),(128,149340264),(27,1024086)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank129 (u : ℕ) : P3_7_1.BankOK (bank129 u) :=
  P3_7_1.checked (bank129 u) (m:=392) (B:=544) (J:=123) (N:=1884803301376) (M:=2519689529) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole129
theorem free129_0 : TransitionSources.Free 2314 41 (bank129 24535) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank129 24535)) 2314 = 9829665313687024 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank129 24535)) 2315 = 13666058920225664 := by decide +kernel
  refine ⟨rank129 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free129_1 : TransitionSources.Free 2412 41 (bank129 10859) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank129 10859)) 2412 = 2010878062774440 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank129 10859)) 2413 = 2731993618748400 := by decide +kernel
  refine ⟨rank129 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole130 : momentEstimate 547 124 = 2580674858 := by
  refine moment_from_blocks [(128,161613875),(128,720440000),(128,919096000),(128,617019723),(128,160982668),(31,1522592)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank130 (u : ℕ) : P3_7_1.BankOK (bank130 u) :=
  P3_7_1.checked (bank130 u) (m:=395) (B:=547) (J:=124) (N:=1928921088000) (M:=2580674858) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole130
theorem free130_0 : TransitionSources.Free 2314 41 (bank130 22726) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank130 22726)) 2314 = 8441779383249952 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank130 22726)) 2315 = 11794458975248420 := by decide +kernel
  refine ⟨rank130 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free130_1 : TransitionSources.Free 2412 41 (bank130 10521) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank130 10521)) 2412 = 1896606713170926 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank130 10521)) 2413 = 2586108465015674 := by decide +kernel
  refine ⟨rank130 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole131 : momentEstimate 550 124 = 2626456108 := by
  refine moment_from_blocks [(128,162687125),(128,726704000),(128,931504000),(128,633278037),(128,170292197),(34,1990749)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank131 (u : ℕ) : P3_7_1.BankOK (bank131 u) :=
  P3_7_1.checked (bank131 u) (m:=397) (B:=550) (J:=124) (N:=1950842880000) (M:=2626456108) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole131
theorem free131_0 : TransitionSources.Free 2314 41 (bank131 21237) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank131 21237)) 2314 = 7393188150201763 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank131 21237)) 2315 = 10351325528156480 := by decide +kernel
  refine ⟨rank131 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free131_1 : TransitionSources.Free 2412 41 (bank131 10228) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank131 10228)) 2412 = 1789574514291207 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank131 10228)) 2413 = 2447968545418118 := by decide +kernel
  refine ⟨rank131 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole132 : momentEstimate 553 124 = 2672787483 := by
  refine moment_from_blocks [(128,163760375),(128,732968000),(128,943912000),(128,649689868),(128,179909765),(37,2547475)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank132 (u : ℕ) : P3_7_1.BankOK (bank132 u) :=
  P3_7_1.checked (bank132 u) (m:=399) (B:=553) (J:=124) (N:=1972895744000) (M:=2672787483) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole132
theorem free132_0 : TransitionSources.Free 2314 36 (bank132 9317) := by
  have left : TransitionArithmetic.value (TransitionSources.request 36 (bank132 9317)) 2314 = 1440820295834343 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 36 (bank132 9317)) 2315 = 2016299617990530 := by decide +kernel
  refine ⟨rank132 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free132_1 : TransitionSources.Free 2412 36 (bank132 6342) := by
  have left : TransitionArithmetic.value (TransitionSources.request 36 (bank132 6342)) 2412 = 694010011326244 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 36 (bank132 6342)) 2413 = 949868696709406 := by decide +kernel
  refine ⟨rank132 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole133 : momentEstimate 558 120 = 2682384904 := by
  refine moment_from_blocks [(128,165517110),(128,730971648),(128,941112832),(128,657448189),(128,184560600),(38,2774525)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank133 (u : ℕ) : P3_7_1.BankOK (bank133 u) :=
  P3_7_1.checked (bank133 u) (m:=400) (B:=558) (J:=120) (N:=1935519252480) (M:=2682384904) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole133
private theorem pole134 : momentEstimate 558 123 = 2734096379 := by
  refine moment_from_blocks [(128,165544805),(128,740369280),(128,958768000),(128,672392258),(128,193574493),(41,3447543)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank134 (u : ℕ) : P3_7_1.BankOK (bank134 u) :=
  P3_7_1.checked (bank134 u) (m:=400) (B:=558) (J:=123) (N:=1971918995456) (M:=2734096379) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole134
private theorem pole135 : momentEstimate 558 126 = 2785382344 := by
  refine moment_from_blocks [(128,165553009),(128,749344704),(128,976148416),(128,687321444),(128,202794984),(44,4219787)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank135 (u : ℕ) : P3_7_1.BankOK (bank135 u) :=
  P3_7_1.checked (bank135 u) (m:=400) (B:=558) (J:=126) (N:=2007957766144) (M:=2785382344) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole135
private theorem pole136 : momentEstimate 566 127 = 2933627832 := by
  refine moment_from_blocks [(128,168415520),(128,769150976),(128,1015566336),(128,738044420),(128,235145821),(53,7304759)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank136 (u : ℕ) : P3_7_1.BankOK (bank136 u) :=
  P3_7_1.checked (bank136 u) (m:=409) (B:=566) (J:=127) (N:=2123022467072) (M:=2933627832) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole136
theorem free136_0 : TransitionSources.Free 2314 40 (bank136 13749) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank136 13749)) 2314 = 3255215478680000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank136 13749)) 2315 = 4596563525620000 := by decide +kernel
  refine ⟨rank136 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free136_1 : TransitionSources.Free 2412 40 (bank136 8209) := by
  have left : TransitionArithmetic.value (TransitionSources.request 40 (bank136 8209)) 2412 = 1218710661667200 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 40 (bank136 8209)) 2413 = 1677541465295520 := by decide +kernel
  refine ⟨rank136 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole137 : momentEstimate 570 128 = 3018995326 := by
  refine moment_from_blocks [(128,169846560),(128,780555264),(128,1038406656),(128,766574099),(128,254077507),(58,9535240)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank137 (u : ℕ) : P3_7_1.BankOK (bank137 u) :=
  P3_7_1.checked (bank137 u) (m:=411) (B:=570) (J:=128) (N:=2159008022528) (M:=3018995326) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole137
theorem free137_0 : TransitionSources.Free 2314 21 (bank137 3540) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank137 3540)) 2314 = 223846242950565 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank137 3540)) 2315 = 314695934885568 := by decide +kernel
  refine ⟨rank137 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free137_1 : TransitionSources.Free 2412 21 (bank137 3019) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank137 3019)) 2412 = 169787891157750 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank137 3019)) 2413 = 233191277807060 := by decide +kernel
  refine ⟨rank137 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole138 : momentEstimate 577 130 = 3177562648 := by
  refine moment_from_blocks [(128,172350880),(128,801276097),(128,1080295168),(128,818936327),(128,290078175),(67,14626001)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank138 (u : ℕ) : P3_7_1.BankOK (bank138 u) :=
  P3_7_1.checked (bank138 u) (m:=416) (B:=577) (J:=130) (N:=2244209803264) (M:=3177562648) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole138
theorem free138_0 : TransitionSources.Free 2314 23 (bank138 3813) := by
  have left : TransitionArithmetic.value (TransitionSources.request 23 (bank138 3813)) 2314 = 269269010920799 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 23 (bank138 3813)) 2315 = 378800921409655 := by decide +kernel
  refine ⟨rank138 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free138_1 : TransitionSources.Free 2412 23 (bank138 3222) := by
  have left : TransitionArithmetic.value (TransitionSources.request 23 (bank138 3222)) 2412 = 204502100134332 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 23 (bank138 3222)) 2413 = 279549579793484 := by decide +kernel
  refine ⟨rank138 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole139 : momentEstimate 630 142 = 4512018338 := by
  refine moment_from_blocks [(128,191312160),(128,950433445),(128,1393016768),(128,1236496949),(128,627994331),(128,112756512),(4,8173)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank139 (u : ℕ) : P3_7_1.BankOK (bank139 u) :=
  P3_7_1.checked (bank139 u) (m:=455) (B:=630) (J:=142) (N:=2930701762560) (M:=4512018338) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole139
theorem free139_0 : TransitionSources.Free 2314 30 (bank139 4862) := by
  have left : TransitionArithmetic.value (TransitionSources.request 30 (bank139 4862)) 2314 = 519942652101288 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 30 (bank139 4862)) 2315 = 749747888835564 := by decide +kernel
  refine ⟨rank139 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free139_1 : TransitionSources.Free 2412 30 (bank139 4010) := by
  have left : TransitionArithmetic.value (TransitionSources.request 30 (bank139 4010)) 2412 = 382803590701560 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 30 (bank139 4010)) 2413 = 532805443510788 := by decide +kernel
  refine ⟨rank139 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole140 : momentEstimate 631 142 = 4535089958 := by
  refine moment_from_blocks [(128,191669920),(128,952657836),(128,1397583616),(128,1243352924),(128,634399963),(128,115411856),(5,13843)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank140 (u : ℕ) : P3_7_1.BankOK (bank140 u) :=
  P3_7_1.checked (bank140 u) (m:=455) (B:=631) (J:=142) (N:=2930701762560) (M:=4535089958) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole140
theorem free140_0 : TransitionSources.Free 2314 25 (bank140 3997) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank140 3997)) 2314 = 366539123977390 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank140 3997)) 2315 = 522334712976509 := by decide +kernel
  refine ⟨rank140 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free140_1 : TransitionSources.Free 2412 25 (bank140 3403) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank140 3403)) 2412 = 272754959300712 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank140 3403)) 2413 = 381114052870618 := by decide +kernel
  refine ⟨rank140 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole141 : momentEstimate 655 141 = 5085275599 := by
  refine moment_from_blocks [(128,200256160),(128,1003174315),(128,1499697216),(128,1400819776),(128,791759028),(128,188197314),(28,1371790)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank141 (u : ℕ) : P3_7_1.BankOK (bank141 u) :=
  P3_7_1.checked (bank141 u) (m:=470) (B:=655) (J:=141) (N:=3134317133824) (M:=5085275599) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole141
private theorem pole142 : momentEstimate 655 144 = 5168862572 := by
  refine moment_from_blocks [(128,200256160),(128,1011625420),(128,1522040640),(128,1424637760),(128,810175516),(128,198296036),(31,1831040)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank142 (u : ℕ) : P3_7_1.BankOK (bank142 u) :=
  P3_7_1.checked (bank142 u) (m:=470) (B:=655) (J:=144) (N:=3184589537280) (M:=5168862572) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole142
private theorem pole143 : momentEstimate 655 148 = 5279398867 := by
  refine moment_from_blocks [(128,200256160),(128,1022181709),(128,1551230656),(128,1456027967),(128,834928971),(128,212186369),(35,2587035)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank143 (u : ℕ) : P3_7_1.BankOK (bank143 u) :=
  P3_7_1.checked (bank143 u) (m:=470) (B:=655) (J:=148) (N:=3250957582336) (M:=5279398867) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole143
end Research6969.TransitionBanks
end Z6969Source0595

end Merged_Z6969Pack0558
