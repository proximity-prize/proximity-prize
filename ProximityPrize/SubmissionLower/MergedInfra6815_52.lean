import ProximityPrize.SubmissionLower.MergedPrefixRows6815_3
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.FinalPrefixData6815
open FinalPrefixRowsCheck6815 FinalPrefixRows6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
def row (r v : ℕ) : Entry := match r with
  | 1 => row1 v
  | 2 => row2 v
  | 3 => row3 v
  | 4 => row4 v
  | 5 => row5 v
  | 6 => row6 v
  | 7 => row7 v
  | 8 => row8 v
  | 9 => row9 v
  | 10 => row10 v
  | 11 => row11 v
  | 12 => row12 v
  | 13 => row13 v
  | 14 => row14 v
  | 15 => row15 v
  | 16 => row16 v
  | 17 => row17 v
  | 18 => row18 v
  | 19 => row19 v
  | 20 => row20 v
  | 21 => row21 v
  | 22 => row22 v
  | 23 => row23 v
  | 24 => row24 v
  | 25 => row25 v
  | 26 => row26 v
  | 27 => row27 v
  | 28 => row28 v
  | 29 => row29 v
  | 30 => row30 v
  | 31 => row31 v
  | 32 => row32 v
  | 33 => row33 v
  | 34 => row34 v
  | 35 => row35 v
  | 36 => row36 v
  | 37 => row37 v
  | 38 => row38 v
  | 39 => row39 v
  | _ => zero
theorem checked (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hY : r+v≤182) :
    check r v (FinalLedgerData6815.row r v) (thresholds (SingletonData6815.row r v)) (row r v) (row (r-1) v) (if v=0 then zero else row r (v-1))=true := by
  interval_cases r
  · exact checked1 v (by omega)
  · exact checked2 v (by omega)
  · exact checked3 v (by omega)
  · exact checked4 v (by omega)
  · exact checked5 v (by omega)
  · exact checked6 v (by omega)
  · exact checked7 v (by omega)
  · exact checked8 v (by omega)
  · exact checked9 v (by omega)
  · exact checked10 v (by omega)
  · exact checked11 v (by omega)
  · exact checked12 v (by omega)
  · exact checked13 v (by omega)
  · exact checked14 v (by omega)
  · exact checked15 v (by omega)
  · exact checked16 v (by omega)
  · exact checked17 v (by omega)
  · exact checked18 v (by omega)
  · exact checked19 v (by omega)
  · exact checked20 v (by omega)
  · exact checked21 v (by omega)
  · exact checked22 v (by omega)
  · exact checked23 v (by omega)
  · exact checked24 v (by omega)
  · exact checked25 v (by omega)
  · exact checked26 v (by omega)
  · exact checked27 v (by omega)
  · exact checked28 v (by omega)
  · exact checked29 v (by omega)
  · exact checked30 v (by omega)
  · exact checked31 v (by omega)
  · exact checked32 v (by omega)
  · exact checked33 v (by omega)
  · exact checked34 v (by omega)
  · exact checked35 v (by omega)
  · exact checked36 v (by omega)
  · exact checked37 v (by omega)
  · exact checked38 v (by omega)
  · exact checked39 v (by omega)
end ProximityPrize.SubmissionLower.FinalPrefixData6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.FinalPrefixSound6815
open FinalPrefixCheck6815 FinalPrefixRowsCheck6815
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def prefixCap (r v j : ℕ) := coeff (FinalPrefixData6815.row r v) j
def seen (r v k : ℕ) := present (FinalPrefixData6815.row r v) k
def cut (r v j : ℕ) := threshold (SingletonCertificate6815.thresholds (SingletonData6815.row r v)) j

theorem curve_valid (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) :
    FinalCurves6815.validFrom (11193-r-v) 0 (FinalLedgerData6815.row r v)=true := by
  have h := FinalLedgerData6815.checked r v hr hR hy
  simp only [FinalLedgerChecks6815.checkRow,Bool.and_eq_true] at h
  exact h.1

theorem prefix_mono (j r v R V : ℕ) (hj : j<13) (hr : r≤R) (hv : v≤V)
    (hR : R≤39) (hy : R+V≤182) : prefixCap r v j≤prefixCap R V j := by
  apply rectangle_mono (fun r v => prefixCap r v j) 39 182 _ _ r v R V hr hv hR hy
  · intro q u hq hu
    have h := (coeff_mono (q+1) u _ _ _ _ _
      (FinalPrefixData6815.checked (q+1) u (by omega) hq hu) j hj).1
    simpa only [prefixCap,Nat.add_sub_cancel] using h
  · intro q u hq hu
    by_cases h0 : q=0
    · subst q; rfl
    have h := (coeff_mono q (u+1) _ _ _ _ _
      (FinalPrefixData6815.checked q (u+1) (by omega) hq (by omega)) j hj).2
    simpa only [prefixCap,Nat.add_sub_cancel,show ¬u+1=0 by omega,if_false] using h

theorem seen_mono (k r v R V : ℕ) (hk : k<5) (hr : r≤R) (hv : v≤V)
    (hR : R≤39) (hy : R+V≤182) (hseen : seen r v k=true) : seen R V k=true := by
  let f := fun r v => if seen r v k then (1:ℕ) else 0
  have bool_le (a b : Bool) (h : a=true → b=true) :
      (if a then (1:ℕ) else 0)≤(if b then 1 else 0) := by
    cases ha : a <;> cases hb : b <;> simp_all
  have hm : f r v≤f R V := by
    apply rectangle_mono f 39 182 _ _ r v R V hr hv hR hy
    · intro q u hq hu
      apply bool_le
      have h := (present_mono (q+1) u _ _ _ _ _
        (FinalPrefixData6815.checked (q+1) u (by omega) hq hu) k hk).1
      simpa only [seen,Nat.add_sub_cancel] using h
    · intro q u hq hu
      by_cases h0 : q=0
      · subst q; rfl
      apply bool_le
      have h := (present_mono q (u+1) _ _ _ _ _
        (FinalPrefixData6815.checked q (u+1) (by omega) hq (by omega)) k hk).2
      simpa only [seen,Nat.add_sub_cancel,show ¬u+1=0 by omega,if_false] using h
  dsimp only [f] at hm
  rw [hseen] at hm
  cases h : seen R V k <;> simp_all

theorem phase_prefix (r v z j : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182)
    (hz : r+v+z≤11192) (hj : j<8) (hcut : z<cut r v (sourceIndex j)) :
    FinalLedgerData6815.cap r v z≤affine (phase j) r v z+prefixCap r v j := by
  exact phaseCheck_sound r v _ _ j (11193-r-v) z _ (curve_valid r v hr hR hy)
    (phase_check _ _ _ _ _ _ _ (FinalPrefixData6815.checked r v hr hR hy) j hj) (by omega) hcut

theorem terminal_prefix (r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182)
    (hz : r+v+z≤11192) (hcut : z<cut r v 5) :
    FinalLedgerData6815.cap r v z≤affine (terminal (classify r v z)) r v z+
      prefixCap r v (classify r v z+8) ∧ seen r v (classify r v z)=true := by
  exact classCheck_sound r v _ _ (classify r v z) z _ _ (curve_valid r v hr hR hy)
    (class_check _ _ _ _ _ _ _ (FinalPrefixData6815.checked r v hr hR hy) _ (class_lt_five _ _ _))
    rfl (by omega) hcut

end ProximityPrize.SubmissionLower.FinalPrefixSound6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.FinalLookup6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def single1 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R01.row v
theorem single1_eq (v : ℕ) : single1 v=SingletonRows6815_R01.row v := rfl
def single2 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R02.row v
theorem single2_eq (v : ℕ) : single2 v=SingletonRows6815_R02.row v := rfl
def single3 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R03.row v
theorem single3_eq (v : ℕ) : single3 v=SingletonRows6815_R03.row v := rfl
def single4 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R04.row v
theorem single4_eq (v : ℕ) : single4 v=SingletonRows6815_R04.row v := rfl
def single5 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R05.row v
theorem single5_eq (v : ℕ) : single5 v=SingletonRows6815_R05.row v := rfl
def single6 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R06.row v
theorem single6_eq (v : ℕ) : single6 v=SingletonRows6815_R06.row v := rfl
def single7 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R07.row v
theorem single7_eq (v : ℕ) : single7 v=SingletonRows6815_R07.row v := rfl
def single8 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R08.row v
theorem single8_eq (v : ℕ) : single8 v=SingletonRows6815_R08.row v := rfl
def single9 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R09.row v
theorem single9_eq (v : ℕ) : single9 v=SingletonRows6815_R09.row v := rfl
def single10 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R10.row v
theorem single10_eq (v : ℕ) : single10 v=SingletonRows6815_R10.row v := rfl
def single11 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R11.row v
theorem single11_eq (v : ℕ) : single11 v=SingletonRows6815_R11.row v := rfl
def single12 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R12.row v
theorem single12_eq (v : ℕ) : single12 v=SingletonRows6815_R12.row v := rfl
def single13 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R13.row v
theorem single13_eq (v : ℕ) : single13 v=SingletonRows6815_R13.row v := rfl
def single14 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R14.row v
theorem single14_eq (v : ℕ) : single14 v=SingletonRows6815_R14.row v := rfl
def single15 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R15.row v
theorem single15_eq (v : ℕ) : single15 v=SingletonRows6815_R15.row v := rfl
def single16 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R16.row v
theorem single16_eq (v : ℕ) : single16 v=SingletonRows6815_R16.row v := rfl
def single17 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R17.row v
theorem single17_eq (v : ℕ) : single17 v=SingletonRows6815_R17.row v := rfl
def single18 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R18.row v
theorem single18_eq (v : ℕ) : single18 v=SingletonRows6815_R18.row v := rfl
def single19 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R19.row v
theorem single19_eq (v : ℕ) : single19 v=SingletonRows6815_R19.row v := rfl
def single20 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R20.row v
theorem single20_eq (v : ℕ) : single20 v=SingletonRows6815_R20.row v := rfl
def single21 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R21.row v
theorem single21_eq (v : ℕ) : single21 v=SingletonRows6815_R21.row v := rfl
def single22 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R22.row v
theorem single22_eq (v : ℕ) : single22 v=SingletonRows6815_R22.row v := rfl
def single23 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R23.row v
theorem single23_eq (v : ℕ) : single23 v=SingletonRows6815_R23.row v := rfl
def single24 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R24.row v
theorem single24_eq (v : ℕ) : single24 v=SingletonRows6815_R24.row v := rfl
def single25 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R25.row v
theorem single25_eq (v : ℕ) : single25 v=SingletonRows6815_R25.row v := rfl
def single26 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R26.row v
theorem single26_eq (v : ℕ) : single26 v=SingletonRows6815_R26.row v := rfl
def single27 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R27.row v
theorem single27_eq (v : ℕ) : single27 v=SingletonRows6815_R27.row v := rfl
def single28 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R28.row v
theorem single28_eq (v : ℕ) : single28 v=SingletonRows6815_R28.row v := rfl
def single29 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R29.row v
theorem single29_eq (v : ℕ) : single29 v=SingletonRows6815_R29.row v := rfl
def single30 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R30.row v
theorem single30_eq (v : ℕ) : single30 v=SingletonRows6815_R30.row v := rfl
def single31 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R31.row v
theorem single31_eq (v : ℕ) : single31 v=SingletonRows6815_R31.row v := rfl
def single32 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R32.row v
theorem single32_eq (v : ℕ) : single32 v=SingletonRows6815_R32.row v := rfl
def single33 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R33.row v
theorem single33_eq (v : ℕ) : single33 v=SingletonRows6815_R33.row v := rfl
def single34 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R34.row v
theorem single34_eq (v : ℕ) : single34 v=SingletonRows6815_R34.row v := rfl
def single35 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R35.row v
theorem single35_eq (v : ℕ) : single35 v=SingletonRows6815_R35.row v := rfl
def single36 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R36.row v
theorem single36_eq (v : ℕ) : single36 v=SingletonRows6815_R36.row v := rfl
def single37 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R37.row v
theorem single37_eq (v : ℕ) : single37 v=SingletonRows6815_R37.row v := rfl
def single38 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R38.row v
theorem single38_eq (v : ℕ) : single38 v=SingletonRows6815_R38.row v := rfl
def single39 (v : ℕ) : SingletonCertificate6815.Row := SingletonRows6815_R39.row v
theorem single39_eq (v : ℕ) : single39 v=SingletonRows6815_R39.row v := rfl
def single (r v : ℕ) : SingletonCertificate6815.Row := match r with
  | 1 => single1 v
  | 2 => single2 v
  | 3 => single3 v
  | 4 => single4 v
  | 5 => single5 v
  | 6 => single6 v
  | 7 => single7 v
  | 8 => single8 v
  | 9 => single9 v
  | 10 => single10 v
  | 11 => single11 v
  | 12 => single12 v
  | 13 => single13 v
  | 14 => single14 v
  | 15 => single15 v
  | 16 => single16 v
  | 17 => single17 v
  | 18 => single18 v
  | 19 => single19 v
  | 20 => single20 v
  | 21 => single21 v
  | 22 => single22 v
  | 23 => single23 v
  | 24 => single24 v
  | 25 => single25 v
  | 26 => single26 v
  | 27 => single27 v
  | 28 => single28 v
  | 29 => single29 v
  | 30 => single30 v
  | 31 => single31 v
  | 32 => single32 v
  | 33 => single33 v
  | 34 => single34 v
  | 35 => single35 v
  | 36 => single36 v
  | 37 => single37 v
  | 38 => single38 v
  | 39 => single39 v
  | _ => default
theorem single_eq (r v : ℕ) (hr : 1≤r) (hR : r≤39) : single r v=SingletonData6815.row r v := by
  interval_cases r
  · exact single1_eq v
  · exact single2_eq v
  · exact single3_eq v
  · exact single4_eq v
  · exact single5_eq v
  · exact single6_eq v
  · exact single7_eq v
  · exact single8_eq v
  · exact single9_eq v
  · exact single10_eq v
  · exact single11_eq v
  · exact single12_eq v
  · exact single13_eq v
  · exact single14_eq v
  · exact single15_eq v
  · exact single16_eq v
  · exact single17_eq v
  · exact single18_eq v
  · exact single19_eq v
  · exact single20_eq v
  · exact single21_eq v
  · exact single22_eq v
  · exact single23_eq v
  · exact single24_eq v
  · exact single25_eq v
  · exact single26_eq v
  · exact single27_eq v
  · exact single28_eq v
  · exact single29_eq v
  · exact single30_eq v
  · exact single31_eq v
  · exact single32_eq v
  · exact single33_eq v
  · exact single34_eq v
  · exact single35_eq v
  · exact single36_eq v
  · exact single37_eq v
  · exact single38_eq v
  · exact single39_eq v
def final1 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row1 v
theorem final1_eq (v : ℕ) : final1 v=FinalLedgerRows6815.row1 v := rfl
def final2 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row2 v
theorem final2_eq (v : ℕ) : final2 v=FinalLedgerRows6815.row2 v := rfl
def final3 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row3 v
theorem final3_eq (v : ℕ) : final3 v=FinalLedgerRows6815.row3 v := rfl
def final4 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row4 v
theorem final4_eq (v : ℕ) : final4 v=FinalLedgerRows6815.row4 v := rfl
def final5 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row5 v
theorem final5_eq (v : ℕ) : final5 v=FinalLedgerRows6815.row5 v := rfl
def final6 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row6 v
theorem final6_eq (v : ℕ) : final6 v=FinalLedgerRows6815.row6 v := rfl
def final7 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row7 v
theorem final7_eq (v : ℕ) : final7 v=FinalLedgerRows6815.row7 v := rfl
def final8 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row8 v
theorem final8_eq (v : ℕ) : final8 v=FinalLedgerRows6815.row8 v := rfl
def final9 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row9 v
theorem final9_eq (v : ℕ) : final9 v=FinalLedgerRows6815.row9 v := rfl
def final10 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row10 v
theorem final10_eq (v : ℕ) : final10 v=FinalLedgerRows6815.row10 v := rfl
def final11 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row11 v
theorem final11_eq (v : ℕ) : final11 v=FinalLedgerRows6815.row11 v := rfl
def final12 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row12 v
theorem final12_eq (v : ℕ) : final12 v=FinalLedgerRows6815.row12 v := rfl
def final13 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row13 v
theorem final13_eq (v : ℕ) : final13 v=FinalLedgerRows6815.row13 v := rfl
def final14 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row14 v
theorem final14_eq (v : ℕ) : final14 v=FinalLedgerRows6815.row14 v := rfl
def final15 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row15 v
theorem final15_eq (v : ℕ) : final15 v=FinalLedgerRows6815.row15 v := rfl
def final16 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row16 v
theorem final16_eq (v : ℕ) : final16 v=FinalLedgerRows6815.row16 v := rfl
def final17 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row17 v
theorem final17_eq (v : ℕ) : final17 v=FinalLedgerRows6815.row17 v := rfl
def final18 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row18 v
theorem final18_eq (v : ℕ) : final18 v=FinalLedgerRows6815.row18 v := rfl
def final19 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row19 v
theorem final19_eq (v : ℕ) : final19 v=FinalLedgerRows6815.row19 v := rfl
def final20 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row20 v
theorem final20_eq (v : ℕ) : final20 v=FinalLedgerRows6815.row20 v := rfl
def final21 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row21 v
theorem final21_eq (v : ℕ) : final21 v=FinalLedgerRows6815.row21 v := rfl
def final22 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row22 v
theorem final22_eq (v : ℕ) : final22 v=FinalLedgerRows6815.row22 v := rfl
def final23 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row23 v
theorem final23_eq (v : ℕ) : final23 v=FinalLedgerRows6815.row23 v := rfl
def final24 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row24 v
theorem final24_eq (v : ℕ) : final24 v=FinalLedgerRows6815.row24 v := rfl
def final25 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row25 v
theorem final25_eq (v : ℕ) : final25 v=FinalLedgerRows6815.row25 v := rfl
def final26 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row26 v
theorem final26_eq (v : ℕ) : final26 v=FinalLedgerRows6815.row26 v := rfl
def final27 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row27 v
theorem final27_eq (v : ℕ) : final27 v=FinalLedgerRows6815.row27 v := rfl
def final28 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row28 v
theorem final28_eq (v : ℕ) : final28 v=FinalLedgerRows6815.row28 v := rfl
def final29 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row29 v
theorem final29_eq (v : ℕ) : final29 v=FinalLedgerRows6815.row29 v := rfl
def final30 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row30 v
theorem final30_eq (v : ℕ) : final30 v=FinalLedgerRows6815.row30 v := rfl
def final31 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row31 v
theorem final31_eq (v : ℕ) : final31 v=FinalLedgerRows6815.row31 v := rfl
def final32 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row32 v
theorem final32_eq (v : ℕ) : final32 v=FinalLedgerRows6815.row32 v := rfl
def final33 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row33 v
theorem final33_eq (v : ℕ) : final33 v=FinalLedgerRows6815.row33 v := rfl
def final34 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row34 v
theorem final34_eq (v : ℕ) : final34 v=FinalLedgerRows6815.row34 v := rfl
def final35 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row35 v
theorem final35_eq (v : ℕ) : final35 v=FinalLedgerRows6815.row35 v := rfl
def final36 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row36 v
theorem final36_eq (v : ℕ) : final36 v=FinalLedgerRows6815.row36 v := rfl
def final37 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row37 v
theorem final37_eq (v : ℕ) : final37 v=FinalLedgerRows6815.row37 v := rfl
def final38 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row38 v
theorem final38_eq (v : ℕ) : final38 v=FinalLedgerRows6815.row38 v := rfl
def final39 (v : ℕ) : List FinalCurves6815.Piece := FinalLedgerRows6815.row39 v
theorem final39_eq (v : ℕ) : final39 v=FinalLedgerRows6815.row39 v := rfl
def final (r v : ℕ) : List FinalCurves6815.Piece := match r with
  | 1 => final1 v
  | 2 => final2 v
  | 3 => final3 v
  | 4 => final4 v
  | 5 => final5 v
  | 6 => final6 v
  | 7 => final7 v
  | 8 => final8 v
  | 9 => final9 v
  | 10 => final10 v
  | 11 => final11 v
  | 12 => final12 v
  | 13 => final13 v
  | 14 => final14 v
  | 15 => final15 v
  | 16 => final16 v
  | 17 => final17 v
  | 18 => final18 v
  | 19 => final19 v
  | 20 => final20 v
  | 21 => final21 v
  | 22 => final22 v
  | 23 => final23 v
  | 24 => final24 v
  | 25 => final25 v
  | 26 => final26 v
  | 27 => final27 v
  | 28 => final28 v
  | 29 => final29 v
  | 30 => final30 v
  | 31 => final31 v
  | 32 => final32 v
  | 33 => final33 v
  | 34 => final34 v
  | 35 => final35 v
  | 36 => final36 v
  | 37 => final37 v
  | 38 => final38 v
  | 39 => final39 v
  | _ => []
theorem final_eq (r v : ℕ) (hr : 1≤r) (hR : r≤39) : final r v=FinalLedgerData6815.row r v := by
  interval_cases r
  · exact final1_eq v
  · exact final2_eq v
  · exact final3_eq v
  · exact final4_eq v
  · exact final5_eq v
  · exact final6_eq v
  · exact final7_eq v
  · exact final8_eq v
  · exact final9_eq v
  · exact final10_eq v
  · exact final11_eq v
  · exact final12_eq v
  · exact final13_eq v
  · exact final14_eq v
  · exact final15_eq v
  · exact final16_eq v
  · exact final17_eq v
  · exact final18_eq v
  · exact final19_eq v
  · exact final20_eq v
  · exact final21_eq v
  · exact final22_eq v
  · exact final23_eq v
  · exact final24_eq v
  · exact final25_eq v
  · exact final26_eq v
  · exact final27_eq v
  · exact final28_eq v
  · exact final29_eq v
  · exact final30_eq v
  · exact final31_eq v
  · exact final32_eq v
  · exact final33_eq v
  · exact final34_eq v
  · exact final35_eq v
  · exact final36_eq v
  · exact final37_eq v
  · exact final38_eq v
  · exact final39_eq v
def pref1 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row1 v
theorem pref1_eq (v : ℕ) : pref1 v=FinalPrefixRows6815.row1 v := rfl
def pref2 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row2 v
theorem pref2_eq (v : ℕ) : pref2 v=FinalPrefixRows6815.row2 v := rfl
def pref3 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row3 v
theorem pref3_eq (v : ℕ) : pref3 v=FinalPrefixRows6815.row3 v := rfl
def pref4 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row4 v
theorem pref4_eq (v : ℕ) : pref4 v=FinalPrefixRows6815.row4 v := rfl
def pref5 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row5 v
theorem pref5_eq (v : ℕ) : pref5 v=FinalPrefixRows6815.row5 v := rfl
def pref6 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row6 v
theorem pref6_eq (v : ℕ) : pref6 v=FinalPrefixRows6815.row6 v := rfl
def pref7 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row7 v
theorem pref7_eq (v : ℕ) : pref7 v=FinalPrefixRows6815.row7 v := rfl
def pref8 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row8 v
theorem pref8_eq (v : ℕ) : pref8 v=FinalPrefixRows6815.row8 v := rfl
def pref9 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row9 v
theorem pref9_eq (v : ℕ) : pref9 v=FinalPrefixRows6815.row9 v := rfl
def pref10 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row10 v
theorem pref10_eq (v : ℕ) : pref10 v=FinalPrefixRows6815.row10 v := rfl
def pref11 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row11 v
theorem pref11_eq (v : ℕ) : pref11 v=FinalPrefixRows6815.row11 v := rfl
def pref12 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row12 v
theorem pref12_eq (v : ℕ) : pref12 v=FinalPrefixRows6815.row12 v := rfl
def pref13 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row13 v
theorem pref13_eq (v : ℕ) : pref13 v=FinalPrefixRows6815.row13 v := rfl
def pref14 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row14 v
theorem pref14_eq (v : ℕ) : pref14 v=FinalPrefixRows6815.row14 v := rfl
def pref15 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row15 v
theorem pref15_eq (v : ℕ) : pref15 v=FinalPrefixRows6815.row15 v := rfl
def pref16 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row16 v
theorem pref16_eq (v : ℕ) : pref16 v=FinalPrefixRows6815.row16 v := rfl
def pref17 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row17 v
theorem pref17_eq (v : ℕ) : pref17 v=FinalPrefixRows6815.row17 v := rfl
def pref18 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row18 v
theorem pref18_eq (v : ℕ) : pref18 v=FinalPrefixRows6815.row18 v := rfl
def pref19 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row19 v
theorem pref19_eq (v : ℕ) : pref19 v=FinalPrefixRows6815.row19 v := rfl
def pref20 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row20 v
theorem pref20_eq (v : ℕ) : pref20 v=FinalPrefixRows6815.row20 v := rfl
def pref21 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row21 v
theorem pref21_eq (v : ℕ) : pref21 v=FinalPrefixRows6815.row21 v := rfl
def pref22 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row22 v
theorem pref22_eq (v : ℕ) : pref22 v=FinalPrefixRows6815.row22 v := rfl
def pref23 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row23 v
theorem pref23_eq (v : ℕ) : pref23 v=FinalPrefixRows6815.row23 v := rfl
def pref24 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row24 v
theorem pref24_eq (v : ℕ) : pref24 v=FinalPrefixRows6815.row24 v := rfl
def pref25 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row25 v
theorem pref25_eq (v : ℕ) : pref25 v=FinalPrefixRows6815.row25 v := rfl
def pref26 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row26 v
theorem pref26_eq (v : ℕ) : pref26 v=FinalPrefixRows6815.row26 v := rfl
def pref27 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row27 v
theorem pref27_eq (v : ℕ) : pref27 v=FinalPrefixRows6815.row27 v := rfl
def pref28 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row28 v
theorem pref28_eq (v : ℕ) : pref28 v=FinalPrefixRows6815.row28 v := rfl
def pref29 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row29 v
theorem pref29_eq (v : ℕ) : pref29 v=FinalPrefixRows6815.row29 v := rfl
def pref30 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row30 v
theorem pref30_eq (v : ℕ) : pref30 v=FinalPrefixRows6815.row30 v := rfl
def pref31 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row31 v
theorem pref31_eq (v : ℕ) : pref31 v=FinalPrefixRows6815.row31 v := rfl
def pref32 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row32 v
theorem pref32_eq (v : ℕ) : pref32 v=FinalPrefixRows6815.row32 v := rfl
def pref33 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row33 v
theorem pref33_eq (v : ℕ) : pref33 v=FinalPrefixRows6815.row33 v := rfl
def pref34 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row34 v
theorem pref34_eq (v : ℕ) : pref34 v=FinalPrefixRows6815.row34 v := rfl
def pref35 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row35 v
theorem pref35_eq (v : ℕ) : pref35 v=FinalPrefixRows6815.row35 v := rfl
def pref36 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row36 v
theorem pref36_eq (v : ℕ) : pref36 v=FinalPrefixRows6815.row36 v := rfl
def pref37 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row37 v
theorem pref37_eq (v : ℕ) : pref37 v=FinalPrefixRows6815.row37 v := rfl
def pref38 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row38 v
theorem pref38_eq (v : ℕ) : pref38 v=FinalPrefixRows6815.row38 v := rfl
def pref39 (v : ℕ) : FinalPrefixRowsCheck6815.Entry := FinalPrefixRows6815.row39 v
theorem pref39_eq (v : ℕ) : pref39 v=FinalPrefixRows6815.row39 v := rfl
def pref (r v : ℕ) : FinalPrefixRowsCheck6815.Entry := match r with
  | 1 => pref1 v
  | 2 => pref2 v
  | 3 => pref3 v
  | 4 => pref4 v
  | 5 => pref5 v
  | 6 => pref6 v
  | 7 => pref7 v
  | 8 => pref8 v
  | 9 => pref9 v
  | 10 => pref10 v
  | 11 => pref11 v
  | 12 => pref12 v
  | 13 => pref13 v
  | 14 => pref14 v
  | 15 => pref15 v
  | 16 => pref16 v
  | 17 => pref17 v
  | 18 => pref18 v
  | 19 => pref19 v
  | 20 => pref20 v
  | 21 => pref21 v
  | 22 => pref22 v
  | 23 => pref23 v
  | 24 => pref24 v
  | 25 => pref25 v
  | 26 => pref26 v
  | 27 => pref27 v
  | 28 => pref28 v
  | 29 => pref29 v
  | 30 => pref30 v
  | 31 => pref31 v
  | 32 => pref32 v
  | 33 => pref33 v
  | 34 => pref34 v
  | 35 => pref35 v
  | 36 => pref36 v
  | 37 => pref37 v
  | 38 => pref38 v
  | 39 => pref39 v
  | _ => FinalPrefixRowsCheck6815.zero
theorem pref_eq (r v : ℕ) (hr : 1≤r) (hR : r≤39) : pref r v=FinalPrefixData6815.row r v := by
  interval_cases r
  · exact pref1_eq v
  · exact pref2_eq v
  · exact pref3_eq v
  · exact pref4_eq v
  · exact pref5_eq v
  · exact pref6_eq v
  · exact pref7_eq v
  · exact pref8_eq v
  · exact pref9_eq v
  · exact pref10_eq v
  · exact pref11_eq v
  · exact pref12_eq v
  · exact pref13_eq v
  · exact pref14_eq v
  · exact pref15_eq v
  · exact pref16_eq v
  · exact pref17_eq v
  · exact pref18_eq v
  · exact pref19_eq v
  · exact pref20_eq v
  · exact pref21_eq v
  · exact pref22_eq v
  · exact pref23_eq v
  · exact pref24_eq v
  · exact pref25_eq v
  · exact pref26_eq v
  · exact pref27_eq v
  · exact pref28_eq v
  · exact pref29_eq v
  · exact pref30_eq v
  · exact pref31_eq v
  · exact pref32_eq v
  · exact pref33_eq v
  · exact pref34_eq v
  · exact pref35_eq v
  · exact pref36_eq v
  · exact pref37_eq v
  · exact pref38_eq v
  · exact pref39_eq v
end ProximityPrize.SubmissionLower.FinalLookup6815
end MergedPart2
