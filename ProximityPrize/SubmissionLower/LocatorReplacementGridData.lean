import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit000
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit001
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit002
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit003
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit004
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit005
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit006
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit007
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit008
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit009
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit010
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit011
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit012
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit013
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit014
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit015
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit016
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit017
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit018
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit019
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit020
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit021
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit022
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit023
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit024
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit025
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit026
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit027
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit028
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit029
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit030
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit031
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit032
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit033
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit034
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit035
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit036
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit037
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit038
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit039
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit040
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit041
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit042
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit043
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit044
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit045
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit046
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit047
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit048
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit049
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit050
import ProximityPrize.SubmissionLower.LocatorReplacementGridHardUnit051

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- The exact width-eight parents that still fail at the 67.81 regular cap. -/
private theorem hardUnit_roster :
    ∀ c : UnitCell, FastHardUnit c →
    UnitAddress c 8 39 336 343 ∨ UnitAddress c 8 39 344 351 ∨ UnitAddress c 8 39 352 359 ∨ UnitAddress c 8 39 360 367 ∨
    UnitAddress c 8 39 368 375 ∨ UnitAddress c 8 39 376 383 ∨ UnitAddress c 8 39 384 391 ∨ UnitAddress c 8 39 392 399 ∨
    UnitAddress c 8 39 400 407 ∨ UnitAddress c 8 39 408 415 ∨ UnitAddress c 8 39 416 423 ∨ UnitAddress c 8 39 424 431 ∨
    UnitAddress c 8 39 432 439 ∨ UnitAddress c 8 38 920 927 ∨ UnitAddress c 8 38 928 935 ∨ UnitAddress c 8 38 936 943 ∨
    UnitAddress c 8 38 944 951 ∨ UnitAddress c 8 38 952 959 ∨ UnitAddress c 8 38 960 967 ∨ UnitAddress c 8 38 968 975 ∨
    UnitAddress c 8 38 976 983 ∨ UnitAddress c 8 38 984 991 ∨ UnitAddress c 8 38 992 999 ∨ UnitAddress c 8 38 1000 1007 ∨
    UnitAddress c 8 38 1008 1015 ∨ UnitAddress c 8 38 1016 1023 ∨ UnitAddress c 8 38 1024 1031 ∨ UnitAddress c 8 38 1032 1039 ∨
    UnitAddress c 8 38 1040 1047 ∨ UnitAddress c 8 38 1048 1055 ∨ UnitAddress c 8 38 1056 1063 ∨ UnitAddress c 8 38 1064 1071 ∨
    UnitAddress c 8 38 1072 1079 ∨ UnitAddress c 8 38 1080 1087 ∨ UnitAddress c 8 38 1088 1095 ∨ UnitAddress c 8 38 1096 1103 ∨
    UnitAddress c 8 38 1104 1111 ∨ UnitAddress c 8 38 1112 1119 ∨ UnitAddress c 8 38 1120 1127 ∨ UnitAddress c 8 38 1128 1135 ∨
    UnitAddress c 8 38 1136 1143 ∨ UnitAddress c 8 38 1144 1151 ∨ UnitAddress c 8 38 1152 1159 ∨ UnitAddress c 8 38 1160 1167 ∨
    UnitAddress c 8 38 1168 1175 ∨ UnitAddress c 8 38 1176 1183 ∨ UnitAddress c 8 38 1184 1191 ∨ UnitAddress c 8 38 1192 1199 ∨
    UnitAddress c 8 38 1200 1207 ∨ UnitAddress c 8 38 1208 1215 ∨ UnitAddress c 8 38 1216 1223 ∨ UnitAddress c 8 38 1224 1231
  := by decide +kernel

theorem receipt_subunit (c : SubunitCell) : Fits (subunitBox c) := by
  apply fastFits_to_fits
  have hfast : FastHardUnit c.parent.1 :=
    ⟨c.parent.2.1, fun h => c.parent.2.2 (fastFits_to_fits _ h)⟩
  have hroster := hardUnit_roster c.parent.1 hfast
  rcases hroster with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51
  · rw [subunitBox_eq_literal c 8 39 336 343 h0]
    exact receipt_hard_unit_000 c.ti
  · rw [subunitBox_eq_literal c 8 39 344 351 h1]
    exact receipt_hard_unit_001 c.ti
  · rw [subunitBox_eq_literal c 8 39 352 359 h2]
    exact receipt_hard_unit_002 c.ti
  · rw [subunitBox_eq_literal c 8 39 360 367 h3]
    exact receipt_hard_unit_003 c.ti
  · rw [subunitBox_eq_literal c 8 39 368 375 h4]
    exact receipt_hard_unit_004 c.ti
  · rw [subunitBox_eq_literal c 8 39 376 383 h5]
    exact receipt_hard_unit_005 c.ti
  · rw [subunitBox_eq_literal c 8 39 384 391 h6]
    exact receipt_hard_unit_006 c.ti
  · rw [subunitBox_eq_literal c 8 39 392 399 h7]
    exact receipt_hard_unit_007 c.ti
  · rw [subunitBox_eq_literal c 8 39 400 407 h8]
    exact receipt_hard_unit_008 c.ti
  · rw [subunitBox_eq_literal c 8 39 408 415 h9]
    exact receipt_hard_unit_009 c.ti
  · rw [subunitBox_eq_literal c 8 39 416 423 h10]
    exact receipt_hard_unit_010 c.ti
  · rw [subunitBox_eq_literal c 8 39 424 431 h11]
    exact receipt_hard_unit_011 c.ti
  · rw [subunitBox_eq_literal c 8 39 432 439 h12]
    exact receipt_hard_unit_012 c.ti
  · rw [subunitBox_eq_literal c 8 38 920 927 h13]
    exact receipt_hard_unit_013 c.ti
  · rw [subunitBox_eq_literal c 8 38 928 935 h14]
    exact receipt_hard_unit_014 c.ti
  · rw [subunitBox_eq_literal c 8 38 936 943 h15]
    exact receipt_hard_unit_015 c.ti
  · rw [subunitBox_eq_literal c 8 38 944 951 h16]
    exact receipt_hard_unit_016 c.ti
  · rw [subunitBox_eq_literal c 8 38 952 959 h17]
    exact receipt_hard_unit_017 c.ti
  · rw [subunitBox_eq_literal c 8 38 960 967 h18]
    exact receipt_hard_unit_018 c.ti
  · rw [subunitBox_eq_literal c 8 38 968 975 h19]
    exact receipt_hard_unit_019 c.ti
  · rw [subunitBox_eq_literal c 8 38 976 983 h20]
    exact receipt_hard_unit_020 c.ti
  · rw [subunitBox_eq_literal c 8 38 984 991 h21]
    exact receipt_hard_unit_021 c.ti
  · rw [subunitBox_eq_literal c 8 38 992 999 h22]
    exact receipt_hard_unit_022 c.ti
  · rw [subunitBox_eq_literal c 8 38 1000 1007 h23]
    exact receipt_hard_unit_023 c.ti
  · rw [subunitBox_eq_literal c 8 38 1008 1015 h24]
    exact receipt_hard_unit_024 c.ti
  · rw [subunitBox_eq_literal c 8 38 1016 1023 h25]
    exact receipt_hard_unit_025 c.ti
  · rw [subunitBox_eq_literal c 8 38 1024 1031 h26]
    exact receipt_hard_unit_026 c.ti
  · rw [subunitBox_eq_literal c 8 38 1032 1039 h27]
    exact receipt_hard_unit_027 c.ti
  · rw [subunitBox_eq_literal c 8 38 1040 1047 h28]
    exact receipt_hard_unit_028 c.ti
  · rw [subunitBox_eq_literal c 8 38 1048 1055 h29]
    exact receipt_hard_unit_029 c.ti
  · rw [subunitBox_eq_literal c 8 38 1056 1063 h30]
    exact receipt_hard_unit_030 c.ti
  · rw [subunitBox_eq_literal c 8 38 1064 1071 h31]
    exact receipt_hard_unit_031 c.ti
  · rw [subunitBox_eq_literal c 8 38 1072 1079 h32]
    exact receipt_hard_unit_032 c.ti
  · rw [subunitBox_eq_literal c 8 38 1080 1087 h33]
    exact receipt_hard_unit_033 c.ti
  · rw [subunitBox_eq_literal c 8 38 1088 1095 h34]
    exact receipt_hard_unit_034 c.ti
  · rw [subunitBox_eq_literal c 8 38 1096 1103 h35]
    exact receipt_hard_unit_035 c.ti
  · rw [subunitBox_eq_literal c 8 38 1104 1111 h36]
    exact receipt_hard_unit_036 c.ti
  · rw [subunitBox_eq_literal c 8 38 1112 1119 h37]
    exact receipt_hard_unit_037 c.ti
  · rw [subunitBox_eq_literal c 8 38 1120 1127 h38]
    exact receipt_hard_unit_038 c.ti
  · rw [subunitBox_eq_literal c 8 38 1128 1135 h39]
    exact receipt_hard_unit_039 c.ti
  · rw [subunitBox_eq_literal c 8 38 1136 1143 h40]
    exact receipt_hard_unit_040 c.ti
  · rw [subunitBox_eq_literal c 8 38 1144 1151 h41]
    exact receipt_hard_unit_041 c.ti
  · rw [subunitBox_eq_literal c 8 38 1152 1159 h42]
    exact receipt_hard_unit_042 c.ti
  · rw [subunitBox_eq_literal c 8 38 1160 1167 h43]
    exact receipt_hard_unit_043 c.ti
  · rw [subunitBox_eq_literal c 8 38 1168 1175 h44]
    exact receipt_hard_unit_044 c.ti
  · rw [subunitBox_eq_literal c 8 38 1176 1183 h45]
    exact receipt_hard_unit_045 c.ti
  · rw [subunitBox_eq_literal c 8 38 1184 1191 h46]
    exact receipt_hard_unit_046 c.ti
  · rw [subunitBox_eq_literal c 8 38 1192 1199 h47]
    exact receipt_hard_unit_047 c.ti
  · rw [subunitBox_eq_literal c 8 38 1200 1207 h48]
    exact receipt_hard_unit_048 c.ti
  · rw [subunitBox_eq_literal c 8 38 1208 1215 h49]
    exact receipt_hard_unit_049 c.ti
  · rw [subunitBox_eq_literal c 8 38 1216 1223 h50]
    exact receipt_hard_unit_050 c.ti
  · rw [subunitBox_eq_literal c 8 38 1224 1231 h51]
    exact receipt_hard_unit_051 c.ti

/-- Every valid leaf has either the direct ordinary rate or a conservative
    source replacement rate.  Coarse, fine, and width-eight failures are
    refined definitionally; generated width-two receipts close the leaves. -/
theorem receipt (c : Cell) : Valid c → Fits (box c) := by
  intro hv
  rcases c with c | c
  · simp only [Valid, box, Leaf] at hv ⊢
    by_contra hfit
    exact hv.2 ⟨hv.1, hfit⟩
  · rcases c with c | c
    · simp only [Valid, box, Leaf] at hv ⊢
      by_contra hfit
      exact hv.2 ⟨hv.1, hfit⟩
    · rcases c with c | c
      · simp only [Valid, box, Leaf] at hv ⊢
        by_contra hfit
        exact hv.2 ⟨hv.1, hfit⟩
      · simpa only [Valid, box, Leaf] using receipt_subunit c

def chosenCost (c : Cell) : ℕ :=
  let b := box c
  if b.ordinaryFits then b.ordinaryCost
  else if RouteFits sourceA 1 b then routeCost sourceA b 1
  else if RouteFits sourceAux 1 b then routeCost sourceAux b 1
  else if RouteFits sourceC 2 b then routeCost sourceC b 2
  else if RouteFits sourceC 3 b then routeCost sourceC b 3
  else if RouteFits sourceC 4 b then routeCost sourceC b 4
  else if RouteFits sourceC 5 b then routeCost sourceC b 5
  else if RouteFits sourceC 6 b then routeCost sourceC b 6
  else if RouteFits sourceC 7 b then routeCost sourceC b 7
  else if RouteFits sourceC 8 b then routeCost sourceC b 8
  else routeCost sourceC b 9

theorem chosenCost_rate (c : Cell) (hv : Valid c) :
    totalCap * chosenCost c ≤ bound * (box c).factorT := by
  have h := receipt c hv
  simp only [Fits] at h
  by_cases ho : (box c).ordinaryFits
  · rw [chosenCost, if_pos ho]
    exact ho
  · have hroutes := h.resolve_left ho
    by_cases hA : RouteFits sourceA 1 (box c)
    · simpa only [chosenCost, ho, hA, if_pos, if_false] using
        hA.2.2.2.2.2.2.2.2
    · have hroutes := hroutes.resolve_left hA
      by_cases hAux : RouteFits sourceAux 1 (box c)
      · simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using
          hAux.2.2.2.2.2.2.2.2
      · have hroutes := hroutes.resolve_left hAux
        by_cases hC2 : RouteFits sourceC 2 (box c)
        · simpa only [chosenCost, ho, hA, hAux, hC2, if_pos, if_false] using
            hC2.2.2.2.2.2.2.2.2
        · have hroutes := hroutes.resolve_left hC2
          by_cases hC3 : RouteFits sourceC 3 (box c)
          · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, if_pos, if_false] using
              hC3.2.2.2.2.2.2.2.2
          · have hroutes := hroutes.resolve_left hC3
            by_cases hC4 : RouteFits sourceC 4 (box c)
            · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
                if_pos, if_false] using hC4.2.2.2.2.2.2.2.2
            · have hroutes := hroutes.resolve_left hC4
              by_cases hC5 : RouteFits sourceC 5 (box c)
              · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                  if_pos, if_false] using hC5.2.2.2.2.2.2.2.2
              · have hroutes := hroutes.resolve_left hC5
                by_cases hC6 : RouteFits sourceC 6 (box c)
                · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                    hC6, if_pos, if_false] using hC6.2.2.2.2.2.2.2.2
                · have hroutes := hroutes.resolve_left hC6
                  by_cases hC7 : RouteFits sourceC 7 (box c)
                  · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                      hC6, hC7, if_pos, if_false] using hC7.2.2.2.2.2.2.2.2
                  · have hroutes := hroutes.resolve_left hC7
                    by_cases hC8 : RouteFits sourceC 8 (box c)
                    · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                        hC6, hC7, hC8, if_pos, if_false] using hC8.2.2.2.2.2.2.2.2
                    · have hC9 := hroutes.resolve_left hC8
                      simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                        hC6, hC7, hC8, if_pos, if_false] using hC9.2.2.2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
