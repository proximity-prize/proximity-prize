import ProximityPrize.SubmissionLower.Koala6844ReceiptsEndpointCover
import ProximityPrize.SubmissionLower.Koala6844ReceiptsBandProof

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem terminalGate_3_stop :
    bandCovers secondAdaptiveFlag ⟨3, 103, 103⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 103, 103⟩ secondAdaptiveGap
    [⟨643, true, true⟩, ⟨804, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_3 :
    bandCovers secondAdaptiveFlag ⟨3, 3, 4944⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 3, 4944⟩ secondAdaptiveGap
    [⟨727, true, true⟩, ⟨740, false, true⟩, ⟨744, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_4 :
    bandCovers secondAdaptiveFlag ⟨3, 4, 4928⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 4, 4928⟩ secondAdaptiveGap
    [⟨730, true, true⟩, ⟨743, false, true⟩, ⟨746, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_5 :
    bandCovers secondAdaptiveFlag ⟨3, 5, 4911⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 5, 4911⟩ secondAdaptiveGap
    [⟨732, true, true⟩, ⟨745, false, true⟩, ⟨749, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_6 :
    bandCovers secondAdaptiveFlag ⟨3, 6, 4894⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 6, 4894⟩ secondAdaptiveGap
    [⟨735, true, true⟩, ⟨748, false, true⟩, ⟨751, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_7 :
    bandCovers secondAdaptiveFlag ⟨3, 7, 4877⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 7, 4877⟩ secondAdaptiveGap
    [⟨738, true, true⟩, ⟨750, false, true⟩, ⟨754, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_8 :
    bandCovers secondAdaptiveFlag ⟨3, 8, 4860⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 8, 4860⟩ secondAdaptiveGap
    [⟨741, true, true⟩, ⟨753, false, true⟩, ⟨756, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_9 :
    bandCovers secondAdaptiveFlag ⟨3, 9, 4843⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 9, 4843⟩ secondAdaptiveGap
    [⟨743, true, true⟩, ⟨756, false, true⟩, ⟨759, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_10 :
    bandCovers secondAdaptiveFlag ⟨3, 10, 4826⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 10, 4826⟩ secondAdaptiveGap
    [⟨746, true, true⟩, ⟨758, false, true⟩, ⟨762, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_11 :
    bandCovers secondAdaptiveFlag ⟨3, 11, 4808⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 11, 4808⟩ secondAdaptiveGap
    [⟨749, true, true⟩, ⟨761, false, true⟩, ⟨765, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_12 :
    bandCovers secondAdaptiveFlag ⟨3, 12, 4791⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 12, 4791⟩ secondAdaptiveGap
    [⟨752, true, true⟩, ⟨764, false, true⟩, ⟨767, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_13 :
    bandCovers secondAdaptiveFlag ⟨3, 13, 4773⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 13, 4773⟩ secondAdaptiveGap
    [⟨755, true, true⟩, ⟨767, false, true⟩, ⟨770, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_14 :
    bandCovers secondAdaptiveFlag ⟨3, 14, 4755⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 14, 4755⟩ secondAdaptiveGap
    [⟨758, true, true⟩, ⟨770, false, true⟩, ⟨773, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_15 :
    bandCovers secondAdaptiveFlag ⟨3, 15, 4737⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 15, 4737⟩ secondAdaptiveGap
    [⟨761, true, true⟩, ⟨773, false, true⟩, ⟨776, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_16 :
    bandCovers secondAdaptiveFlag ⟨3, 16, 4719⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 16, 4719⟩ secondAdaptiveGap
    [⟨764, true, true⟩, ⟨776, false, true⟩, ⟨779, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_17 :
    bandCovers secondAdaptiveFlag ⟨3, 17, 4701⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 17, 4701⟩ secondAdaptiveGap
    [⟨767, true, true⟩, ⟨779, false, true⟩, ⟨782, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_18 :
    bandCovers secondAdaptiveFlag ⟨3, 18, 4682⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 18, 4682⟩ secondAdaptiveGap
    [⟨771, true, true⟩, ⟨782, false, true⟩, ⟨785, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_19 :
    bandCovers secondAdaptiveFlag ⟨3, 19, 4664⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 19, 4664⟩ secondAdaptiveGap
    [⟨774, true, true⟩, ⟨785, false, true⟩, ⟨788, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_20 :
    bandCovers secondAdaptiveFlag ⟨3, 20, 4645⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 20, 4645⟩ secondAdaptiveGap
    [⟨777, true, true⟩, ⟨788, false, true⟩, ⟨791, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_21 :
    bandCovers secondAdaptiveFlag ⟨3, 21, 4626⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 21, 4626⟩ secondAdaptiveGap
    [⟨780, true, true⟩, ⟨791, false, true⟩, ⟨795, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_22 :
    bandCovers secondAdaptiveFlag ⟨3, 22, 4607⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 22, 4607⟩ secondAdaptiveGap
    [⟨784, true, true⟩, ⟨795, false, true⟩, ⟨798, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_23 :
    bandCovers secondAdaptiveFlag ⟨3, 23, 4588⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 23, 4588⟩ secondAdaptiveGap
    [⟨787, true, true⟩, ⟨798, false, true⟩, ⟨801, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_24 :
    bandCovers secondAdaptiveFlag ⟨3, 24, 4568⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 24, 4568⟩ secondAdaptiveGap
    [⟨791, true, true⟩, ⟨801, false, true⟩, ⟨805, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_25 :
    bandCovers secondAdaptiveFlag ⟨3, 25, 4549⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 25, 4549⟩ secondAdaptiveGap
    [⟨794, true, true⟩, ⟨805, false, true⟩, ⟨808, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_26 :
    bandCovers secondAdaptiveFlag ⟨3, 26, 4529⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 26, 4529⟩ secondAdaptiveGap
    [⟨798, true, true⟩, ⟨808, false, true⟩, ⟨812, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_27 :
    bandCovers secondAdaptiveFlag ⟨3, 27, 4509⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 27, 4509⟩ secondAdaptiveGap
    [⟨802, true, true⟩, ⟨812, false, true⟩, ⟨815, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_28 :
    bandCovers secondAdaptiveFlag ⟨3, 28, 4488⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 28, 4488⟩ secondAdaptiveGap
    [⟨806, true, true⟩, ⟨816, false, true⟩, ⟨819, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_29 :
    bandCovers secondAdaptiveFlag ⟨3, 29, 4468⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 29, 4468⟩ secondAdaptiveGap
    [⟨810, true, true⟩, ⟨819, false, true⟩, ⟨823, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_30 :
    bandCovers secondAdaptiveFlag ⟨3, 30, 4447⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 30, 4447⟩ secondAdaptiveGap
    [⟨814, true, true⟩, ⟨823, false, true⟩, ⟨827, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_31 :
    bandCovers secondAdaptiveFlag ⟨3, 31, 4426⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 31, 4426⟩ secondAdaptiveGap
    [⟨818, true, true⟩, ⟨827, false, true⟩, ⟨831, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_32 :
    bandCovers secondAdaptiveFlag ⟨3, 32, 4405⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 32, 4405⟩ secondAdaptiveGap
    [⟨822, true, true⟩, ⟨831, false, true⟩, ⟨835, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_33 :
    bandCovers secondAdaptiveFlag ⟨3, 33, 4384⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 33, 4384⟩ secondAdaptiveGap
    [⟨826, true, true⟩, ⟨835, false, true⟩, ⟨839, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_34 :
    bandCovers secondAdaptiveFlag ⟨3, 34, 4362⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 34, 4362⟩ secondAdaptiveGap
    [⟨830, true, true⟩, ⟨839, false, true⟩, ⟨843, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_35 :
    bandCovers secondAdaptiveFlag ⟨3, 35, 4340⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 35, 4340⟩ secondAdaptiveGap
    [⟨835, true, true⟩, ⟨843, false, true⟩, ⟨847, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_36 :
    bandCovers secondAdaptiveFlag ⟨3, 36, 4318⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 36, 4318⟩ secondAdaptiveGap
    [⟨839, true, true⟩, ⟨848, false, true⟩, ⟨851, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_37 :
    bandCovers secondAdaptiveFlag ⟨3, 37, 4296⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 37, 4296⟩ secondAdaptiveGap
    [⟨844, true, true⟩, ⟨852, false, true⟩, ⟨856, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_38 :
    bandCovers secondAdaptiveFlag ⟨3, 38, 4273⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 38, 4273⟩ secondAdaptiveGap
    [⟨849, true, true⟩, ⟨857, false, true⟩, ⟨860, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_39 :
    bandCovers secondAdaptiveFlag ⟨3, 39, 4250⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 39, 4250⟩ secondAdaptiveGap
    [⟨853, true, true⟩, ⟨861, false, true⟩, ⟨865, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_40 :
    bandCovers secondAdaptiveFlag ⟨3, 40, 4226⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 40, 4226⟩ secondAdaptiveGap
    [⟨859, true, true⟩, ⟨866, false, true⟩, ⟨870, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_41 :
    bandCovers secondAdaptiveFlag ⟨3, 41, 4203⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 41, 4203⟩ secondAdaptiveGap
    [⟨864, true, true⟩, ⟨871, false, true⟩, ⟨875, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_42 :
    bandCovers secondAdaptiveFlag ⟨3, 42, 4179⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 42, 4179⟩ secondAdaptiveGap
    [⟨869, true, true⟩, ⟨876, false, true⟩, ⟨880, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_43 :
    bandCovers secondAdaptiveFlag ⟨3, 43, 4154⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 43, 4154⟩ secondAdaptiveGap
    [⟨874, true, true⟩, ⟨881, false, true⟩, ⟨885, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_44 :
    bandCovers secondAdaptiveFlag ⟨3, 44, 4130⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 44, 4130⟩ secondAdaptiveGap
    [⟨880, true, true⟩, ⟨886, false, true⟩, ⟨890, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_45 :
    bandCovers secondAdaptiveFlag ⟨3, 45, 4105⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 45, 4105⟩ secondAdaptiveGap
    [⟨885, true, true⟩, ⟨892, false, true⟩, ⟨896, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_46 :
    bandCovers secondAdaptiveFlag ⟨3, 46, 4079⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 46, 4079⟩ secondAdaptiveGap
    [⟨891, true, true⟩, ⟨898, false, true⟩, ⟨901, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_47 :
    bandCovers secondAdaptiveFlag ⟨3, 47, 4053⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 47, 4053⟩ secondAdaptiveGap
    [⟨897, true, true⟩, ⟨903, false, true⟩, ⟨907, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_48 :
    bandCovers secondAdaptiveFlag ⟨3, 48, 4027⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 48, 4027⟩ secondAdaptiveGap
    [⟨903, true, true⟩, ⟨909, false, true⟩, ⟨913, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_49 :
    bandCovers secondAdaptiveFlag ⟨3, 49, 4000⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 49, 4000⟩ secondAdaptiveGap
    [⟨910, true, true⟩, ⟨915, false, true⟩, ⟨919, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_50 :
    bandCovers secondAdaptiveFlag ⟨3, 50, 3972⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 50, 3972⟩ secondAdaptiveGap
    [⟨916, true, true⟩, ⟨922, false, true⟩, ⟨926, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_51 :
    bandCovers secondAdaptiveFlag ⟨3, 51, 3944⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 51, 3944⟩ secondAdaptiveGap
    [⟨923, true, true⟩, ⟨928, false, true⟩, ⟨932, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_52 :
    bandCovers secondAdaptiveFlag ⟨3, 52, 3916⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 52, 3916⟩ secondAdaptiveGap
    [⟨930, true, true⟩, ⟨935, false, true⟩, ⟨939, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_53 :
    bandCovers secondAdaptiveFlag ⟨3, 53, 3887⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 53, 3887⟩ secondAdaptiveGap
    [⟨937, true, true⟩, ⟨942, false, true⟩, ⟨946, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_54 :
    bandCovers secondAdaptiveFlag ⟨3, 54, 3857⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 54, 3857⟩ secondAdaptiveGap
    [⟨945, true, true⟩, ⟨949, false, true⟩, ⟨953, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_55 :
    bandCovers secondAdaptiveFlag ⟨3, 55, 3827⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 55, 3827⟩ secondAdaptiveGap
    [⟨953, true, true⟩, ⟨957, false, true⟩, ⟨961, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_56 :
    bandCovers secondAdaptiveFlag ⟨3, 56, 3796⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 56, 3796⟩ secondAdaptiveGap
    [⟨961, true, true⟩, ⟨965, false, true⟩, ⟨969, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_57 :
    bandCovers secondAdaptiveFlag ⟨3, 57, 3764⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 57, 3764⟩ secondAdaptiveGap
    [⟨970, true, true⟩, ⟨973, false, true⟩, ⟨977, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_58 :
    bandCovers secondAdaptiveFlag ⟨3, 58, 3732⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 58, 3732⟩ secondAdaptiveGap
    [⟨978, true, true⟩, ⟨981, false, true⟩, ⟨985, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_59 :
    bandCovers secondAdaptiveFlag ⟨3, 59, 3698⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 59, 3698⟩ secondAdaptiveGap
    [⟨988, true, true⟩, ⟨990, false, true⟩, ⟨994, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_60 :
    bandCovers secondAdaptiveFlag ⟨3, 60, 3664⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 60, 3664⟩ secondAdaptiveGap
    [⟨997, true, true⟩, ⟨999, false, true⟩, ⟨1004, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_61 :
    bandCovers secondAdaptiveFlag ⟨3, 61, 3628⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 61, 3628⟩ secondAdaptiveGap
    [⟨1008, true, true⟩, ⟨1009, false, true⟩, ⟨1014, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_62 :
    bandCovers secondAdaptiveFlag ⟨3, 62, 3592⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 62, 3592⟩ secondAdaptiveGap
    [⟨1018, true, true⟩, ⟨1019, false, true⟩, ⟨1024, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_63 :
    bandCovers secondAdaptiveFlag ⟨3, 63, 3554⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 63, 3554⟩ secondAdaptiveGap
    [⟨1030, true, true⟩, ⟨1035, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_64 :
    bandCovers secondAdaptiveFlag ⟨3, 64, 3514⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 64, 3514⟩ secondAdaptiveGap
    [⟨1042, true, true⟩, ⟨1046, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_65 :
    bandCovers secondAdaptiveFlag ⟨3, 65, 3474⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 65, 3474⟩ secondAdaptiveGap
    [⟨1038, true, true⟩, ⟨1054, true, false⟩, ⟨1058, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_66 :
    bandCovers secondAdaptiveFlag ⟨3, 66, 3431⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 66, 3431⟩ secondAdaptiveGap
    [⟨1021, true, true⟩, ⟨1068, true, false⟩, ⟨1072, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_67 :
    bandCovers secondAdaptiveFlag ⟨3, 67, 3386⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 67, 3386⟩ secondAdaptiveGap
    [⟨1005, true, true⟩, ⟨1083, true, false⟩, ⟨1086, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_68 :
    bandCovers secondAdaptiveFlag ⟨3, 68, 3340⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 68, 3340⟩ secondAdaptiveGap
    [⟨990, true, true⟩, ⟨1099, true, false⟩, ⟨1101, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_69 :
    bandCovers secondAdaptiveFlag ⟨3, 69, 3291⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 69, 3291⟩ secondAdaptiveGap
    [⟨975, true, true⟩, ⟨1116, true, false⟩, ⟨1117, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_70 :
    bandCovers secondAdaptiveFlag ⟨3, 70, 3239⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 70, 3239⟩ secondAdaptiveGap
    [⟨960, true, true⟩, ⟨1134, true, false⟩, ⟨1135, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_71 :
    bandCovers secondAdaptiveFlag ⟨3, 71, 3185⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 71, 3185⟩ secondAdaptiveGap
    [⟨946, true, true⟩, ⟨1154, true, false⟩, ⟨1155, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_72 :
    bandCovers secondAdaptiveFlag ⟨3, 72, 3128⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 72, 3128⟩ secondAdaptiveGap
    [⟨932, true, true⟩, ⟨1150, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_73 :
    bandCovers secondAdaptiveFlag ⟨3, 73, 3068⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 73, 3068⟩ secondAdaptiveGap
    [⟨919, true, true⟩, ⟨1134, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_74 :
    bandCovers secondAdaptiveFlag ⟨3, 74, 3005⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 74, 3005⟩ secondAdaptiveGap
    [⟨906, true, true⟩, ⟨1119, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_75 :
    bandCovers secondAdaptiveFlag ⟨3, 75, 2940⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 75, 2940⟩ secondAdaptiveGap
    [⟨893, true, true⟩, ⟨1104, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_76 :
    bandCovers secondAdaptiveFlag ⟨3, 76, 2872⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 76, 2872⟩ secondAdaptiveGap
    [⟨881, true, true⟩, ⟨1089, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_77 :
    bandCovers secondAdaptiveFlag ⟨3, 77, 2801⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 77, 2801⟩ secondAdaptiveGap
    [⟨869, true, true⟩, ⟨1075, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_78 :
    bandCovers secondAdaptiveFlag ⟨3, 78, 2727⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 78, 2727⟩ secondAdaptiveGap
    [⟨858, true, true⟩, ⟨1062, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_79 :
    bandCovers secondAdaptiveFlag ⟨3, 79, 2651⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 79, 2651⟩ secondAdaptiveGap
    [⟨846, true, true⟩, ⟨1048, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_80 :
    bandCovers secondAdaptiveFlag ⟨3, 80, 2572⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 80, 2572⟩ secondAdaptiveGap
    [⟨835, true, true⟩, ⟨1035, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_81 :
    bandCovers secondAdaptiveFlag ⟨3, 81, 2490⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 81, 2490⟩ secondAdaptiveGap
    [⟨825, true, true⟩, ⟨1022, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_82 :
    bandCovers secondAdaptiveFlag ⟨3, 82, 2405⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 82, 2405⟩ secondAdaptiveGap
    [⟨814, true, true⟩, ⟨1010, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_83 :
    bandCovers secondAdaptiveFlag ⟨3, 83, 2317⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 83, 2317⟩ secondAdaptiveGap
    [⟨804, true, true⟩, ⟨998, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_84 :
    bandCovers secondAdaptiveFlag ⟨3, 84, 2227⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 84, 2227⟩ secondAdaptiveGap
    [⟨794, true, true⟩, ⟨986, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_85 :
    bandCovers secondAdaptiveFlag ⟨3, 85, 2134⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 85, 2134⟩ secondAdaptiveGap
    [⟨784, true, true⟩, ⟨974, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_86 :
    bandCovers secondAdaptiveFlag ⟨3, 86, 2038⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 86, 2038⟩ secondAdaptiveGap
    [⟨775, true, true⟩, ⟨963, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_87 :
    bandCovers secondAdaptiveFlag ⟨3, 87, 1939⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 87, 1939⟩ secondAdaptiveGap
    [⟨766, true, true⟩, ⟨952, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_88 :
    bandCovers secondAdaptiveFlag ⟨3, 88, 1838⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 88, 1838⟩ secondAdaptiveGap
    [⟨757, true, true⟩, ⟨941, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_89 :
    bandCovers secondAdaptiveFlag ⟨3, 89, 1734⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 89, 1734⟩ secondAdaptiveGap
    [⟨748, true, true⟩, ⟨930, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_90 :
    bandCovers secondAdaptiveFlag ⟨3, 90, 1627⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 90, 1627⟩ secondAdaptiveGap
    [⟨739, true, true⟩, ⟨920, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_91 :
    bandCovers secondAdaptiveFlag ⟨3, 91, 1517⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 91, 1517⟩ secondAdaptiveGap
    [⟨731, true, true⟩, ⟨910, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_92 :
    bandCovers secondAdaptiveFlag ⟨3, 92, 1404⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 92, 1404⟩ secondAdaptiveGap
    [⟨723, true, true⟩, ⟨900, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_93 :
    bandCovers secondAdaptiveFlag ⟨3, 93, 1289⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 93, 1289⟩ secondAdaptiveGap
    [⟨715, true, true⟩, ⟨890, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_94 :
    bandCovers secondAdaptiveFlag ⟨3, 94, 1171⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 94, 1171⟩ secondAdaptiveGap
    [⟨707, true, true⟩, ⟨881, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_95 :
    bandCovers secondAdaptiveFlag ⟨3, 95, 1050⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 95, 1050⟩ secondAdaptiveGap
    [⟨699, true, true⟩, ⟨871, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_96 :
    bandCovers secondAdaptiveFlag ⟨3, 96, 926⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 96, 926⟩ secondAdaptiveGap
    [⟨692, true, true⟩, ⟨862, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_97 :
    bandCovers secondAdaptiveFlag ⟨3, 97, 800⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 97, 800⟩ secondAdaptiveGap
    [⟨684, true, true⟩, ⟨854, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_98 :
    bandCovers secondAdaptiveFlag ⟨3, 98, 670⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 98, 670⟩ secondAdaptiveGap
    [⟨677, true, true⟩, ⟨845, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_99 :
    bandCovers secondAdaptiveFlag ⟨3, 99, 538⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 99, 538⟩ secondAdaptiveGap
    [⟨670, true, true⟩, ⟨836, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_100 :
    bandCovers secondAdaptiveFlag ⟨3, 100, 404⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 100, 404⟩ secondAdaptiveGap
    [⟨663, true, true⟩, ⟨828, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_101 :
    bandCovers secondAdaptiveFlag ⟨3, 101, 266⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 101, 266⟩ secondAdaptiveGap
    [⟨656, true, true⟩, ⟨820, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_3_102 :
    bandCovers secondAdaptiveFlag ⟨3, 102, 126⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨3, 102, 126⟩ secondAdaptiveGap
    [⟨650, true, true⟩, ⟨812, true, false⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape03 : TerminalSlopeTape 3 3 :=  TerminalSlopeTape.row (r := 3) (y := 3) 4943 (by decide) terminalGate_3_3 (
  TerminalSlopeTape.row (r := 3) (y := 4) 4927 (by decide) terminalGate_3_4 (
  TerminalSlopeTape.row (r := 3) (y := 5) 4910 (by decide) terminalGate_3_5 (
  TerminalSlopeTape.row (r := 3) (y := 6) 4893 (by decide) terminalGate_3_6 (
  TerminalSlopeTape.row (r := 3) (y := 7) 4876 (by decide) terminalGate_3_7 (
  TerminalSlopeTape.row (r := 3) (y := 8) 4859 (by decide) terminalGate_3_8 (
  TerminalSlopeTape.row (r := 3) (y := 9) 4842 (by decide) terminalGate_3_9 (
  TerminalSlopeTape.row (r := 3) (y := 10) 4825 (by decide) terminalGate_3_10 (
  TerminalSlopeTape.row (r := 3) (y := 11) 4807 (by decide) terminalGate_3_11 (
  TerminalSlopeTape.row (r := 3) (y := 12) 4790 (by decide) terminalGate_3_12 (
  TerminalSlopeTape.row (r := 3) (y := 13) 4772 (by decide) terminalGate_3_13 (
  TerminalSlopeTape.row (r := 3) (y := 14) 4754 (by decide) terminalGate_3_14 (
  TerminalSlopeTape.row (r := 3) (y := 15) 4736 (by decide) terminalGate_3_15 (
  TerminalSlopeTape.row (r := 3) (y := 16) 4718 (by decide) terminalGate_3_16 (
  TerminalSlopeTape.row (r := 3) (y := 17) 4700 (by decide) terminalGate_3_17 (
  TerminalSlopeTape.row (r := 3) (y := 18) 4681 (by decide) terminalGate_3_18 (
  TerminalSlopeTape.row (r := 3) (y := 19) 4663 (by decide) terminalGate_3_19 (
  TerminalSlopeTape.row (r := 3) (y := 20) 4644 (by decide) terminalGate_3_20 (
  TerminalSlopeTape.row (r := 3) (y := 21) 4625 (by decide) terminalGate_3_21 (
  TerminalSlopeTape.row (r := 3) (y := 22) 4606 (by decide) terminalGate_3_22 (
  TerminalSlopeTape.row (r := 3) (y := 23) 4587 (by decide) terminalGate_3_23 (
  TerminalSlopeTape.row (r := 3) (y := 24) 4567 (by decide) terminalGate_3_24 (
  TerminalSlopeTape.row (r := 3) (y := 25) 4548 (by decide) terminalGate_3_25 (
  TerminalSlopeTape.row (r := 3) (y := 26) 4528 (by decide) terminalGate_3_26 (
  TerminalSlopeTape.row (r := 3) (y := 27) 4508 (by decide) terminalGate_3_27 (
  TerminalSlopeTape.row (r := 3) (y := 28) 4487 (by decide) terminalGate_3_28 (
  TerminalSlopeTape.row (r := 3) (y := 29) 4467 (by decide) terminalGate_3_29 (
  TerminalSlopeTape.row (r := 3) (y := 30) 4446 (by decide) terminalGate_3_30 (
  TerminalSlopeTape.row (r := 3) (y := 31) 4425 (by decide) terminalGate_3_31 (
  TerminalSlopeTape.row (r := 3) (y := 32) 4404 (by decide) terminalGate_3_32 (
  TerminalSlopeTape.row (r := 3) (y := 33) 4383 (by decide) terminalGate_3_33 (
  TerminalSlopeTape.row (r := 3) (y := 34) 4361 (by decide) terminalGate_3_34 (
  TerminalSlopeTape.row (r := 3) (y := 35) 4339 (by decide) terminalGate_3_35 (
  TerminalSlopeTape.row (r := 3) (y := 36) 4317 (by decide) terminalGate_3_36 (
  TerminalSlopeTape.row (r := 3) (y := 37) 4295 (by decide) terminalGate_3_37 (
  TerminalSlopeTape.row (r := 3) (y := 38) 4272 (by decide) terminalGate_3_38 (
  TerminalSlopeTape.row (r := 3) (y := 39) 4249 (by decide) terminalGate_3_39 (
  TerminalSlopeTape.row (r := 3) (y := 40) 4225 (by decide) terminalGate_3_40 (
  TerminalSlopeTape.row (r := 3) (y := 41) 4202 (by decide) terminalGate_3_41 (
  TerminalSlopeTape.row (r := 3) (y := 42) 4178 (by decide) terminalGate_3_42 (
  TerminalSlopeTape.row (r := 3) (y := 43) 4153 (by decide) terminalGate_3_43 (
  TerminalSlopeTape.row (r := 3) (y := 44) 4129 (by decide) terminalGate_3_44 (
  TerminalSlopeTape.row (r := 3) (y := 45) 4104 (by decide) terminalGate_3_45 (
  TerminalSlopeTape.row (r := 3) (y := 46) 4078 (by decide) terminalGate_3_46 (
  TerminalSlopeTape.row (r := 3) (y := 47) 4052 (by decide) terminalGate_3_47 (
  TerminalSlopeTape.row (r := 3) (y := 48) 4026 (by decide) terminalGate_3_48 (
  TerminalSlopeTape.row (r := 3) (y := 49) 3999 (by decide) terminalGate_3_49 (
  TerminalSlopeTape.row (r := 3) (y := 50) 3971 (by decide) terminalGate_3_50 (
  TerminalSlopeTape.row (r := 3) (y := 51) 3943 (by decide) terminalGate_3_51 (
  TerminalSlopeTape.row (r := 3) (y := 52) 3915 (by decide) terminalGate_3_52 (
  TerminalSlopeTape.row (r := 3) (y := 53) 3886 (by decide) terminalGate_3_53 (
  TerminalSlopeTape.row (r := 3) (y := 54) 3856 (by decide) terminalGate_3_54 (
  TerminalSlopeTape.row (r := 3) (y := 55) 3826 (by decide) terminalGate_3_55 (
  TerminalSlopeTape.row (r := 3) (y := 56) 3795 (by decide) terminalGate_3_56 (
  TerminalSlopeTape.row (r := 3) (y := 57) 3763 (by decide) terminalGate_3_57 (
  TerminalSlopeTape.row (r := 3) (y := 58) 3731 (by decide) terminalGate_3_58 (
  TerminalSlopeTape.row (r := 3) (y := 59) 3697 (by decide) terminalGate_3_59 (
  TerminalSlopeTape.row (r := 3) (y := 60) 3663 (by decide) terminalGate_3_60 (
  TerminalSlopeTape.row (r := 3) (y := 61) 3627 (by decide) terminalGate_3_61 (
  TerminalSlopeTape.row (r := 3) (y := 62) 3591 (by decide) terminalGate_3_62 (
  TerminalSlopeTape.row (r := 3) (y := 63) 3553 (by decide) terminalGate_3_63 (
  TerminalSlopeTape.row (r := 3) (y := 64) 3513 (by decide) terminalGate_3_64 (
  TerminalSlopeTape.row (r := 3) (y := 65) 3473 (by decide) terminalGate_3_65 (
  TerminalSlopeTape.row (r := 3) (y := 66) 3430 (by decide) terminalGate_3_66 (
  TerminalSlopeTape.row (r := 3) (y := 67) 3385 (by decide) terminalGate_3_67 (
  TerminalSlopeTape.row (r := 3) (y := 68) 3339 (by decide) terminalGate_3_68 (
  TerminalSlopeTape.row (r := 3) (y := 69) 3290 (by decide) terminalGate_3_69 (
  TerminalSlopeTape.row (r := 3) (y := 70) 3238 (by decide) terminalGate_3_70 (
  TerminalSlopeTape.row (r := 3) (y := 71) 3184 (by decide) terminalGate_3_71 (
  TerminalSlopeTape.row (r := 3) (y := 72) 3127 (by decide) terminalGate_3_72 (
  TerminalSlopeTape.row (r := 3) (y := 73) 3067 (by decide) terminalGate_3_73 (
  TerminalSlopeTape.row (r := 3) (y := 74) 3004 (by decide) terminalGate_3_74 (
  TerminalSlopeTape.row (r := 3) (y := 75) 2939 (by decide) terminalGate_3_75 (
  TerminalSlopeTape.row (r := 3) (y := 76) 2871 (by decide) terminalGate_3_76 (
  TerminalSlopeTape.row (r := 3) (y := 77) 2800 (by decide) terminalGate_3_77 (
  TerminalSlopeTape.row (r := 3) (y := 78) 2726 (by decide) terminalGate_3_78 (
  TerminalSlopeTape.row (r := 3) (y := 79) 2650 (by decide) terminalGate_3_79 (
  TerminalSlopeTape.row (r := 3) (y := 80) 2571 (by decide) terminalGate_3_80 (
  TerminalSlopeTape.row (r := 3) (y := 81) 2489 (by decide) terminalGate_3_81 (
  TerminalSlopeTape.row (r := 3) (y := 82) 2404 (by decide) terminalGate_3_82 (
  TerminalSlopeTape.row (r := 3) (y := 83) 2316 (by decide) terminalGate_3_83 (
  TerminalSlopeTape.row (r := 3) (y := 84) 2226 (by decide) terminalGate_3_84 (
  TerminalSlopeTape.row (r := 3) (y := 85) 2133 (by decide) terminalGate_3_85 (
  TerminalSlopeTape.row (r := 3) (y := 86) 2037 (by decide) terminalGate_3_86 (
  TerminalSlopeTape.row (r := 3) (y := 87) 1938 (by decide) terminalGate_3_87 (
  TerminalSlopeTape.row (r := 3) (y := 88) 1837 (by decide) terminalGate_3_88 (
  TerminalSlopeTape.row (r := 3) (y := 89) 1733 (by decide) terminalGate_3_89 (
  TerminalSlopeTape.row (r := 3) (y := 90) 1626 (by decide) terminalGate_3_90 (
  TerminalSlopeTape.row (r := 3) (y := 91) 1516 (by decide) terminalGate_3_91 (
  TerminalSlopeTape.row (r := 3) (y := 92) 1403 (by decide) terminalGate_3_92 (
  TerminalSlopeTape.row (r := 3) (y := 93) 1288 (by decide) terminalGate_3_93 (
  TerminalSlopeTape.row (r := 3) (y := 94) 1170 (by decide) terminalGate_3_94 (
  TerminalSlopeTape.row (r := 3) (y := 95) 1049 (by decide) terminalGate_3_95 (
  TerminalSlopeTape.row (r := 3) (y := 96) 925 (by decide) terminalGate_3_96 (
  TerminalSlopeTape.row (r := 3) (y := 97) 799 (by decide) terminalGate_3_97 (
  TerminalSlopeTape.row (r := 3) (y := 98) 669 (by decide) terminalGate_3_98 (
  TerminalSlopeTape.row (r := 3) (y := 99) 537 (by decide) terminalGate_3_99 (
  TerminalSlopeTape.row (r := 3) (y := 100) 403 (by decide) terminalGate_3_100 (
  TerminalSlopeTape.row (r := 3) (y := 101) 265 (by decide) terminalGate_3_101 (
  TerminalSlopeTape.row (r := 3) (y := 102) 125 (by decide) terminalGate_3_102 (
  TerminalSlopeTape.stop (r := 3) (y := 103) terminalGate_3_stop))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem terminalGate_4_stop :
    bandCovers secondAdaptiveFlag ⟨4, 102, 102⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 102, 102⟩ secondAdaptiveGap
    [⟨656, true, true⟩, ⟨812, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_4 :
    bandCovers secondAdaptiveFlag ⟨4, 4, 4864⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 4, 4864⟩ secondAdaptiveGap
    [⟨739, true, true⟩, ⟨753, false, true⟩, ⟨756, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_5 :
    bandCovers secondAdaptiveFlag ⟨4, 5, 4847⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 5, 4847⟩ secondAdaptiveGap
    [⟨742, true, true⟩, ⟨755, false, true⟩, ⟨758, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_6 :
    bandCovers secondAdaptiveFlag ⟨4, 6, 4830⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 6, 4830⟩ secondAdaptiveGap
    [⟨745, true, true⟩, ⟨758, false, true⟩, ⟨761, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_7 :
    bandCovers secondAdaptiveFlag ⟨4, 7, 4813⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 7, 4813⟩ secondAdaptiveGap
    [⟨748, true, true⟩, ⟨761, false, true⟩, ⟨764, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_8 :
    bandCovers secondAdaptiveFlag ⟨4, 8, 4796⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 8, 4796⟩ secondAdaptiveGap
    [⟨751, true, true⟩, ⟨763, false, true⟩, ⟨767, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_9 :
    bandCovers secondAdaptiveFlag ⟨4, 9, 4779⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 9, 4779⟩ secondAdaptiveGap
    [⟨753, true, true⟩, ⟨766, false, true⟩, ⟨769, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_10 :
    bandCovers secondAdaptiveFlag ⟨4, 10, 4761⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 10, 4761⟩ secondAdaptiveGap
    [⟨756, true, true⟩, ⟨769, false, true⟩, ⟨772, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_11 :
    bandCovers secondAdaptiveFlag ⟨4, 11, 4744⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 11, 4744⟩ secondAdaptiveGap
    [⟨759, true, true⟩, ⟨772, false, true⟩, ⟨775, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_12 :
    bandCovers secondAdaptiveFlag ⟨4, 12, 4726⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 12, 4726⟩ secondAdaptiveGap
    [⟨762, true, true⟩, ⟨775, false, true⟩, ⟨778, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_13 :
    bandCovers secondAdaptiveFlag ⟨4, 13, 4709⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 13, 4709⟩ secondAdaptiveGap
    [⟨765, true, true⟩, ⟨777, false, true⟩, ⟨781, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_14 :
    bandCovers secondAdaptiveFlag ⟨4, 14, 4691⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 14, 4691⟩ secondAdaptiveGap
    [⟨768, true, true⟩, ⟨780, false, true⟩, ⟨784, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_15 :
    bandCovers secondAdaptiveFlag ⟨4, 15, 4672⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 15, 4672⟩ secondAdaptiveGap
    [⟨772, true, true⟩, ⟨784, false, true⟩, ⟨787, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_16 :
    bandCovers secondAdaptiveFlag ⟨4, 16, 4654⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 16, 4654⟩ secondAdaptiveGap
    [⟨775, true, true⟩, ⟨787, false, true⟩, ⟨790, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_17 :
    bandCovers secondAdaptiveFlag ⟨4, 17, 4636⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 17, 4636⟩ secondAdaptiveGap
    [⟨778, true, true⟩, ⟨790, false, true⟩, ⟨793, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_18 :
    bandCovers secondAdaptiveFlag ⟨4, 18, 4617⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 18, 4617⟩ secondAdaptiveGap
    [⟨781, true, true⟩, ⟨793, false, true⟩, ⟨796, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_19 :
    bandCovers secondAdaptiveFlag ⟨4, 19, 4599⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 19, 4599⟩ secondAdaptiveGap
    [⟨785, true, true⟩, ⟨796, false, true⟩, ⟨799, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_20 :
    bandCovers secondAdaptiveFlag ⟨4, 20, 4580⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 20, 4580⟩ secondAdaptiveGap
    [⟨788, true, true⟩, ⟨799, false, true⟩, ⟨803, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_21 :
    bandCovers secondAdaptiveFlag ⟨4, 21, 4561⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 21, 4561⟩ secondAdaptiveGap
    [⟨792, true, true⟩, ⟨803, false, true⟩, ⟨806, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_22 :
    bandCovers secondAdaptiveFlag ⟨4, 22, 4541⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 22, 4541⟩ secondAdaptiveGap
    [⟨795, true, true⟩, ⟨806, false, true⟩, ⟨810, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_23 :
    bandCovers secondAdaptiveFlag ⟨4, 23, 4522⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 23, 4522⟩ secondAdaptiveGap
    [⟨799, true, true⟩, ⟨810, false, true⟩, ⟨813, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_24 :
    bandCovers secondAdaptiveFlag ⟨4, 24, 4502⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 24, 4502⟩ secondAdaptiveGap
    [⟨803, true, true⟩, ⟨813, false, true⟩, ⟨817, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_25 :
    bandCovers secondAdaptiveFlag ⟨4, 25, 4483⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 25, 4483⟩ secondAdaptiveGap
    [⟨806, true, true⟩, ⟨817, false, true⟩, ⟨820, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_26 :
    bandCovers secondAdaptiveFlag ⟨4, 26, 4463⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 26, 4463⟩ secondAdaptiveGap
    [⟨810, true, true⟩, ⟨820, false, true⟩, ⟨824, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_27 :
    bandCovers secondAdaptiveFlag ⟨4, 27, 4442⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 27, 4442⟩ secondAdaptiveGap
    [⟨814, true, true⟩, ⟨824, false, true⟩, ⟨828, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_28 :
    bandCovers secondAdaptiveFlag ⟨4, 28, 4422⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 28, 4422⟩ secondAdaptiveGap
    [⟨818, true, true⟩, ⟨828, false, true⟩, ⟨831, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_29 :
    bandCovers secondAdaptiveFlag ⟨4, 29, 4401⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 29, 4401⟩ secondAdaptiveGap
    [⟨822, true, true⟩, ⟨832, false, true⟩, ⟨835, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_30 :
    bandCovers secondAdaptiveFlag ⟨4, 30, 4380⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 30, 4380⟩ secondAdaptiveGap
    [⟨826, true, true⟩, ⟨836, false, true⟩, ⟨839, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_31 :
    bandCovers secondAdaptiveFlag ⟨4, 31, 4359⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 31, 4359⟩ secondAdaptiveGap
    [⟨830, true, true⟩, ⟨840, false, true⟩, ⟨843, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_32 :
    bandCovers secondAdaptiveFlag ⟨4, 32, 4338⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 32, 4338⟩ secondAdaptiveGap
    [⟨835, true, true⟩, ⟨844, false, true⟩, ⟨848, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_33 :
    bandCovers secondAdaptiveFlag ⟨4, 33, 4316⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 33, 4316⟩ secondAdaptiveGap
    [⟨839, true, true⟩, ⟨848, false, true⟩, ⟨852, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_34 :
    bandCovers secondAdaptiveFlag ⟨4, 34, 4295⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 34, 4295⟩ secondAdaptiveGap
    [⟨843, true, true⟩, ⟨853, false, true⟩, ⟨856, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_35 :
    bandCovers secondAdaptiveFlag ⟨4, 35, 4273⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 35, 4273⟩ secondAdaptiveGap
    [⟨848, true, true⟩, ⟨857, false, true⟩, ⟨860, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_36 :
    bandCovers secondAdaptiveFlag ⟨4, 36, 4250⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 36, 4250⟩ secondAdaptiveGap
    [⟨853, true, true⟩, ⟨862, false, true⟩, ⟨865, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_37 :
    bandCovers secondAdaptiveFlag ⟨4, 37, 4228⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 37, 4228⟩ secondAdaptiveGap
    [⟨858, true, true⟩, ⟨866, false, true⟩, ⟨870, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_38 :
    bandCovers secondAdaptiveFlag ⟨4, 38, 4205⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 38, 4205⟩ secondAdaptiveGap
    [⟨862, true, true⟩, ⟨871, false, true⟩, ⟨874, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_39 :
    bandCovers secondAdaptiveFlag ⟨4, 39, 4181⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 39, 4181⟩ secondAdaptiveGap
    [⟨868, true, true⟩, ⟨876, false, true⟩, ⟨879, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_40 :
    bandCovers secondAdaptiveFlag ⟨4, 40, 4158⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 40, 4158⟩ secondAdaptiveGap
    [⟨873, true, true⟩, ⟨881, false, true⟩, ⟨884, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_41 :
    bandCovers secondAdaptiveFlag ⟨4, 41, 4134⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 41, 4134⟩ secondAdaptiveGap
    [⟨878, true, true⟩, ⟨886, false, true⟩, ⟨889, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_42 :
    bandCovers secondAdaptiveFlag ⟨4, 42, 4110⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 42, 4110⟩ secondAdaptiveGap
    [⟨883, true, true⟩, ⟨891, false, true⟩, ⟨895, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_43 :
    bandCovers secondAdaptiveFlag ⟨4, 43, 4085⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 43, 4085⟩ secondAdaptiveGap
    [⟨889, true, true⟩, ⟨896, false, true⟩, ⟨900, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_44 :
    bandCovers secondAdaptiveFlag ⟨4, 44, 4060⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 44, 4060⟩ secondAdaptiveGap
    [⟨895, true, true⟩, ⟨902, false, true⟩, ⟨906, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_45 :
    bandCovers secondAdaptiveFlag ⟨4, 45, 4034⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 45, 4034⟩ secondAdaptiveGap
    [⟨901, true, true⟩, ⟨908, false, true⟩, ⟨911, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_46 :
    bandCovers secondAdaptiveFlag ⟨4, 46, 4009⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 46, 4009⟩ secondAdaptiveGap
    [⟨907, true, true⟩, ⟨913, false, true⟩, ⟨917, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_47 :
    bandCovers secondAdaptiveFlag ⟨4, 47, 3982⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 47, 3982⟩ secondAdaptiveGap
    [⟨913, true, true⟩, ⟨920, false, true⟩, ⟨923, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_48 :
    bandCovers secondAdaptiveFlag ⟨4, 48, 3956⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 48, 3956⟩ secondAdaptiveGap
    [⟨920, true, true⟩, ⟨926, false, true⟩, ⟨929, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_49 :
    bandCovers secondAdaptiveFlag ⟨4, 49, 3928⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 49, 3928⟩ secondAdaptiveGap
    [⟨927, true, true⟩, ⟨932, false, true⟩, ⟨936, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_50 :
    bandCovers secondAdaptiveFlag ⟨4, 50, 3901⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 50, 3901⟩ secondAdaptiveGap
    [⟨933, true, true⟩, ⟨939, false, true⟩, ⟨943, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_51 :
    bandCovers secondAdaptiveFlag ⟨4, 51, 3873⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 51, 3873⟩ secondAdaptiveGap
    [⟨940, true, true⟩, ⟨946, false, true⟩, ⟨949, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_52 :
    bandCovers secondAdaptiveFlag ⟨4, 52, 3844⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 52, 3844⟩ secondAdaptiveGap
    [⟨948, true, true⟩, ⟨953, false, true⟩, ⟨957, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_53 :
    bandCovers secondAdaptiveFlag ⟨4, 53, 3814⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 53, 3814⟩ secondAdaptiveGap
    [⟨956, true, true⟩, ⟨960, false, true⟩, ⟨964, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_54 :
    bandCovers secondAdaptiveFlag ⟨4, 54, 3784⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 54, 3784⟩ secondAdaptiveGap
    [⟨964, true, true⟩, ⟨968, false, true⟩, ⟨972, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_55 :
    bandCovers secondAdaptiveFlag ⟨4, 55, 3753⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 55, 3753⟩ secondAdaptiveGap
    [⟨972, true, true⟩, ⟨976, false, true⟩, ⟨980, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_56 :
    bandCovers secondAdaptiveFlag ⟨4, 56, 3722⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 56, 3722⟩ secondAdaptiveGap
    [⟨980, true, true⟩, ⟨984, false, true⟩, ⟨988, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_57 :
    bandCovers secondAdaptiveFlag ⟨4, 57, 3690⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 57, 3690⟩ secondAdaptiveGap
    [⟨989, true, true⟩, ⟨993, false, true⟩, ⟨996, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_58 :
    bandCovers secondAdaptiveFlag ⟨4, 58, 3656⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 58, 3656⟩ secondAdaptiveGap
    [⟨999, true, true⟩, ⟨1002, false, true⟩, ⟨1006, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_59 :
    bandCovers secondAdaptiveFlag ⟨4, 59, 3622⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 59, 3622⟩ secondAdaptiveGap
    [⟨1009, true, true⟩, ⟨1011, false, true⟩, ⟨1015, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_60 :
    bandCovers secondAdaptiveFlag ⟨4, 60, 3587⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 60, 3587⟩ secondAdaptiveGap
    [⟨1019, true, true⟩, ⟨1021, false, true⟩, ⟨1025, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_61 :
    bandCovers secondAdaptiveFlag ⟨4, 61, 3551⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 61, 3551⟩ secondAdaptiveGap
    [⟨1030, true, true⟩, ⟨1031, false, true⟩, ⟨1035, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_62 :
    bandCovers secondAdaptiveFlag ⟨4, 62, 3514⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 62, 3514⟩ secondAdaptiveGap
    [⟨1041, true, true⟩, ⟨1042, false, true⟩, ⟨1046, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_63 :
    bandCovers secondAdaptiveFlag ⟨4, 63, 3475⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 63, 3475⟩ secondAdaptiveGap
    [⟨1053, true, true⟩, ⟨1054, false, true⟩, ⟨1058, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_64 :
    bandCovers secondAdaptiveFlag ⟨4, 64, 3435⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 64, 3435⟩ secondAdaptiveGap
    [⟨1066, true, true⟩, ⟨1070, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_65 :
    bandCovers secondAdaptiveFlag ⟨4, 65, 3393⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 65, 3393⟩ secondAdaptiveGap
    [⟨1055, true, true⟩, ⟨1080, true, false⟩, ⟨1084, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_66 :
    bandCovers secondAdaptiveFlag ⟨4, 66, 3349⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 66, 3349⟩ secondAdaptiveGap
    [⟨1038, true, true⟩, ⟨1095, true, false⟩, ⟨1098, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_67 :
    bandCovers secondAdaptiveFlag ⟨4, 67, 3303⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 67, 3303⟩ secondAdaptiveGap
    [⟨1021, true, true⟩, ⟨1111, true, false⟩, ⟨1113, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_68 :
    bandCovers secondAdaptiveFlag ⟨4, 68, 3255⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 68, 3255⟩ secondAdaptiveGap
    [⟨1005, true, true⟩, ⟨1128, true, false⟩, ⟨1130, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_69 :
    bandCovers secondAdaptiveFlag ⟨4, 69, 3204⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 69, 3204⟩ secondAdaptiveGap
    [⟨990, true, true⟩, ⟨1147, true, false⟩, ⟨1148, false, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_70 :
    bandCovers secondAdaptiveFlag ⟨4, 70, 3151⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 70, 3151⟩ secondAdaptiveGap
    [⟨975, true, true⟩, ⟨1167, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_71 :
    bandCovers secondAdaptiveFlag ⟨4, 71, 3094⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 71, 3094⟩ secondAdaptiveGap
    [⟨960, true, true⟩, ⟨1166, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_72 :
    bandCovers secondAdaptiveFlag ⟨4, 72, 3036⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 72, 3036⟩ secondAdaptiveGap
    [⟨946, true, true⟩, ⟨1150, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_73 :
    bandCovers secondAdaptiveFlag ⟨4, 73, 2974⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 73, 2974⟩ secondAdaptiveGap
    [⟨932, true, true⟩, ⟨1134, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_74 :
    bandCovers secondAdaptiveFlag ⟨4, 74, 2910⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 74, 2910⟩ secondAdaptiveGap
    [⟨919, true, true⟩, ⟨1119, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_75 :
    bandCovers secondAdaptiveFlag ⟨4, 75, 2842⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 75, 2842⟩ secondAdaptiveGap
    [⟨906, true, true⟩, ⟨1104, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_76 :
    bandCovers secondAdaptiveFlag ⟨4, 76, 2773⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 76, 2773⟩ secondAdaptiveGap
    [⟨893, true, true⟩, ⟨1089, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_77 :
    bandCovers secondAdaptiveFlag ⟨4, 77, 2700⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 77, 2700⟩ secondAdaptiveGap
    [⟨881, true, true⟩, ⟨1075, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_78 :
    bandCovers secondAdaptiveFlag ⟨4, 78, 2624⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 78, 2624⟩ secondAdaptiveGap
    [⟨869, true, true⟩, ⟨1062, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_79 :
    bandCovers secondAdaptiveFlag ⟨4, 79, 2546⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 79, 2546⟩ secondAdaptiveGap
    [⟨858, true, true⟩, ⟨1048, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_80 :
    bandCovers secondAdaptiveFlag ⟨4, 80, 2465⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 80, 2465⟩ secondAdaptiveGap
    [⟨846, true, true⟩, ⟨1035, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_81 :
    bandCovers secondAdaptiveFlag ⟨4, 81, 2381⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 81, 2381⟩ secondAdaptiveGap
    [⟨835, true, true⟩, ⟨1022, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_82 :
    bandCovers secondAdaptiveFlag ⟨4, 82, 2295⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 82, 2295⟩ secondAdaptiveGap
    [⟨825, true, true⟩, ⟨1010, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_83 :
    bandCovers secondAdaptiveFlag ⟨4, 83, 2205⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 83, 2205⟩ secondAdaptiveGap
    [⟨814, true, true⟩, ⟨998, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_84 :
    bandCovers secondAdaptiveFlag ⟨4, 84, 2113⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 84, 2113⟩ secondAdaptiveGap
    [⟨804, true, true⟩, ⟨986, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_85 :
    bandCovers secondAdaptiveFlag ⟨4, 85, 2018⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 85, 2018⟩ secondAdaptiveGap
    [⟨794, true, true⟩, ⟨974, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_86 :
    bandCovers secondAdaptiveFlag ⟨4, 86, 1921⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 86, 1921⟩ secondAdaptiveGap
    [⟨784, true, true⟩, ⟨963, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_87 :
    bandCovers secondAdaptiveFlag ⟨4, 87, 1820⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 87, 1820⟩ secondAdaptiveGap
    [⟨775, true, true⟩, ⟨952, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_88 :
    bandCovers secondAdaptiveFlag ⟨4, 88, 1717⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 88, 1717⟩ secondAdaptiveGap
    [⟨766, true, true⟩, ⟨941, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_89 :
    bandCovers secondAdaptiveFlag ⟨4, 89, 1611⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 89, 1611⟩ secondAdaptiveGap
    [⟨757, true, true⟩, ⟨930, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_90 :
    bandCovers secondAdaptiveFlag ⟨4, 90, 1503⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 90, 1503⟩ secondAdaptiveGap
    [⟨748, true, true⟩, ⟨920, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_91 :
    bandCovers secondAdaptiveFlag ⟨4, 91, 1391⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 91, 1391⟩ secondAdaptiveGap
    [⟨739, true, true⟩, ⟨910, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_92 :
    bandCovers secondAdaptiveFlag ⟨4, 92, 1277⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 92, 1277⟩ secondAdaptiveGap
    [⟨731, true, true⟩, ⟨900, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_93 :
    bandCovers secondAdaptiveFlag ⟨4, 93, 1160⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 93, 1160⟩ secondAdaptiveGap
    [⟨723, true, true⟩, ⟨890, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_94 :
    bandCovers secondAdaptiveFlag ⟨4, 94, 1040⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 94, 1040⟩ secondAdaptiveGap
    [⟨715, true, true⟩, ⟨881, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_95 :
    bandCovers secondAdaptiveFlag ⟨4, 95, 917⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 95, 917⟩ secondAdaptiveGap
    [⟨707, true, true⟩, ⟨871, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_96 :
    bandCovers secondAdaptiveFlag ⟨4, 96, 792⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 96, 792⟩ secondAdaptiveGap
    [⟨699, true, true⟩, ⟨862, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_97 :
    bandCovers secondAdaptiveFlag ⟨4, 97, 664⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 97, 664⟩ secondAdaptiveGap
    [⟨692, true, true⟩, ⟨854, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_98 :
    bandCovers secondAdaptiveFlag ⟨4, 98, 533⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 98, 533⟩ secondAdaptiveGap
    [⟨684, true, true⟩, ⟨845, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_99 :
    bandCovers secondAdaptiveFlag ⟨4, 99, 399⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 99, 399⟩ secondAdaptiveGap
    [⟨677, true, true⟩, ⟨836, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_100 :
    bandCovers secondAdaptiveFlag ⟨4, 100, 262⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 100, 262⟩ secondAdaptiveGap
    [⟨670, true, true⟩, ⟨828, true, false⟩] (by decide +kernel) (by decide +kernel)

private theorem terminalGate_4_101 :
    bandCovers secondAdaptiveFlag ⟨4, 101, 123⟩ secondAdaptiveGap = true :=
  bandCovers_of_pieces secondAdaptiveFlag ⟨4, 101, 123⟩ secondAdaptiveGap
    [⟨663, true, true⟩, ⟨820, true, false⟩] (by decide +kernel) (by decide +kernel)

private def terminalSlopeTape04 : TerminalSlopeTape 4 4 :=  TerminalSlopeTape.row (r := 4) (y := 4) 4863 (by decide) terminalGate_4_4 (
  TerminalSlopeTape.row (r := 4) (y := 5) 4846 (by decide) terminalGate_4_5 (
  TerminalSlopeTape.row (r := 4) (y := 6) 4829 (by decide) terminalGate_4_6 (
  TerminalSlopeTape.row (r := 4) (y := 7) 4812 (by decide) terminalGate_4_7 (
  TerminalSlopeTape.row (r := 4) (y := 8) 4795 (by decide) terminalGate_4_8 (
  TerminalSlopeTape.row (r := 4) (y := 9) 4778 (by decide) terminalGate_4_9 (
  TerminalSlopeTape.row (r := 4) (y := 10) 4760 (by decide) terminalGate_4_10 (
  TerminalSlopeTape.row (r := 4) (y := 11) 4743 (by decide) terminalGate_4_11 (
  TerminalSlopeTape.row (r := 4) (y := 12) 4725 (by decide) terminalGate_4_12 (
  TerminalSlopeTape.row (r := 4) (y := 13) 4708 (by decide) terminalGate_4_13 (
  TerminalSlopeTape.row (r := 4) (y := 14) 4690 (by decide) terminalGate_4_14 (
  TerminalSlopeTape.row (r := 4) (y := 15) 4671 (by decide) terminalGate_4_15 (
  TerminalSlopeTape.row (r := 4) (y := 16) 4653 (by decide) terminalGate_4_16 (
  TerminalSlopeTape.row (r := 4) (y := 17) 4635 (by decide) terminalGate_4_17 (
  TerminalSlopeTape.row (r := 4) (y := 18) 4616 (by decide) terminalGate_4_18 (
  TerminalSlopeTape.row (r := 4) (y := 19) 4598 (by decide) terminalGate_4_19 (
  TerminalSlopeTape.row (r := 4) (y := 20) 4579 (by decide) terminalGate_4_20 (
  TerminalSlopeTape.row (r := 4) (y := 21) 4560 (by decide) terminalGate_4_21 (
  TerminalSlopeTape.row (r := 4) (y := 22) 4540 (by decide) terminalGate_4_22 (
  TerminalSlopeTape.row (r := 4) (y := 23) 4521 (by decide) terminalGate_4_23 (
  TerminalSlopeTape.row (r := 4) (y := 24) 4501 (by decide) terminalGate_4_24 (
  TerminalSlopeTape.row (r := 4) (y := 25) 4482 (by decide) terminalGate_4_25 (
  TerminalSlopeTape.row (r := 4) (y := 26) 4462 (by decide) terminalGate_4_26 (
  TerminalSlopeTape.row (r := 4) (y := 27) 4441 (by decide) terminalGate_4_27 (
  TerminalSlopeTape.row (r := 4) (y := 28) 4421 (by decide) terminalGate_4_28 (
  TerminalSlopeTape.row (r := 4) (y := 29) 4400 (by decide) terminalGate_4_29 (
  TerminalSlopeTape.row (r := 4) (y := 30) 4379 (by decide) terminalGate_4_30 (
  TerminalSlopeTape.row (r := 4) (y := 31) 4358 (by decide) terminalGate_4_31 (
  TerminalSlopeTape.row (r := 4) (y := 32) 4337 (by decide) terminalGate_4_32 (
  TerminalSlopeTape.row (r := 4) (y := 33) 4315 (by decide) terminalGate_4_33 (
  TerminalSlopeTape.row (r := 4) (y := 34) 4294 (by decide) terminalGate_4_34 (
  TerminalSlopeTape.row (r := 4) (y := 35) 4272 (by decide) terminalGate_4_35 (
  TerminalSlopeTape.row (r := 4) (y := 36) 4249 (by decide) terminalGate_4_36 (
  TerminalSlopeTape.row (r := 4) (y := 37) 4227 (by decide) terminalGate_4_37 (
  TerminalSlopeTape.row (r := 4) (y := 38) 4204 (by decide) terminalGate_4_38 (
  TerminalSlopeTape.row (r := 4) (y := 39) 4180 (by decide) terminalGate_4_39 (
  TerminalSlopeTape.row (r := 4) (y := 40) 4157 (by decide) terminalGate_4_40 (
  TerminalSlopeTape.row (r := 4) (y := 41) 4133 (by decide) terminalGate_4_41 (
  TerminalSlopeTape.row (r := 4) (y := 42) 4109 (by decide) terminalGate_4_42 (
  TerminalSlopeTape.row (r := 4) (y := 43) 4084 (by decide) terminalGate_4_43 (
  TerminalSlopeTape.row (r := 4) (y := 44) 4059 (by decide) terminalGate_4_44 (
  TerminalSlopeTape.row (r := 4) (y := 45) 4033 (by decide) terminalGate_4_45 (
  TerminalSlopeTape.row (r := 4) (y := 46) 4008 (by decide) terminalGate_4_46 (
  TerminalSlopeTape.row (r := 4) (y := 47) 3981 (by decide) terminalGate_4_47 (
  TerminalSlopeTape.row (r := 4) (y := 48) 3955 (by decide) terminalGate_4_48 (
  TerminalSlopeTape.row (r := 4) (y := 49) 3927 (by decide) terminalGate_4_49 (
  TerminalSlopeTape.row (r := 4) (y := 50) 3900 (by decide) terminalGate_4_50 (
  TerminalSlopeTape.row (r := 4) (y := 51) 3872 (by decide) terminalGate_4_51 (
  TerminalSlopeTape.row (r := 4) (y := 52) 3843 (by decide) terminalGate_4_52 (
  TerminalSlopeTape.row (r := 4) (y := 53) 3813 (by decide) terminalGate_4_53 (
  TerminalSlopeTape.row (r := 4) (y := 54) 3783 (by decide) terminalGate_4_54 (
  TerminalSlopeTape.row (r := 4) (y := 55) 3752 (by decide) terminalGate_4_55 (
  TerminalSlopeTape.row (r := 4) (y := 56) 3721 (by decide) terminalGate_4_56 (
  TerminalSlopeTape.row (r := 4) (y := 57) 3689 (by decide) terminalGate_4_57 (
  TerminalSlopeTape.row (r := 4) (y := 58) 3655 (by decide) terminalGate_4_58 (
  TerminalSlopeTape.row (r := 4) (y := 59) 3621 (by decide) terminalGate_4_59 (
  TerminalSlopeTape.row (r := 4) (y := 60) 3586 (by decide) terminalGate_4_60 (
  TerminalSlopeTape.row (r := 4) (y := 61) 3550 (by decide) terminalGate_4_61 (
  TerminalSlopeTape.row (r := 4) (y := 62) 3513 (by decide) terminalGate_4_62 (
  TerminalSlopeTape.row (r := 4) (y := 63) 3474 (by decide) terminalGate_4_63 (
  TerminalSlopeTape.row (r := 4) (y := 64) 3434 (by decide) terminalGate_4_64 (
  TerminalSlopeTape.row (r := 4) (y := 65) 3392 (by decide) terminalGate_4_65 (
  TerminalSlopeTape.row (r := 4) (y := 66) 3348 (by decide) terminalGate_4_66 (
  TerminalSlopeTape.row (r := 4) (y := 67) 3302 (by decide) terminalGate_4_67 (
  TerminalSlopeTape.row (r := 4) (y := 68) 3254 (by decide) terminalGate_4_68 (
  TerminalSlopeTape.row (r := 4) (y := 69) 3203 (by decide) terminalGate_4_69 (
  TerminalSlopeTape.row (r := 4) (y := 70) 3150 (by decide) terminalGate_4_70 (
  TerminalSlopeTape.row (r := 4) (y := 71) 3093 (by decide) terminalGate_4_71 (
  TerminalSlopeTape.row (r := 4) (y := 72) 3035 (by decide) terminalGate_4_72 (
  TerminalSlopeTape.row (r := 4) (y := 73) 2973 (by decide) terminalGate_4_73 (
  TerminalSlopeTape.row (r := 4) (y := 74) 2909 (by decide) terminalGate_4_74 (
  TerminalSlopeTape.row (r := 4) (y := 75) 2841 (by decide) terminalGate_4_75 (
  TerminalSlopeTape.row (r := 4) (y := 76) 2772 (by decide) terminalGate_4_76 (
  TerminalSlopeTape.row (r := 4) (y := 77) 2699 (by decide) terminalGate_4_77 (
  TerminalSlopeTape.row (r := 4) (y := 78) 2623 (by decide) terminalGate_4_78 (
  TerminalSlopeTape.row (r := 4) (y := 79) 2545 (by decide) terminalGate_4_79 (
  TerminalSlopeTape.row (r := 4) (y := 80) 2464 (by decide) terminalGate_4_80 (
  TerminalSlopeTape.row (r := 4) (y := 81) 2380 (by decide) terminalGate_4_81 (
  TerminalSlopeTape.row (r := 4) (y := 82) 2294 (by decide) terminalGate_4_82 (
  TerminalSlopeTape.row (r := 4) (y := 83) 2204 (by decide) terminalGate_4_83 (
  TerminalSlopeTape.row (r := 4) (y := 84) 2112 (by decide) terminalGate_4_84 (
  TerminalSlopeTape.row (r := 4) (y := 85) 2017 (by decide) terminalGate_4_85 (
  TerminalSlopeTape.row (r := 4) (y := 86) 1920 (by decide) terminalGate_4_86 (
  TerminalSlopeTape.row (r := 4) (y := 87) 1819 (by decide) terminalGate_4_87 (
  TerminalSlopeTape.row (r := 4) (y := 88) 1716 (by decide) terminalGate_4_88 (
  TerminalSlopeTape.row (r := 4) (y := 89) 1610 (by decide) terminalGate_4_89 (
  TerminalSlopeTape.row (r := 4) (y := 90) 1502 (by decide) terminalGate_4_90 (
  TerminalSlopeTape.row (r := 4) (y := 91) 1390 (by decide) terminalGate_4_91 (
  TerminalSlopeTape.row (r := 4) (y := 92) 1276 (by decide) terminalGate_4_92 (
  TerminalSlopeTape.row (r := 4) (y := 93) 1159 (by decide) terminalGate_4_93 (
  TerminalSlopeTape.row (r := 4) (y := 94) 1039 (by decide) terminalGate_4_94 (
  TerminalSlopeTape.row (r := 4) (y := 95) 916 (by decide) terminalGate_4_95 (
  TerminalSlopeTape.row (r := 4) (y := 96) 791 (by decide) terminalGate_4_96 (
  TerminalSlopeTape.row (r := 4) (y := 97) 663 (by decide) terminalGate_4_97 (
  TerminalSlopeTape.row (r := 4) (y := 98) 532 (by decide) terminalGate_4_98 (
  TerminalSlopeTape.row (r := 4) (y := 99) 398 (by decide) terminalGate_4_99 (
  TerminalSlopeTape.row (r := 4) (y := 100) 261 (by decide) terminalGate_4_100 (
  TerminalSlopeTape.row (r := 4) (y := 101) 122 (by decide) terminalGate_4_101 (
  TerminalSlopeTape.stop (r := 4) (y := 102) terminalGate_4_stop))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def terminalTapeGroup01 : List TerminalCoveredSlope := [
  ⟨3, terminalSlopeTape03⟩,
  ⟨4, terminalSlopeTape04⟩
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
