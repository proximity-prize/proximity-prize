import ProximityPrize.SubmissionLower.R6962B1RescueSchedule

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Lower6962.B1.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase phaseBlock phaseBlock_append phase_of_block)

private theorem mom_810_174_part0 :
    blockEstimate 810 174 174 128 = 255708960 := by decide +kernel
private theorem mom_810_174_part1 :
    blockEstimate 810 174 302 128 = 1441937865 := by decide +kernel
private theorem mom_810_174_part2 :
    blockEstimate 810 174 430 128 = 2534929600 := by decide +kernel
private theorem mom_810_174_part3 :
    blockEstimate 810 174 558 128 = 2904798400 := by decide +kernel
private theorem mom_810_174_part4 :
    blockEstimate 810 174 686 128 = 2540667263 := by decide +kernel
private theorem mom_810_174_part5 :
    blockEstimate 810 174 814 128 = 1559409298 := by decide +kernel
private theorem mom_810_174_part6 :
    blockEstimate 810 174 942 128 = 560980122 := by decide +kernel
private theorem mom_810_174_part7 :
    blockEstimate 810 174 1070 88 = 45957120 := by decide +kernel
private theorem mom_810_174_join0 :
    blockEstimate 810 174 174 256 = 1697646825 :=
  block_append mom_810_174_part0 mom_810_174_part1 rfl rfl rfl
private theorem mom_810_174_join1 :
    blockEstimate 810 174 430 256 = 5439728000 :=
  block_append mom_810_174_part2 mom_810_174_part3 rfl rfl rfl
private theorem mom_810_174_join2 :
    blockEstimate 810 174 174 512 = 7137374825 :=
  block_append mom_810_174_join0 mom_810_174_join1 rfl rfl rfl
private theorem mom_810_174_join3 :
    blockEstimate 810 174 686 256 = 4100076561 :=
  block_append mom_810_174_part4 mom_810_174_part5 rfl rfl rfl
private theorem mom_810_174_join4 :
    blockEstimate 810 174 942 216 = 606937242 :=
  block_append mom_810_174_part6 mom_810_174_part7 rfl rfl rfl
private theorem mom_810_174_join5 :
    blockEstimate 810 174 686 472 = 4707013803 :=
  block_append mom_810_174_join3 mom_810_174_join4 rfl rfl rfl
private theorem mom_810_174_join6 :
    blockEstimate 810 174 174 984 = 11844388628 :=
  block_append mom_810_174_join2 mom_810_174_join5 rfl rfl rfl
private theorem mom_810_174 : momentEstimate 810 174 = 11844388628 := mom_810_174_join6
private theorem rc_3_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2360 0 1 1 1 0) 0 128 = 187352572763816831738400 := by decide +kernel
private theorem rc_3_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2360 0 1 1 1 0) 128 47 = 12160093117900446448620 := by decide +kernel
private theorem rc_3_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2360 0 1 1 1 0) 0 175 = 199512665881717278187020 :=
  phaseBlock_append rc_3_0_2360_0_part0 rc_3_0_2360_0_part1 rfl rfl rfl
private theorem rc_3_0_2360_0 : fastPhase (bank 3 0).shape 179808 2360 0 1 1 1 0 = 199512665881717278187020 :=
  phase_of_block (n := 175) (by decide +kernel) rc_3_0_2360_0_join0
private theorem rc_3_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2360 0 1 1 1 1) 0 128 = 185383448138439055470240 := by decide +kernel
private theorem rc_3_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2360 0 1 1 1 1) 128 47 = 11635210697308894612180 := by decide +kernel
private theorem rc_3_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2360 0 1 1 1 1) 0 175 = 197018658835747950082420 :=
  phaseBlock_append rc_3_0_2360_1_part0 rc_3_0_2360_1_part1 rfl rfl rfl
private theorem rc_3_0_2360_1 : fastPhase (bank 3 0).shape 179808 2360 0 1 1 1 1 = 197018658835747950082420 :=
  phase_of_block (n := 175) (by decide +kernel) rc_3_0_2360_1_join0
private theorem rc_3_0_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2361 0 1 1 1 0) 0 128 = 187353879089032153085600 := by decide +kernel
private theorem rc_3_0_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2361 0 1 1 1 0) 128 47 = 12160123318244719132380 := by decide +kernel
private theorem rc_3_0_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2361 0 1 1 1 0) 0 175 = 199514002407276872217980 :=
  phaseBlock_append rc_3_0_2361_0_part0 rc_3_0_2361_0_part1 rfl rfl rfl
private theorem rc_3_0_2361_0 : fastPhase (bank 3 0).shape 179808 2361 0 1 1 1 0 = 199514002407276872217980 :=
  phase_of_block (n := 175) (by decide +kernel) rc_3_0_2361_0_join0
private theorem rc_3_0_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2361 0 1 1 1 1) 0 128 = 185384740037380805315616 := by decide +kernel
private theorem rc_3_0_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2361 0 1 1 1 1) 128 47 = 11635239688135747106124 := by decide +kernel
private theorem rc_3_0_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179808 2361 0 1 1 1 1) 0 175 = 197019979725516552421740 :=
  phaseBlock_append rc_3_0_2361_1_part0 rc_3_0_2361_1_part1 rfl rfl rfl
private theorem rc_3_0_2361_1 : fastPhase (bank 3 0).shape 179808 2361 0 1 1 1 1 = 197019979725516552421740 :=
  phase_of_block (n := 175) (by decide +kernel) rc_3_0_2361_1_join0
private theorem receipt_3_0 : B1Checked (bank 3 0) 0 1 1 := by
  refine b1_checked_from_values (bank 3 0) 0 1 1
    (P3_7_1.checked (bank 3 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_810_174)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_0_2360_0 rc_3_0_2360_1 rc_3_0_2361_0 rc_3_0_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_897_193_part0 :
    blockEstimate 897 193 193 128 = 286834080 := by decide +kernel
private theorem mom_897_193_part1 :
    blockEstimate 897 193 321 128 = 1682388528 := by decide +kernel
private theorem mom_897_193_part2 :
    blockEstimate 897 193 449 128 = 3178365632 := by decide +kernel
private theorem mom_897_193_part3 :
    blockEstimate 897 193 577 128 = 3895116480 := by decide +kernel
private theorem mom_897_193_part4 :
    blockEstimate 897 193 705 128 = 3798172352 := by decide +kernel
private theorem mom_897_193_part5 :
    blockEstimate 897 193 833 128 = 2900529071 := by decide +kernel
private theorem mom_897_193_part6 :
    blockEstimate 897 193 961 128 = 1573863415 := by decide +kernel
private theorem mom_897_193_part7 :
    blockEstimate 897 193 1089 128 = 480100752 := by decide +kernel
private theorem mom_897_193_part8 :
    blockEstimate 897 193 1217 66 = 22204618 := by decide +kernel
private theorem mom_897_193_join0 :
    blockEstimate 897 193 193 256 = 1969222608 :=
  block_append mom_897_193_part0 mom_897_193_part1 rfl rfl rfl
private theorem mom_897_193_join1 :
    blockEstimate 897 193 449 256 = 7073482112 :=
  block_append mom_897_193_part2 mom_897_193_part3 rfl rfl rfl
private theorem mom_897_193_join2 :
    blockEstimate 897 193 193 512 = 9042704720 :=
  block_append mom_897_193_join0 mom_897_193_join1 rfl rfl rfl
private theorem mom_897_193_join3 :
    blockEstimate 897 193 705 256 = 6698701423 :=
  block_append mom_897_193_part4 mom_897_193_part5 rfl rfl rfl
private theorem mom_897_193_join4 :
    blockEstimate 897 193 1089 194 = 502305370 :=
  block_append mom_897_193_part7 mom_897_193_part8 rfl rfl rfl
private theorem mom_897_193_join5 :
    blockEstimate 897 193 961 322 = 2076168785 :=
  block_append mom_897_193_part6 mom_897_193_join4 rfl rfl rfl
private theorem mom_897_193_join6 :
    blockEstimate 897 193 705 578 = 8774870208 :=
  block_append mom_897_193_join3 mom_897_193_join5 rfl rfl rfl
private theorem mom_897_193_join7 :
    blockEstimate 897 193 193 1090 = 17817574928 :=
  block_append mom_897_193_join2 mom_897_193_join6 rfl rfl rfl
private theorem mom_897_193 : momentEstimate 897 193 = 17817574928 := mom_897_193_join7
private theorem rc_3_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2360 1 1 1 1 0) 0 128 = 323468730139703988535072 := by decide +kernel
private theorem rc_3_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2360 1 1 1 1 0) 128 66 = 35639508066663236928907 := by decide +kernel
private theorem rc_3_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2360 1 1 1 1 0) 0 194 = 359108238206367225463979 :=
  phaseBlock_append rc_3_1_2360_0_part0 rc_3_1_2360_0_part1 rfl rfl rfl
private theorem rc_3_1_2360_0 : fastPhase (bank 3 1).shape 179808 2360 1 1 1 1 0 = 359108238206367225463979 :=
  phase_of_block (n := 194) (by decide +kernel) rc_3_1_2360_0_join0
private theorem rc_3_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2360 1 1 1 1 1) 0 128 = 320527559613893559217056 := by decide +kernel
private theorem rc_3_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2360 1 1 1 1 1) 128 66 = 34528329820458776407248 := by decide +kernel
private theorem rc_3_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2360 1 1 1 1 1) 0 194 = 355055889434352335624304 :=
  phaseBlock_append rc_3_1_2360_1_part0 rc_3_1_2360_1_part1 rfl rfl rfl
private theorem rc_3_1_2360_1 : fastPhase (bank 3 1).shape 179808 2360 1 1 1 1 1 = 355055889434352335624304 :=
  phase_of_block (n := 194) (by decide +kernel) rc_3_1_2360_1_join0
private theorem rc_3_1_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2361 1 1 1 1 0) 0 128 = 323471025935405350603168 := by decide +kernel
private theorem rc_3_1_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2361 1 1 1 1 0) 128 66 = 35639609190587982280679 := by decide +kernel
private theorem rc_3_1_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2361 1 1 1 1 0) 0 194 = 359110635125993332883847 :=
  phaseBlock_append rc_3_1_2361_0_part0 rc_3_1_2361_0_part1 rfl rfl rfl
private theorem rc_3_1_2361_0 : fastPhase (bank 3 1).shape 179808 2361 1 1 1 1 0 = 359110635125993332883847 :=
  phase_of_block (n := 194) (by decide +kernel) rc_3_1_2361_0_join0
private theorem rc_3_1_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2361 1 1 1 1 1) 0 128 = 320529833020314888197344 := by decide +kernel
private theorem rc_3_1_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2361 1 1 1 1 1) 128 66 = 34528428036105665213552 := by decide +kernel
private theorem rc_3_1_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2361 1 1 1 1 1) 0 194 = 355058261056420553410896 :=
  phaseBlock_append rc_3_1_2361_1_part0 rc_3_1_2361_1_part1 rfl rfl rfl
private theorem rc_3_1_2361_1 : fastPhase (bank 3 1).shape 179808 2361 1 1 1 1 1 = 355058261056420553410896 :=
  phase_of_block (n := 194) (by decide +kernel) rc_3_1_2361_1_join0
private theorem receipt_3_1 : B1Checked (bank 3 1) 1 1 1 := by
  refine b1_checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_897_193)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_1_2360_0 rc_3_1_2360_1 rc_3_1_2361_0 rc_3_1_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1039_223_part0 :
    blockEstimate 1039 223 223 128 = 337636000 := by decide +kernel
private theorem mom_1039_223_part1 :
    blockEstimate 1039 223 351 128 = 2055958392 := by decide +kernel
private theorem mom_1039_223_part2 :
    blockEstimate 1039 223 479 128 = 4272421888 := by decide +kernel
private theorem mom_1039_223_part3 :
    blockEstimate 1039 223 607 128 = 5676203008 := by decide +kernel
private theorem mom_1039_223_part4 :
    blockEstimate 1039 223 735 128 = 6140460032 := by decide +kernel
private theorem mom_1039_223_part5 :
    blockEstimate 1039 223 863 128 = 5665192960 := by decide +kernel
private theorem mom_1039_223_part6 :
    blockEstimate 1039 223 991 128 = 4279992181 := by decide +kernel
private theorem mom_1039_223_part7 :
    blockEstimate 1039 223 1119 128 = 2480180155 := by decide +kernel
private theorem mom_1039_223_part8 :
    blockEstimate 1039 223 1247 128 = 948161662 := by decide +kernel
private theorem mom_1039_223_part9 :
    blockEstimate 1039 223 1375 110 = 114125942 := by decide +kernel
private theorem mom_1039_223_join0 :
    blockEstimate 1039 223 223 256 = 2393594392 :=
  block_append mom_1039_223_part0 mom_1039_223_part1 rfl rfl rfl
private theorem mom_1039_223_join1 :
    blockEstimate 1039 223 607 256 = 11816663040 :=
  block_append mom_1039_223_part3 mom_1039_223_part4 rfl rfl rfl
private theorem mom_1039_223_join2 :
    blockEstimate 1039 223 479 384 = 16089084928 :=
  block_append mom_1039_223_part2 mom_1039_223_join1 rfl rfl rfl
private theorem mom_1039_223_join3 :
    blockEstimate 1039 223 223 640 = 18482679320 :=
  block_append mom_1039_223_join0 mom_1039_223_join2 rfl rfl rfl
private theorem mom_1039_223_join4 :
    blockEstimate 1039 223 863 256 = 9945185141 :=
  block_append mom_1039_223_part5 mom_1039_223_part6 rfl rfl rfl
private theorem mom_1039_223_join5 :
    blockEstimate 1039 223 1247 238 = 1062287604 :=
  block_append mom_1039_223_part8 mom_1039_223_part9 rfl rfl rfl
private theorem mom_1039_223_join6 :
    blockEstimate 1039 223 1119 366 = 3542467759 :=
  block_append mom_1039_223_part7 mom_1039_223_join5 rfl rfl rfl
private theorem mom_1039_223_join7 :
    blockEstimate 1039 223 863 622 = 13487652900 :=
  block_append mom_1039_223_join4 mom_1039_223_join6 rfl rfl rfl
private theorem mom_1039_223_join8 :
    blockEstimate 1039 223 223 1262 = 31970332220 :=
  block_append mom_1039_223_join3 mom_1039_223_join7 rfl rfl rfl
private theorem mom_1039_223 : momentEstimate 1039 223 = 31970332220 := mom_1039_223_join8
private theorem rc_3_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2360 2 1 1 1 0) 0 128 = 596579024158939780461216 := by decide +kernel
private theorem rc_3_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2360 2 1 1 1 0) 128 96 = 114267753667533516221304 := by decide +kernel
private theorem rc_3_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2360 2 1 1 1 0) 0 224 = 710846777826473296682520 :=
  phaseBlock_append rc_3_2_2360_0_part0 rc_3_2_2360_0_part1 rfl rfl rfl
private theorem rc_3_2_2360_0 : fastPhase (bank 3 2).shape 179808 2360 2 1 1 1 0 = 710846777826473296682520 :=
  phase_of_block (n := 224) (by decide +kernel) rc_3_2_2360_0_join0
private theorem rc_3_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2360 2 1 1 1 1) 0 128 = 592109192041031335655520 := by decide +kernel
private theorem rc_3_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2360 2 1 1 1 1) 128 96 = 111784186619724107359944 := by decide +kernel
private theorem rc_3_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2360 2 1 1 1 1) 0 224 = 703893378660755443015464 :=
  phaseBlock_append rc_3_2_2360_1_part0 rc_3_2_2360_1_part1 rfl rfl rfl
private theorem rc_3_2_2360_1 : fastPhase (bank 3 2).shape 179808 2360 2 1 1 1 1 = 703893378660755443015464 :=
  phase_of_block (n := 224) (by decide +kernel) rc_3_2_2360_1_join0
private theorem rc_3_2_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2361 2 1 1 1 0) 0 128 = 596583361737338074638336 := by decide +kernel
private theorem rc_3_2_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2361 2 1 1 1 0) 128 96 = 114268131394967071705344 := by decide +kernel
private theorem rc_3_2_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2361 2 1 1 1 0) 0 224 = 710851493132305146343680 :=
  phaseBlock_append rc_3_2_2361_0_part0 rc_3_2_2361_0_part1 rfl rfl rfl
private theorem rc_3_2_2361_0 : fastPhase (bank 3 2).shape 179808 2361 2 1 1 1 0 = 710851493132305146343680 :=
  phase_of_block (n := 224) (by decide +kernel) rc_3_2_2361_0_join0
private theorem rc_3_2_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2361 2 1 1 1 1) 0 128 = 592113494048681420876416 := by decide +kernel
private theorem rc_3_2_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2361 2 1 1 1 1) 128 96 = 111784556791568211465440 := by decide +kernel
private theorem rc_3_2_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2361 2 1 1 1 1) 0 224 = 703898050840249632341856 :=
  phaseBlock_append rc_3_2_2361_1_part0 rc_3_2_2361_1_part1 rfl rfl rfl
private theorem rc_3_2_2361_1 : fastPhase (bank 3 2).shape 179808 2361 2 1 1 1 1 = 703898050840249632341856 :=
  phase_of_block (n := 224) (by decide +kernel) rc_3_2_2361_1_join0
private theorem receipt_3_2 : B1Checked (bank 3 2) 2 1 1 := by
  refine b1_checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1039_223)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_2_2360_0 rc_3_2_2360_1 rc_3_2_2361_0 rc_3_2_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1112_239_part0 :
    blockEstimate 1112 239 239 128 = 363752480 := by decide +kernel
private theorem mom_1112_239_part1 :
    blockEstimate 1112 239 367 128 = 2240398460 := by decide +kernel
private theorem mom_1112_239_part2 :
    blockEstimate 1112 239 495 128 = 4851525120 := by decide +kernel
private theorem mom_1112_239_part3 :
    blockEstimate 1112 239 623 128 = 6674081280 := by decide +kernel
private theorem mom_1112_239_part4 :
    blockEstimate 1112 239 751 128 = 7490004480 := by decide +kernel
private theorem mom_1112_239_part5 :
    blockEstimate 1112 239 879 128 = 7299294720 := by decide +kernel
private theorem mom_1112_239_part6 :
    blockEstimate 1112 239 1007 128 = 6102662886 := by decide +kernel
private theorem mom_1112_239_part7 :
    blockEstimate 1112 239 1135 128 = 4128125783 := by decide +kernel
private theorem mom_1112_239_part8 :
    blockEstimate 1112 239 1263 128 = 2135809541 := by decide +kernel
private theorem mom_1112_239_part9 :
    blockEstimate 1112 239 1391 128 = 650405408 := by decide +kernel
private theorem mom_1112_239_part10 :
    blockEstimate 1112 239 1519 71 = 34266042 := by decide +kernel
private theorem mom_1112_239_join0 :
    blockEstimate 1112 239 239 256 = 2604150940 :=
  block_append mom_1112_239_part0 mom_1112_239_part1 rfl rfl rfl
private theorem mom_1112_239_join1 :
    blockEstimate 1112 239 623 256 = 14164085760 :=
  block_append mom_1112_239_part3 mom_1112_239_part4 rfl rfl rfl
private theorem mom_1112_239_join2 :
    blockEstimate 1112 239 495 384 = 19015610880 :=
  block_append mom_1112_239_part2 mom_1112_239_join1 rfl rfl rfl
private theorem mom_1112_239_join3 :
    blockEstimate 1112 239 239 640 = 21619761820 :=
  block_append mom_1112_239_join0 mom_1112_239_join2 rfl rfl rfl
private theorem mom_1112_239_join4 :
    blockEstimate 1112 239 1007 256 = 10230788669 :=
  block_append mom_1112_239_part6 mom_1112_239_part7 rfl rfl rfl
private theorem mom_1112_239_join5 :
    blockEstimate 1112 239 879 384 = 17530083389 :=
  block_append mom_1112_239_part5 mom_1112_239_join4 rfl rfl rfl
private theorem mom_1112_239_join6 :
    blockEstimate 1112 239 1391 199 = 684671450 :=
  block_append mom_1112_239_part9 mom_1112_239_part10 rfl rfl rfl
private theorem mom_1112_239_join7 :
    blockEstimate 1112 239 1263 327 = 2820480991 :=
  block_append mom_1112_239_part8 mom_1112_239_join6 rfl rfl rfl
private theorem mom_1112_239_join8 :
    blockEstimate 1112 239 879 711 = 20350564380 :=
  block_append mom_1112_239_join5 mom_1112_239_join7 rfl rfl rfl
private theorem mom_1112_239_join9 :
    blockEstimate 1112 239 239 1351 = 41970326200 :=
  block_append mom_1112_239_join3 mom_1112_239_join8 rfl rfl rfl
private theorem mom_1112_239 : momentEstimate 1112 239 = 41970326200 := mom_1112_239_join9
private theorem rc_3_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2360 3 1 1 1 0) 0 128 = 889797609972830333686560 := by decide +kernel
private theorem rc_3_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2360 3 1 1 1 0) 128 112 = 211868369603288778684892 := by decide +kernel
private theorem rc_3_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2360 3 1 1 1 0) 0 240 = 1101665979576119112371452 :=
  phaseBlock_append rc_3_3_2360_0_part0 rc_3_3_2360_0_part1 rfl rfl rfl
private theorem rc_3_3_2360_0 : fastPhase (bank 3 3).shape 179808 2360 3 1 1 1 0 = 1101665979576119112371452 :=
  phase_of_block (n := 240) (by decide +kernel) rc_3_3_2360_0_join0
private theorem rc_3_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2360 3 1 1 1 1) 0 128 = 883704021637379150709664 := by decide +kernel
private theorem rc_3_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2360 3 1 1 1 1) 128 112 = 207900510975350536780108 := by decide +kernel
private theorem rc_3_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2360 3 1 1 1 1) 0 240 = 1091604532612729687489772 :=
  phaseBlock_append rc_3_3_2360_1_part0 rc_3_3_2360_1_part1 rfl rfl rfl
private theorem rc_3_3_2360_1 : fastPhase (bank 3 3).shape 179808 2360 3 1 1 1 1 = 1091604532612729687489772 :=
  phase_of_block (n := 240) (by decide +kernel) rc_3_3_2360_1_join0
private theorem rc_3_3_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2361 3 1 1 1 0) 0 128 = 889804159112450038083360 := by decide +kernel
private theorem rc_3_3_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2361 3 1 1 1 0) 128 112 = 211869109639688407479132 := by decide +kernel
private theorem rc_3_3_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2361 3 1 1 1 0) 0 240 = 1101673268752138445562492 :=
  phaseBlock_append rc_3_3_2361_0_part0 rc_3_3_2361_0_part1 rfl rfl rfl
private theorem rc_3_3_2361_0 : fastPhase (bank 3 3).shape 179808 2361 3 1 1 1 0 = 1101673268752138445562492 :=
  phase_of_block (n := 240) (by decide +kernel) rc_3_3_2361_0_join0
private theorem rc_3_3_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2361 3 1 1 1 1) 0 128 = 883710521302861915901920 := by decide +kernel
private theorem rc_3_3_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2361 3 1 1 1 1) 128 112 = 207901238271336991946180 := by decide +kernel
private theorem rc_3_3_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2361 3 1 1 1 1) 0 240 = 1091611759574198907848100 :=
  phaseBlock_append rc_3_3_2361_1_part0 rc_3_3_2361_1_part1 rfl rfl rfl
private theorem rc_3_3_2361_1 : fastPhase (bank 3 3).shape 179808 2361 3 1 1 1 1 = 1091611759574198907848100 :=
  phase_of_block (n := 240) (by decide +kernel) rc_3_3_2361_1_join0
private theorem receipt_3_3 : B1Checked (bank 3 3) 3 1 1 := by
  refine b1_checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1112_239)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_3_2360_0 rc_3_3_2360_1 rc_3_3_2361_0 rc_3_3_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1277_275_part0 :
    blockEstimate 1277 275 275 128 = 422782880 := by decide +kernel
private theorem mom_1277_275_part1 :
    blockEstimate 1277 275 403 128 = 2648864672 := by decide +kernel
private theorem mom_1277_275_part2 :
    blockEstimate 1277 275 531 128 = 6143188023 := by decide +kernel
private theorem mom_1277_275_part3 :
    blockEstimate 1277 275 659 128 = 9065491584 := by decide +kernel
private theorem mom_1277_275_part4 :
    blockEstimate 1277 275 787 128 = 10831326336 := by decide +kernel
private theorem mom_1277_275_part5 :
    blockEstimate 1277 275 915 128 = 11439533184 := by decide +kernel
private theorem mom_1277_275_part6 :
    blockEstimate 1277 275 1043 128 = 10890112128 := by decide +kernel
private theorem mom_1277_275_part7 :
    blockEstimate 1277 275 1171 128 = 9183773922 := by decide +kernel
private theorem mom_1277_275_part8 :
    blockEstimate 1277 275 1299 128 = 6570380075 := by decide +kernel
private theorem mom_1277_275_part9 :
    blockEstimate 1277 275 1427 128 = 3877134261 := by decide +kernel
private theorem mom_1277_275_part10 :
    blockEstimate 1277 275 1555 128 = 1650229792 := by decide +kernel
private theorem mom_1277_275_part11 :
    blockEstimate 1277 275 1683 128 = 310047264 := by decide +kernel
private theorem mom_1277_275_part12 :
    blockEstimate 1277 275 1811 16 = 563940 := by decide +kernel
private theorem mom_1277_275_join0 :
    blockEstimate 1277 275 403 256 = 8792052695 :=
  block_append mom_1277_275_part1 mom_1277_275_part2 rfl rfl rfl
private theorem mom_1277_275_join1 :
    blockEstimate 1277 275 275 384 = 9214835575 :=
  block_append mom_1277_275_part0 mom_1277_275_join0 rfl rfl rfl
private theorem mom_1277_275_join2 :
    blockEstimate 1277 275 787 256 = 22270859520 :=
  block_append mom_1277_275_part4 mom_1277_275_part5 rfl rfl rfl
private theorem mom_1277_275_join3 :
    blockEstimate 1277 275 659 384 = 31336351104 :=
  block_append mom_1277_275_part3 mom_1277_275_join2 rfl rfl rfl
private theorem mom_1277_275_join4 :
    blockEstimate 1277 275 275 768 = 40551186679 :=
  block_append mom_1277_275_join1 mom_1277_275_join3 rfl rfl rfl
private theorem mom_1277_275_join5 :
    blockEstimate 1277 275 1171 256 = 15754153997 :=
  block_append mom_1277_275_part7 mom_1277_275_part8 rfl rfl rfl
private theorem mom_1277_275_join6 :
    blockEstimate 1277 275 1043 384 = 26644266125 :=
  block_append mom_1277_275_part6 mom_1277_275_join5 rfl rfl rfl
private theorem mom_1277_275_join7 :
    blockEstimate 1277 275 1427 256 = 5527364053 :=
  block_append mom_1277_275_part9 mom_1277_275_part10 rfl rfl rfl
private theorem mom_1277_275_join8 :
    blockEstimate 1277 275 1683 144 = 310611204 :=
  block_append mom_1277_275_part11 mom_1277_275_part12 rfl rfl rfl
private theorem mom_1277_275_join9 :
    blockEstimate 1277 275 1427 400 = 5837975257 :=
  block_append mom_1277_275_join7 mom_1277_275_join8 rfl rfl rfl
private theorem mom_1277_275_join10 :
    blockEstimate 1277 275 1043 784 = 32482241382 :=
  block_append mom_1277_275_join6 mom_1277_275_join9 rfl rfl rfl
private theorem mom_1277_275_join11 :
    blockEstimate 1277 275 275 1552 = 73033428061 :=
  block_append mom_1277_275_join4 mom_1277_275_join10 rfl rfl rfl
private theorem mom_1277_275 : momentEstimate 1277 275 = 73033428061 := mom_1277_275_join11
private theorem rc_3_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 0) 0 128 = 1578238049334750103645728 := by decide +kernel
private theorem rc_3_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 0) 128 128 = 539740798039908357094944 := by decide +kernel
private theorem rc_3_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 0) 256 20 = 9146057316987197000751 := by decide +kernel
private theorem rc_3_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 0) 128 148 = 548886855356895554095695 :=
  phaseBlock_append rc_3_4_2360_0_part1 rc_3_4_2360_0_part2 rfl rfl rfl
private theorem rc_3_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 0) 0 276 = 2127124904691645657741423 :=
  phaseBlock_append rc_3_4_2360_0_part0 rc_3_4_2360_0_join0 rfl rfl rfl
private theorem rc_3_4_2360_0 : fastPhase (bank 3 4).shape 179808 2360 4 1 1 1 0 = 2127124904691645657741423 :=
  phase_of_block (n := 276) (by decide +kernel) rc_3_4_2360_0_join1
private theorem rc_3_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 1) 0 128 = 1569174193944921287335840 := by decide +kernel
private theorem rc_3_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 1) 128 128 = 532771479601416261160864 := by decide +kernel
private theorem rc_3_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 1) 256 20 = 8265969346945347785391 := by decide +kernel
private theorem rc_3_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 1) 128 148 = 541037448948361608946255 :=
  phaseBlock_append rc_3_4_2360_1_part1 rc_3_4_2360_1_part2 rfl rfl rfl
private theorem rc_3_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2360 4 1 1 1 1) 0 276 = 2110211642893282896282095 :=
  phaseBlock_append rc_3_4_2360_1_part0 rc_3_4_2360_1_join0 rfl rfl rfl
private theorem rc_3_4_2360_1 : fastPhase (bank 3 4).shape 179808 2360 4 1 1 1 1 = 2110211642893282896282095 :=
  phase_of_block (n := 276) (by decide +kernel) rc_3_4_2360_1_join1
private theorem rc_3_4_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 0) 0 128 = 1578249960692044609820192 := by decide +kernel
private theorem rc_3_4_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 0) 128 128 = 539742905586732966094368 := by decide +kernel
private theorem rc_3_4_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 0) 256 20 = 9146069575350040492047 := by decide +kernel
private theorem rc_3_4_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 0) 128 148 = 548888975162083006586415 :=
  phaseBlock_append rc_3_4_2361_0_part1 rc_3_4_2361_0_part2 rfl rfl rfl
private theorem rc_3_4_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 0) 0 276 = 2127138935854127616406607 :=
  phaseBlock_append rc_3_4_2361_0_part0 rc_3_4_2361_0_join0 rfl rfl rfl
private theorem rc_3_4_2361_0 : fastPhase (bank 3 4).shape 179808 2361 4 1 1 1 0 = 2127138935854127616406607 :=
  phase_of_block (n := 276) (by decide +kernel) rc_3_4_2361_0_join1
private theorem rc_3_4_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 1) 0 128 = 1569186028934682642094880 := by decide +kernel
private theorem rc_3_4_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 1) 128 128 = 532773560415725922126624 := by decide +kernel
private theorem rc_3_4_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 1) 256 20 = 8265980472444961427091 := by decide +kernel
private theorem rc_3_4_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 1) 128 148 = 541039540888170883553715 :=
  phaseBlock_append rc_3_4_2361_1_part1 rc_3_4_2361_1_part2 rfl rfl rfl
private theorem rc_3_4_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2361 4 1 1 1 1) 0 276 = 2110225569822853525648595 :=
  phaseBlock_append rc_3_4_2361_1_part0 rc_3_4_2361_1_join0 rfl rfl rfl
private theorem rc_3_4_2361_1 : fastPhase (bank 3 4).shape 179808 2361 4 1 1 1 1 = 2110225569822853525648595 :=
  phase_of_block (n := 276) (by decide +kernel) rc_3_4_2361_1_join1
private theorem receipt_3_4 : B1Checked (bank 3 4) 4 1 1 := by
  refine b1_checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1277_275)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_4_2360_0 rc_3_4_2360_1 rc_3_4_2361_0 rc_3_4_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1469_316_part0 :
    blockEstimate 1469 316 316 128 = 491472800 := by decide +kernel
private theorem mom_1469_316_part1 :
    blockEstimate 1469 316 444 128 = 3123353504 := by decide +kernel
private theorem mom_1469_316_part2 :
    blockEstimate 1469 316 572 128 = 7567080831 := by decide +kernel
private theorem mom_1469_316_part3 :
    blockEstimate 1469 316 700 128 = 11985359168 := by decide +kernel
private theorem mom_1469_316_part4 :
    blockEstimate 1469 316 828 128 = 15117177152 := by decide +kernel
private theorem mom_1469_316_part5 :
    blockEstimate 1469 316 956 128 = 16919400768 := by decide +kernel
private theorem mom_1469_316_part6 :
    blockEstimate 1469 316 1084 128 = 17392030016 := by decide +kernel
private theorem mom_1469_316_part7 :
    blockEstimate 1469 316 1212 128 = 16535064896 := by decide +kernel
private theorem mom_1469_316_part8 :
    blockEstimate 1469 316 1340 128 = 14348505408 := by decide +kernel
private theorem mom_1469_316_part9 :
    blockEstimate 1469 316 1468 128 = 11000923653 := by decide +kernel
private theorem mom_1469_316_part10 :
    blockEstimate 1469 316 1596 128 = 7358707046 := by decide +kernel
private theorem mom_1469_316_part11 :
    blockEstimate 1469 316 1724 128 = 4061868147 := by decide +kernel
private theorem mom_1469_316_part12 :
    blockEstimate 1469 316 1852 128 = 1555773328 := by decide +kernel
private theorem mom_1469_316_part13 :
    blockEstimate 1469 316 1980 121 = 216422594 := by decide +kernel
private theorem mom_1469_316_join0 :
    blockEstimate 1469 316 444 256 = 10690434335 :=
  block_append mom_1469_316_part1 mom_1469_316_part2 rfl rfl rfl
private theorem mom_1469_316_join1 :
    blockEstimate 1469 316 316 384 = 11181907135 :=
  block_append mom_1469_316_part0 mom_1469_316_join0 rfl rfl rfl
private theorem mom_1469_316_join2 :
    blockEstimate 1469 316 700 256 = 27102536320 :=
  block_append mom_1469_316_part3 mom_1469_316_part4 rfl rfl rfl
private theorem mom_1469_316_join3 :
    blockEstimate 1469 316 956 256 = 34311430784 :=
  block_append mom_1469_316_part5 mom_1469_316_part6 rfl rfl rfl
private theorem mom_1469_316_join4 :
    blockEstimate 1469 316 700 512 = 61413967104 :=
  block_append mom_1469_316_join2 mom_1469_316_join3 rfl rfl rfl
private theorem mom_1469_316_join5 :
    blockEstimate 1469 316 316 896 = 72595874239 :=
  block_append mom_1469_316_join1 mom_1469_316_join4 rfl rfl rfl
private theorem mom_1469_316_join6 :
    blockEstimate 1469 316 1340 256 = 25349429061 :=
  block_append mom_1469_316_part8 mom_1469_316_part9 rfl rfl rfl
private theorem mom_1469_316_join7 :
    blockEstimate 1469 316 1212 384 = 41884493957 :=
  block_append mom_1469_316_part7 mom_1469_316_join6 rfl rfl rfl
private theorem mom_1469_316_join8 :
    blockEstimate 1469 316 1596 256 = 11420575193 :=
  block_append mom_1469_316_part10 mom_1469_316_part11 rfl rfl rfl
private theorem mom_1469_316_join9 :
    blockEstimate 1469 316 1852 249 = 1772195922 :=
  block_append mom_1469_316_part12 mom_1469_316_part13 rfl rfl rfl
private theorem mom_1469_316_join10 :
    blockEstimate 1469 316 1596 505 = 13192771115 :=
  block_append mom_1469_316_join8 mom_1469_316_join9 rfl rfl rfl
private theorem mom_1469_316_join11 :
    blockEstimate 1469 316 1212 889 = 55077265072 :=
  block_append mom_1469_316_join7 mom_1469_316_join10 rfl rfl rfl
private theorem mom_1469_316_join12 :
    blockEstimate 1469 316 316 1785 = 127673139311 :=
  block_append mom_1469_316_join5 mom_1469_316_join11 rfl rfl rfl
private theorem mom_1469_316 : momentEstimate 1469 316 = 127673139311 := mom_1469_316_join12
private theorem rc_3_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 0) 0 128 = 3256933226913436795597664 := by decide +kernel
private theorem rc_3_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 0) 128 128 = 1412324712710337835139936 := by decide +kernel
private theorem rc_3_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 0) 256 61 = 146833924750855391002000 := by decide +kernel
private theorem rc_3_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 0) 128 189 = 1559158637461193226141936 :=
  phaseBlock_append rc_3_5_2360_0_part1 rc_3_5_2360_0_part2 rfl rfl rfl
private theorem rc_3_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 0) 0 317 = 4816091864374630021739600 :=
  phaseBlock_append rc_3_5_2360_0_part0 rc_3_5_2360_0_join0 rfl rfl rfl
private theorem rc_3_5_2360_0 : fastPhase (bank 3 5).shape 179808 2360 6 1 1 1 0 = 4816091864374630021739600 :=
  phase_of_block (n := 317) (by decide +kernel) rc_3_5_2360_0_join1
private theorem rc_3_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 1) 0 128 = 3241157067379506989373216 := by decide +kernel
private theorem rc_3_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 1) 128 128 = 1399614223713537134585632 := by decide +kernel
private theorem rc_3_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 1) 256 61 = 141969834134336212588409 := by decide +kernel
private theorem rc_3_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 1) 128 189 = 1541584057847873347174041 :=
  phaseBlock_append rc_3_5_2360_1_part1 rc_3_5_2360_1_part2 rfl rfl rfl
private theorem rc_3_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2360 6 1 1 1 1) 0 317 = 4782741125227380336547257 :=
  phaseBlock_append rc_3_5_2360_1_part0 rc_3_5_2360_1_join0 rfl rfl rfl
private theorem rc_3_5_2360_1 : fastPhase (bank 3 5).shape 179808 2360 6 1 1 1 1 = 4782741125227380336547257 :=
  phase_of_block (n := 317) (by decide +kernel) rc_3_5_2360_1_join1
private theorem rc_3_5_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 0) 0 128 = 3256958395272217559278784 := by decide +kernel
private theorem rc_3_5_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 0) 128 128 = 1412330955137831904421056 := by decide +kernel
private theorem rc_3_5_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 0) 256 61 = 146834211732771735071292 := by decide +kernel
private theorem rc_3_5_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 0) 128 189 = 1559165166870603639492348 :=
  phaseBlock_append rc_3_5_2361_0_part1 rc_3_5_2361_0_part2 rfl rfl rfl
private theorem rc_3_5_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 0) 0 317 = 4816123562142821198771132 :=
  phaseBlock_append rc_3_5_2361_0_part0 rc_3_5_2361_0_join0 rfl rfl rfl
private theorem rc_3_5_2361_0 : fastPhase (bank 3 5).shape 179808 2361 6 1 1 1 0 = 4816123562142821198771132 :=
  phase_of_block (n := 317) (by decide +kernel) rc_3_5_2361_0_join1
private theorem rc_3_5_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 1) 0 128 = 3241182098435332235600256 := by decide +kernel
private theorem rc_3_5_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 1) 128 128 = 1399620407290412905218432 := by decide +kernel
private theorem rc_3_5_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 1) 256 61 = 141970112271610561955184 := by decide +kernel
private theorem rc_3_5_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 1) 128 189 = 1541590519562023467173616 :=
  phaseBlock_append rc_3_5_2361_1_part1 rc_3_5_2361_1_part2 rfl rfl rfl
private theorem rc_3_5_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2361 6 1 1 1 1) 0 317 = 4782772617997355702773872 :=
  phaseBlock_append rc_3_5_2361_1_part0 rc_3_5_2361_1_join0 rfl rfl rfl
private theorem rc_3_5_2361_1 : fastPhase (bank 3 5).shape 179808 2361 6 1 1 1 1 = 4782772617997355702773872 :=
  phase_of_block (n := 317) (by decide +kernel) rc_3_5_2361_1_join1
private theorem receipt_3_5 : B1Checked (bank 3 5) 6 1 1 := by
  refine b1_checked_from_values (bank 3 5) 6 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1469_316)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_5_2360_0 rc_3_5_2360_1 rc_3_5_2361_0 rc_3_5_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1754_377_part0 :
    blockEstimate 1754 377 377 128 = 593434400 := by decide +kernel
private theorem mom_1754_377_part1 :
    blockEstimate 1754 377 505 128 = 3827672864 := by decide +kernel
private theorem mom_1754_377_part2 :
    blockEstimate 1754 377 633 128 = 9529133810 := by decide +kernel
private theorem mom_1754_377_part3 :
    blockEstimate 1754 377 761 128 = 16369504704 := by decide +kernel
private theorem mom_1754_377_part4 :
    blockEstimate 1754 377 889 128 = 22057914816 := by decide +kernel
private theorem mom_1754_377_part5 :
    blockEstimate 1754 377 1017 128 = 26160878016 := by decide +kernel
private theorem mom_1754_377_part6 :
    blockEstimate 1754 377 1145 128 = 28678394304 := by decide +kernel
private theorem mom_1754_377_part7 :
    blockEstimate 1754 377 1273 128 = 29610463680 := by decide +kernel
private theorem mom_1754_377_part8 :
    blockEstimate 1754 377 1401 128 = 28957086144 := by decide +kernel
private theorem mom_1754_377_part9 :
    blockEstimate 1754 377 1529 128 = 26718261696 := by decide +kernel
private theorem mom_1754_377_part10 :
    blockEstimate 1754 377 1657 128 = 22896679896 := by decide +kernel
private theorem mom_1754_377_part11 :
    blockEstimate 1754 377 1785 128 = 17878493995 := by decide +kernel
private theorem mom_1754_377_part12 :
    blockEstimate 1754 377 1913 128 = 12679477919 := by decide +kernel
private theorem mom_1754_377_part13 :
    blockEstimate 1754 377 2041 128 = 7882509500 := by decide +kernel
private theorem mom_1754_377_part14 :
    blockEstimate 1754 377 2169 128 = 3925705536 := by decide +kernel
private theorem mom_1754_377_part15 :
    blockEstimate 1754 377 2297 128 = 1237719872 := by decide +kernel
private theorem mom_1754_377_part16 :
    blockEstimate 1754 377 2425 83 = 86245992 := by decide +kernel
private theorem mom_1754_377_join0 :
    blockEstimate 1754 377 377 256 = 4421107264 :=
  block_append mom_1754_377_part0 mom_1754_377_part1 rfl rfl rfl
private theorem mom_1754_377_join1 :
    blockEstimate 1754 377 633 256 = 25898638514 :=
  block_append mom_1754_377_part2 mom_1754_377_part3 rfl rfl rfl
private theorem mom_1754_377_join2 :
    blockEstimate 1754 377 377 512 = 30319745778 :=
  block_append mom_1754_377_join0 mom_1754_377_join1 rfl rfl rfl
private theorem mom_1754_377_join3 :
    blockEstimate 1754 377 889 256 = 48218792832 :=
  block_append mom_1754_377_part4 mom_1754_377_part5 rfl rfl rfl
private theorem mom_1754_377_join4 :
    blockEstimate 1754 377 1145 256 = 58288857984 :=
  block_append mom_1754_377_part6 mom_1754_377_part7 rfl rfl rfl
private theorem mom_1754_377_join5 :
    blockEstimate 1754 377 889 512 = 106507650816 :=
  block_append mom_1754_377_join3 mom_1754_377_join4 rfl rfl rfl
private theorem mom_1754_377_join6 :
    blockEstimate 1754 377 377 1024 = 136827396594 :=
  block_append mom_1754_377_join2 mom_1754_377_join5 rfl rfl rfl
private theorem mom_1754_377_join7 :
    blockEstimate 1754 377 1401 256 = 55675347840 :=
  block_append mom_1754_377_part8 mom_1754_377_part9 rfl rfl rfl
private theorem mom_1754_377_join8 :
    blockEstimate 1754 377 1657 256 = 40775173891 :=
  block_append mom_1754_377_part10 mom_1754_377_part11 rfl rfl rfl
private theorem mom_1754_377_join9 :
    blockEstimate 1754 377 1401 512 = 96450521731 :=
  block_append mom_1754_377_join7 mom_1754_377_join8 rfl rfl rfl
private theorem mom_1754_377_join10 :
    blockEstimate 1754 377 1913 256 = 20561987419 :=
  block_append mom_1754_377_part12 mom_1754_377_part13 rfl rfl rfl
private theorem mom_1754_377_join11 :
    blockEstimate 1754 377 2297 211 = 1323965864 :=
  block_append mom_1754_377_part15 mom_1754_377_part16 rfl rfl rfl
private theorem mom_1754_377_join12 :
    blockEstimate 1754 377 2169 339 = 5249671400 :=
  block_append mom_1754_377_part14 mom_1754_377_join11 rfl rfl rfl
private theorem mom_1754_377_join13 :
    blockEstimate 1754 377 1913 595 = 25811658819 :=
  block_append mom_1754_377_join10 mom_1754_377_join12 rfl rfl rfl
private theorem mom_1754_377_join14 :
    blockEstimate 1754 377 1401 1107 = 122262180550 :=
  block_append mom_1754_377_join9 mom_1754_377_join13 rfl rfl rfl
private theorem mom_1754_377_join15 :
    blockEstimate 1754 377 377 2131 = 259089577144 :=
  block_append mom_1754_377_join6 mom_1754_377_join14 rfl rfl rfl
private theorem mom_1754_377 : momentEstimate 1754 377 = 259089577144 := mom_1754_377_join15
private theorem rc_3_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 0) 0 128 = 8082763888795647144618720 := by decide +kernel
private theorem rc_3_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 0) 128 128 = 4293466336693093933980384 := by decide +kernel
private theorem rc_3_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 0) 256 122 = 1200688042360492565899866 := by decide +kernel
private theorem rc_3_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 0) 128 250 = 5494154379053586499880250 :=
  phaseBlock_append rc_3_6_2360_0_part1 rc_3_6_2360_0_part2 rfl rfl rfl
private theorem rc_3_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 0) 0 378 = 13576918267849233644498970 :=
  phaseBlock_append rc_3_6_2360_0_part0 rc_3_6_2360_0_join0 rfl rfl rfl
private theorem rc_3_6_2360_0 : fastPhase (bank 3 6).shape 179808 2360 9 1 1 1 0 = 13576918267849233644498970 :=
  phase_of_block (n := 378) (by decide +kernel) rc_3_6_2360_0_join1
private theorem rc_3_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 1) 0 128 = 8051003130346904112057696 := by decide +kernel
private theorem rc_3_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 1) 128 128 = 4266699359258901866052960 := by decide +kernel
private theorem rc_3_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 1) 256 122 = 1180326510240874781305290 := by decide +kernel
private theorem rc_3_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 1) 128 250 = 5447025869499776647358250 :=
  phaseBlock_append rc_3_6_2360_1_part1 rc_3_6_2360_1_part2 rfl rfl rfl
private theorem rc_3_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2360 9 1 1 1 1) 0 378 = 13498028999846680759415946 :=
  phaseBlock_append rc_3_6_2360_1_part0 rc_3_6_2360_1_join0 rfl rfl rfl
private theorem rc_3_6_2360_1 : fastPhase (bank 3 6).shape 179808 2360 9 1 1 1 1 = 13498028999846680759415946 :=
  phase_of_block (n := 378) (by decide +kernel) rc_3_6_2360_1_join1
private theorem rc_3_6_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 0) 0 128 = 8082827759654420712895680 := by decide +kernel
private theorem rc_3_6_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 0) 128 128 = 4293488041988475956688064 := by decide +kernel
private theorem rc_3_6_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 0) 256 122 = 1200691194544908197730236 := by decide +kernel
private theorem rc_3_6_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 0) 128 250 = 5494179236533384154418300 :=
  phaseBlock_append rc_3_6_2361_0_part1 rc_3_6_2361_0_part2 rfl rfl rfl
private theorem rc_3_6_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 0) 0 378 = 13577006996187804867313980 :=
  phaseBlock_append rc_3_6_2361_0_part0 rc_3_6_2361_0_join0 rfl rfl rfl
private theorem rc_3_6_2361_0 : fastPhase (bank 3 6).shape 179808 2361 9 1 1 1 0 = 13577006996187804867313980 :=
  phase_of_block (n := 378) (by decide +kernel) rc_3_6_2361_0_join1
private theorem rc_3_6_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 1) 0 128 = 8051066716338637182782592 := by decide +kernel
private theorem rc_3_6_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 1) 128 128 = 4266720917342209346530432 := by decide +kernel
private theorem rc_3_6_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 1) 256 122 = 1180329613306803624255668 := by decide +kernel
private theorem rc_3_6_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 1) 128 250 = 5447050530649012970786100 :=
  phaseBlock_append rc_3_6_2361_1_part1 rc_3_6_2361_1_part2 rfl rfl rfl
private theorem rc_3_6_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2361 9 1 1 1 1) 0 378 = 13498117246987650153568692 :=
  phaseBlock_append rc_3_6_2361_1_part0 rc_3_6_2361_1_join0 rfl rfl rfl
private theorem rc_3_6_2361_1 : fastPhase (bank 3 6).shape 179808 2361 9 1 1 1 1 = 13498117246987650153568692 :=
  phase_of_block (n := 378) (by decide +kernel) rc_3_6_2361_1_join1
private theorem receipt_3_6 : B1Checked (bank 3 6) 9 1 1 := by
  refine b1_checked_from_values (bank 3 6) 9 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1754_377)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_6_2360_0 rc_3_6_2360_1 rc_3_6_2361_0 rc_3_6_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2134_459_part0 :
    blockEstimate 2134 459 459 128 = 729383200 := by decide +kernel
private theorem mom_2134_459_part1 :
    blockEstimate 2134 459 587 128 = 4766765344 := by decide +kernel
private theorem mom_2134_459_part2 :
    blockEstimate 2134 459 715 128 = 12068364576 := by decide +kernel
private theorem mom_2134_459_part3 :
    blockEstimate 2134 459 843 128 = 21788301385 := by decide +kernel
private theorem mom_2134_459_part4 :
    blockEstimate 2134 459 971 128 = 31761888640 := by decide +kernel
private theorem mom_2134_459_part5 :
    blockEstimate 2134 459 1099 128 = 39927838080 := by decide +kernel
private theorem mom_2134_459_part6 :
    blockEstimate 2134 459 1227 128 = 46164407680 := by decide +kernel
private theorem mom_2134_459_part7 :
    blockEstimate 2134 459 1355 128 = 50471597440 := by decide +kernel
private theorem mom_2134_459_part8 :
    blockEstimate 2134 459 1483 128 = 52849407360 := by decide +kernel
private theorem mom_2134_459_part9 :
    blockEstimate 2134 459 1611 128 = 53297837440 := by decide +kernel
private theorem mom_2134_459_part10 :
    blockEstimate 2134 459 1739 128 = 51816887680 := by decide +kernel
private theorem mom_2134_459_part11 :
    blockEstimate 2134 459 1867 128 = 48406558080 := by decide +kernel
private theorem mom_2134_459_part12 :
    blockEstimate 2134 459 1995 128 = 43066848640 := by decide +kernel
private theorem mom_2134_459_part13 :
    blockEstimate 2134 459 2123 128 = 35979616835 := by decide +kernel
private theorem mom_2134_459_part14 :
    blockEstimate 2134 459 2251 128 = 28244549285 := by decide +kernel
private theorem mom_2134_459_part15 :
    blockEstimate 2134 459 2379 128 = 20647635418 := by decide +kernel
private theorem mom_2134_459_part16 :
    blockEstimate 2134 459 2507 128 = 13680533529 := by decide +kernel
private theorem mom_2134_459_part17 :
    blockEstimate 2134 459 2635 128 = 7760513968 := by decide +kernel
private theorem mom_2134_459_part18 :
    blockEstimate 2134 459 2763 128 = 3347888048 := by decide +kernel
private theorem mom_2134_459_part19 :
    blockEstimate 2134 459 2891 128 = 729047984 := by decide +kernel
private theorem mom_2134_459_part20 :
    blockEstimate 2134 459 3019 33 = 7241250 := by decide +kernel
private theorem mom_2134_459_join0 :
    blockEstimate 2134 459 459 256 = 5496148544 :=
  block_append mom_2134_459_part0 mom_2134_459_part1 rfl rfl rfl
private theorem mom_2134_459_join1 :
    blockEstimate 2134 459 843 256 = 53550190025 :=
  block_append mom_2134_459_part3 mom_2134_459_part4 rfl rfl rfl
private theorem mom_2134_459_join2 :
    blockEstimate 2134 459 715 384 = 65618554601 :=
  block_append mom_2134_459_part2 mom_2134_459_join1 rfl rfl rfl
private theorem mom_2134_459_join3 :
    blockEstimate 2134 459 459 640 = 71114703145 :=
  block_append mom_2134_459_join0 mom_2134_459_join2 rfl rfl rfl
private theorem mom_2134_459_join4 :
    blockEstimate 2134 459 1099 256 = 86092245760 :=
  block_append mom_2134_459_part5 mom_2134_459_part6 rfl rfl rfl
private theorem mom_2134_459_join5 :
    blockEstimate 2134 459 1483 256 = 106147244800 :=
  block_append mom_2134_459_part8 mom_2134_459_part9 rfl rfl rfl
private theorem mom_2134_459_join6 :
    blockEstimate 2134 459 1355 384 = 156618842240 :=
  block_append mom_2134_459_part7 mom_2134_459_join5 rfl rfl rfl
private theorem mom_2134_459_join7 :
    blockEstimate 2134 459 1099 640 = 242711088000 :=
  block_append mom_2134_459_join4 mom_2134_459_join6 rfl rfl rfl
private theorem mom_2134_459_join8 :
    blockEstimate 2134 459 459 1280 = 313825791145 :=
  block_append mom_2134_459_join3 mom_2134_459_join7 rfl rfl rfl
private theorem mom_2134_459_join9 :
    blockEstimate 2134 459 1739 256 = 100223445760 :=
  block_append mom_2134_459_part10 mom_2134_459_part11 rfl rfl rfl
private theorem mom_2134_459_join10 :
    blockEstimate 2134 459 2123 256 = 64224166120 :=
  block_append mom_2134_459_part13 mom_2134_459_part14 rfl rfl rfl
private theorem mom_2134_459_join11 :
    blockEstimate 2134 459 1995 384 = 107291014760 :=
  block_append mom_2134_459_part12 mom_2134_459_join10 rfl rfl rfl
private theorem mom_2134_459_join12 :
    blockEstimate 2134 459 1739 640 = 207514460520 :=
  block_append mom_2134_459_join9 mom_2134_459_join11 rfl rfl rfl
private theorem mom_2134_459_join13 :
    blockEstimate 2134 459 2507 256 = 21441047497 :=
  block_append mom_2134_459_part16 mom_2134_459_part17 rfl rfl rfl
private theorem mom_2134_459_join14 :
    blockEstimate 2134 459 2379 384 = 42088682915 :=
  block_append mom_2134_459_part15 mom_2134_459_join13 rfl rfl rfl
private theorem mom_2134_459_join15 :
    blockEstimate 2134 459 2891 161 = 736289234 :=
  block_append mom_2134_459_part19 mom_2134_459_part20 rfl rfl rfl
private theorem mom_2134_459_join16 :
    blockEstimate 2134 459 2763 289 = 4084177282 :=
  block_append mom_2134_459_part18 mom_2134_459_join15 rfl rfl rfl
private theorem mom_2134_459_join17 :
    blockEstimate 2134 459 2379 673 = 46172860197 :=
  block_append mom_2134_459_join14 mom_2134_459_join16 rfl rfl rfl
private theorem mom_2134_459_join18 :
    blockEstimate 2134 459 1739 1313 = 253687320717 :=
  block_append mom_2134_459_join12 mom_2134_459_join17 rfl rfl rfl
private theorem mom_2134_459_join19 :
    blockEstimate 2134 459 459 2593 = 567513111862 :=
  block_append mom_2134_459_join8 mom_2134_459_join18 rfl rfl rfl
private theorem mom_2134_459 : momentEstimate 2134 459 = 567513111862 := mom_2134_459_join19
private theorem rc_3_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 0 128 = 22101867133530961450880640 := by decide +kernel
private theorem rc_3_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 128 128 = 13693028398097290653560448 := by decide +kernel
private theorem rc_3_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 256 128 = 6482111187051505204530816 := by decide +kernel
private theorem rc_3_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 384 76 = 961666934600058594339432 := by decide +kernel
private theorem rc_3_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 0 256 = 35794895531628252104441088 :=
  phaseBlock_append rc_3_7_2360_0_part0 rc_3_7_2360_0_part1 rfl rfl rfl
private theorem rc_3_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 256 204 = 7443778121651563798870248 :=
  phaseBlock_append rc_3_7_2360_0_part2 rc_3_7_2360_0_part3 rfl rfl rfl
private theorem rc_3_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 0) 0 460 = 43238673653279815903311336 :=
  phaseBlock_append rc_3_7_2360_0_join0 rc_3_7_2360_0_join1 rfl rfl rfl
private theorem rc_3_7_2360_0 : fastPhase (bank 3 7).shape 179808 2360 13 1 1 1 0 = 43238673653279815903311336 :=
  phase_of_block (n := 460) (by decide +kernel) rc_3_7_2360_0_join2
private theorem rc_3_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 0 128 = 22032601737992111881099776 := by decide +kernel
private theorem rc_3_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 128 128 = 13632424472222556202547712 := by decide +kernel
private theorem rc_3_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 256 128 = 6430970455626511224396288 := by decide +kernel
private theorem rc_3_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 384 76 = 936102243218113333543020 := by decide +kernel
private theorem rc_3_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 0 256 = 35665026210214668083647488 :=
  phaseBlock_append rc_3_7_2360_1_part0 rc_3_7_2360_1_part1 rfl rfl rfl
private theorem rc_3_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 256 204 = 7367072698844624557939308 :=
  phaseBlock_append rc_3_7_2360_1_part2 rc_3_7_2360_1_part3 rfl rfl rfl
private theorem rc_3_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2360 13 1 1 1 1) 0 460 = 43032098909059292641586796 :=
  phaseBlock_append rc_3_7_2360_1_join0 rc_3_7_2360_1_join1 rfl rfl rfl
private theorem rc_3_7_2360_1 : fastPhase (bank 3 7).shape 179808 2360 13 1 1 1 1 = 43032098909059292641586796 :=
  phase_of_block (n := 460) (by decide +kernel) rc_3_7_2360_1_join2
private theorem rc_3_7_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 0 128 = 22102046065805090177490720 := by decide +kernel
private theorem rc_3_7_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 128 128 = 13693106548398911871463200 := by decide +kernel
private theorem rc_3_7_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 256 128 = 6482133763145910056730400 := by decide +kernel
private theorem rc_3_7_2361_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 384 76 = 961668616822435682845685 := by decide +kernel
private theorem rc_3_7_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 0 256 = 35795152614204002048953920 :=
  phaseBlock_append rc_3_7_2361_0_part0 rc_3_7_2361_0_part1 rfl rfl rfl
private theorem rc_3_7_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 256 204 = 7443802379968345739576085 :=
  phaseBlock_append rc_3_7_2361_0_part2 rc_3_7_2361_0_part3 rfl rfl rfl
private theorem rc_3_7_2361_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 0) 0 460 = 43238954994172347788530005 :=
  phaseBlock_append rc_3_7_2361_0_join0 rc_3_7_2361_0_join1 rfl rfl rfl
private theorem rc_3_7_2361_0 : fastPhase (bank 3 7).shape 179808 2361 13 1 1 1 0 = 43238954994172347788530005 :=
  phase_of_block (n := 460) (by decide +kernel) rc_3_7_2361_0_join2
private theorem rc_3_7_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 0 128 = 22032780029766429885810144 := by decide +kernel
private theorem rc_3_7_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 128 128 = 13632502238141174050665952 := by decide +kernel
private theorem rc_3_7_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 256 128 = 6430992844460601473443296 := by decide +kernel
private theorem rc_3_7_2361_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 384 76 = 936103883770598227987715 := by decide +kernel
private theorem rc_3_7_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 0 256 = 35665282267907603936476096 :=
  phaseBlock_append rc_3_7_2361_1_part0 rc_3_7_2361_1_part1 rfl rfl rfl
private theorem rc_3_7_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 256 204 = 7367096728231199701431011 :=
  phaseBlock_append rc_3_7_2361_1_part2 rc_3_7_2361_1_part3 rfl rfl rfl
private theorem rc_3_7_2361_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2361 13 1 1 1 1) 0 460 = 43032378996138803637907107 :=
  phaseBlock_append rc_3_7_2361_1_join0 rc_3_7_2361_1_join1 rfl rfl rfl
private theorem rc_3_7_2361_1 : fastPhase (bank 3 7).shape 179808 2361 13 1 1 1 1 = 43032378996138803637907107 :=
  phase_of_block (n := 460) (by decide +kernel) rc_3_7_2361_1_join2
private theorem receipt_3_7 : B1Checked (bank 3 7) 13 1 1 := by
  refine b1_checked_from_values (bank 3 7) 13 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2134_459)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_7_2360_0 rc_3_7_2360_1 rc_3_7_2361_0 rc_3_7_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2445_526_part0 :
    blockEstimate 2445 526 526 128 = 840646560 := by decide +kernel
private theorem mom_2445_526_part1 :
    blockEstimate 2445 526 654 128 = 5535338400 := by decide +kernel
private theorem mom_2445_526_part2 :
    blockEstimate 2445 526 782 128 = 14146461600 := by decide +kernel
private theorem mom_2445_526_part3 :
    blockEstimate 2445 526 910 128 = 25868709792 := by decide +kernel
private theorem mom_2445_526_part4 :
    blockEstimate 2445 526 1038 128 = 39443952838 := by decide +kernel
private theorem mom_2445_526_part5 :
    blockEstimate 2445 526 1166 128 = 51772952192 := by decide +kernel
private theorem mom_2445_526_part6 :
    blockEstimate 2445 526 1294 128 = 61892431488 := by decide +kernel
private theorem mom_2445_526_part7 :
    blockEstimate 2445 526 1422 128 = 69801512576 := by decide +kernel
private theorem mom_2445_526_part8 :
    blockEstimate 2445 526 1550 128 = 75500195456 := by decide +kernel
private theorem mom_2445_526_part9 :
    blockEstimate 2445 526 1678 128 = 78988480128 := by decide +kernel
private theorem mom_2445_526_part10 :
    blockEstimate 2445 526 1806 128 = 80266366592 := by decide +kernel
private theorem mom_2445_526_part11 :
    blockEstimate 2445 526 1934 128 = 79333854848 := by decide +kernel
private theorem mom_2445_526_part12 :
    blockEstimate 2445 526 2062 128 = 76190944896 := by decide +kernel
private theorem mom_2445_526_part13 :
    blockEstimate 2445 526 2190 128 = 70837636736 := by decide +kernel
private theorem mom_2445_526_part14 :
    blockEstimate 2445 526 2318 128 = 63273930368 := by decide +kernel
private theorem mom_2445_526_part15 :
    blockEstimate 2445 526 2446 128 = 53777739427 := by decide +kernel
private theorem mom_2445_526_part16 :
    blockEstimate 2445 526 2574 128 = 43617363704 := by decide +kernel
private theorem mom_2445_526_part17 :
    blockEstimate 2445 526 2702 128 = 33557793299 := by decide +kernel
private theorem mom_2445_526_part18 :
    blockEstimate 2445 526 2830 128 = 24104636706 := by decide +kernel
private theorem mom_2445_526_part19 :
    blockEstimate 2445 526 2958 128 = 15677839979 := by decide +kernel
private theorem mom_2445_526_part20 :
    blockEstimate 2445 526 3086 128 = 8739535776 := by decide +kernel
private theorem mom_2445_526_part21 :
    blockEstimate 2445 526 3214 128 = 3680547744 := by decide +kernel
private theorem mom_2445_526_part22 :
    blockEstimate 2445 526 3342 128 = 753249184 := by decide +kernel
private theorem mom_2445_526_part23 :
    blockEstimate 2445 526 3470 27 = 4683511 := by decide +kernel
private theorem mom_2445_526_join0 :
    blockEstimate 2445 526 654 256 = 19681800000 :=
  block_append mom_2445_526_part1 mom_2445_526_part2 rfl rfl rfl
private theorem mom_2445_526_join1 :
    blockEstimate 2445 526 526 384 = 20522446560 :=
  block_append mom_2445_526_part0 mom_2445_526_join0 rfl rfl rfl
private theorem mom_2445_526_join2 :
    blockEstimate 2445 526 1038 256 = 91216905030 :=
  block_append mom_2445_526_part4 mom_2445_526_part5 rfl rfl rfl
private theorem mom_2445_526_join3 :
    blockEstimate 2445 526 910 384 = 117085614822 :=
  block_append mom_2445_526_part3 mom_2445_526_join2 rfl rfl rfl
private theorem mom_2445_526_join4 :
    blockEstimate 2445 526 526 768 = 137608061382 :=
  block_append mom_2445_526_join1 mom_2445_526_join3 rfl rfl rfl
private theorem mom_2445_526_join5 :
    blockEstimate 2445 526 1422 256 = 145301708032 :=
  block_append mom_2445_526_part7 mom_2445_526_part8 rfl rfl rfl
private theorem mom_2445_526_join6 :
    blockEstimate 2445 526 1294 384 = 207194139520 :=
  block_append mom_2445_526_part6 mom_2445_526_join5 rfl rfl rfl
private theorem mom_2445_526_join7 :
    blockEstimate 2445 526 1806 256 = 159600221440 :=
  block_append mom_2445_526_part10 mom_2445_526_part11 rfl rfl rfl
private theorem mom_2445_526_join8 :
    blockEstimate 2445 526 1678 384 = 238588701568 :=
  block_append mom_2445_526_part9 mom_2445_526_join7 rfl rfl rfl
private theorem mom_2445_526_join9 :
    blockEstimate 2445 526 1294 768 = 445782841088 :=
  block_append mom_2445_526_join6 mom_2445_526_join8 rfl rfl rfl
private theorem mom_2445_526_join10 :
    blockEstimate 2445 526 526 1536 = 583390902470 :=
  block_append mom_2445_526_join4 mom_2445_526_join9 rfl rfl rfl
private theorem mom_2445_526_join11 :
    blockEstimate 2445 526 2190 256 = 134111567104 :=
  block_append mom_2445_526_part13 mom_2445_526_part14 rfl rfl rfl
private theorem mom_2445_526_join12 :
    blockEstimate 2445 526 2062 384 = 210302512000 :=
  block_append mom_2445_526_part12 mom_2445_526_join11 rfl rfl rfl
private theorem mom_2445_526_join13 :
    blockEstimate 2445 526 2574 256 = 77175157003 :=
  block_append mom_2445_526_part16 mom_2445_526_part17 rfl rfl rfl
private theorem mom_2445_526_join14 :
    blockEstimate 2445 526 2446 384 = 130952896430 :=
  block_append mom_2445_526_part15 mom_2445_526_join13 rfl rfl rfl
private theorem mom_2445_526_join15 :
    blockEstimate 2445 526 2062 768 = 341255408430 :=
  block_append mom_2445_526_join12 mom_2445_526_join14 rfl rfl rfl
private theorem mom_2445_526_join16 :
    blockEstimate 2445 526 2958 256 = 24417375755 :=
  block_append mom_2445_526_part19 mom_2445_526_part20 rfl rfl rfl
private theorem mom_2445_526_join17 :
    blockEstimate 2445 526 2830 384 = 48522012461 :=
  block_append mom_2445_526_part18 mom_2445_526_join16 rfl rfl rfl
private theorem mom_2445_526_join18 :
    blockEstimate 2445 526 3342 155 = 757932695 :=
  block_append mom_2445_526_part22 mom_2445_526_part23 rfl rfl rfl
private theorem mom_2445_526_join19 :
    blockEstimate 2445 526 3214 283 = 4438480439 :=
  block_append mom_2445_526_part21 mom_2445_526_join18 rfl rfl rfl
private theorem mom_2445_526_join20 :
    blockEstimate 2445 526 2830 667 = 52960492900 :=
  block_append mom_2445_526_join17 mom_2445_526_join19 rfl rfl rfl
private theorem mom_2445_526_join21 :
    blockEstimate 2445 526 2062 1435 = 394215901330 :=
  block_append mom_2445_526_join15 mom_2445_526_join20 rfl rfl rfl
private theorem mom_2445_526_join22 :
    blockEstimate 2445 526 526 2971 = 977606803800 :=
  block_append mom_2445_526_join10 mom_2445_526_join21 rfl rfl rfl
private theorem mom_2445_526 : momentEstimate 2445 526 = 977606803800 := mom_2445_526_join22
private theorem rc_3_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 0 128 = 57014680733231589042691200 := by decide +kernel
private theorem rc_3_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 128 128 = 38240616762771692948208768 := by decide +kernel
private theorem rc_3_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 256 128 = 21714033435852281075031168 := by decide +kernel
private theorem rc_3_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 384 128 = 7596487946188488549072000 := by decide +kernel
private theorem rc_3_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 512 15 = 83115368935692186269904 := by decide +kernel
private theorem rc_3_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 0 256 = 95255297496003281990899968 :=
  phaseBlock_append rc_3_8_2360_0_part0 rc_3_8_2360_0_part1 rfl rfl rfl
private theorem rc_3_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 384 143 = 7679603315124180735341904 :=
  phaseBlock_append rc_3_8_2360_0_part3 rc_3_8_2360_0_part4 rfl rfl rfl
private theorem rc_3_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 256 271 = 29393636750976461810373072 :=
  phaseBlock_append rc_3_8_2360_0_part2 rc_3_8_2360_0_join1 rfl rfl rfl
private theorem rc_3_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 0) 0 527 = 124648934246979743801273040 :=
  phaseBlock_append rc_3_8_2360_0_join0 rc_3_8_2360_0_join2 rfl rfl rfl
private theorem rc_3_8_2360_0 : fastPhase (bank 3 8).shape 179808 2360 19 1 1 1 0 = 124648934246979743801273040 :=
  phase_of_block (n := 527) (by decide +kernel) rc_3_8_2360_0_join3
private theorem rc_3_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 0 128 = 56861582188353368491055808 := by decide +kernel
private theorem rc_3_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 128 128 = 38103802057240845056752320 := by decide +kernel
private theorem rc_3_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 256 128 = 21594871841385923411974848 := by decide +kernel
private theorem rc_3_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 384 128 = 7496329961857638894402240 := by decide +kernel
private theorem rc_3_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 512 15 = 72683801042881815144099 := by decide +kernel
private theorem rc_3_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 0 256 = 94965384245594213547808128 :=
  phaseBlock_append rc_3_8_2360_1_part0 rc_3_8_2360_1_part1 rfl rfl rfl
private theorem rc_3_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 384 143 = 7569013762900520709546339 :=
  phaseBlock_append rc_3_8_2360_1_part3 rc_3_8_2360_1_part4 rfl rfl rfl
private theorem rc_3_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 256 271 = 29163885604286444121521187 :=
  phaseBlock_append rc_3_8_2360_1_part2 rc_3_8_2360_1_join1 rfl rfl rfl
private theorem rc_3_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2360 19 1 1 1 1) 0 527 = 124129269849880657669329315 :=
  phaseBlock_append rc_3_8_2360_1_join0 rc_3_8_2360_1_join2 rfl rfl rfl
private theorem rc_3_8_2360_1 : fastPhase (bank 3 8).shape 179808 2360 19 1 1 1 1 = 124129269849880657669329315 :=
  phase_of_block (n := 527) (by decide +kernel) rc_3_8_2360_1_join3
private theorem rc_3_8_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 0 128 = 57015147220542829949704800 := by decide +kernel
private theorem rc_3_8_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 128 128 = 38240849088193265740819040 := by decide +kernel
private theorem rc_3_8_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 256 128 = 21714121977455948824509024 := by decide +kernel
private theorem rc_3_8_2361_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 384 128 = 7596505254851605230635616 := by decide +kernel
private theorem rc_3_8_2361_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 512 15 = 83115450773746652771820 := by decide +kernel
private theorem rc_3_8_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 0 256 = 95255996308736095690523840 :=
  phaseBlock_append rc_3_8_2361_0_part0 rc_3_8_2361_0_part1 rfl rfl rfl
private theorem rc_3_8_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 384 143 = 7679620705625351883407436 :=
  phaseBlock_append rc_3_8_2361_0_part3 rc_3_8_2361_0_part4 rfl rfl rfl
private theorem rc_3_8_2361_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 256 271 = 29393742683081300707916460 :=
  phaseBlock_append rc_3_8_2361_0_part2 rc_3_8_2361_0_join1 rfl rfl rfl
private theorem rc_3_8_2361_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 0) 0 527 = 124649738991817396398440300 :=
  phaseBlock_append rc_3_8_2361_0_join0 rc_3_8_2361_0_join2 rfl rfl rfl
private theorem rc_3_8_2361_0 : fastPhase (bank 3 8).shape 179808 2361 19 1 1 1 0 = 124649738991817396398440300 :=
  phase_of_block (n := 527) (by decide +kernel) rc_3_8_2361_0_join3
private theorem rc_3_8_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 0 128 = 56862047239622089158860768 := by decide +kernel
private theorem rc_3_8_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 128 128 = 38104033450090632062504928 := by decide +kernel
private theorem rc_3_8_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 256 128 = 21594959855382291568099296 := by decide +kernel
private theorem rc_3_8_2361_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 384 128 = 7496347050713953338519520 := by decide +kernel
private theorem rc_3_8_2361_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 512 15 = 72683872830464488821893 := by decide +kernel
private theorem rc_3_8_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 0 256 = 94966080689712721221365696 :=
  phaseBlock_append rc_3_8_2361_1_part0 rc_3_8_2361_1_part1 rfl rfl rfl
private theorem rc_3_8_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 384 143 = 7569030923544417827341413 :=
  phaseBlock_append rc_3_8_2361_1_part3 rc_3_8_2361_1_part4 rfl rfl rfl
private theorem rc_3_8_2361_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 256 271 = 29163990778926709395440709 :=
  phaseBlock_append rc_3_8_2361_1_part2 rc_3_8_2361_1_join1 rfl rfl rfl
private theorem rc_3_8_2361_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2361 19 1 1 1 1) 0 527 = 124130071468639430616806405 :=
  phaseBlock_append rc_3_8_2361_1_join0 rc_3_8_2361_1_join2 rfl rfl rfl
private theorem rc_3_8_2361_1 : fastPhase (bank 3 8).shape 179808 2361 19 1 1 1 1 = 124130071468639430616806405 :=
  phase_of_block (n := 527) (by decide +kernel) rc_3_8_2361_1_join3
private theorem receipt_3_8 : B1Checked (bank 3 8) 19 1 1 := by
  refine b1_checked_from_values (bank 3 8) 19 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2445_526)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_8_2360_0 rc_3_8_2360_1 rc_3_8_2361_0 rc_3_8_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_3021_650_part0 :
    blockEstimate 3021 650 650 128 = 1046716320 := by decide +kernel
private theorem mom_3021_650_part1 :
    blockEstimate 3021 650 778 128 = 6958804896 := by decide +kernel
private theorem mom_3021_650_part2 :
    blockEstimate 3021 650 906 128 = 17995284384 := by decide +kernel
private theorem mom_3021_650_part3 :
    blockEstimate 3021 650 1034 128 = 33350848416 := by decide +kernel
private theorem mom_3021_650_part4 :
    blockEstimate 3021 650 1162 128 = 52220190624 := by decide +kernel
private theorem mom_3021_650_part5 :
    blockEstimate 3021 650 1290 128 = 73172875863 := by decide +kernel
private theorem mom_3021_650_part6 :
    blockEstimate 3021 650 1418 128 = 92477914368 := by decide +kernel
private theorem mom_3021_650_part7 :
    blockEstimate 3021 650 1546 128 = 109052853504 := by decide +kernel
private theorem mom_3021_650_part8 :
    blockEstimate 3021 650 1674 128 = 122897300736 := by decide +kernel
private theorem mom_3021_650_part9 :
    blockEstimate 3021 650 1802 128 = 134011256064 := by decide +kernel
private theorem mom_3021_650_part10 :
    blockEstimate 3021 650 1930 128 = 142394719488 := by decide +kernel
private theorem mom_3021_650_part11 :
    blockEstimate 3021 650 2058 128 = 148047691008 := by decide +kernel
private theorem mom_3021_650_part12 :
    blockEstimate 3021 650 2186 128 = 150970170624 := by decide +kernel
private theorem mom_3021_650_part13 :
    blockEstimate 3021 650 2314 128 = 151162158336 := by decide +kernel
private theorem mom_3021_650_part14 :
    blockEstimate 3021 650 2442 128 = 148623654144 := by decide +kernel
private theorem mom_3021_650_part15 :
    blockEstimate 3021 650 2570 128 = 143354658048 := by decide +kernel
private theorem mom_3021_650_part16 :
    blockEstimate 3021 650 2698 128 = 135355170048 := by decide +kernel
private theorem mom_3021_650_part17 :
    blockEstimate 3021 650 2826 128 = 124625190144 := by decide +kernel
private theorem mom_3021_650_part18 :
    blockEstimate 3021 650 2954 128 = 111199382441 := by decide +kernel
private theorem mom_3021_650_part19 :
    blockEstimate 3021 650 3082 128 = 96033242862 := by decide +kernel
private theorem mom_3021_650_part20 :
    blockEstimate 3021 650 3210 128 = 80468597487 := by decide +kernel
private theorem mom_3021_650_part21 :
    blockEstimate 3021 650 3338 128 = 65091119332 := by decide +kernel
private theorem mom_3021_650_part22 :
    blockEstimate 3021 650 3466 128 = 50406598667 := by decide +kernel
private theorem mom_3021_650_part23 :
    blockEstimate 3021 650 3594 128 = 36866200547 := by decide +kernel
private theorem mom_3021_650_part24 :
    blockEstimate 3021 650 3722 128 = 24837588544 := by decide +kernel
private theorem mom_3021_650_part25 :
    blockEstimate 3021 650 3850 128 = 14874400320 := by decide +kernel
private theorem mom_3021_650_part26 :
    blockEstimate 3021 650 3978 128 = 7277258304 := by decide +kernel
private theorem mom_3021_650_part27 :
    blockEstimate 3021 650 4106 128 = 2297820736 := by decide +kernel
private theorem mom_3021_650_part28 :
    blockEstimate 3021 650 4234 87 = 172145996 := by decide +kernel
private theorem mom_3021_650_join0 :
    blockEstimate 3021 650 778 256 = 24954089280 :=
  block_append mom_3021_650_part1 mom_3021_650_part2 rfl rfl rfl
private theorem mom_3021_650_join1 :
    blockEstimate 3021 650 650 384 = 26000805600 :=
  block_append mom_3021_650_part0 mom_3021_650_join0 rfl rfl rfl
private theorem mom_3021_650_join2 :
    blockEstimate 3021 650 1034 256 = 85571039040 :=
  block_append mom_3021_650_part3 mom_3021_650_part4 rfl rfl rfl
private theorem mom_3021_650_join3 :
    blockEstimate 3021 650 1290 256 = 165650790231 :=
  block_append mom_3021_650_part5 mom_3021_650_part6 rfl rfl rfl
private theorem mom_3021_650_join4 :
    blockEstimate 3021 650 1034 512 = 251221829271 :=
  block_append mom_3021_650_join2 mom_3021_650_join3 rfl rfl rfl
private theorem mom_3021_650_join5 :
    blockEstimate 3021 650 650 896 = 277222634871 :=
  block_append mom_3021_650_join1 mom_3021_650_join4 rfl rfl rfl
private theorem mom_3021_650_join6 :
    blockEstimate 3021 650 1674 256 = 256908556800 :=
  block_append mom_3021_650_part8 mom_3021_650_part9 rfl rfl rfl
private theorem mom_3021_650_join7 :
    blockEstimate 3021 650 1546 384 = 365961410304 :=
  block_append mom_3021_650_part7 mom_3021_650_join6 rfl rfl rfl
private theorem mom_3021_650_join8 :
    blockEstimate 3021 650 1930 256 = 290442410496 :=
  block_append mom_3021_650_part10 mom_3021_650_part11 rfl rfl rfl
private theorem mom_3021_650_join9 :
    blockEstimate 3021 650 2186 256 = 302132328960 :=
  block_append mom_3021_650_part12 mom_3021_650_part13 rfl rfl rfl
private theorem mom_3021_650_join10 :
    blockEstimate 3021 650 1930 512 = 592574739456 :=
  block_append mom_3021_650_join8 mom_3021_650_join9 rfl rfl rfl
private theorem mom_3021_650_join11 :
    blockEstimate 3021 650 1546 896 = 958536149760 :=
  block_append mom_3021_650_join7 mom_3021_650_join10 rfl rfl rfl
private theorem mom_3021_650_join12 :
    blockEstimate 3021 650 650 1792 = 1235758784631 :=
  block_append mom_3021_650_join5 mom_3021_650_join11 rfl rfl rfl
private theorem mom_3021_650_join13 :
    blockEstimate 3021 650 2570 256 = 278709828096 :=
  block_append mom_3021_650_part15 mom_3021_650_part16 rfl rfl rfl
private theorem mom_3021_650_join14 :
    blockEstimate 3021 650 2442 384 = 427333482240 :=
  block_append mom_3021_650_part14 mom_3021_650_join13 rfl rfl rfl
private theorem mom_3021_650_join15 :
    blockEstimate 3021 650 2826 256 = 235824572585 :=
  block_append mom_3021_650_part17 mom_3021_650_part18 rfl rfl rfl
private theorem mom_3021_650_join16 :
    blockEstimate 3021 650 3082 256 = 176501840349 :=
  block_append mom_3021_650_part19 mom_3021_650_part20 rfl rfl rfl
private theorem mom_3021_650_join17 :
    blockEstimate 3021 650 2826 512 = 412326412934 :=
  block_append mom_3021_650_join15 mom_3021_650_join16 rfl rfl rfl
private theorem mom_3021_650_join18 :
    blockEstimate 3021 650 2442 896 = 839659895174 :=
  block_append mom_3021_650_join14 mom_3021_650_join17 rfl rfl rfl
private theorem mom_3021_650_join19 :
    blockEstimate 3021 650 3338 256 = 115497717999 :=
  block_append mom_3021_650_part21 mom_3021_650_part22 rfl rfl rfl
private theorem mom_3021_650_join20 :
    blockEstimate 3021 650 3594 256 = 61703789091 :=
  block_append mom_3021_650_part23 mom_3021_650_part24 rfl rfl rfl
private theorem mom_3021_650_join21 :
    blockEstimate 3021 650 3338 512 = 177201507090 :=
  block_append mom_3021_650_join19 mom_3021_650_join20 rfl rfl rfl
private theorem mom_3021_650_join22 :
    blockEstimate 3021 650 3850 256 = 22151658624 :=
  block_append mom_3021_650_part25 mom_3021_650_part26 rfl rfl rfl
private theorem mom_3021_650_join23 :
    blockEstimate 3021 650 4106 215 = 2469966732 :=
  block_append mom_3021_650_part27 mom_3021_650_part28 rfl rfl rfl
private theorem mom_3021_650_join24 :
    blockEstimate 3021 650 3850 471 = 24621625356 :=
  block_append mom_3021_650_join22 mom_3021_650_join23 rfl rfl rfl
private theorem mom_3021_650_join25 :
    blockEstimate 3021 650 3338 983 = 201823132446 :=
  block_append mom_3021_650_join21 mom_3021_650_join24 rfl rfl rfl
private theorem mom_3021_650_join26 :
    blockEstimate 3021 650 2442 1879 = 1041483027620 :=
  block_append mom_3021_650_join18 mom_3021_650_join25 rfl rfl rfl
private theorem mom_3021_650_join27 :
    blockEstimate 3021 650 650 3671 = 2277241812251 :=
  block_append mom_3021_650_join12 mom_3021_650_join26 rfl rfl rfl
private theorem mom_3021_650 : momentEstimate 3021 650 = 2277241812251 := mom_3021_650_join27
private theorem rc_3_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 0 128 = 201350338568691730944625152 := by decide +kernel
private theorem rc_3_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 128 128 = 148256473733686861302778368 := by decide +kernel
private theorem rc_3_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 256 128 = 100076513278334872900176384 := by decide +kernel
private theorem rc_3_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 384 128 = 57108096077004921119721984 := by decide +kernel
private theorem rc_3_9_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 512 128 = 19645776062625189373610496 := by decide +kernel
private theorem rc_3_9_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 640 11 = 126216389893096070877408 := by decide +kernel
private theorem rc_3_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 128 256 = 248332987012021734202954752 :=
  phaseBlock_append rc_3_9_2360_0_part1 rc_3_9_2360_0_part2 rfl rfl rfl
private theorem rc_3_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 0 384 = 449683325580713465147579904 :=
  phaseBlock_append rc_3_9_2360_0_part0 rc_3_9_2360_0_join0 rfl rfl rfl
private theorem rc_3_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 512 139 = 19771992452518285444487904 :=
  phaseBlock_append rc_3_9_2360_0_part4 rc_3_9_2360_0_part5 rfl rfl rfl
private theorem rc_3_9_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 384 267 = 76880088529523206564209888 :=
  phaseBlock_append rc_3_9_2360_0_part3 rc_3_9_2360_0_join2 rfl rfl rfl
private theorem rc_3_9_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 0) 0 651 = 526563414110236671711789792 :=
  phaseBlock_append rc_3_9_2360_0_join1 rc_3_9_2360_0_join3 rfl rfl rfl
private theorem rc_3_9_2360_0 : fastPhase (bank 3 9).shape 179808 2360 28 1 1 1 0 = 526563414110236671711789792 :=
  phase_of_block (n := 651) (by decide +kernel) rc_3_9_2360_0_join4
private theorem rc_3_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 0 128 = 200922607675765574567671104 := by decide +kernel
private theorem rc_3_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 128 128 = 147864490929767776266057024 := by decide +kernel
private theorem rc_3_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 256 128 = 99722793834931270265845056 := by decide +kernel
private theorem rc_3_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 384 128 = 56795129892430889073636672 := by decide +kernel
private theorem rc_3_9_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 512 128 = 19376027738774923426936128 := by decide +kernel
private theorem rc_3_9_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 640 11 = 105130828729955062459656 := by decide +kernel
private theorem rc_3_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 128 256 = 247587284764699046531902080 :=
  phaseBlock_append rc_3_9_2360_1_part1 rc_3_9_2360_1_part2 rfl rfl rfl
private theorem rc_3_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 0 384 = 448509892440464621099573184 :=
  phaseBlock_append rc_3_9_2360_1_part0 rc_3_9_2360_1_join0 rfl rfl rfl
private theorem rc_3_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 512 139 = 19481158567504878489395784 :=
  phaseBlock_append rc_3_9_2360_1_part4 rc_3_9_2360_1_part5 rfl rfl rfl
private theorem rc_3_9_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 384 267 = 76276288459935767563032456 :=
  phaseBlock_append rc_3_9_2360_1_part3 rc_3_9_2360_1_join2 rfl rfl rfl
private theorem rc_3_9_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2360 28 1 1 1 1) 0 651 = 524786180900400388662605640 :=
  phaseBlock_append rc_3_9_2360_1_join1 rc_3_9_2360_1_join3 rfl rfl rfl
private theorem rc_3_9_2360_1 : fastPhase (bank 3 9).shape 179808 2360 28 1 1 1 1 = 524786180900400388662605640 :=
  phase_of_block (n := 651) (by decide +kernel) rc_3_9_2360_1_join4
private theorem rc_3_9_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 0 128 = 201352011163320576512605056 := by decide +kernel
private theorem rc_3_9_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 128 128 = 148257449918565576755747712 := by decide +kernel
private theorem rc_3_9_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 256 128 = 100077006338742327358749568 := by decide +kernel
private theorem rc_3_9_2361_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 384 128 = 57108286951488121290447744 := by decide +kernel
private theorem rc_3_9_2361_0_part4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 512 128 = 19645813641033382410271616 := by decide +kernel
private theorem rc_3_9_2361_0_part5 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 640 11 = 126216500794207988460120 := by decide +kernel
private theorem rc_3_9_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 128 256 = 248334456257307904114497280 :=
  phaseBlock_append rc_3_9_2361_0_part1 rc_3_9_2361_0_part2 rfl rfl rfl
private theorem rc_3_9_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 0 384 = 449686467420628480627102336 :=
  phaseBlock_append rc_3_9_2361_0_part0 rc_3_9_2361_0_join0 rfl rfl rfl
private theorem rc_3_9_2361_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 512 139 = 19772030141827590398731736 :=
  phaseBlock_append rc_3_9_2361_0_part4 rc_3_9_2361_0_part5 rfl rfl rfl
private theorem rc_3_9_2361_0_join3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 384 267 = 76880317093315711689179480 :=
  phaseBlock_append rc_3_9_2361_0_part3 rc_3_9_2361_0_join2 rfl rfl rfl
private theorem rc_3_9_2361_0_join4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 0) 0 651 = 526566784513944192316281816 :=
  phaseBlock_append rc_3_9_2361_0_join1 rc_3_9_2361_0_join3 rfl rfl rfl
private theorem rc_3_9_2361_0 : fastPhase (bank 3 9).shape 179808 2361 28 1 1 1 0 = 526566784513944192316281816 :=
  phase_of_block (n := 651) (by decide +kernel) rc_3_9_2361_0_join4
private theorem rc_3_9_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 0 128 = 200924276181055598834051328 := by decide +kernel
private theorem rc_3_9_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 128 128 = 147865464190505144256579840 := by decide +kernel
private theorem rc_3_9_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 256 128 = 99723284957946891647527168 := by decide +kernel
private theorem rc_3_9_2361_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 384 128 = 56795319639632115811354880 := by decide +kernel
private theorem rc_3_9_2361_1_part4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 512 128 = 19376064825174017647634688 := by decide +kernel
private theorem rc_3_9_2361_1_part5 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 640 11 = 105130921364295216757686 := by decide +kernel
private theorem rc_3_9_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 128 256 = 247588749148452035904107008 :=
  phaseBlock_append rc_3_9_2361_1_part1 rc_3_9_2361_1_part2 rfl rfl rfl
private theorem rc_3_9_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 0 384 = 448513025329507634738158336 :=
  phaseBlock_append rc_3_9_2361_1_part0 rc_3_9_2361_1_join0 rfl rfl rfl
private theorem rc_3_9_2361_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 512 139 = 19481195746538312864392374 :=
  phaseBlock_append rc_3_9_2361_1_part4 rc_3_9_2361_1_part5 rfl rfl rfl
private theorem rc_3_9_2361_1_join3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 384 267 = 76276515386170428675747254 :=
  phaseBlock_append rc_3_9_2361_1_part3 rc_3_9_2361_1_join2 rfl rfl rfl
private theorem rc_3_9_2361_1_join4 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2361 28 1 1 1 1) 0 651 = 524789540715678063413905590 :=
  phaseBlock_append rc_3_9_2361_1_join1 rc_3_9_2361_1_join3 rfl rfl rfl
private theorem rc_3_9_2361_1 : fastPhase (bank 3 9).shape 179808 2361 28 1 1 1 1 = 524789540715678063413905590 :=
  phase_of_block (n := 651) (by decide +kernel) rc_3_9_2361_1_join4
private theorem receipt_3_9 : B1Checked (bank 3 9) 28 1 1 := by
  refine b1_checked_from_values (bank 3 9) 28 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_3021_650)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_9_2360_0 rc_3_9_2360_1 rc_3_9_2361_0 rc_3_9_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_3764_809_part0 :
    blockEstimate 3764 809 809 128 = 1312532000 := by decide +kernel
private theorem mom_3764_809_part1 :
    blockEstimate 3764 809 937 128 = 8794977824 := by decide +kernel
private theorem mom_3764_809_part2 :
    blockEstimate 3764 809 1065 128 = 22959998496 := by decide +kernel
private theorem mom_3764_809_part3 :
    blockEstimate 3764 809 1193 128 = 43002287648 := by decide +kernel
private theorem mom_3764_809_part4 :
    blockEstimate 3764 809 1321 128 = 68116538912 := by decide +kernel
private theorem mom_3764_809_part5 :
    blockEstimate 3764 809 1449 128 = 97497445920 := by decide +kernel
private theorem mom_3764_809_part6 :
    blockEstimate 3764 809 1577 128 = 130022537830 := by decide +kernel
private theorem mom_3764_809_part7 :
    blockEstimate 3764 809 1705 128 = 161526882240 := by decide +kernel
private theorem mom_3764_809_part8 :
    blockEstimate 3764 809 1833 128 = 189668122560 := by decide +kernel
private theorem mom_3764_809_part9 :
    blockEstimate 3764 809 1961 128 = 214411976640 := by decide +kernel
private theorem mom_3764_809_part10 :
    blockEstimate 3764 809 2089 128 = 235758444480 := by decide +kernel
private theorem mom_3764_809_part11 :
    blockEstimate 3764 809 2217 128 = 253707526080 := by decide +kernel
private theorem mom_3764_809_part12 :
    blockEstimate 3764 809 2345 128 = 268259221440 := by decide +kernel
private theorem mom_3764_809_part13 :
    blockEstimate 3764 809 2473 128 = 279413530560 := by decide +kernel
private theorem mom_3764_809_part14 :
    blockEstimate 3764 809 2601 128 = 287170453440 := by decide +kernel
private theorem mom_3764_809_part15 :
    blockEstimate 3764 809 2729 128 = 291529990080 := by decide +kernel
private theorem mom_3764_809_part16 :
    blockEstimate 3764 809 2857 128 = 292492140480 := by decide +kernel
private theorem mom_3764_809_part17 :
    blockEstimate 3764 809 2985 128 = 290056904640 := by decide +kernel
private theorem mom_3764_809_part18 :
    blockEstimate 3764 809 3113 128 = 284224282560 := by decide +kernel
private theorem mom_3764_809_part19 :
    blockEstimate 3764 809 3241 128 = 274994274240 := by decide +kernel
private theorem mom_3764_809_part20 :
    blockEstimate 3764 809 3369 128 = 262366879680 := by decide +kernel
private theorem mom_3764_809_part21 :
    blockEstimate 3764 809 3497 128 = 246342098880 := by decide +kernel
private theorem mom_3764_809_part22 :
    blockEstimate 3764 809 3625 128 = 226919931840 := by decide +kernel
private theorem mom_3764_809_part23 :
    blockEstimate 3764 809 3753 128 = 204408071777 := by decide +kernel
private theorem mom_3764_809_part24 :
    blockEstimate 3764 809 3881 128 = 180554774428 := by decide +kernel
private theorem mom_3764_809_part25 :
    blockEstimate 3764 809 4009 128 = 156374073954 := by decide +kernel
private theorem mom_3764_809_part26 :
    blockEstimate 3764 809 4137 128 = 132409131224 := by decide +kernel
private theorem mom_3764_809_part27 :
    blockEstimate 3764 809 4265 128 = 109171092819 := by decide +kernel
private theorem mom_3764_809_part28 :
    blockEstimate 3764 809 4393 128 = 87139289335 := by decide +kernel
private theorem mom_3764_809_part29 :
    blockEstimate 3764 809 4521 128 = 66711535082 := by decide +kernel
private theorem mom_3764_809_part30 :
    blockEstimate 3764 809 4649 128 = 48250397616 := by decide +kernel
private theorem mom_3764_809_part31 :
    blockEstimate 3764 809 4777 128 = 32388327344 := by decide +kernel
private theorem mom_3764_809_part32 :
    blockEstimate 3764 809 4905 128 = 19407940528 := by decide +kernel
private theorem mom_3764_809_part33 :
    blockEstimate 3764 809 5033 128 = 9560895408 := by decide +kernel
private theorem mom_3764_809_part34 :
    blockEstimate 3764 809 5161 128 = 3098850224 := by decide +kernel
private theorem mom_3764_809_part35 :
    blockEstimate 3764 809 5289 93 = 261635940 := by decide +kernel
private theorem mom_3764_809_join0 :
    blockEstimate 3764 809 809 256 = 10107509824 :=
  block_append mom_3764_809_part0 mom_3764_809_part1 rfl rfl rfl
private theorem mom_3764_809_join1 :
    blockEstimate 3764 809 1065 256 = 65962286144 :=
  block_append mom_3764_809_part2 mom_3764_809_part3 rfl rfl rfl
private theorem mom_3764_809_join2 :
    blockEstimate 3764 809 809 512 = 76069795968 :=
  block_append mom_3764_809_join0 mom_3764_809_join1 rfl rfl rfl
private theorem mom_3764_809_join3 :
    blockEstimate 3764 809 1321 256 = 165613984832 :=
  block_append mom_3764_809_part4 mom_3764_809_part5 rfl rfl rfl
private theorem mom_3764_809_join4 :
    blockEstimate 3764 809 1705 256 = 351195004800 :=
  block_append mom_3764_809_part7 mom_3764_809_part8 rfl rfl rfl
private theorem mom_3764_809_join5 :
    blockEstimate 3764 809 1577 384 = 481217542630 :=
  block_append mom_3764_809_part6 mom_3764_809_join4 rfl rfl rfl
private theorem mom_3764_809_join6 :
    blockEstimate 3764 809 1321 640 = 646831527462 :=
  block_append mom_3764_809_join3 mom_3764_809_join5 rfl rfl rfl
private theorem mom_3764_809_join7 :
    blockEstimate 3764 809 809 1152 = 722901323430 :=
  block_append mom_3764_809_join2 mom_3764_809_join6 rfl rfl rfl
private theorem mom_3764_809_join8 :
    blockEstimate 3764 809 1961 256 = 450170421120 :=
  block_append mom_3764_809_part9 mom_3764_809_part10 rfl rfl rfl
private theorem mom_3764_809_join9 :
    blockEstimate 3764 809 2217 256 = 521966747520 :=
  block_append mom_3764_809_part11 mom_3764_809_part12 rfl rfl rfl
private theorem mom_3764_809_join10 :
    blockEstimate 3764 809 1961 512 = 972137168640 :=
  block_append mom_3764_809_join8 mom_3764_809_join9 rfl rfl rfl
private theorem mom_3764_809_join11 :
    blockEstimate 3764 809 2473 256 = 566583984000 :=
  block_append mom_3764_809_part13 mom_3764_809_part14 rfl rfl rfl
private theorem mom_3764_809_join12 :
    blockEstimate 3764 809 2857 256 = 582549045120 :=
  block_append mom_3764_809_part16 mom_3764_809_part17 rfl rfl rfl
private theorem mom_3764_809_join13 :
    blockEstimate 3764 809 2729 384 = 874079035200 :=
  block_append mom_3764_809_part15 mom_3764_809_join12 rfl rfl rfl
private theorem mom_3764_809_join14 :
    blockEstimate 3764 809 2473 640 = 1440663019200 :=
  block_append mom_3764_809_join11 mom_3764_809_join13 rfl rfl rfl
private theorem mom_3764_809_join15 :
    blockEstimate 3764 809 1961 1152 = 2412800187840 :=
  block_append mom_3764_809_join10 mom_3764_809_join14 rfl rfl rfl
private theorem mom_3764_809_join16 :
    blockEstimate 3764 809 809 2304 = 3135701511270 :=
  block_append mom_3764_809_join7 mom_3764_809_join15 rfl rfl rfl
private theorem mom_3764_809_join17 :
    blockEstimate 3764 809 3113 256 = 559218556800 :=
  block_append mom_3764_809_part18 mom_3764_809_part19 rfl rfl rfl
private theorem mom_3764_809_join18 :
    blockEstimate 3764 809 3369 256 = 508708978560 :=
  block_append mom_3764_809_part20 mom_3764_809_part21 rfl rfl rfl
private theorem mom_3764_809_join19 :
    blockEstimate 3764 809 3113 512 = 1067927535360 :=
  block_append mom_3764_809_join17 mom_3764_809_join18 rfl rfl rfl
private theorem mom_3764_809_join20 :
    blockEstimate 3764 809 3625 256 = 431328003617 :=
  block_append mom_3764_809_part22 mom_3764_809_part23 rfl rfl rfl
private theorem mom_3764_809_join21 :
    blockEstimate 3764 809 4009 256 = 288783205178 :=
  block_append mom_3764_809_part25 mom_3764_809_part26 rfl rfl rfl
private theorem mom_3764_809_join22 :
    blockEstimate 3764 809 3881 384 = 469337979606 :=
  block_append mom_3764_809_part24 mom_3764_809_join21 rfl rfl rfl
private theorem mom_3764_809_join23 :
    blockEstimate 3764 809 3625 640 = 900665983223 :=
  block_append mom_3764_809_join20 mom_3764_809_join22 rfl rfl rfl
private theorem mom_3764_809_join24 :
    blockEstimate 3764 809 3113 1152 = 1968593518583 :=
  block_append mom_3764_809_join19 mom_3764_809_join23 rfl rfl rfl
private theorem mom_3764_809_join25 :
    blockEstimate 3764 809 4265 256 = 196310382154 :=
  block_append mom_3764_809_part27 mom_3764_809_part28 rfl rfl rfl
private theorem mom_3764_809_join26 :
    blockEstimate 3764 809 4521 256 = 114961932698 :=
  block_append mom_3764_809_part29 mom_3764_809_part30 rfl rfl rfl
private theorem mom_3764_809_join27 :
    blockEstimate 3764 809 4265 512 = 311272314852 :=
  block_append mom_3764_809_join25 mom_3764_809_join26 rfl rfl rfl
private theorem mom_3764_809_join28 :
    blockEstimate 3764 809 4777 256 = 51796267872 :=
  block_append mom_3764_809_part31 mom_3764_809_part32 rfl rfl rfl
private theorem mom_3764_809_join29 :
    blockEstimate 3764 809 5161 221 = 3360486164 :=
  block_append mom_3764_809_part34 mom_3764_809_part35 rfl rfl rfl
private theorem mom_3764_809_join30 :
    blockEstimate 3764 809 5033 349 = 12921381572 :=
  block_append mom_3764_809_part33 mom_3764_809_join29 rfl rfl rfl
private theorem mom_3764_809_join31 :
    blockEstimate 3764 809 4777 605 = 64717649444 :=
  block_append mom_3764_809_join28 mom_3764_809_join30 rfl rfl rfl
private theorem mom_3764_809_join32 :
    blockEstimate 3764 809 4265 1117 = 375989964296 :=
  block_append mom_3764_809_join27 mom_3764_809_join31 rfl rfl rfl
private theorem mom_3764_809_join33 :
    blockEstimate 3764 809 3113 2269 = 2344583482879 :=
  block_append mom_3764_809_join24 mom_3764_809_join32 rfl rfl rfl
private theorem mom_3764_809_join34 :
    blockEstimate 3764 809 809 4573 = 5480284994149 :=
  block_append mom_3764_809_join16 mom_3764_809_join33 rfl rfl rfl
private theorem mom_3764_809 : momentEstimate 3764 809 = 5480284994149 := mom_3764_809_join34
private theorem rc_3_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 0 128 = 748254716400117064366699104 := by decide +kernel
private theorem rc_3_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 128 128 = 591215970951037318494208608 := by decide +kernel
private theorem rc_3_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 256 128 = 445393660721462925227414112 := by decide +kernel
private theorem rc_3_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 384 128 = 311354020266400025539109472 := by decide +kernel
private theorem rc_3_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 512 128 = 189659043006056834122412640 := by decide +kernel
private theorem rc_3_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 640 128 = 80866490679312673613480544 := by decide +kernel
private theorem rc_3_10_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 768 42 = 5088616088207599740436539 := by decide +kernel
private theorem rc_3_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 128 256 = 1036609631672500243721622720 :=
  phaseBlock_append rc_3_10_2360_0_part1 rc_3_10_2360_0_part2 rfl rfl rfl
private theorem rc_3_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 0 384 = 1784864348072617308088321824 :=
  phaseBlock_append rc_3_10_2360_0_part0 rc_3_10_2360_0_join0 rfl rfl rfl
private theorem rc_3_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 384 256 = 501013063272456859661522112 :=
  phaseBlock_append rc_3_10_2360_0_part3 rc_3_10_2360_0_part4 rfl rfl rfl
private theorem rc_3_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 640 170 = 85955106767520273353917083 :=
  phaseBlock_append rc_3_10_2360_0_part5 rc_3_10_2360_0_part6 rfl rfl rfl
private theorem rc_3_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 384 426 = 586968170039977133015439195 :=
  phaseBlock_append rc_3_10_2360_0_join2 rc_3_10_2360_0_join3 rfl rfl rfl
private theorem rc_3_10_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 0) 0 810 = 2371832518112594441103761019 :=
  phaseBlock_append rc_3_10_2360_0_join1 rc_3_10_2360_0_join4 rfl rfl rfl
private theorem rc_3_10_2360_0 : fastPhase (bank 3 10).shape 179808 2360 40 1 1 1 0 = 2371832518112594441103761019 :=
  phase_of_block (n := 810) (by decide +kernel) rc_3_10_2360_0_join5
private theorem rc_3_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 0 128 = 747001805163360491846926432 := by decide +kernel
private theorem rc_3_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 128 128 = 590044945967084597817757792 := by decide +kernel
private theorem rc_3_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 256 128 = 444309295403155666405761120 := by decide +kernel
private theorem rc_3_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 384 128 = 310361053164172497705791584 := by decide +kernel
private theorem rc_3_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 512 128 = 188762177884710395734638688 := by decide +kernel
private theorem rc_3_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 640 128 = 80070396594790202653741152 := by decide +kernel
private theorem rc_3_10_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 768 42 = 4850139917667962091598571 := by decide +kernel
private theorem rc_3_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 128 256 = 1034354241370240264223518912 :=
  phaseBlock_append rc_3_10_2360_1_part1 rc_3_10_2360_1_part2 rfl rfl rfl
private theorem rc_3_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 0 384 = 1781356046533600756070445344 :=
  phaseBlock_append rc_3_10_2360_1_part0 rc_3_10_2360_1_join0 rfl rfl rfl
private theorem rc_3_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 384 256 = 499123231048882893440430272 :=
  phaseBlock_append rc_3_10_2360_1_part3 rc_3_10_2360_1_part4 rfl rfl rfl
private theorem rc_3_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 640 170 = 84920536512458164745339723 :=
  phaseBlock_append rc_3_10_2360_1_part5 rc_3_10_2360_1_part6 rfl rfl rfl
private theorem rc_3_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 384 426 = 584043767561341058185769995 :=
  phaseBlock_append rc_3_10_2360_1_join2 rc_3_10_2360_1_join3 rfl rfl rfl
private theorem rc_3_10_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2360 40 1 1 1 1) 0 810 = 2365399814094941814256215339 :=
  phaseBlock_append rc_3_10_2360_1_join1 rc_3_10_2360_1_join4 rfl rfl rfl
private theorem rc_3_10_2360_1 : fastPhase (bank 3 10).shape 179808 2360 40 1 1 1 1 = 2365399814094941814256215339 :=
  phase_of_block (n := 810) (by decide +kernel) rc_3_10_2360_1_join5
private theorem rc_3_10_2361_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 0 128 = 748261016523098792903249248 := by decide +kernel
private theorem rc_3_10_2361_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 128 128 = 591220124409923143634558304 := by decide +kernel
private theorem rc_3_10_2361_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 256 128 = 445396186645791034246835552 := by decide +kernel
private theorem rc_3_10_2361_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 384 128 = 311355377167799580680502624 := by decide +kernel
private theorem rc_3_10_2361_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 512 128 = 189659629186553677155224928 := by decide +kernel
private theorem rc_3_10_2361_0_part5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 640 128 = 80866644638755421090405728 := by decide +kernel
private theorem rc_3_10_2361_0_part6 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 768 42 = 5088621301859289380887715 := by decide +kernel
private theorem rc_3_10_2361_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 128 256 = 1036616311055714177881393856 :=
  phaseBlock_append rc_3_10_2361_0_part1 rc_3_10_2361_0_part2 rfl rfl rfl
private theorem rc_3_10_2361_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 0 384 = 1784877327578812970784643104 :=
  phaseBlock_append rc_3_10_2361_0_part0 rc_3_10_2361_0_join0 rfl rfl rfl
private theorem rc_3_10_2361_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 384 256 = 501015006354353257835727552 :=
  phaseBlock_append rc_3_10_2361_0_part3 rc_3_10_2361_0_part4 rfl rfl rfl
private theorem rc_3_10_2361_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 640 170 = 85955265940614710471293443 :=
  phaseBlock_append rc_3_10_2361_0_part5 rc_3_10_2361_0_part6 rfl rfl rfl
private theorem rc_3_10_2361_0_join4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 384 426 = 586970272294967968307020995 :=
  phaseBlock_append rc_3_10_2361_0_join2 rc_3_10_2361_0_join3 rfl rfl rfl
private theorem rc_3_10_2361_0_join5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 0) 0 810 = 2371847599873780939091664099 :=
  phaseBlock_append rc_3_10_2361_0_join1 rc_3_10_2361_0_join4 rfl rfl rfl
private theorem rc_3_10_2361_0 : fastPhase (bank 3 10).shape 179808 2361 40 1 1 1 0 = 2371847599873780939091664099 :=
  phase_of_block (n := 810) (by decide +kernel) rc_3_10_2361_0_join5
private theorem rc_3_10_2361_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 0 128 = 747008093109580377353298208 := by decide +kernel
private theorem rc_3_10_2361_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 128 128 = 590049090042323184811102496 := by decide +kernel
private theorem rc_3_10_2361_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 256 128 = 444311814402993872878731552 := by decide +kernel
private theorem rc_3_10_2361_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 384 128 = 310362405268758606177841440 := by decide +kernel
private theorem rc_3_10_2361_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 512 128 = 188762761067060122813849888 := by decide +kernel
private theorem rc_3_10_2361_1_part5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 640 128 = 80070549028207159296430368 := by decide +kernel
private theorem rc_3_10_2361_1_part6 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 768 42 = 4850144896489749984443309 := by decide +kernel
private theorem rc_3_10_2361_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 128 256 = 1034360904445317057689834048 :=
  phaseBlock_append rc_3_10_2361_1_part1 rc_3_10_2361_1_part2 rfl rfl rfl
private theorem rc_3_10_2361_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 0 384 = 1781368997554897435043132256 :=
  phaseBlock_append rc_3_10_2361_1_part0 rc_3_10_2361_1_join0 rfl rfl rfl
private theorem rc_3_10_2361_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 384 256 = 499125166335818728991691328 :=
  phaseBlock_append rc_3_10_2361_1_part3 rc_3_10_2361_1_part4 rfl rfl rfl
private theorem rc_3_10_2361_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 640 170 = 84920693924696909280873677 :=
  phaseBlock_append rc_3_10_2361_1_part5 rc_3_10_2361_1_part6 rfl rfl rfl
private theorem rc_3_10_2361_1_join4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 384 426 = 584045860260515638272565005 :=
  phaseBlock_append rc_3_10_2361_1_join2 rc_3_10_2361_1_join3 rfl rfl rfl
private theorem rc_3_10_2361_1_join5 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2361 40 1 1 1 1) 0 810 = 2365414857815413073315697261 :=
  phaseBlock_append rc_3_10_2361_1_join1 rc_3_10_2361_1_join4 rfl rfl rfl
private theorem rc_3_10_2361_1 : fastPhase (bank 3 10).shape 179808 2361 40 1 1 1 1 = 2365414857815413073315697261 :=
  phase_of_block (n := 810) (by decide +kernel) rc_3_10_2361_1_join5
private theorem receipt_3_10 : B1Checked (bank 3 10) 40 1 1 := by
  refine b1_checked_from_values (bank 3 10) 40 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_3764_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_3_10_2360_0 rc_3_10_2360_1 rc_3_10_2361_0 rc_3_10_2361_1 (by decide +kernel) (by decide +kernel)

theorem rect3_checked (i : Fin 11) :
    B1Checked (bank 3 i) (reserve i) (excess 3) (seed 3) := by
  fin_cases i
  · exact receipt_3_0
  · exact receipt_3_1
  · exact receipt_3_2
  · exact receipt_3_3
  · exact receipt_3_4
  · exact receipt_3_5
  · exact receipt_3_6
  · exact receipt_3_7
  · exact receipt_3_8
  · exact receipt_3_9
  · exact receipt_3_10

#print axioms rect3_checked
end Lower6962.B1.RescueSource
