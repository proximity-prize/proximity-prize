import ProximityPrize.SubmissionLower.R6962B1RescueSchedule

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Lower6962.B1.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase phaseBlock phaseBlock_append phase_of_block)

private theorem mom_1254_266_part0 :
    blockEstimate 1254 266 266 128 = 414554400 := by decide +kernel
private theorem mom_1254_266_part1 :
    blockEstimate 1254 266 394 128 = 2592024864 := by decide +kernel
private theorem mom_1254_266_part2 :
    blockEstimate 1254 266 522 128 = 5941781556 := by decide +kernel
private theorem mom_1254_266_part3 :
    blockEstimate 1254 266 650 128 = 8649450048 := by decide +kernel
private theorem mom_1254_266_part4 :
    blockEstimate 1254 266 778 128 = 10237403712 := by decide +kernel
private theorem mom_1254_266_part5 :
    blockEstimate 1254 266 906 128 = 10705478208 := by decide +kernel
private theorem mom_1254_266_part6 :
    blockEstimate 1254 266 1034 128 = 10053673536 := by decide +kernel
private theorem mom_1254_266_part7 :
    blockEstimate 1254 266 1162 128 = 8285073672 := by decide +kernel
private theorem mom_1254_266_part8 :
    blockEstimate 1254 266 1290 128 = 5720788929 := by decide +kernel
private theorem mom_1254_266_part9 :
    blockEstimate 1254 266 1418 128 = 3185602299 := by decide +kernel
private theorem mom_1254_266_part10 :
    blockEstimate 1254 266 1546 128 = 1194106368 := by decide +kernel
private theorem mom_1254_266_part11 :
    blockEstimate 1254 266 1674 112 = 146457472 := by decide +kernel
private theorem mom_1254_266_join0 :
    blockEstimate 1254 266 394 256 = 8533806420 :=
  block_append mom_1254_266_part1 mom_1254_266_part2 rfl rfl rfl
private theorem mom_1254_266_join1 :
    blockEstimate 1254 266 266 384 = 8948360820 :=
  block_append mom_1254_266_part0 mom_1254_266_join0 rfl rfl rfl
private theorem mom_1254_266_join2 :
    blockEstimate 1254 266 778 256 = 20942881920 :=
  block_append mom_1254_266_part4 mom_1254_266_part5 rfl rfl rfl
private theorem mom_1254_266_join3 :
    blockEstimate 1254 266 650 384 = 29592331968 :=
  block_append mom_1254_266_part3 mom_1254_266_join2 rfl rfl rfl
private theorem mom_1254_266_join4 :
    blockEstimate 1254 266 266 768 = 38540692788 :=
  block_append mom_1254_266_join1 mom_1254_266_join3 rfl rfl rfl
private theorem mom_1254_266_join5 :
    blockEstimate 1254 266 1162 256 = 14005862601 :=
  block_append mom_1254_266_part7 mom_1254_266_part8 rfl rfl rfl
private theorem mom_1254_266_join6 :
    blockEstimate 1254 266 1034 384 = 24059536137 :=
  block_append mom_1254_266_part6 mom_1254_266_join5 rfl rfl rfl
private theorem mom_1254_266_join7 :
    blockEstimate 1254 266 1546 240 = 1340563840 :=
  block_append mom_1254_266_part10 mom_1254_266_part11 rfl rfl rfl
private theorem mom_1254_266_join8 :
    blockEstimate 1254 266 1418 368 = 4526166139 :=
  block_append mom_1254_266_part9 mom_1254_266_join7 rfl rfl rfl
private theorem mom_1254_266_join9 :
    blockEstimate 1254 266 1034 752 = 28585702276 :=
  block_append mom_1254_266_join6 mom_1254_266_join8 rfl rfl rfl
private theorem mom_1254_266_join10 :
    blockEstimate 1254 266 266 1520 = 67126395064 :=
  block_append mom_1254_266_join4 mom_1254_266_join9 rfl rfl rfl
private theorem mom_1254_266 : momentEstimate 1254 266 = 67126395064 := mom_1254_266_join10
private theorem rc_2_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 0) 0 128 = 4161426643183447286428864 := by decide +kernel
private theorem rc_2_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 0) 128 128 = 1334756274009305630852454 := by decide +kernel
private theorem rc_2_0_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 0) 256 11 = 8153341496714836574460 := by decide +kernel
private theorem rc_2_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 0) 128 139 = 1342909615506020467426914 :=
  phaseBlock_append rc_2_0_2360_0_part1 rc_2_0_2360_0_part2 rfl rfl rfl
private theorem rc_2_0_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 0) 0 267 = 5504336258689467753855778 :=
  phaseBlock_append rc_2_0_2360_0_part0 rc_2_0_2360_0_join0 rfl rfl rfl
private theorem rc_2_0_2360_0 : fastPhase (bank 2 0).shape 179808 2360 0 1 0 7 0 = 5504336258689467753855778 :=
  phase_of_block (n := 267) (by decide +kernel) rc_2_0_2360_0_join1
private theorem rc_2_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 1) 0 128 = 4136360589284816701360320 := by decide +kernel
private theorem rc_2_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 1) 128 128 = 1315895405194247578233042 := by decide +kernel
private theorem rc_2_0_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 1) 256 11 = 6789015490881816302220 := by decide +kernel
private theorem rc_2_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 1) 128 139 = 1322684420685129394535262 :=
  phaseBlock_append rc_2_0_2360_1_part1 rc_2_0_2360_1_part2 rfl rfl rfl
private theorem rc_2_0_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2360 0 1 0 7 1) 0 267 = 5459045009969946095895582 :=
  phaseBlock_append rc_2_0_2360_1_part0 rc_2_0_2360_1_join0 rfl rfl rfl
private theorem rc_2_0_2360_1 : fastPhase (bank 2 0).shape 179808 2360 0 1 0 7 1 = 5459045009969946095895582 :=
  phase_of_block (n := 267) (by decide +kernel) rc_2_0_2360_1_join1
private theorem rc_2_0_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 0) 0 128 = 4161461412140739818222464 := by decide +kernel
private theorem rc_2_0_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 0) 128 128 = 1334764093025490991506531 := by decide +kernel
private theorem rc_2_0_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 0) 256 11 = 8153371958486730387500 := by decide +kernel
private theorem rc_2_0_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 0) 128 139 = 1342917464983977721894031 :=
  phaseBlock_append rc_2_0_2361_0_part1 rc_2_0_2361_0_part2 rfl rfl rfl
private theorem rc_2_0_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 0) 0 267 = 5504378877124717540116495 :=
  phaseBlock_append rc_2_0_2361_0_part0 rc_2_0_2361_0_join0 rfl rfl rfl
private theorem rc_2_0_2361_0 : fastPhase (bank 2 0).shape 179808 2361 0 1 0 7 0 = 5504378877124717540116495 :=
  phase_of_block (n := 267) (by decide +kernel) rc_2_0_2361_0_join1
private theorem rc_2_0_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 1) 0 128 = 4136395183576910970289408 := by decide +kernel
private theorem rc_2_0_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 1) 128 128 = 1315903129885243700911400 := by decide +kernel
private theorem rc_2_0_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 1) 256 11 = 6789040952192850072216 := by decide +kernel
private theorem rc_2_0_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 1) 128 139 = 1322692170837436550983616 :=
  phaseBlock_append rc_2_0_2361_1_part1 rc_2_0_2361_1_part2 rfl rfl rfl
private theorem rc_2_0_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179808 2361 0 1 0 7 1) 0 267 = 5459087354414347521273024 :=
  phaseBlock_append rc_2_0_2361_1_part0 rc_2_0_2361_1_join0 rfl rfl rfl
private theorem rc_2_0_2361_1 : fastPhase (bank 2 0).shape 179808 2361 0 1 0 7 1 = 5459087354414347521273024 :=
  phase_of_block (n := 267) (by decide +kernel) rc_2_0_2361_1_join1
private theorem receipt_2_0 : B1Checked (bank 2 0) 0 0 7 := by
  refine b1_checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1254_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_0_2360_0 rc_2_0_2360_1 rc_2_0_2361_0 rc_2_0_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1388_294_part0 :
    blockEstimate 1388 294 294 128 = 462494240 := by decide +kernel
private theorem mom_1388_294_part1 :
    blockEstimate 1388 294 422 128 = 2923178528 := by decide +kernel
private theorem mom_1388_294_part2 :
    blockEstimate 1388 294 550 128 = 6958839417 := by decide +kernel
private theorem mom_1388_294_part3 :
    blockEstimate 1388 294 678 128 = 10655702080 := by decide +kernel
private theorem mom_1388_294_part4 :
    blockEstimate 1388 294 806 128 = 13125508160 := by decide +kernel
private theorem mom_1388_294_part5 :
    blockEstimate 1388 294 934 128 = 14357994560 := by decide +kernel
private theorem mom_1388_294_part6 :
    blockEstimate 1388 294 1062 128 = 14353161280 := by decide +kernel
private theorem mom_1388_294_part7 :
    blockEstimate 1388 294 1190 128 = 13111008320 := by decide +kernel
private theorem mom_1388_294_part8 :
    blockEstimate 1388 294 1318 128 = 10645949057 := by decide +kernel
private theorem mom_1388_294_part9 :
    blockEstimate 1388 294 1446 128 = 7441127313 := by decide +kernel
private theorem mom_1388_294_part10 :
    blockEstimate 1388 294 1574 128 = 4343788377 := by decide +kernel
private theorem mom_1388_294_part11 :
    blockEstimate 1388 294 1702 128 = 1842929776 := by decide +kernel
private theorem mom_1388_294_part12 :
    blockEstimate 1388 294 1830 128 = 352179312 := by decide +kernel
private theorem mom_1388_294_part13 :
    blockEstimate 1388 294 1958 18 = 848825 := by decide +kernel
private theorem mom_1388_294_join0 :
    blockEstimate 1388 294 422 256 = 9882017945 :=
  block_append mom_1388_294_part1 mom_1388_294_part2 rfl rfl rfl
private theorem mom_1388_294_join1 :
    blockEstimate 1388 294 294 384 = 10344512185 :=
  block_append mom_1388_294_part0 mom_1388_294_join0 rfl rfl rfl
private theorem mom_1388_294_join2 :
    blockEstimate 1388 294 678 256 = 23781210240 :=
  block_append mom_1388_294_part3 mom_1388_294_part4 rfl rfl rfl
private theorem mom_1388_294_join3 :
    blockEstimate 1388 294 934 256 = 28711155840 :=
  block_append mom_1388_294_part5 mom_1388_294_part6 rfl rfl rfl
private theorem mom_1388_294_join4 :
    blockEstimate 1388 294 678 512 = 52492366080 :=
  block_append mom_1388_294_join2 mom_1388_294_join3 rfl rfl rfl
private theorem mom_1388_294_join5 :
    blockEstimate 1388 294 294 896 = 62836878265 :=
  block_append mom_1388_294_join1 mom_1388_294_join4 rfl rfl rfl
private theorem mom_1388_294_join6 :
    blockEstimate 1388 294 1318 256 = 18087076370 :=
  block_append mom_1388_294_part8 mom_1388_294_part9 rfl rfl rfl
private theorem mom_1388_294_join7 :
    blockEstimate 1388 294 1190 384 = 31198084690 :=
  block_append mom_1388_294_part7 mom_1388_294_join6 rfl rfl rfl
private theorem mom_1388_294_join8 :
    blockEstimate 1388 294 1574 256 = 6186718153 :=
  block_append mom_1388_294_part10 mom_1388_294_part11 rfl rfl rfl
private theorem mom_1388_294_join9 :
    blockEstimate 1388 294 1830 146 = 353028137 :=
  block_append mom_1388_294_part12 mom_1388_294_part13 rfl rfl rfl
private theorem mom_1388_294_join10 :
    blockEstimate 1388 294 1574 402 = 6539746290 :=
  block_append mom_1388_294_join8 mom_1388_294_join9 rfl rfl rfl
private theorem mom_1388_294_join11 :
    blockEstimate 1388 294 1190 786 = 37737830980 :=
  block_append mom_1388_294_join7 mom_1388_294_join10 rfl rfl rfl
private theorem mom_1388_294_join12 :
    blockEstimate 1388 294 294 1682 = 100574709245 :=
  block_append mom_1388_294_join5 mom_1388_294_join11 rfl rfl rfl
private theorem mom_1388_294 : momentEstimate 1388 294 = 100574709245 := mom_1388_294_join12
private theorem rc_2_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 0) 0 128 = 6848446753270367221841856 := by decide +kernel
private theorem rc_2_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 0) 128 128 = 2671984543715760692422393 := by decide +kernel
private theorem rc_2_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 0) 256 39 = 141516253836813529953596 := by decide +kernel
private theorem rc_2_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 0) 128 167 = 2813500797552574222375989 :=
  phaseBlock_append rc_2_1_2360_0_part1 rc_2_1_2360_0_part2 rfl rfl rfl
private theorem rc_2_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 0) 0 295 = 9661947550822941444217845 :=
  phaseBlock_append rc_2_1_2360_0_part0 rc_2_1_2360_0_join0 rfl rfl rfl
private theorem rc_2_1_2360_0 : fastPhase (bank 2 1).shape 179808 2360 1 1 0 7 0 = 9661947550822941444217845 :=
  phase_of_block (n := 295) (by decide +kernel) rc_2_1_2360_0_join1
private theorem rc_2_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 1) 0 128 = 6811919976710958766200576 := by decide +kernel
private theorem rc_2_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 1) 128 128 = 2643683817219346172082536 := by decide +kernel
private theorem rc_2_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 1) 256 39 = 134343167331193808985211 := by decide +kernel
private theorem rc_2_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 1) 128 167 = 2778026984550539981067747 :=
  phaseBlock_append rc_2_1_2360_1_part1 rc_2_1_2360_1_part2 rfl rfl rfl
private theorem rc_2_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2360 1 1 0 7 1) 0 295 = 9589946961261498747268323 :=
  phaseBlock_append rc_2_1_2360_1_part0 rc_2_1_2360_1_join0 rfl rfl rfl
private theorem rc_2_1_2360_1 : fastPhase (bank 2 1).shape 179808 2360 1 1 0 7 1 = 9589946961261498747268323 :=
  phase_of_block (n := 295) (by decide +kernel) rc_2_1_2360_1_join1
private theorem rc_2_1_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 0) 0 128 = 6848504459456055737758336 := by decide +kernel
private theorem rc_2_1_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 0) 128 128 = 2672000876520074084103585 := by decide +kernel
private theorem rc_2_1_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 0) 256 39 = 141516838288042661238584 := by decide +kernel
private theorem rc_2_1_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 0) 128 167 = 2813517714808116745342169 :=
  phaseBlock_append rc_2_1_2361_0_part1 rc_2_1_2361_0_part2 rfl rfl rfl
private theorem rc_2_1_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 0) 0 295 = 9662022174264172483100505 :=
  phaseBlock_append rc_2_1_2361_0_part0 rc_2_1_2361_0_join0 rfl rfl rfl
private theorem rc_2_1_2361_0 : fastPhase (bank 2 1).shape 179808 2361 1 1 0 7 0 = 9662022174264172483100505 :=
  phase_of_block (n := 295) (by decide +kernel) rc_2_1_2361_0_join1
private theorem rc_2_1_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 1) 0 128 = 6811977426084627845582784 := by decide +kernel
private theorem rc_2_1_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 1) 128 128 = 2643700000416201349614669 := by decide +kernel
private theorem rc_2_1_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 1) 256 39 = 134343723903523839384512 := by decide +kernel
private theorem rc_2_1_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 1) 128 167 = 2778043724319725188999181 :=
  phaseBlock_append rc_2_1_2361_1_part1 rc_2_1_2361_1_part2 rfl rfl rfl
private theorem rc_2_1_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2361 1 1 0 7 1) 0 295 = 9590021150404353034581965 :=
  phaseBlock_append rc_2_1_2361_1_part0 rc_2_1_2361_1_join0 rfl rfl rfl
private theorem rc_2_1_2361_1 : fastPhase (bank 2 1).shape 179808 2361 1 1 0 7 1 = 9590021150404353034581965 :=
  phase_of_block (n := 295) (by decide +kernel) rc_2_1_2361_1_join1
private theorem receipt_2_1 : B1Checked (bank 2 1) 1 0 7 := by
  refine b1_checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1388_294)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_1_2360_0 rc_2_1_2360_1 rc_2_1_2361_0 rc_2_1_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1507_319_part0 :
    blockEstimate 1507 319 319 128 = 505067680 := by decide +kernel
private theorem mom_1507_319_part1 :
    blockEstimate 1507 319 447 128 = 3217262752 := by decide +kernel
private theorem mom_1507_319_part2 :
    blockEstimate 1507 319 575 128 = 7826605648 := by decide +kernel
private theorem mom_1507_319_part3 :
    blockEstimate 1507 319 703 128 = 12485847040 := by decide +kernel
private theorem mom_1507_319_part4 :
    blockEstimate 1507 319 831 128 = 15854397440 := by decide +kernel
private theorem mom_1507_319_part5 :
    blockEstimate 1507 319 959 128 = 17880770560 := by decide +kernel
private theorem mom_1507_319_part6 :
    blockEstimate 1507 319 1087 128 = 18564966400 := by decide +kernel
private theorem mom_1507_319_part7 :
    blockEstimate 1507 319 1215 128 = 17906984960 := by decide +kernel
private theorem mom_1507_319_part8 :
    blockEstimate 1507 319 1343 128 = 15906826240 := by decide +kernel
private theorem mom_1507_319_part9 :
    blockEstimate 1507 319 1471 128 = 12628487677 := by decide +kernel
private theorem mom_1507_319_part10 :
    blockEstimate 1507 319 1599 128 = 8803292768 := by decide +kernel
private theorem mom_1507_319_part11 :
    blockEstimate 1507 319 1727 128 = 5210560163 := by decide +kernel
private theorem mom_1507_319_part12 :
    blockEstimate 1507 319 1855 128 = 2309917392 := by decide +kernel
private theorem mom_1507_319_part13 :
    blockEstimate 1507 319 1983 128 = 515886800 := by decide +kernel
private theorem mom_1507_319_part14 :
    blockEstimate 1507 319 2111 34 = 5553660 := by decide +kernel
private theorem mom_1507_319_join0 :
    blockEstimate 1507 319 447 256 = 11043868400 :=
  block_append mom_1507_319_part1 mom_1507_319_part2 rfl rfl rfl
private theorem mom_1507_319_join1 :
    blockEstimate 1507 319 319 384 = 11548936080 :=
  block_append mom_1507_319_part0 mom_1507_319_join0 rfl rfl rfl
private theorem mom_1507_319_join2 :
    blockEstimate 1507 319 703 256 = 28340244480 :=
  block_append mom_1507_319_part3 mom_1507_319_part4 rfl rfl rfl
private theorem mom_1507_319_join3 :
    blockEstimate 1507 319 959 256 = 36445736960 :=
  block_append mom_1507_319_part5 mom_1507_319_part6 rfl rfl rfl
private theorem mom_1507_319_join4 :
    blockEstimate 1507 319 703 512 = 64785981440 :=
  block_append mom_1507_319_join2 mom_1507_319_join3 rfl rfl rfl
private theorem mom_1507_319_join5 :
    blockEstimate 1507 319 319 896 = 76334917520 :=
  block_append mom_1507_319_join1 mom_1507_319_join4 rfl rfl rfl
private theorem mom_1507_319_join6 :
    blockEstimate 1507 319 1215 256 = 33813811200 :=
  block_append mom_1507_319_part7 mom_1507_319_part8 rfl rfl rfl
private theorem mom_1507_319_join7 :
    blockEstimate 1507 319 1471 256 = 21431780445 :=
  block_append mom_1507_319_part9 mom_1507_319_part10 rfl rfl rfl
private theorem mom_1507_319_join8 :
    blockEstimate 1507 319 1215 512 = 55245591645 :=
  block_append mom_1507_319_join6 mom_1507_319_join7 rfl rfl rfl
private theorem mom_1507_319_join9 :
    blockEstimate 1507 319 1727 256 = 7520477555 :=
  block_append mom_1507_319_part11 mom_1507_319_part12 rfl rfl rfl
private theorem mom_1507_319_join10 :
    blockEstimate 1507 319 1983 162 = 521440460 :=
  block_append mom_1507_319_part13 mom_1507_319_part14 rfl rfl rfl
private theorem mom_1507_319_join11 :
    blockEstimate 1507 319 1727 418 = 8041918015 :=
  block_append mom_1507_319_join9 mom_1507_319_join10 rfl rfl rfl
private theorem mom_1507_319_join12 :
    blockEstimate 1507 319 1215 930 = 63287509660 :=
  block_append mom_1507_319_join8 mom_1507_319_join11 rfl rfl rfl
private theorem mom_1507_319_join13 :
    blockEstimate 1507 319 319 1826 = 139622427180 :=
  block_append mom_1507_319_join5 mom_1507_319_join12 rfl rfl rfl
private theorem mom_1507_319 : momentEstimate 1507 319 = 139622427180 := mom_1507_319_join13
private theorem rc_2_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 0) 0 128 = 10774454443116894571246464 := by decide +kernel
private theorem rc_2_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 0) 128 128 = 4754293193149855102699119 := by decide +kernel
private theorem rc_2_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 0) 256 64 = 542376697008242273601529 := by decide +kernel
private theorem rc_2_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 0) 128 192 = 5296669890158097376300648 :=
  phaseBlock_append rc_2_2_2360_0_part1 rc_2_2_2360_0_part2 rfl rfl rfl
private theorem rc_2_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 0) 0 320 = 16071124333274991947547112 :=
  phaseBlock_append rc_2_2_2360_0_part0 rc_2_2_2360_0_join0 rfl rfl rfl
private theorem rc_2_2_2360_0 : fastPhase (bank 2 2).shape 179808 2360 2 1 0 7 0 = 16071124333274991947547112 :=
  phase_of_block (n := 320) (by decide +kernel) rc_2_2_2360_0_join1
private theorem rc_2_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 1) 0 128 = 10722362348277347969509056 := by decide +kernel
private theorem rc_2_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 1) 128 128 = 4713016239468227544176778 := by decide +kernel
private theorem rc_2_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 1) 256 64 = 525339419889523778822199 := by decide +kernel
private theorem rc_2_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 1) 128 192 = 5238355659357751322998977 :=
  phaseBlock_append rc_2_2_2360_1_part1 rc_2_2_2360_1_part2 rfl rfl rfl
private theorem rc_2_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2360 2 1 0 7 1) 0 320 = 15960718007635099292508033 :=
  phaseBlock_append rc_2_2_2360_1_part0 rc_2_2_2360_1_join0 rfl rfl rfl
private theorem rc_2_2_2360_1 : fastPhase (bank 2 2).shape 179808 2360 2 1 0 7 1 = 15960718007635099292508033 :=
  phase_of_block (n := 320) (by decide +kernel) rc_2_2_2360_1_join1
private theorem rc_2_2_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 0) 0 128 = 10774545658823582431575808 := by decide +kernel
private theorem rc_2_2_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 0) 128 128 = 4754323263316418327740064 := by decide +kernel
private theorem rc_2_2_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 0) 256 64 = 542379092109251048702232 := by decide +kernel
private theorem rc_2_2_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 0) 128 192 = 5296702355425669376442296 :=
  phaseBlock_append rc_2_2_2361_0_part1 rc_2_2_2361_0_part2 rfl rfl rfl
private theorem rc_2_2_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 0) 0 320 = 16071248014249251808018104 :=
  phaseBlock_append rc_2_2_2361_0_part0 rc_2_2_2361_0_join0 rfl rfl rfl
private theorem rc_2_2_2361_0 : fastPhase (bank 2 2).shape 179808 2361 2 1 0 7 0 = 16071248014249251808018104 :=
  phase_of_block (n := 320) (by decide +kernel) rc_2_2_2361_0_join1
private theorem rc_2_2_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 1) 0 128 = 10722453196043897472736320 := by decide +kernel
private theorem rc_2_2_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 1) 128 128 = 4713046083148854507331646 := by decide +kernel
private theorem rc_2_2_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 1) 256 64 = 525341746025920628848512 := by decide +kernel
private theorem rc_2_2_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 1) 128 192 = 5238387829174775136180158 :=
  phaseBlock_append rc_2_2_2361_1_part1 rc_2_2_2361_1_part2 rfl rfl rfl
private theorem rc_2_2_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2361 2 1 0 7 1) 0 320 = 15960841025218672608916478 :=
  phaseBlock_append rc_2_2_2361_1_part0 rc_2_2_2361_1_join0 rfl rfl rfl
private theorem rc_2_2_2361_1 : fastPhase (bank 2 2).shape 179808 2361 2 1 0 7 1 = 15960841025218672608916478 :=
  phase_of_block (n := 320) (by decide +kernel) rc_2_2_2361_1_join1
private theorem receipt_2_2 : B1Checked (bank 2 2) 2 0 7 := by
  refine b1_checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1507_319)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_2_2360_0 rc_2_2_2360_1 rc_2_2_2361_0 rc_2_2_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1720_365_part0 :
    blockEstimate 1720 365 365 128 = 581270560 := by decide +kernel
private theorem mom_1720_365_part1 :
    blockEstimate 1720 365 493 128 = 3743648800 := by decide +kernel
private theorem mom_1720_365_part2 :
    blockEstimate 1720 365 621 128 = 9300494175 := by decide +kernel
private theorem mom_1720_365_part3 :
    blockEstimate 1720 365 749 128 = 15793386048 := by decide +kernel
private theorem mom_1720_365_part4 :
    blockEstimate 1720 365 877 128 = 21061349952 := by decide +kernel
private theorem mom_1720_365_part5 :
    blockEstimate 1720 365 1005 128 = 24794198592 := by decide +kernel
private theorem mom_1720_365_part6 :
    blockEstimate 1720 365 1133 128 = 26991931968 := by decide +kernel
private theorem mom_1720_365_part7 :
    blockEstimate 1720 365 1261 128 = 27654550080 := by decide +kernel
private theorem mom_1720_365_part8 :
    blockEstimate 1720 365 1389 128 = 26782052928 := by decide +kernel
private theorem mom_1720_365_part9 :
    blockEstimate 1720 365 1517 128 = 24374440512 := by decide +kernel
private theorem mom_1720_365_part10 :
    blockEstimate 1720 365 1645 128 = 20445090673 := by decide +kernel
private theorem mom_1720_365_part11 :
    blockEstimate 1720 365 1773 128 = 15531849306 := by decide +kernel
private theorem mom_1720_365_part12 :
    blockEstimate 1720 365 1901 128 = 10605870330 := by decide +kernel
private theorem mom_1720_365_part13 :
    blockEstimate 1720 365 2029 128 = 6195104926 := by decide +kernel
private theorem mom_1720_365_part14 :
    blockEstimate 1720 365 2157 128 = 2737990256 := by decide +kernel
private theorem mom_1720_365_part15 :
    blockEstimate 1720 365 2285 128 = 623967856 := by decide +kernel
private theorem mom_1720_365_part16 :
    blockEstimate 1720 365 2413 37 = 8090725 := by decide +kernel
private theorem mom_1720_365_join0 :
    blockEstimate 1720 365 365 256 = 4324919360 :=
  block_append mom_1720_365_part0 mom_1720_365_part1 rfl rfl rfl
private theorem mom_1720_365_join1 :
    blockEstimate 1720 365 621 256 = 25093880223 :=
  block_append mom_1720_365_part2 mom_1720_365_part3 rfl rfl rfl
private theorem mom_1720_365_join2 :
    blockEstimate 1720 365 365 512 = 29418799583 :=
  block_append mom_1720_365_join0 mom_1720_365_join1 rfl rfl rfl
private theorem mom_1720_365_join3 :
    blockEstimate 1720 365 877 256 = 45855548544 :=
  block_append mom_1720_365_part4 mom_1720_365_part5 rfl rfl rfl
private theorem mom_1720_365_join4 :
    blockEstimate 1720 365 1133 256 = 54646482048 :=
  block_append mom_1720_365_part6 mom_1720_365_part7 rfl rfl rfl
private theorem mom_1720_365_join5 :
    blockEstimate 1720 365 877 512 = 100502030592 :=
  block_append mom_1720_365_join3 mom_1720_365_join4 rfl rfl rfl
private theorem mom_1720_365_join6 :
    blockEstimate 1720 365 365 1024 = 129920830175 :=
  block_append mom_1720_365_join2 mom_1720_365_join5 rfl rfl rfl
private theorem mom_1720_365_join7 :
    blockEstimate 1720 365 1389 256 = 51156493440 :=
  block_append mom_1720_365_part8 mom_1720_365_part9 rfl rfl rfl
private theorem mom_1720_365_join8 :
    blockEstimate 1720 365 1645 256 = 35976939979 :=
  block_append mom_1720_365_part10 mom_1720_365_part11 rfl rfl rfl
private theorem mom_1720_365_join9 :
    blockEstimate 1720 365 1389 512 = 87133433419 :=
  block_append mom_1720_365_join7 mom_1720_365_join8 rfl rfl rfl
private theorem mom_1720_365_join10 :
    blockEstimate 1720 365 1901 256 = 16800975256 :=
  block_append mom_1720_365_part12 mom_1720_365_part13 rfl rfl rfl
private theorem mom_1720_365_join11 :
    blockEstimate 1720 365 2285 165 = 632058581 :=
  block_append mom_1720_365_part15 mom_1720_365_part16 rfl rfl rfl
private theorem mom_1720_365_join12 :
    blockEstimate 1720 365 2157 293 = 3370048837 :=
  block_append mom_1720_365_part14 mom_1720_365_join11 rfl rfl rfl
private theorem mom_1720_365_join13 :
    blockEstimate 1720 365 1901 549 = 20171024093 :=
  block_append mom_1720_365_join10 mom_1720_365_join12 rfl rfl rfl
private theorem mom_1720_365_join14 :
    blockEstimate 1720 365 1389 1061 = 107304457512 :=
  block_append mom_1720_365_join9 mom_1720_365_join13 rfl rfl rfl
private theorem mom_1720_365_join15 :
    blockEstimate 1720 365 365 2085 = 237225287687 :=
  block_append mom_1720_365_join6 mom_1720_365_join14 rfl rfl rfl
private theorem mom_1720_365 : momentEstimate 1720 365 = 237225287687 := mom_1720_365_join15
private theorem rc_2_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 0) 0 128 = 17320904330590945229304096 := by decide +kernel
private theorem rc_2_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 0) 128 128 = 8905837792872927812255000 := by decide +kernel
private theorem rc_2_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 0) 256 110 = 2195043987181806681074539 := by decide +kernel
private theorem rc_2_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 0) 128 238 = 11100881780054734493329539 :=
  phaseBlock_append rc_2_3_2360_0_part1 rc_2_3_2360_0_part2 rfl rfl rfl
private theorem rc_2_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 0) 0 366 = 28421786110645679722633635 :=
  phaseBlock_append rc_2_3_2360_0_part0 rc_2_3_2360_0_join0 rfl rfl rfl
private theorem rc_2_3_2360_0 : fastPhase (bank 2 3).shape 179808 2360 3 1 0 7 0 = 28421786110645679722633635 :=
  phase_of_block (n := 366) (by decide +kernel) rc_2_3_2360_0_join1
private theorem rc_2_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 1) 0 128 = 17249032035222151579151520 := by decide +kernel
private theorem rc_2_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 1) 128 128 = 8847326762185684764989592 := by decide +kernel
private theorem rc_2_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 1) 256 110 = 2154215185599217021935969 := by decide +kernel
private theorem rc_2_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 1) 128 238 = 11001541947784901786925561 :=
  phaseBlock_append rc_2_3_2360_1_part1 rc_2_3_2360_1_part2 rfl rfl rfl
private theorem rc_2_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2360 3 1 0 7 1) 0 366 = 28250573983007053366077081 :=
  phaseBlock_append rc_2_3_2360_1_part0 rc_2_3_2360_1_join0 rfl rfl rfl
private theorem rc_2_3_2360_1 : fastPhase (bank 2 3).shape 179808 2360 3 1 0 7 1 = 28250573983007053366077081 :=
  phase_of_block (n := 366) (by decide +kernel) rc_2_3_2360_1_join1
private theorem rc_2_3_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 0) 0 128 = 17321052654226491520607040 := by decide +kernel
private theorem rc_2_3_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 0) 128 128 = 8905897304632794896096093 := by decide +kernel
private theorem rc_2_3_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 0) 256 110 = 2195054604049530658412187 := by decide +kernel
private theorem rc_2_3_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 0) 128 238 = 11100951908682325554508280 :=
  phaseBlock_append rc_2_3_2361_0_part1 rc_2_3_2361_0_part2 rfl rfl rfl
private theorem rc_2_3_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 0) 0 366 = 28422004562908817075115320 :=
  phaseBlock_append rc_2_3_2361_0_part0 rc_2_3_2361_0_join0 rfl rfl rfl
private theorem rc_2_3_2361_0 : fastPhase (bank 2 3).shape 179808 2361 3 1 0 7 0 = 28422004562908817075115320 :=
  phase_of_block (n := 366) (by decide +kernel) rc_2_3_2361_0_join1
private theorem rc_2_3_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 1) 0 128 = 17249179845424167823044800 := by decide +kernel
private theorem rc_2_3_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 1) 128 128 = 8847385935195404932749435 := by decide +kernel
private theorem rc_2_3_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 1) 256 110 = 2154225627491305304748966 := by decide +kernel
private theorem rc_2_3_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 1) 128 238 = 11001611562686710237498401 :=
  phaseBlock_append rc_2_3_2361_1_part1 rc_2_3_2361_1_part2 rfl rfl rfl
private theorem rc_2_3_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2361 3 1 0 7 1) 0 366 = 28250791408110878060543201 :=
  phaseBlock_append rc_2_3_2361_1_part0 rc_2_3_2361_1_join0 rfl rfl rfl
private theorem rc_2_3_2361_1 : fastPhase (bank 2 3).shape 179808 2361 3 1 0 7 1 = 28250791408110878060543201 :=
  phase_of_block (n := 366) (by decide +kernel) rc_2_3_2361_1_join1
private theorem receipt_2_3 : B1Checked (bank 2 3) 3 0 7 := by
  refine b1_checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1720_365)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_3_2360_0 rc_2_3_2360_1 rc_2_3_2361_0 rc_2_3_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1856_393_part0 :
    blockEstimate 1856 393 393 128 = 629925920 := by decide +kernel
private theorem mom_1856_393_part1 :
    blockEstimate 1856 393 521 128 = 4079745056 := by decide +kernel
private theorem mom_1856_393_part2 :
    blockEstimate 1856 393 649 128 = 10210773024 := by decide +kernel
private theorem mom_1856_393_part3 :
    blockEstimate 1856 393 777 128 = 17831759086 := by decide +kernel
private theorem mom_1856_393_part4 :
    blockEstimate 1856 393 905 128 = 24470854592 := by decide +kernel
private theorem mom_1856_393_part5 :
    blockEstimate 1856 393 1033 128 = 29457570752 := by decide +kernel
private theorem mom_1856_393_part6 :
    blockEstimate 1856 393 1161 128 = 32791731136 := by decide +kernel
private theorem mom_1856_393_part7 :
    blockEstimate 1856 393 1289 128 = 34473335744 := by decide +kernel
private theorem mom_1856_393_part8 :
    blockEstimate 1856 393 1417 128 = 34502384576 := by decide +kernel
private theorem mom_1856_393_part9 :
    blockEstimate 1856 393 1545 128 = 32878877632 := by decide +kernel
private theorem mom_1856_393_part10 :
    blockEstimate 1856 393 1673 128 = 29602814912 := by decide +kernel
private theorem mom_1856_393_part11 :
    blockEstimate 1856 393 1801 128 = 24712272455 := by decide +kernel
private theorem mom_1856_393_part12 :
    blockEstimate 1856 393 1929 128 = 18933347452 := by decide +kernel
private theorem mom_1856_393_part13 :
    blockEstimate 1856 393 2057 128 = 13212630129 := by decide +kernel
private theorem mom_1856_393_part14 :
    blockEstimate 1856 393 2185 128 = 8057464054 := by decide +kernel
private theorem mom_1856_393_part15 :
    blockEstimate 1856 393 2313 128 = 3902014256 := by decide +kernel
private theorem mom_1856_393_part16 :
    blockEstimate 1856 393 2441 128 = 1156751152 := by decide +kernel
private theorem mom_1856_393_part17 :
    blockEstimate 1856 393 2569 73 = 62777729 := by decide +kernel
private theorem mom_1856_393_join0 :
    blockEstimate 1856 393 393 256 = 4709670976 :=
  block_append mom_1856_393_part0 mom_1856_393_part1 rfl rfl rfl
private theorem mom_1856_393_join1 :
    blockEstimate 1856 393 649 256 = 28042532110 :=
  block_append mom_1856_393_part2 mom_1856_393_part3 rfl rfl rfl
private theorem mom_1856_393_join2 :
    blockEstimate 1856 393 393 512 = 32752203086 :=
  block_append mom_1856_393_join0 mom_1856_393_join1 rfl rfl rfl
private theorem mom_1856_393_join3 :
    blockEstimate 1856 393 905 256 = 53928425344 :=
  block_append mom_1856_393_part4 mom_1856_393_part5 rfl rfl rfl
private theorem mom_1856_393_join4 :
    blockEstimate 1856 393 1289 256 = 68975720320 :=
  block_append mom_1856_393_part7 mom_1856_393_part8 rfl rfl rfl
private theorem mom_1856_393_join5 :
    blockEstimate 1856 393 1161 384 = 101767451456 :=
  block_append mom_1856_393_part6 mom_1856_393_join4 rfl rfl rfl
private theorem mom_1856_393_join6 :
    blockEstimate 1856 393 905 640 = 155695876800 :=
  block_append mom_1856_393_join3 mom_1856_393_join5 rfl rfl rfl
private theorem mom_1856_393_join7 :
    blockEstimate 1856 393 393 1152 = 188448079886 :=
  block_append mom_1856_393_join2 mom_1856_393_join6 rfl rfl rfl
private theorem mom_1856_393_join8 :
    blockEstimate 1856 393 1545 256 = 62481692544 :=
  block_append mom_1856_393_part9 mom_1856_393_part10 rfl rfl rfl
private theorem mom_1856_393_join9 :
    blockEstimate 1856 393 1801 256 = 43645619907 :=
  block_append mom_1856_393_part11 mom_1856_393_part12 rfl rfl rfl
private theorem mom_1856_393_join10 :
    blockEstimate 1856 393 1545 512 = 106127312451 :=
  block_append mom_1856_393_join8 mom_1856_393_join9 rfl rfl rfl
private theorem mom_1856_393_join11 :
    blockEstimate 1856 393 2057 256 = 21270094183 :=
  block_append mom_1856_393_part13 mom_1856_393_part14 rfl rfl rfl
private theorem mom_1856_393_join12 :
    blockEstimate 1856 393 2441 201 = 1219528881 :=
  block_append mom_1856_393_part16 mom_1856_393_part17 rfl rfl rfl
private theorem mom_1856_393_join13 :
    blockEstimate 1856 393 2313 329 = 5121543137 :=
  block_append mom_1856_393_part15 mom_1856_393_join12 rfl rfl rfl
private theorem mom_1856_393_join14 :
    blockEstimate 1856 393 2057 585 = 26391637320 :=
  block_append mom_1856_393_join11 mom_1856_393_join13 rfl rfl rfl
private theorem mom_1856_393_join15 :
    blockEstimate 1856 393 1545 1097 = 132518949771 :=
  block_append mom_1856_393_join10 mom_1856_393_join14 rfl rfl rfl
private theorem mom_1856_393_join16 :
    blockEstimate 1856 393 393 2249 = 320967029657 :=
  block_append mom_1856_393_join7 mom_1856_393_join15 rfl rfl rfl
private theorem mom_1856_393 : momentEstimate 1856 393 = 320967029657 := mom_1856_393_join16
private theorem rc_2_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 0 128 = 25514532388880329323171168 := by decide +kernel
private theorem rc_2_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 128 128 = 14045751787541088428614285 := by decide +kernel
private theorem rc_2_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 256 128 = 4665024556180460287488191 := by decide +kernel
private theorem rc_2_4_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 384 10 = 24901275122057540686194 := by decide +kernel
private theorem rc_2_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 0 256 = 39560284176421417751785453 :=
  phaseBlock_append rc_2_4_2360_0_part0 rc_2_4_2360_0_part1 rfl rfl rfl
private theorem rc_2_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 256 138 = 4689925831302517828174385 :=
  phaseBlock_append rc_2_4_2360_0_part2 rc_2_4_2360_0_part3 rfl rfl rfl
private theorem rc_2_4_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 0) 0 394 = 44250210007723935579959838 :=
  phaseBlock_append rc_2_4_2360_0_join0 rc_2_4_2360_0_join1 rfl rfl rfl
private theorem rc_2_4_2360_0 : fastPhase (bank 2 4).shape 179808 2360 4 1 0 7 0 = 44250210007723935579959838 :=
  phase_of_block (n := 394) (by decide +kernel) rc_2_4_2360_0_join2
private theorem rc_2_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 0 128 = 25417331177706278690382048 := by decide +kernel
private theorem rc_2_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 128 128 = 13965341940058407410159144 := by decide +kernel
private theorem rc_2_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 256 128 = 4599544909354263966068024 := by decide +kernel
private theorem rc_2_4_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 384 10 = 20362461424868383580034 := by decide +kernel
private theorem rc_2_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 0 256 = 39382673117764686100541192 :=
  phaseBlock_append rc_2_4_2360_1_part0 rc_2_4_2360_1_part1 rfl rfl rfl
private theorem rc_2_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 256 138 = 4619907370779132349648058 :=
  phaseBlock_append rc_2_4_2360_1_part2 rc_2_4_2360_1_part3 rfl rfl rfl
private theorem rc_2_4_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2360 4 1 0 7 1) 0 394 = 44002580488543818450189250 :=
  phaseBlock_append rc_2_4_2360_1_join0 rc_2_4_2360_1_join1 rfl rfl rfl
private theorem rc_2_4_2360_1 : fastPhase (bank 2 4).shape 179808 2360 4 1 0 7 1 = 44002580488543818450189250 :=
  phase_of_block (n := 394) (by decide +kernel) rc_2_4_2360_1_join2
private theorem rc_2_4_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 0 128 = 25514751755321499713831872 := by decide +kernel
private theorem rc_2_4_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 128 128 = 14045848125848076458589585 := by decide +kernel
private theorem rc_2_4_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 256 128 = 4665048136044922567991678 := by decide +kernel
private theorem rc_2_4_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 384 10 = 24901364621203183301430 := by decide +kernel
private theorem rc_2_4_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 0 256 = 39560599881169576172421457 :=
  phaseBlock_append rc_2_4_2361_0_part0 rc_2_4_2361_0_part1 rfl rfl rfl
private theorem rc_2_4_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 256 138 = 4689949500666125751293108 :=
  phaseBlock_append rc_2_4_2361_0_part2 rc_2_4_2361_0_part3 rfl rfl rfl
private theorem rc_2_4_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 0) 0 394 = 44250549381835701923714565 :=
  phaseBlock_append rc_2_4_2361_0_join0 rc_2_4_2361_0_join1 rfl rfl rfl
private theorem rc_2_4_2361_0 : fastPhase (bank 2 4).shape 179808 2361 4 1 0 7 0 = 44250549381835701923714565 :=
  phase_of_block (n := 394) (by decide +kernel) rc_2_4_2361_0_join2
private theorem rc_2_4_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 0 128 = 25417549847004195300194880 := by decide +kernel
private theorem rc_2_4_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 128 128 = 13965437801359194910036902 := by decide +kernel
private theorem rc_2_4_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 256 128 = 4599568196606378901298979 := by decide +kernel
private theorem rc_2_4_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 384 10 = 20362534806633213789276 := by decide +kernel
private theorem rc_2_4_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 0 256 = 39382987648363390210231782 :=
  phaseBlock_append rc_2_4_2361_1_part0 rc_2_4_2361_1_part1 rfl rfl rfl
private theorem rc_2_4_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 256 138 = 4619930731413012115088255 :=
  phaseBlock_append rc_2_4_2361_1_part2 rc_2_4_2361_1_part3 rfl rfl rfl
private theorem rc_2_4_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2361 4 1 0 7 1) 0 394 = 44002918379776402325320037 :=
  phaseBlock_append rc_2_4_2361_1_join0 rc_2_4_2361_1_join1 rfl rfl rfl
private theorem rc_2_4_2361_1 : fastPhase (bank 2 4).shape 179808 2361 4 1 0 7 1 = 44002918379776402325320037 :=
  phase_of_block (n := 394) (by decide +kernel) rc_2_4_2361_1_join2
private theorem receipt_2_4 : B1Checked (bank 2 4) 4 0 7 := by
  refine b1_checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1856_393)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_4_2360_0 rc_2_4_2360_1 rc_2_4_2361_0 rc_2_4_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2125_450_part0 :
    blockEstimate 2125 450 450 128 = 726163360 := by decide +kernel
private theorem mom_2125_450_part1 :
    blockEstimate 2125 450 578 128 = 4744523680 := by decide +kernel
private theorem mom_2125_450_part2 :
    blockEstimate 2125 450 706 128 = 12008226720 := by decide +kernel
private theorem mom_2125_450_part3 :
    blockEstimate 2125 450 834 128 = 21647276893 := by decide +kernel
private theorem mom_2125_450_part4 :
    blockEstimate 2125 450 962 128 = 31362698752 := by decide +kernel
private theorem mom_2125_450_part5 :
    blockEstimate 2125 450 1090 128 = 39269125632 := by decide +kernel
private theorem mom_2125_450_part6 :
    blockEstimate 2125 450 1218 128 = 45283921408 := by decide +kernel
private theorem mom_2125_450_part7 :
    blockEstimate 2125 450 1346 128 = 49407086080 := by decide +kernel
private theorem mom_2125_450_part8 :
    blockEstimate 2125 450 1474 128 = 51638619648 := by decide +kernel
private theorem mom_2125_450_part9 :
    blockEstimate 2125 450 1602 128 = 51978522112 := by decide +kernel
private theorem mom_2125_450_part10 :
    blockEstimate 2125 450 1730 128 = 50426793472 := by decide +kernel
private theorem mom_2125_450_part11 :
    blockEstimate 2125 450 1858 128 = 46983433728 := by decide +kernel
private theorem mom_2125_450_part12 :
    blockEstimate 2125 450 1986 128 = 41648442880 := by decide +kernel
private theorem mom_2125_450_part13 :
    blockEstimate 2125 450 2114 128 = 34604888916 := by decide +kernel
private theorem mom_2125_450_part14 :
    blockEstimate 2125 450 2242 128 = 26958471741 := by decide +kernel
private theorem mom_2125_450_part15 :
    blockEstimate 2125 450 2370 128 = 19496129588 := by decide +kernel
private theorem mom_2125_450_part16 :
    blockEstimate 2125 450 2498 128 = 12705638320 := by decide +kernel
private theorem mom_2125_450_part17 :
    blockEstimate 2125 450 2626 128 = 7008020160 := by decide +kernel
private theorem mom_2125_450_part18 :
    blockEstimate 2125 450 2754 128 = 2852529856 := by decide +kernel
private theorem mom_2125_450_part19 :
    blockEstimate 2125 450 2882 128 = 516777664 := by decide +kernel
private theorem mom_2125_450_part20 :
    blockEstimate 2125 450 3010 15 = 788120 := by decide +kernel
private theorem mom_2125_450_join0 :
    blockEstimate 2125 450 450 256 = 5470687040 :=
  block_append mom_2125_450_part0 mom_2125_450_part1 rfl rfl rfl
private theorem mom_2125_450_join1 :
    blockEstimate 2125 450 834 256 = 53009975645 :=
  block_append mom_2125_450_part3 mom_2125_450_part4 rfl rfl rfl
private theorem mom_2125_450_join2 :
    blockEstimate 2125 450 706 384 = 65018202365 :=
  block_append mom_2125_450_part2 mom_2125_450_join1 rfl rfl rfl
private theorem mom_2125_450_join3 :
    blockEstimate 2125 450 450 640 = 70488889405 :=
  block_append mom_2125_450_join0 mom_2125_450_join2 rfl rfl rfl
private theorem mom_2125_450_join4 :
    blockEstimate 2125 450 1090 256 = 84553047040 :=
  block_append mom_2125_450_part5 mom_2125_450_part6 rfl rfl rfl
private theorem mom_2125_450_join5 :
    blockEstimate 2125 450 1474 256 = 103617141760 :=
  block_append mom_2125_450_part8 mom_2125_450_part9 rfl rfl rfl
private theorem mom_2125_450_join6 :
    blockEstimate 2125 450 1346 384 = 153024227840 :=
  block_append mom_2125_450_part7 mom_2125_450_join5 rfl rfl rfl
private theorem mom_2125_450_join7 :
    blockEstimate 2125 450 1090 640 = 237577274880 :=
  block_append mom_2125_450_join4 mom_2125_450_join6 rfl rfl rfl
private theorem mom_2125_450_join8 :
    blockEstimate 2125 450 450 1280 = 308066164285 :=
  block_append mom_2125_450_join3 mom_2125_450_join7 rfl rfl rfl
private theorem mom_2125_450_join9 :
    blockEstimate 2125 450 1730 256 = 97410227200 :=
  block_append mom_2125_450_part10 mom_2125_450_part11 rfl rfl rfl
private theorem mom_2125_450_join10 :
    blockEstimate 2125 450 2114 256 = 61563360657 :=
  block_append mom_2125_450_part13 mom_2125_450_part14 rfl rfl rfl
private theorem mom_2125_450_join11 :
    blockEstimate 2125 450 1986 384 = 103211803537 :=
  block_append mom_2125_450_part12 mom_2125_450_join10 rfl rfl rfl
private theorem mom_2125_450_join12 :
    blockEstimate 2125 450 1730 640 = 200622030737 :=
  block_append mom_2125_450_join9 mom_2125_450_join11 rfl rfl rfl
private theorem mom_2125_450_join13 :
    blockEstimate 2125 450 2498 256 = 19713658480 :=
  block_append mom_2125_450_part16 mom_2125_450_part17 rfl rfl rfl
private theorem mom_2125_450_join14 :
    blockEstimate 2125 450 2370 384 = 39209788068 :=
  block_append mom_2125_450_part15 mom_2125_450_join13 rfl rfl rfl
private theorem mom_2125_450_join15 :
    blockEstimate 2125 450 2882 143 = 517565784 :=
  block_append mom_2125_450_part19 mom_2125_450_part20 rfl rfl rfl
private theorem mom_2125_450_join16 :
    blockEstimate 2125 450 2754 271 = 3370095640 :=
  block_append mom_2125_450_part18 mom_2125_450_join15 rfl rfl rfl
private theorem mom_2125_450_join17 :
    blockEstimate 2125 450 2370 655 = 42579883708 :=
  block_append mom_2125_450_join14 mom_2125_450_join16 rfl rfl rfl
private theorem mom_2125_450_join18 :
    blockEstimate 2125 450 1730 1295 = 243201914445 :=
  block_append mom_2125_450_join12 mom_2125_450_join17 rfl rfl rfl
private theorem mom_2125_450_join19 :
    blockEstimate 2125 450 450 2575 = 551268078730 :=
  block_append mom_2125_450_join8 mom_2125_450_join18 rfl rfl rfl
private theorem mom_2125_450 : momentEstimate 2125 450 = 551268078730 := mom_2125_450_join19
private theorem rc_2_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 0 128 = 50686277870614498751304960 := by decide +kernel
private theorem rc_2_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 128 128 = 30896306105378360750535936 := by decide +kernel
private theorem rc_2_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 256 128 = 14253601051002752796543816 := by decide +kernel
private theorem rc_2_5_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 384 67 = 1788075615919106198383230 := by decide +kernel
private theorem rc_2_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 0 256 = 81582583975992859501840896 :=
  phaseBlock_append rc_2_5_2360_0_part0 rc_2_5_2360_0_part1 rfl rfl rfl
private theorem rc_2_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 256 195 = 16041676666921858994927046 :=
  phaseBlock_append rc_2_5_2360_0_part2 rc_2_5_2360_0_part3 rfl rfl rfl
private theorem rc_2_5_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 0) 0 451 = 97624260642914718496767942 :=
  phaseBlock_append rc_2_5_2360_0_join0 rc_2_5_2360_0_join1 rfl rfl rfl
private theorem rc_2_5_2360_0 : fastPhase (bank 2 5).shape 179808 2360 6 1 0 7 0 = 97624260642914718496767942 :=
  phase_of_block (n := 451) (by decide +kernel) rc_2_5_2360_0_join2
private theorem rc_2_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 0 128 = 50520597073096395528118080 := by decide +kernel
private theorem rc_2_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 128 128 = 30755746024233404529450816 := by decide +kernel
private theorem rc_2_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 256 128 = 14135731789929949006155999 := by decide +kernel
private theorem rc_2_5_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 384 67 = 1734645149614697850442353 := by decide +kernel
private theorem rc_2_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 0 256 = 81276343097329800057568896 :=
  phaseBlock_append rc_2_5_2360_1_part0 rc_2_5_2360_1_part1 rfl rfl rfl
private theorem rc_2_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 256 195 = 15870376939544646856598352 :=
  phaseBlock_append rc_2_5_2360_1_part2 rc_2_5_2360_1_part3 rfl rfl rfl
private theorem rc_2_5_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2360 6 1 0 7 1) 0 451 = 97146720036874446914167248 :=
  phaseBlock_append rc_2_5_2360_1_join0 rc_2_5_2360_1_join1 rfl rfl rfl
private theorem rc_2_5_2360_1 : fastPhase (bank 2 5).shape 179808 2360 6 1 0 7 1 = 97146720036874446914167248 :=
  phase_of_block (n := 451) (by decide +kernel) rc_2_5_2360_1_join2
private theorem rc_2_5_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 0 128 = 50686717385555532727094880 := by decide +kernel
private theorem rc_2_5_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 128 128 = 30896527275788531853000288 := by decide +kernel
private theorem rc_2_5_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 256 128 = 14253679895020520558050657 := by decide +kernel
private theorem rc_2_5_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 384 67 = 1788082999306814620158686 := by decide +kernel
private theorem rc_2_5_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 0 256 = 81583244661344064580095168 :=
  phaseBlock_append rc_2_5_2361_0_part0 rc_2_5_2361_0_part1 rfl rfl rfl
private theorem rc_2_5_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 256 195 = 16041762894327335178209343 :=
  phaseBlock_append rc_2_5_2361_0_part2 rc_2_5_2361_0_part3 rfl rfl rfl
private theorem rc_2_5_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 0) 0 451 = 97625007555671399758304511 :=
  phaseBlock_append rc_2_5_2361_0_join0 rc_2_5_2361_0_join1 rfl rfl rfl
private theorem rc_2_5_2361_0 : fastPhase (bank 2 5).shape 179808 2361 6 1 0 7 0 = 97625007555671399758304511 :=
  phase_of_block (n := 451) (by decide +kernel) rc_2_5_2361_0_join2
private theorem rc_2_5_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 0 128 = 50521035390794909142851040 := by decide +kernel
private theorem rc_2_5_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 128 128 = 30755966328708484704603616 := by decide +kernel
private theorem rc_2_5_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 256 128 = 14135810052815249860203933 := by decide +kernel
private theorem rc_2_5_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 384 67 = 1734652327062673408416467 := by decide +kernel
private theorem rc_2_5_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 0 256 = 81277001719503393847454656 :=
  phaseBlock_append rc_2_5_2361_1_part0 rc_2_5_2361_1_part1 rfl rfl rfl
private theorem rc_2_5_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 256 195 = 15870462379877923268620400 :=
  phaseBlock_append rc_2_5_2361_1_part2 rc_2_5_2361_1_part3 rfl rfl rfl
private theorem rc_2_5_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2361 6 1 0 7 1) 0 451 = 97147464099381317116075056 :=
  phaseBlock_append rc_2_5_2361_1_join0 rc_2_5_2361_1_join1 rfl rfl rfl
private theorem rc_2_5_2361_1 : fastPhase (bank 2 5).shape 179808 2361 6 1 0 7 1 = 97147464099381317116075056 :=
  phase_of_block (n := 451) (by decide +kernel) rc_2_5_2361_1_join2
private theorem receipt_2_5 : B1Checked (bank 2 5) 6 0 7 := by
  refine b1_checked_from_values (bank 2 5) 6 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2125_450)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_5_2360_0 rc_2_5_2360_1 rc_2_5_2361_0 rc_2_5_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2549_540_part0 :
    blockEstimate 2549 540 540 128 = 877853600 := by decide +kernel
private theorem mom_2549_540_part1 :
    blockEstimate 2549 540 668 128 = 5792353184 := by decide +kernel
private theorem mom_2549_540_part2 :
    blockEstimate 2549 540 796 128 = 14841387936 := by decide +kernel
private theorem mom_2549_540_part3 :
    blockEstimate 2549 540 924 128 = 27219651488 := by decide +kernel
private theorem mom_2549_540_part4 :
    blockEstimate 2549 540 1052 128 = 41799453047 := by decide +kernel
private theorem mom_2549_540_part5 :
    blockEstimate 2549 540 1180 128 = 55433335616 := by decide +kernel
private theorem mom_2549_540_part6 :
    blockEstimate 2549 540 1308 128 = 66805519168 := by decide +kernel
private theorem mom_2549_540_part7 :
    blockEstimate 2549 540 1436 128 = 75908584256 := by decide +kernel
private theorem mom_2549_540_part8 :
    blockEstimate 2549 540 1564 128 = 82742530880 := by decide +kernel
private theorem mom_2549_540_part9 :
    blockEstimate 2549 540 1692 128 = 87307359040 := by decide +kernel
private theorem mom_2549_540_part10 :
    blockEstimate 2549 540 1820 128 = 89603068736 := by decide +kernel
private theorem mom_2549_540_part11 :
    blockEstimate 2549 540 1948 128 = 89629659968 := by decide +kernel
private theorem mom_2549_540_part12 :
    blockEstimate 2549 540 2076 128 = 87387132736 := by decide +kernel
private theorem mom_2549_540_part13 :
    blockEstimate 2549 540 2204 128 = 82875487040 := by decide +kernel
private theorem mom_2549_540_part14 :
    blockEstimate 2549 540 2332 128 = 76094722880 := by decide +kernel
private theorem mom_2549_540_part15 :
    blockEstimate 2549 540 2460 128 = 67052599096 := by decide +kernel
private theorem mom_2549_540_part16 :
    blockEstimate 2549 540 2588 128 = 56365397576 := by decide +kernel
private theorem mom_2549_540_part17 :
    blockEstimate 2549 540 2716 128 = 45336770782 := by decide +kernel
private theorem mom_2549_540_part18 :
    blockEstimate 2549 540 2844 128 = 34587354458 := by decide +kernel
private theorem mom_2549_540_part19 :
    blockEstimate 2549 540 2972 128 = 24610579002 := by decide +kernel
private theorem mom_2549_540_part20 :
    blockEstimate 2549 540 3100 128 = 15803337168 := by decide +kernel
private theorem mom_2549_540_part21 :
    blockEstimate 2549 540 3228 128 = 8659215824 := by decide +kernel
private theorem mom_2549_540_part22 :
    blockEstimate 2549 540 3356 128 = 3523838416 := by decide +kernel
private theorem mom_2549_540_part23 :
    blockEstimate 2549 540 3484 128 = 648863184 := by decide +kernel
private theorem mom_2549_540_part24 :
    blockEstimate 2549 540 3612 17 = 1334375 := by decide +kernel
private theorem mom_2549_540_join0 :
    blockEstimate 2549 540 668 256 = 20633741120 :=
  block_append mom_2549_540_part1 mom_2549_540_part2 rfl rfl rfl
private theorem mom_2549_540_join1 :
    blockEstimate 2549 540 540 384 = 21511594720 :=
  block_append mom_2549_540_part0 mom_2549_540_join0 rfl rfl rfl
private theorem mom_2549_540_join2 :
    blockEstimate 2549 540 1052 256 = 97232788663 :=
  block_append mom_2549_540_part4 mom_2549_540_part5 rfl rfl rfl
private theorem mom_2549_540_join3 :
    blockEstimate 2549 540 924 384 = 124452440151 :=
  block_append mom_2549_540_part3 mom_2549_540_join2 rfl rfl rfl
private theorem mom_2549_540_join4 :
    blockEstimate 2549 540 540 768 = 145964034871 :=
  block_append mom_2549_540_join1 mom_2549_540_join3 rfl rfl rfl
private theorem mom_2549_540_join5 :
    blockEstimate 2549 540 1436 256 = 158651115136 :=
  block_append mom_2549_540_part7 mom_2549_540_part8 rfl rfl rfl
private theorem mom_2549_540_join6 :
    blockEstimate 2549 540 1308 384 = 225456634304 :=
  block_append mom_2549_540_part6 mom_2549_540_join5 rfl rfl rfl
private theorem mom_2549_540_join7 :
    blockEstimate 2549 540 1820 256 = 179232728704 :=
  block_append mom_2549_540_part10 mom_2549_540_part11 rfl rfl rfl
private theorem mom_2549_540_join8 :
    blockEstimate 2549 540 1692 384 = 266540087744 :=
  block_append mom_2549_540_part9 mom_2549_540_join7 rfl rfl rfl
private theorem mom_2549_540_join9 :
    blockEstimate 2549 540 1308 768 = 491996722048 :=
  block_append mom_2549_540_join6 mom_2549_540_join8 rfl rfl rfl
private theorem mom_2549_540_join10 :
    blockEstimate 2549 540 540 1536 = 637960756919 :=
  block_append mom_2549_540_join4 mom_2549_540_join9 rfl rfl rfl
private theorem mom_2549_540_join11 :
    blockEstimate 2549 540 2204 256 = 158970209920 :=
  block_append mom_2549_540_part13 mom_2549_540_part14 rfl rfl rfl
private theorem mom_2549_540_join12 :
    blockEstimate 2549 540 2076 384 = 246357342656 :=
  block_append mom_2549_540_part12 mom_2549_540_join11 rfl rfl rfl
private theorem mom_2549_540_join13 :
    blockEstimate 2549 540 2588 256 = 101702168358 :=
  block_append mom_2549_540_part16 mom_2549_540_part17 rfl rfl rfl
private theorem mom_2549_540_join14 :
    blockEstimate 2549 540 2460 384 = 168754767454 :=
  block_append mom_2549_540_part15 mom_2549_540_join13 rfl rfl rfl
private theorem mom_2549_540_join15 :
    blockEstimate 2549 540 2076 768 = 415112110110 :=
  block_append mom_2549_540_join12 mom_2549_540_join14 rfl rfl rfl
private theorem mom_2549_540_join16 :
    blockEstimate 2549 540 2972 256 = 40413916170 :=
  block_append mom_2549_540_part19 mom_2549_540_part20 rfl rfl rfl
private theorem mom_2549_540_join17 :
    blockEstimate 2549 540 2844 384 = 75001270628 :=
  block_append mom_2549_540_part18 mom_2549_540_join16 rfl rfl rfl
private theorem mom_2549_540_join18 :
    blockEstimate 2549 540 3228 256 = 12183054240 :=
  block_append mom_2549_540_part21 mom_2549_540_part22 rfl rfl rfl
private theorem mom_2549_540_join19 :
    blockEstimate 2549 540 3484 145 = 650197559 :=
  block_append mom_2549_540_part23 mom_2549_540_part24 rfl rfl rfl
private theorem mom_2549_540_join20 :
    blockEstimate 2549 540 3228 401 = 12833251799 :=
  block_append mom_2549_540_join18 mom_2549_540_join19 rfl rfl rfl
private theorem mom_2549_540_join21 :
    blockEstimate 2549 540 2844 785 = 87834522427 :=
  block_append mom_2549_540_join17 mom_2549_540_join20 rfl rfl rfl
private theorem mom_2549_540_join22 :
    blockEstimate 2549 540 2076 1553 = 502946632537 :=
  block_append mom_2549_540_join15 mom_2549_540_join21 rfl rfl rfl
private theorem mom_2549_540_join23 :
    blockEstimate 2549 540 540 3089 = 1140907389456 :=
  block_append mom_2549_540_join10 mom_2549_540_join22 rfl rfl rfl
private theorem mom_2549_540 : momentEstimate 2549 540 = 1140907389456 := mom_2549_540_join23
private theorem rc_2_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 0 128 = 124247495118296578663067520 := by decide +kernel
private theorem rc_2_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 128 128 = 84041124760828584974307200 := by decide +kernel
private theorem rc_2_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 256 128 = 49175440948628297488076150 := by decide +kernel
private theorem rc_2_6_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 384 128 = 19209906412827141687667819 := by decide +kernel
private theorem rc_2_6_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 512 29 = 658550611256132366286284 := by decide +kernel
private theorem rc_2_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 0 256 = 208288619879125163637374720 :=
  phaseBlock_append rc_2_6_2360_0_part0 rc_2_6_2360_0_part1 rfl rfl rfl
private theorem rc_2_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 384 157 = 19868457024083274053954103 :=
  phaseBlock_append rc_2_6_2360_0_part3 rc_2_6_2360_0_part4 rfl rfl rfl
private theorem rc_2_6_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 256 285 = 69043897972711571542030253 :=
  phaseBlock_append rc_2_6_2360_0_part2 rc_2_6_2360_0_join1 rfl rfl rfl
private theorem rc_2_6_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 0) 0 541 = 277332517851836735179404973 :=
  phaseBlock_append rc_2_6_2360_0_join0 rc_2_6_2360_0_join2 rfl rfl rfl
private theorem rc_2_6_2360_0 : fastPhase (bank 2 6).shape 179808 2360 9 1 0 7 0 = 277332517851836735179404973 :=
  phase_of_block (n := 541) (by decide +kernel) rc_2_6_2360_0_join3
private theorem rc_2_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 0 128 = 123915508843528062610072896 := by decide +kernel
private theorem rc_2_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 128 128 = 83751416673256098620990784 := by decide +kernel
private theorem rc_2_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 256 128 = 48924594128317001703979206 := by decide +kernel
private theorem rc_2_6_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 384 128 = 18994642192674741092633751 := by decide +kernel
private theorem rc_2_6_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 512 29 = 614397150162156286912740 := by decide +kernel
private theorem rc_2_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 0 256 = 207666925516784161231063680 :=
  phaseBlock_append rc_2_6_2360_1_part0 rc_2_6_2360_1_part1 rfl rfl rfl
private theorem rc_2_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 384 157 = 19609039342836897379546491 :=
  phaseBlock_append rc_2_6_2360_1_part3 rc_2_6_2360_1_part4 rfl rfl rfl
private theorem rc_2_6_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 256 285 = 68533633471153899083525697 :=
  phaseBlock_append rc_2_6_2360_1_part2 rc_2_6_2360_1_join1 rfl rfl rfl
private theorem rc_2_6_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2360 9 1 0 7 1) 0 541 = 276200558987938060314589377 :=
  phaseBlock_append rc_2_6_2360_1_join0 rc_2_6_2360_1_join2 rfl rfl rfl
private theorem rc_2_6_2360_1 : fastPhase (bank 2 6).shape 179808 2360 9 1 0 7 1 = 276200558987938060314589377 :=
  phase_of_block (n := 541) (by decide +kernel) rc_2_6_2360_1_join3
private theorem rc_2_6_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 0 128 = 124248582595425443762186400 := by decide +kernel
private theorem rc_2_6_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 128 128 = 84041755152473329750874272 := by decide +kernel
private theorem rc_2_6_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 256 128 = 49175743867026540579458597 := by decide +kernel
private theorem rc_2_6_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 384 128 = 19209998016137573292740114 := by decide +kernel
private theorem rc_2_6_2361_0_part4 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 512 29 = 658553028747267577967172 := by decide +kernel
private theorem rc_2_6_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 0 256 = 208290337747898773513060672 :=
  phaseBlock_append rc_2_6_2361_0_part0 rc_2_6_2361_0_part1 rfl rfl rfl
private theorem rc_2_6_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 384 157 = 19868551044884840870707286 :=
  phaseBlock_append rc_2_6_2361_0_part3 rc_2_6_2361_0_part4 rfl rfl rfl
private theorem rc_2_6_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 256 285 = 69044294911911381450165883 :=
  phaseBlock_append rc_2_6_2361_0_part2 rc_2_6_2361_0_join1 rfl rfl rfl
private theorem rc_2_6_2361_0_join3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 0) 0 541 = 277334632659810154963226555 :=
  phaseBlock_append rc_2_6_2361_0_join0 rc_2_6_2361_0_join2 rfl rfl rfl
private theorem rc_2_6_2361_0 : fastPhase (bank 2 6).shape 179808 2361 9 1 0 7 0 = 277334632659810154963226555 :=
  phase_of_block (n := 541) (by decide +kernel) rc_2_6_2361_0_join3
private theorem rc_2_6_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 0 128 = 123916593902272021133491936 := by decide +kernel
private theorem rc_2_6_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 128 128 = 83752045207299935932772064 := by decide +kernel
private theorem rc_2_6_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 256 128 = 48924895682744293237814630 := by decide +kernel
private theorem rc_2_6_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 384 128 = 18994732864085406852644087 := by decide +kernel
private theorem rc_2_6_2361_1_part4 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 512 29 = 614399409925363862788090 := by decide +kernel
private theorem rc_2_6_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 0 256 = 207668639109571957066264000 :=
  phaseBlock_append rc_2_6_2361_1_part0 rc_2_6_2361_1_part1 rfl rfl rfl
private theorem rc_2_6_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 384 157 = 19609132274010770715432177 :=
  phaseBlock_append rc_2_6_2361_1_part3 rc_2_6_2361_1_part4 rfl rfl rfl
private theorem rc_2_6_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 256 285 = 68534027956755063953246807 :=
  phaseBlock_append rc_2_6_2361_1_part2 rc_2_6_2361_1_join1 rfl rfl rfl
private theorem rc_2_6_2361_1_join3 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2361 9 1 0 7 1) 0 541 = 276202667066327021019510807 :=
  phaseBlock_append rc_2_6_2361_1_join0 rc_2_6_2361_1_join2 rfl rfl rfl
private theorem rc_2_6_2361_1 : fastPhase (bank 2 6).shape 179808 2361 9 1 0 7 1 = 276202667066327021019510807 :=
  phase_of_block (n := 541) (by decide +kernel) rc_2_6_2361_1_join3
private theorem receipt_2_6 : B1Checked (bank 2 6) 9 0 7 := by
  refine b1_checked_from_values (bank 2 6) 9 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2549_540)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_6_2360_0 rc_2_6_2360_1 rc_2_6_2361_0 rc_2_6_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_3090_655_part0 :
    blockEstimate 3090 655 655 128 = 1071401760 := by decide +kernel
private theorem mom_3090_655_part1 :
    blockEstimate 3090 655 783 128 = 7129324320 := by decide +kernel
private theorem mom_3090_655_part2 :
    blockEstimate 3090 655 911 128 = 18456341280 := by decide +kernel
private theorem mom_3090_655_part3 :
    blockEstimate 3090 655 1039 128 = 34247146272 := by decide +kernel
private theorem mom_3090_655_part4 :
    blockEstimate 3090 655 1167 128 = 53696432928 := by decide +kernel
private theorem mom_3090_655_part5 :
    blockEstimate 3090 655 1295 128 = 75433624132 := by decide +kernel
private theorem mom_3090_655_part6 :
    blockEstimate 3090 655 1423 128 = 95654435328 := by decide +kernel
private theorem mom_3090_655_part7 :
    blockEstimate 3090 655 1551 128 = 113125153280 := by decide +kernel
private theorem mom_3090_655_part8 :
    blockEstimate 3090 655 1679 128 = 127844407808 := by decide +kernel
private theorem mom_3090_655_part9 :
    blockEstimate 3090 655 1807 128 = 139812198912 := by decide +kernel
private theorem mom_3090_655_part10 :
    blockEstimate 3090 655 1935 128 = 149028526592 := by decide +kernel
private theorem mom_3090_655_part11 :
    blockEstimate 3090 655 2063 128 = 155493390848 := by decide +kernel
private theorem mom_3090_655_part12 :
    blockEstimate 3090 655 2191 128 = 159206791680 := by decide +kernel
private theorem mom_3090_655_part13 :
    blockEstimate 3090 655 2319 128 = 160168729088 := by decide +kernel
private theorem mom_3090_655_part14 :
    blockEstimate 3090 655 2447 128 = 158379203072 := by decide +kernel
private theorem mom_3090_655_part15 :
    blockEstimate 3090 655 2575 128 = 153838213632 := by decide +kernel
private theorem mom_3090_655_part16 :
    blockEstimate 3090 655 2703 128 = 146545760768 := by decide +kernel
private theorem mom_3090_655_part17 :
    blockEstimate 3090 655 2831 128 = 136501844480 := by decide +kernel
private theorem mom_3090_655_part18 :
    blockEstimate 3090 655 2959 128 = 123706464768 := by decide +kernel
private theorem mom_3090_655_part19 :
    blockEstimate 3090 655 3087 128 = 108475662127 := by decide +kernel
private theorem mom_3090_655_part20 :
    blockEstimate 3090 655 3215 128 = 92338108726 := by decide +kernel
private theorem mom_3090_655_part21 :
    blockEstimate 3090 655 3343 128 = 76161244685 := by decide +kernel
private theorem mom_3090_655_part22 :
    blockEstimate 3090 655 3471 128 = 60471251414 := by decide +kernel
private theorem mom_3090_655_part23 :
    blockEstimate 3090 655 3599 128 = 45755026539 := by decide +kernel
private theorem mom_3090_655_part24 :
    blockEstimate 3090 655 3727 128 = 32402010379 := by decide +kernel
private theorem mom_3090_655_part25 :
    blockEstimate 3090 655 3855 128 = 20879026736 := by decide +kernel
private theorem mom_3090_655_part26 :
    blockEstimate 3090 655 3983 128 = 11646768688 := by decide +kernel
private theorem mom_3090_655_part27 :
    blockEstimate 3090 655 4111 128 = 4959076912 := by decide +kernel
private theorem mom_3090_655_part28 :
    blockEstimate 3090 655 4239 128 = 1067609648 := by decide +kernel
private theorem mom_3090_655_part29 :
    blockEstimate 3090 655 4367 33 = 10507902 := by decide +kernel
private theorem mom_3090_655_join0 :
    blockEstimate 3090 655 783 256 = 25585665600 :=
  block_append mom_3090_655_part1 mom_3090_655_part2 rfl rfl rfl
private theorem mom_3090_655_join1 :
    blockEstimate 3090 655 655 384 = 26657067360 :=
  block_append mom_3090_655_part0 mom_3090_655_join0 rfl rfl rfl
private theorem mom_3090_655_join2 :
    blockEstimate 3090 655 1039 256 = 87943579200 :=
  block_append mom_3090_655_part3 mom_3090_655_part4 rfl rfl rfl
private theorem mom_3090_655_join3 :
    blockEstimate 3090 655 1295 256 = 171088059460 :=
  block_append mom_3090_655_part5 mom_3090_655_part6 rfl rfl rfl
private theorem mom_3090_655_join4 :
    blockEstimate 3090 655 1039 512 = 259031638660 :=
  block_append mom_3090_655_join2 mom_3090_655_join3 rfl rfl rfl
private theorem mom_3090_655_join5 :
    blockEstimate 3090 655 655 896 = 285688706020 :=
  block_append mom_3090_655_join1 mom_3090_655_join4 rfl rfl rfl
private theorem mom_3090_655_join6 :
    blockEstimate 3090 655 1551 256 = 240969561088 :=
  block_append mom_3090_655_part7 mom_3090_655_part8 rfl rfl rfl
private theorem mom_3090_655_join7 :
    blockEstimate 3090 655 1807 256 = 288840725504 :=
  block_append mom_3090_655_part9 mom_3090_655_part10 rfl rfl rfl
private theorem mom_3090_655_join8 :
    blockEstimate 3090 655 1551 512 = 529810286592 :=
  block_append mom_3090_655_join6 mom_3090_655_join7 rfl rfl rfl
private theorem mom_3090_655_join9 :
    blockEstimate 3090 655 2063 256 = 314700182528 :=
  block_append mom_3090_655_part11 mom_3090_655_part12 rfl rfl rfl
private theorem mom_3090_655_join10 :
    blockEstimate 3090 655 2319 256 = 318547932160 :=
  block_append mom_3090_655_part13 mom_3090_655_part14 rfl rfl rfl
private theorem mom_3090_655_join11 :
    blockEstimate 3090 655 2063 512 = 633248114688 :=
  block_append mom_3090_655_join9 mom_3090_655_join10 rfl rfl rfl
private theorem mom_3090_655_join12 :
    blockEstimate 3090 655 1551 1024 = 1163058401280 :=
  block_append mom_3090_655_join8 mom_3090_655_join11 rfl rfl rfl
private theorem mom_3090_655_join13 :
    blockEstimate 3090 655 655 1920 = 1448747107300 :=
  block_append mom_3090_655_join5 mom_3090_655_join12 rfl rfl rfl
private theorem mom_3090_655_join14 :
    blockEstimate 3090 655 2703 256 = 283047605248 :=
  block_append mom_3090_655_part16 mom_3090_655_part17 rfl rfl rfl
private theorem mom_3090_655_join15 :
    blockEstimate 3090 655 2575 384 = 436885818880 :=
  block_append mom_3090_655_part15 mom_3090_655_join14 rfl rfl rfl
private theorem mom_3090_655_join16 :
    blockEstimate 3090 655 2959 256 = 232182126895 :=
  block_append mom_3090_655_part18 mom_3090_655_part19 rfl rfl rfl
private theorem mom_3090_655_join17 :
    blockEstimate 3090 655 3215 256 = 168499353411 :=
  block_append mom_3090_655_part20 mom_3090_655_part21 rfl rfl rfl
private theorem mom_3090_655_join18 :
    blockEstimate 3090 655 2959 512 = 400681480306 :=
  block_append mom_3090_655_join16 mom_3090_655_join17 rfl rfl rfl
private theorem mom_3090_655_join19 :
    blockEstimate 3090 655 2575 896 = 837567299186 :=
  block_append mom_3090_655_join15 mom_3090_655_join18 rfl rfl rfl
private theorem mom_3090_655_join20 :
    blockEstimate 3090 655 3471 256 = 106226277953 :=
  block_append mom_3090_655_part22 mom_3090_655_part23 rfl rfl rfl
private theorem mom_3090_655_join21 :
    blockEstimate 3090 655 3727 256 = 53281037115 :=
  block_append mom_3090_655_part24 mom_3090_655_part25 rfl rfl rfl
private theorem mom_3090_655_join22 :
    blockEstimate 3090 655 3471 512 = 159507315068 :=
  block_append mom_3090_655_join20 mom_3090_655_join21 rfl rfl rfl
private theorem mom_3090_655_join23 :
    blockEstimate 3090 655 3983 256 = 16605845600 :=
  block_append mom_3090_655_part26 mom_3090_655_part27 rfl rfl rfl
private theorem mom_3090_655_join24 :
    blockEstimate 3090 655 4239 161 = 1078117550 :=
  block_append mom_3090_655_part28 mom_3090_655_part29 rfl rfl rfl
private theorem mom_3090_655_join25 :
    blockEstimate 3090 655 3983 417 = 17683963150 :=
  block_append mom_3090_655_join23 mom_3090_655_join24 rfl rfl rfl
private theorem mom_3090_655_join26 :
    blockEstimate 3090 655 3471 929 = 177191278218 :=
  block_append mom_3090_655_join22 mom_3090_655_join25 rfl rfl rfl
private theorem mom_3090_655_join27 :
    blockEstimate 3090 655 2575 1825 = 1014758577404 :=
  block_append mom_3090_655_join19 mom_3090_655_join26 rfl rfl rfl
private theorem mom_3090_655_join28 :
    blockEstimate 3090 655 655 3745 = 2463505684704 :=
  block_append mom_3090_655_join13 mom_3090_655_join27 rfl rfl rfl
private theorem mom_3090_655 : momentEstimate 3090 655 = 2463505684704 := mom_3090_655_join28
private theorem rc_2_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 0 128 = 329781155536028417303786528 := by decide +kernel
private theorem rc_2_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 128 128 = 242221399922830690810242080 := by decide +kernel
private theorem rc_2_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 256 128 = 164251342338608156090888062 := by decide +kernel
private theorem rc_2_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 384 128 = 95221862397521441211014453 := by decide +kernel
private theorem rc_2_7_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 512 128 = 34505515005799846195708264 := by decide +kernel
private theorem rc_2_7_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 640 16 = 434353775670597154228278 := by decide +kernel
private theorem rc_2_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 128 256 = 406472742261438846901130142 :=
  phaseBlock_append rc_2_7_2360_0_part1 rc_2_7_2360_0_part2 rfl rfl rfl
private theorem rc_2_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 0 384 = 736253897797467264204916670 :=
  phaseBlock_append rc_2_7_2360_0_part0 rc_2_7_2360_0_join0 rfl rfl rfl
private theorem rc_2_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 512 144 = 34939868781470443349936542 :=
  phaseBlock_append rc_2_7_2360_0_part4 rc_2_7_2360_0_part5 rfl rfl rfl
private theorem rc_2_7_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 384 272 = 130161731178991884560950995 :=
  phaseBlock_append rc_2_7_2360_0_part3 rc_2_7_2360_0_join2 rfl rfl rfl
private theorem rc_2_7_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 0) 0 656 = 866415628976459148765867665 :=
  phaseBlock_append rc_2_7_2360_0_join1 rc_2_7_2360_0_join3 rfl rfl rfl
private theorem rc_2_7_2360_0 : fastPhase (bank 2 7).shape 179808 2360 13 1 0 7 0 = 866415628976459148765867665 :=
  phase_of_block (n := 656) (by decide +kernel) rc_2_7_2360_0_join4
private theorem rc_2_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 0 128 = 329066941882507234868502432 := by decide +kernel
private theorem rc_2_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 128 128 = 241582542531131723470147488 := by decide +kernel
private theorem rc_2_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 256 128 = 163682823886121236351228460 := by decide +kernel
private theorem rc_2_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 384 128 = 94718833695636889483868146 := by decide +kernel
private theorem rc_2_7_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 512 128 = 34063291632368382951798458 := by decide +kernel
private theorem rc_2_7_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 640 16 = 383124328044969942906868 := by decide +kernel
private theorem rc_2_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 128 256 = 405265366417252959821375948 :=
  phaseBlock_append rc_2_7_2360_1_part1 rc_2_7_2360_1_part2 rfl rfl rfl
private theorem rc_2_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 0 384 = 734332308299760194689878380 :=
  phaseBlock_append rc_2_7_2360_1_part0 rc_2_7_2360_1_join0 rfl rfl rfl
private theorem rc_2_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 512 144 = 34446415960413352894705326 :=
  phaseBlock_append rc_2_7_2360_1_part4 rc_2_7_2360_1_part5 rfl rfl rfl
private theorem rc_2_7_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 384 272 = 129165249656050242378573472 :=
  phaseBlock_append rc_2_7_2360_1_part3 rc_2_7_2360_1_join2 rfl rfl rfl
private theorem rc_2_7_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2360 13 1 0 7 1) 0 656 = 863497557955810437068451852 :=
  phaseBlock_append rc_2_7_2360_1_join1 rc_2_7_2360_1_join3 rfl rfl rfl
private theorem rc_2_7_2360_1 : fastPhase (bank 2 7).shape 179808 2360 13 1 0 7 1 = 863497557955810437068451852 :=
  phase_of_block (n := 656) (by decide +kernel) rc_2_7_2360_1_join4
private theorem rc_2_7_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 0 128 = 329784066137960375534038720 := by decide +kernel
private theorem rc_2_7_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 128 128 = 242223289730356490664103616 := by decide +kernel
private theorem rc_2_7_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 256 128 = 164252445605816025045766878 := by decide +kernel
private theorem rc_2_7_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 384 128 = 95222391866162805939998358 := by decide +kernel
private theorem rc_2_7_2361_0_part4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 512 128 = 34505666947991827617505955 := by decide +kernel
private theorem rc_2_7_2361_0_part5 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 640 16 = 434355299577014092967364 := by decide +kernel
private theorem rc_2_7_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 128 256 = 406475735336172515709870494 :=
  phaseBlock_append rc_2_7_2361_0_part1 rc_2_7_2361_0_part2 rfl rfl rfl
private theorem rc_2_7_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 0 384 = 736259801474132891243909214 :=
  phaseBlock_append rc_2_7_2361_0_part0 rc_2_7_2361_0_join0 rfl rfl rfl
private theorem rc_2_7_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 512 144 = 34940022247568841710473319 :=
  phaseBlock_append rc_2_7_2361_0_part4 rc_2_7_2361_0_part5 rfl rfl rfl
private theorem rc_2_7_2361_0_join3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 384 272 = 130162414113731647650471677 :=
  phaseBlock_append rc_2_7_2361_0_part3 rc_2_7_2361_0_join2 rfl rfl rfl
private theorem rc_2_7_2361_0_join4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 0) 0 656 = 866422215587864538894380891 :=
  phaseBlock_append rc_2_7_2361_0_join1 rc_2_7_2361_0_join3 rfl rfl rfl
private theorem rc_2_7_2361_0 : fastPhase (bank 2 7).shape 179808 2361 13 1 0 7 0 = 866422215587864538894380891 :=
  phase_of_block (n := 656) (by decide +kernel) rc_2_7_2361_0_join4
private theorem rc_2_7_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 0 128 = 329069847246126768141881088 := by decide +kernel
private theorem rc_2_7_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 128 128 = 241584428105774647206285056 := by decide +kernel
private theorem rc_2_7_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 256 128 = 163683923825071981571621624 := by decide +kernel
private theorem rc_2_7_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 384 128 = 94719360651049791458542378 := by decide +kernel
private theorem rc_2_7_2361_1_part4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 512 128 = 34063441784714380465320537 := by decide +kernel
private theorem rc_2_7_2361_1_part5 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 640 16 = 383125674474913990705128 := by decide +kernel
private theorem rc_2_7_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 128 256 = 405268351930846628777906680 :=
  phaseBlock_append rc_2_7_2361_1_part1 rc_2_7_2361_1_part2 rfl rfl rfl
private theorem rc_2_7_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 0 384 = 734338199176973396919787768 :=
  phaseBlock_append rc_2_7_2361_1_part0 rc_2_7_2361_1_join0 rfl rfl rfl
private theorem rc_2_7_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 512 144 = 34446567459189294456025665 :=
  phaseBlock_append rc_2_7_2361_1_part4 rc_2_7_2361_1_part5 rfl rfl rfl
private theorem rc_2_7_2361_1_join3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 384 272 = 129165928110239085914568043 :=
  phaseBlock_append rc_2_7_2361_1_part3 rc_2_7_2361_1_join2 rfl rfl rfl
private theorem rc_2_7_2361_1_join4 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2361 13 1 0 7 1) 0 656 = 863504127287212482834355811 :=
  phaseBlock_append rc_2_7_2361_1_join1 rc_2_7_2361_1_join3 rfl rfl rfl
private theorem rc_2_7_2361_1 : fastPhase (bank 2 7).shape 179808 2361 13 1 0 7 1 = 863504127287212482834355811 :=
  phase_of_block (n := 656) (by decide +kernel) rc_2_7_2361_1_join4
private theorem receipt_2_7 : B1Checked (bank 2 7) 13 0 7 := by
  refine b1_checked_from_values (bank 2 7) 13 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_3090_655)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_7_2360_0 rc_2_7_2360_1 rc_2_7_2361_0 rc_2_7_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_3136_665_part0 :
    blockEstimate 3136 665 665 128 = 1087858720 := by decide +kernel
private theorem mom_3136_665_part1 :
    blockEstimate 3136 665 793 128 = 7243003936 := by decide +kernel
private theorem mom_3136_665_part2 :
    blockEstimate 3136 665 921 128 = 18763712544 := by decide +kernel
private theorem mom_3136_665_part3 :
    blockEstimate 3136 665 1049 128 = 34844678176 := by decide +kernel
private theorem mom_3136_665_part4 :
    blockEstimate 3136 665 1177 128 = 54680594464 := by decide +kernel
private theorem mom_3136_665_part5 :
    blockEstimate 3136 665 1305 128 = 77030152538 := by decide +kernel
private theorem mom_3136_665_part6 :
    blockEstimate 3136 665 1433 128 = 98110623168 := by decide +kernel
private theorem mom_3136_665_part7 :
    blockEstimate 3136 665 1561 128 = 116404161984 := by decide +kernel
private theorem mom_3136_665_part8 :
    blockEstimate 3136 665 1689 128 = 131904294336 := by decide +kernel
private theorem mom_3136_665_part9 :
    blockEstimate 3136 665 1817 128 = 144611020224 := by decide +kernel
private theorem mom_3136_665_part10 :
    blockEstimate 3136 665 1945 128 = 154524339648 := by decide +kernel
private theorem mom_3136_665_part11 :
    blockEstimate 3136 665 2073 128 = 161644252608 := by decide +kernel
private theorem mom_3136_665_part12 :
    blockEstimate 3136 665 2201 128 = 165970759104 := by decide +kernel
private theorem mom_3136_665_part13 :
    blockEstimate 3136 665 2329 128 = 167503859136 := by decide +kernel
private theorem mom_3136_665_part14 :
    blockEstimate 3136 665 2457 128 = 166243552704 := by decide +kernel
private theorem mom_3136_665_part15 :
    blockEstimate 3136 665 2585 128 = 162189839808 := by decide +kernel
private theorem mom_3136_665_part16 :
    blockEstimate 3136 665 2713 128 = 155342720448 := by decide +kernel
private theorem mom_3136_665_part17 :
    blockEstimate 3136 665 2841 128 = 145702194624 := by decide +kernel
private theorem mom_3136_665_part18 :
    blockEstimate 3136 665 2969 128 = 133268262336 := by decide +kernel
private theorem mom_3136_665_part19 :
    blockEstimate 3136 665 3097 128 = 118154722097 := by decide +kernel
private theorem mom_3136_665_part20 :
    blockEstimate 3136 665 3225 128 = 101659620403 := by decide +kernel
private theorem mom_3136_665_part21 :
    blockEstimate 3136 665 3353 128 = 84947593966 := by decide +kernel
private theorem mom_3136_665_part22 :
    blockEstimate 3136 665 3481 128 = 68565240813 := by decide +kernel
private theorem mom_3136_665_part23 :
    blockEstimate 3136 665 3609 128 = 53012098460 := by decide +kernel
private theorem mom_3136_665_part24 :
    blockEstimate 3136 665 3737 128 = 38725218584 := by decide +kernel
private theorem mom_3136_665_part25 :
    blockEstimate 3136 665 3865 128 = 26082852272 := by decide +kernel
private theorem mom_3136_665_part26 :
    blockEstimate 3136 665 3993 128 = 15637674416 := by decide +kernel
private theorem mom_3136_665_part27 :
    blockEstimate 3136 665 4121 128 = 7675196848 := by decide +kernel
private theorem mom_3136_665_part28 :
    blockEstimate 3136 665 4249 128 = 2447077808 := by decide +kernel
private theorem mom_3136_665_part29 :
    blockEstimate 3136 665 4377 89 = 191128367 := by decide +kernel
private theorem mom_3136_665_join0 :
    blockEstimate 3136 665 793 256 = 26006716480 :=
  block_append mom_3136_665_part1 mom_3136_665_part2 rfl rfl rfl
private theorem mom_3136_665_join1 :
    blockEstimate 3136 665 665 384 = 27094575200 :=
  block_append mom_3136_665_part0 mom_3136_665_join0 rfl rfl rfl
private theorem mom_3136_665_join2 :
    blockEstimate 3136 665 1049 256 = 89525272640 :=
  block_append mom_3136_665_part3 mom_3136_665_part4 rfl rfl rfl
private theorem mom_3136_665_join3 :
    blockEstimate 3136 665 1305 256 = 175140775706 :=
  block_append mom_3136_665_part5 mom_3136_665_part6 rfl rfl rfl
private theorem mom_3136_665_join4 :
    blockEstimate 3136 665 1049 512 = 264666048346 :=
  block_append mom_3136_665_join2 mom_3136_665_join3 rfl rfl rfl
private theorem mom_3136_665_join5 :
    blockEstimate 3136 665 665 896 = 291760623546 :=
  block_append mom_3136_665_join1 mom_3136_665_join4 rfl rfl rfl
private theorem mom_3136_665_join6 :
    blockEstimate 3136 665 1561 256 = 248308456320 :=
  block_append mom_3136_665_part7 mom_3136_665_part8 rfl rfl rfl
private theorem mom_3136_665_join7 :
    blockEstimate 3136 665 1817 256 = 299135359872 :=
  block_append mom_3136_665_part9 mom_3136_665_part10 rfl rfl rfl
private theorem mom_3136_665_join8 :
    blockEstimate 3136 665 1561 512 = 547443816192 :=
  block_append mom_3136_665_join6 mom_3136_665_join7 rfl rfl rfl
private theorem mom_3136_665_join9 :
    blockEstimate 3136 665 2073 256 = 327615011712 :=
  block_append mom_3136_665_part11 mom_3136_665_part12 rfl rfl rfl
private theorem mom_3136_665_join10 :
    blockEstimate 3136 665 2329 256 = 333747411840 :=
  block_append mom_3136_665_part13 mom_3136_665_part14 rfl rfl rfl
private theorem mom_3136_665_join11 :
    blockEstimate 3136 665 2073 512 = 661362423552 :=
  block_append mom_3136_665_join9 mom_3136_665_join10 rfl rfl rfl
private theorem mom_3136_665_join12 :
    blockEstimate 3136 665 1561 1024 = 1208806239744 :=
  block_append mom_3136_665_join8 mom_3136_665_join11 rfl rfl rfl
private theorem mom_3136_665_join13 :
    blockEstimate 3136 665 665 1920 = 1500566863290 :=
  block_append mom_3136_665_join5 mom_3136_665_join12 rfl rfl rfl
private theorem mom_3136_665_join14 :
    blockEstimate 3136 665 2713 256 = 301044915072 :=
  block_append mom_3136_665_part16 mom_3136_665_part17 rfl rfl rfl
private theorem mom_3136_665_join15 :
    blockEstimate 3136 665 2585 384 = 463234754880 :=
  block_append mom_3136_665_part15 mom_3136_665_join14 rfl rfl rfl
private theorem mom_3136_665_join16 :
    blockEstimate 3136 665 2969 256 = 251422984433 :=
  block_append mom_3136_665_part18 mom_3136_665_part19 rfl rfl rfl
private theorem mom_3136_665_join17 :
    blockEstimate 3136 665 3225 256 = 186607214369 :=
  block_append mom_3136_665_part20 mom_3136_665_part21 rfl rfl rfl
private theorem mom_3136_665_join18 :
    blockEstimate 3136 665 2969 512 = 438030198802 :=
  block_append mom_3136_665_join16 mom_3136_665_join17 rfl rfl rfl
private theorem mom_3136_665_join19 :
    blockEstimate 3136 665 2585 896 = 901264953682 :=
  block_append mom_3136_665_join15 mom_3136_665_join18 rfl rfl rfl
private theorem mom_3136_665_join20 :
    blockEstimate 3136 665 3481 256 = 121577339273 :=
  block_append mom_3136_665_part22 mom_3136_665_part23 rfl rfl rfl
private theorem mom_3136_665_join21 :
    blockEstimate 3136 665 3737 256 = 64808070856 :=
  block_append mom_3136_665_part24 mom_3136_665_part25 rfl rfl rfl
private theorem mom_3136_665_join22 :
    blockEstimate 3136 665 3481 512 = 186385410129 :=
  block_append mom_3136_665_join20 mom_3136_665_join21 rfl rfl rfl
private theorem mom_3136_665_join23 :
    blockEstimate 3136 665 3993 256 = 23312871264 :=
  block_append mom_3136_665_part26 mom_3136_665_part27 rfl rfl rfl
private theorem mom_3136_665_join24 :
    blockEstimate 3136 665 4249 217 = 2638206175 :=
  block_append mom_3136_665_part28 mom_3136_665_part29 rfl rfl rfl
private theorem mom_3136_665_join25 :
    blockEstimate 3136 665 3993 473 = 25951077439 :=
  block_append mom_3136_665_join23 mom_3136_665_join24 rfl rfl rfl
private theorem mom_3136_665_join26 :
    blockEstimate 3136 665 3481 985 = 212336487568 :=
  block_append mom_3136_665_join22 mom_3136_665_join25 rfl rfl rfl
private theorem mom_3136_665_join27 :
    blockEstimate 3136 665 2585 1881 = 1113601441250 :=
  block_append mom_3136_665_join19 mom_3136_665_join26 rfl rfl rfl
private theorem mom_3136_665_join28 :
    blockEstimate 3136 665 665 3801 = 2614168304540 :=
  block_append mom_3136_665_join13 mom_3136_665_join27 rfl rfl rfl
private theorem mom_3136_665 : momentEstimate 3136 665 = 2614168304540 := mom_3136_665_join28
private theorem rc_2_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 0 128 = 1051958183777756009871685632 := by decide +kernel
private theorem rc_2_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 128 128 = 781232104689197147678103552 := by decide +kernel
private theorem rc_2_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 256 128 = 537501471487320806526553122 := by decide +kernel
private theorem rc_2_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 384 128 = 319192182921517810054831968 := by decide +kernel
private theorem rc_2_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 512 128 = 124764829955652972111810252 := by decide +kernel
private theorem rc_2_8_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 640 26 = 3619684804228904662183037 := by decide +kernel
private theorem rc_2_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 128 256 = 1318733576176517954204656674 :=
  phaseBlock_append rc_2_8_2360_0_part1 rc_2_8_2360_0_part2 rfl rfl rfl
private theorem rc_2_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 0 384 = 2370691759954273964076342306 :=
  phaseBlock_append rc_2_8_2360_0_part0 rc_2_8_2360_0_join0 rfl rfl rfl
private theorem rc_2_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 512 154 = 128384514759881876773993289 :=
  phaseBlock_append rc_2_8_2360_0_part4 rc_2_8_2360_0_part5 rfl rfl rfl
private theorem rc_2_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 384 282 = 447576697681399686828825257 :=
  phaseBlock_append rc_2_8_2360_0_part3 rc_2_8_2360_0_join2 rfl rfl rfl
private theorem rc_2_8_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 0) 0 666 = 2818268457635673650905167563 :=
  phaseBlock_append rc_2_8_2360_0_join1 rc_2_8_2360_0_join3 rfl rfl rfl
private theorem rc_2_8_2360_0 : fastPhase (bank 2 8).shape 179808 2360 19 1 0 7 0 = 2818268457635673650905167563 :=
  phase_of_block (n := 666) (by decide +kernel) rc_2_8_2360_0_join4
private theorem rc_2_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 0 128 = 1049761824445635695425946880 := by decide +kernel
private theorem rc_2_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 128 128 = 779246347090018265734440192 := by decide +kernel
private theorem rc_2_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 256 128 = 535714237134904031259389047 := by decide +kernel
private theorem rc_2_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 384 128 = 317591664292996871138323774 := by decide +kernel
private theorem rc_2_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 512 128 = 123339485127710233838872465 := by decide +kernel
private theorem rc_2_8_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 640 26 = 3350550155963744304788385 := by decide +kernel
private theorem rc_2_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 128 256 = 1314960584224922296993829239 :=
  phaseBlock_append rc_2_8_2360_1_part1 rc_2_8_2360_1_part2 rfl rfl rfl
private theorem rc_2_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 0 384 = 2364722408670557992419776119 :=
  phaseBlock_append rc_2_8_2360_1_part0 rc_2_8_2360_1_join0 rfl rfl rfl
private theorem rc_2_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 512 154 = 126690035283673978143660850 :=
  phaseBlock_append rc_2_8_2360_1_part4 rc_2_8_2360_1_part5 rfl rfl rfl
private theorem rc_2_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 384 282 = 444281699576670849281984624 :=
  phaseBlock_append rc_2_8_2360_1_part3 rc_2_8_2360_1_join2 rfl rfl rfl
private theorem rc_2_8_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2360 19 1 0 7 1) 0 666 = 2809004108247228841701760743 :=
  phaseBlock_append rc_2_8_2360_1_join1 rc_2_8_2360_1_join3 rfl rfl rfl
private theorem rc_2_8_2360_1 : fastPhase (bank 2 8).shape 179808 2360 19 1 0 7 1 = 2809004108247228841701760743 :=
  phase_of_block (n := 666) (by decide +kernel) rc_2_8_2360_1_join4
private theorem rc_2_8_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 0 128 = 1051967409921265574380441728 := by decide +kernel
private theorem rc_2_8_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 128 128 = 781238167226763509224312960 := by decide +kernel
private theorem rc_2_8_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 256 128 = 537505067502147766499524893 := by decide +kernel
private theorem rc_2_8_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 384 128 = 319193954174255787884057171 := by decide +kernel
private theorem rc_2_8_2361_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 512 128 = 124765378378042076802521548 := by decide +kernel
private theorem rc_2_8_2361_0_part5 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 640 26 = 3619697472378011617153442 := by decide +kernel
private theorem rc_2_8_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 128 256 = 1318743234728911275723837853 :=
  phaseBlock_append rc_2_8_2361_0_part1 rc_2_8_2361_0_part2 rfl rfl rfl
private theorem rc_2_8_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 0 384 = 2370710644650176850104279581 :=
  phaseBlock_append rc_2_8_2361_0_part0 rc_2_8_2361_0_join0 rfl rfl rfl
private theorem rc_2_8_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 512 154 = 128385075850420088419674990 :=
  phaseBlock_append rc_2_8_2361_0_part4 rc_2_8_2361_0_part5 rfl rfl rfl
private theorem rc_2_8_2361_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 384 282 = 447579030024675876303732161 :=
  phaseBlock_append rc_2_8_2361_0_part3 rc_2_8_2361_0_join2 rfl rfl rfl
private theorem rc_2_8_2361_0_join4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 0) 0 666 = 2818289674674852726408011742 :=
  phaseBlock_append rc_2_8_2361_0_join1 rc_2_8_2361_0_join3 rfl rfl rfl
private theorem rc_2_8_2361_0 : fastPhase (bank 2 8).shape 179808 2361 19 1 0 7 0 = 2818289674674852726408011742 :=
  phase_of_block (n := 666) (by decide +kernel) rc_2_8_2361_0_join4
private theorem rc_2_8_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 0 128 = 1049771034663015451904508160 := by decide +kernel
private theorem rc_2_8_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 128 128 = 779252396598009198105018624 := by decide +kernel
private theorem rc_2_8_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 256 128 = 535717822767993516516717201 := by decide +kernel
private theorem rc_2_8_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 384 128 = 317593427592288894400066804 := by decide +kernel
private theorem rc_2_8_2361_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 512 128 = 123340027792119947778932494 := by decide +kernel
private theorem rc_2_8_2361_1_part5 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 640 26 = 3350561901304462727115254 := by decide +kernel
private theorem rc_2_8_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 128 256 = 1314970219366002714621735825 :=
  phaseBlock_append rc_2_8_2361_1_part1 rc_2_8_2361_1_part2 rfl rfl rfl
private theorem rc_2_8_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 0 384 = 2364741254029018166526243985 :=
  phaseBlock_append rc_2_8_2361_1_part0 rc_2_8_2361_1_join0 rfl rfl rfl
private theorem rc_2_8_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 512 154 = 126690589693424410506047748 :=
  phaseBlock_append rc_2_8_2361_1_part4 rc_2_8_2361_1_part5 rfl rfl rfl
private theorem rc_2_8_2361_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 384 282 = 444284017285713304906114552 :=
  phaseBlock_append rc_2_8_2361_1_part3 rc_2_8_2361_1_join2 rfl rfl rfl
private theorem rc_2_8_2361_1_join4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2361 19 1 0 7 1) 0 666 = 2809025271314731471432358537 :=
  phaseBlock_append rc_2_8_2361_1_join1 rc_2_8_2361_1_join3 rfl rfl rfl
private theorem rc_2_8_2361_1 : fastPhase (bank 2 8).shape 179808 2361 19 1 0 7 1 = 2809025271314731471432358537 :=
  phase_of_block (n := 666) (by decide +kernel) rc_2_8_2361_1_join4
private theorem receipt_2_8 : B1Checked (bank 2 8) 19 0 7 := by
  refine b1_checked_from_values (bank 2 8) 19 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_3136_665)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_8_2360_0 rc_2_8_2360_1 rc_2_8_2361_0 rc_2_8_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_5265_1116_part0 :
    blockEstimate 5265 1116 1116 128 = 1849529760 := by decide +kernel
private theorem mom_5265_1116_part1 :
    blockEstimate 5265 1116 1244 128 = 12504393120 := by decide +kernel
private theorem mom_5265_1116_part2 :
    blockEstimate 5265 1116 1372 128 = 32989656480 := by decide +kernel
private theorem mom_5265_1116_part3 :
    blockEstimate 5265 1116 1500 128 = 62500013472 := by decide +kernel
private theorem mom_5265_1116_part4 :
    blockEstimate 5265 1116 1628 128 = 100230157728 := by decide +kernel
private theorem mom_5265_1116_part5 :
    blockEstimate 5265 1116 1756 128 = 145374782880 := by decide +kernel
private theorem mom_5265_1116_part6 :
    blockEstimate 5265 1116 1884 128 = 197128582560 := by decide +kernel
private theorem mom_5265_1116_part7 :
    blockEstimate 5265 1116 2012 128 = 254686250400 := by decide +kernel
private theorem mom_5265_1116_part8 :
    blockEstimate 5265 1116 2140 128 = 317210448207 := by decide +kernel
private theorem mom_5265_1116_part9 :
    blockEstimate 5265 1116 2268 128 = 381063995968 := by decide +kernel
private theorem mom_5265_1116_part10 :
    blockEstimate 5265 1116 2396 128 = 440779924032 := by decide +kernel
private theorem mom_5265_1116_part11 :
    blockEstimate 5265 1116 2524 128 = 495810814528 := by decide +kernel
private theorem mom_5265_1116_part12 :
    blockEstimate 5265 1116 2652 128 = 546156667456 := by decide +kernel
private theorem mom_5265_1116_part13 :
    blockEstimate 5265 1116 2780 128 = 591817482816 := by decide +kernel
private theorem mom_5265_1116_part14 :
    blockEstimate 5265 1116 2908 128 = 632793260608 := by decide +kernel
private theorem mom_5265_1116_part15 :
    blockEstimate 5265 1116 3036 128 = 669084000832 := by decide +kernel
private theorem mom_5265_1116_part16 :
    blockEstimate 5265 1116 3164 128 = 700689703488 := by decide +kernel
private theorem mom_5265_1116_part17 :
    blockEstimate 5265 1116 3292 128 = 727610368576 := by decide +kernel
private theorem mom_5265_1116_part18 :
    blockEstimate 5265 1116 3420 128 = 749845996096 := by decide +kernel
private theorem mom_5265_1116_part19 :
    blockEstimate 5265 1116 3548 128 = 767396586048 := by decide +kernel
private theorem mom_5265_1116_part20 :
    blockEstimate 5265 1116 3676 128 = 780262138432 := by decide +kernel
private theorem mom_5265_1116_part21 :
    blockEstimate 5265 1116 3804 128 = 788442653248 := by decide +kernel
private theorem mom_5265_1116_part22 :
    blockEstimate 5265 1116 3932 128 = 791938130496 := by decide +kernel
private theorem mom_5265_1116_part23 :
    blockEstimate 5265 1116 4060 128 = 790748570176 := by decide +kernel
private theorem mom_5265_1116_part24 :
    blockEstimate 5265 1116 4188 128 = 784873972288 := by decide +kernel
private theorem mom_5265_1116_part25 :
    blockEstimate 5265 1116 4316 128 = 774314336832 := by decide +kernel
private theorem mom_5265_1116_part26 :
    blockEstimate 5265 1116 4444 128 = 759069663808 := by decide +kernel
private theorem mom_5265_1116_part27 :
    blockEstimate 5265 1116 4572 128 = 739139953216 := by decide +kernel
private theorem mom_5265_1116_part28 :
    blockEstimate 5265 1116 4700 128 = 714525205056 := by decide +kernel
private theorem mom_5265_1116_part29 :
    blockEstimate 5265 1116 4828 128 = 685225419328 := by decide +kernel
private theorem mom_5265_1116_part30 :
    blockEstimate 5265 1116 4956 128 = 651240596032 := by decide +kernel
private theorem mom_5265_1116_part31 :
    blockEstimate 5265 1116 5084 128 = 612570735168 := by decide +kernel
private theorem mom_5265_1116_part32 :
    blockEstimate 5265 1116 5212 128 = 569327587125 := by decide +kernel
private theorem mom_5265_1116_part33 :
    blockEstimate 5265 1116 5340 128 = 523352535357 := by decide +kernel
private theorem mom_5265_1116_part34 :
    blockEstimate 5265 1116 5468 128 = 476478087524 := by decide +kernel
private theorem mom_5265_1116_part35 :
    blockEstimate 5265 1116 5596 128 = 429307369095 := by decide +kernel
private theorem mom_5265_1116_part36 :
    blockEstimate 5265 1116 5724 128 = 382384610207 := by decide +kernel
private theorem mom_5265_1116_part37 :
    blockEstimate 5265 1116 5852 128 = 336230971183 := by decide +kernel
private theorem mom_5265_1116_part38 :
    blockEstimate 5265 1116 5980 128 = 291344541906 := by decide +kernel
private theorem mom_5265_1116_part39 :
    blockEstimate 5265 1116 6108 128 = 248200340908 := by decide +kernel
private theorem mom_5265_1116_part40 :
    blockEstimate 5265 1116 6236 128 = 207250316963 := by decide +kernel
private theorem mom_5265_1116_part41 :
    blockEstimate 5265 1116 6364 128 = 168725087622 := by decide +kernel
private theorem mom_5265_1116_part42 :
    blockEstimate 5265 1116 6492 128 = 133109136016 := by decide +kernel
private theorem mom_5265_1116_part43 :
    blockEstimate 5265 1116 6620 128 = 101156867728 := by decide +kernel
private theorem mom_5265_1116_part44 :
    blockEstimate 5265 1116 6748 128 = 73125421712 := by decide +kernel
private theorem mom_5265_1116_part45 :
    blockEstimate 5265 1116 6876 128 = 49266456208 := by decide +kernel
private theorem mom_5265_1116_part46 :
    blockEstimate 5265 1116 7004 128 = 29831629456 := by decide +kernel
private theorem mom_5265_1116_part47 :
    blockEstimate 5265 1116 7132 128 = 15072599696 := by decide +kernel
private theorem mom_5265_1116_part48 :
    blockEstimate 5265 1116 7260 128 = 5241025168 := by decide +kernel
private theorem mom_5265_1116_part49 :
    blockEstimate 5265 1116 7388 109 = 586222182 := by decide +kernel
private theorem mom_5265_1116_join0 :
    blockEstimate 5265 1116 1244 256 = 45494049600 :=
  block_append mom_5265_1116_part1 mom_5265_1116_part2 rfl rfl rfl
private theorem mom_5265_1116_join1 :
    blockEstimate 5265 1116 1116 384 = 47343579360 :=
  block_append mom_5265_1116_part0 mom_5265_1116_join0 rfl rfl rfl
private theorem mom_5265_1116_join2 :
    blockEstimate 5265 1116 1628 256 = 245604940608 :=
  block_append mom_5265_1116_part4 mom_5265_1116_part5 rfl rfl rfl
private theorem mom_5265_1116_join3 :
    blockEstimate 5265 1116 1500 384 = 308104954080 :=
  block_append mom_5265_1116_part3 mom_5265_1116_join2 rfl rfl rfl
private theorem mom_5265_1116_join4 :
    blockEstimate 5265 1116 1116 768 = 355448533440 :=
  block_append mom_5265_1116_join1 mom_5265_1116_join3 rfl rfl rfl
private theorem mom_5265_1116_join5 :
    blockEstimate 5265 1116 2012 256 = 571896698607 :=
  block_append mom_5265_1116_part7 mom_5265_1116_part8 rfl rfl rfl
private theorem mom_5265_1116_join6 :
    blockEstimate 5265 1116 1884 384 = 769025281167 :=
  block_append mom_5265_1116_part6 mom_5265_1116_join5 rfl rfl rfl
private theorem mom_5265_1116_join7 :
    blockEstimate 5265 1116 2396 256 = 936590738560 :=
  block_append mom_5265_1116_part10 mom_5265_1116_part11 rfl rfl rfl
private theorem mom_5265_1116_join8 :
    blockEstimate 5265 1116 2268 384 = 1317654734528 :=
  block_append mom_5265_1116_part9 mom_5265_1116_join7 rfl rfl rfl
private theorem mom_5265_1116_join9 :
    blockEstimate 5265 1116 1884 768 = 2086680015695 :=
  block_append mom_5265_1116_join6 mom_5265_1116_join8 rfl rfl rfl
private theorem mom_5265_1116_join10 :
    blockEstimate 5265 1116 1116 1536 = 2442128549135 :=
  block_append mom_5265_1116_join4 mom_5265_1116_join9 rfl rfl rfl
private theorem mom_5265_1116_join11 :
    blockEstimate 5265 1116 2780 256 = 1224610743424 :=
  block_append mom_5265_1116_part13 mom_5265_1116_part14 rfl rfl rfl
private theorem mom_5265_1116_join12 :
    blockEstimate 5265 1116 2652 384 = 1770767410880 :=
  block_append mom_5265_1116_part12 mom_5265_1116_join11 rfl rfl rfl
private theorem mom_5265_1116_join13 :
    blockEstimate 5265 1116 3164 256 = 1428300072064 :=
  block_append mom_5265_1116_part16 mom_5265_1116_part17 rfl rfl rfl
private theorem mom_5265_1116_join14 :
    blockEstimate 5265 1116 3036 384 = 2097384072896 :=
  block_append mom_5265_1116_part15 mom_5265_1116_join13 rfl rfl rfl
private theorem mom_5265_1116_join15 :
    blockEstimate 5265 1116 2652 768 = 3868151483776 :=
  block_append mom_5265_1116_join12 mom_5265_1116_join14 rfl rfl rfl
private theorem mom_5265_1116_join16 :
    blockEstimate 5265 1116 3548 256 = 1547658724480 :=
  block_append mom_5265_1116_part19 mom_5265_1116_part20 rfl rfl rfl
private theorem mom_5265_1116_join17 :
    blockEstimate 5265 1116 3420 384 = 2297504720576 :=
  block_append mom_5265_1116_part18 mom_5265_1116_join16 rfl rfl rfl
private theorem mom_5265_1116_join18 :
    blockEstimate 5265 1116 3804 256 = 1580380783744 :=
  block_append mom_5265_1116_part21 mom_5265_1116_part22 rfl rfl rfl
private theorem mom_5265_1116_join19 :
    blockEstimate 5265 1116 4060 256 = 1575622542464 :=
  block_append mom_5265_1116_part23 mom_5265_1116_part24 rfl rfl rfl
private theorem mom_5265_1116_join20 :
    blockEstimate 5265 1116 3804 512 = 3156003326208 :=
  block_append mom_5265_1116_join18 mom_5265_1116_join19 rfl rfl rfl
private theorem mom_5265_1116_join21 :
    blockEstimate 5265 1116 3420 896 = 5453508046784 :=
  block_append mom_5265_1116_join17 mom_5265_1116_join20 rfl rfl rfl
private theorem mom_5265_1116_join22 :
    blockEstimate 5265 1116 2652 1664 = 9321659530560 :=
  block_append mom_5265_1116_join15 mom_5265_1116_join21 rfl rfl rfl
private theorem mom_5265_1116_join23 :
    blockEstimate 5265 1116 1116 3200 = 11763788079695 :=
  block_append mom_5265_1116_join10 mom_5265_1116_join22 rfl rfl rfl
private theorem mom_5265_1116_join24 :
    blockEstimate 5265 1116 4444 256 = 1498209617024 :=
  block_append mom_5265_1116_part26 mom_5265_1116_part27 rfl rfl rfl
private theorem mom_5265_1116_join25 :
    blockEstimate 5265 1116 4316 384 = 2272523953856 :=
  block_append mom_5265_1116_part25 mom_5265_1116_join24 rfl rfl rfl
private theorem mom_5265_1116_join26 :
    blockEstimate 5265 1116 4828 256 = 1336466015360 :=
  block_append mom_5265_1116_part29 mom_5265_1116_part30 rfl rfl rfl
private theorem mom_5265_1116_join27 :
    blockEstimate 5265 1116 4700 384 = 2050991220416 :=
  block_append mom_5265_1116_part28 mom_5265_1116_join26 rfl rfl rfl
private theorem mom_5265_1116_join28 :
    blockEstimate 5265 1116 4316 768 = 4323515174272 :=
  block_append mom_5265_1116_join25 mom_5265_1116_join27 rfl rfl rfl
private theorem mom_5265_1116_join29 :
    blockEstimate 5265 1116 5212 256 = 1092680122482 :=
  block_append mom_5265_1116_part32 mom_5265_1116_part33 rfl rfl rfl
private theorem mom_5265_1116_join30 :
    blockEstimate 5265 1116 5084 384 = 1705250857650 :=
  block_append mom_5265_1116_part31 mom_5265_1116_join29 rfl rfl rfl
private theorem mom_5265_1116_join31 :
    blockEstimate 5265 1116 5596 256 = 811691979302 :=
  block_append mom_5265_1116_part35 mom_5265_1116_part36 rfl rfl rfl
private theorem mom_5265_1116_join32 :
    blockEstimate 5265 1116 5468 384 = 1288170066826 :=
  block_append mom_5265_1116_part34 mom_5265_1116_join31 rfl rfl rfl
private theorem mom_5265_1116_join33 :
    blockEstimate 5265 1116 5084 768 = 2993420924476 :=
  block_append mom_5265_1116_join30 mom_5265_1116_join32 rfl rfl rfl
private theorem mom_5265_1116_join34 :
    blockEstimate 5265 1116 4316 1536 = 7316936098748 :=
  block_append mom_5265_1116_join28 mom_5265_1116_join33 rfl rfl rfl
private theorem mom_5265_1116_join35 :
    blockEstimate 5265 1116 5980 256 = 539544882814 :=
  block_append mom_5265_1116_part38 mom_5265_1116_part39 rfl rfl rfl
private theorem mom_5265_1116_join36 :
    blockEstimate 5265 1116 5852 384 = 875775853997 :=
  block_append mom_5265_1116_part37 mom_5265_1116_join35 rfl rfl rfl
private theorem mom_5265_1116_join37 :
    blockEstimate 5265 1116 6364 256 = 301834223638 :=
  block_append mom_5265_1116_part41 mom_5265_1116_part42 rfl rfl rfl
private theorem mom_5265_1116_join38 :
    blockEstimate 5265 1116 6236 384 = 509084540601 :=
  block_append mom_5265_1116_part40 mom_5265_1116_join37 rfl rfl rfl
private theorem mom_5265_1116_join39 :
    blockEstimate 5265 1116 5852 768 = 1384860394598 :=
  block_append mom_5265_1116_join36 mom_5265_1116_join38 rfl rfl rfl
private theorem mom_5265_1116_join40 :
    blockEstimate 5265 1116 6748 256 = 122391877920 :=
  block_append mom_5265_1116_part44 mom_5265_1116_part45 rfl rfl rfl
private theorem mom_5265_1116_join41 :
    blockEstimate 5265 1116 6620 384 = 223548745648 :=
  block_append mom_5265_1116_part43 mom_5265_1116_join40 rfl rfl rfl
private theorem mom_5265_1116_join42 :
    blockEstimate 5265 1116 7004 256 = 44904229152 :=
  block_append mom_5265_1116_part46 mom_5265_1116_part47 rfl rfl rfl
private theorem mom_5265_1116_join43 :
    blockEstimate 5265 1116 7260 237 = 5827247350 :=
  block_append mom_5265_1116_part48 mom_5265_1116_part49 rfl rfl rfl
private theorem mom_5265_1116_join44 :
    blockEstimate 5265 1116 7004 493 = 50731476502 :=
  block_append mom_5265_1116_join42 mom_5265_1116_join43 rfl rfl rfl
private theorem mom_5265_1116_join45 :
    blockEstimate 5265 1116 6620 877 = 274280222150 :=
  block_append mom_5265_1116_join41 mom_5265_1116_join44 rfl rfl rfl
private theorem mom_5265_1116_join46 :
    blockEstimate 5265 1116 5852 1645 = 1659140616748 :=
  block_append mom_5265_1116_join39 mom_5265_1116_join45 rfl rfl rfl
private theorem mom_5265_1116_join47 :
    blockEstimate 5265 1116 4316 3181 = 8976076715496 :=
  block_append mom_5265_1116_join34 mom_5265_1116_join46 rfl rfl rfl
private theorem mom_5265_1116_join48 :
    blockEstimate 5265 1116 1116 6381 = 20739864795191 :=
  block_append mom_5265_1116_join23 mom_5265_1116_join47 rfl rfl rfl
private theorem mom_5265_1116 : momentEstimate 5265 1116 = 20739864795191 := mom_5265_1116_join48
private theorem rc_2_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 0 128 = 4439120194869237793902019488 := by decide +kernel
private theorem rc_2_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 128 128 = 3752040717025661213885100960 := by decide +kernel
private theorem rc_2_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 256 128 = 3109456904825867800667562912 := by decide +kernel
private theorem rc_2_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 384 128 = 2509594245701973779171103648 := by decide +kernel
private theorem rc_2_9_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 512 128 = 1950714437197403108696724735 := by decide +kernel
private theorem rc_2_9_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 640 128 = 1431115956264467212348508568 := by decide +kernel
private theorem rc_2_9_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 768 128 = 949132556846837246420368182 := by decide +kernel
private theorem rc_2_9_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 896 128 = 503130008454294213959316720 := by decide +kernel
private theorem rc_2_9_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 1024 93 = 105470891725862154648041103 := by decide +kernel
private theorem rc_2_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 0 256 = 8191160911894899007787120448 :=
  phaseBlock_append rc_2_9_2360_0_part0 rc_2_9_2360_0_part1 rfl rfl rfl
private theorem rc_2_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 256 256 = 5619051150527841579838666560 :=
  phaseBlock_append rc_2_9_2360_0_part2 rc_2_9_2360_0_part3 rfl rfl rfl
private theorem rc_2_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 0 512 = 13810212062422740587625787008 :=
  phaseBlock_append rc_2_9_2360_0_join0 rc_2_9_2360_0_join1 rfl rfl rfl
private theorem rc_2_9_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 512 256 = 3381830393461870321045233303 :=
  phaseBlock_append rc_2_9_2360_0_part4 rc_2_9_2360_0_part5 rfl rfl rfl
private theorem rc_2_9_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 896 221 = 608600900180156368607357823 :=
  phaseBlock_append rc_2_9_2360_0_part7 rc_2_9_2360_0_part8 rfl rfl rfl
private theorem rc_2_9_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 768 349 = 1557733457026993615027726005 :=
  phaseBlock_append rc_2_9_2360_0_part6 rc_2_9_2360_0_join4 rfl rfl rfl
private theorem rc_2_9_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 512 605 = 4939563850488863936072959308 :=
  phaseBlock_append rc_2_9_2360_0_join3 rc_2_9_2360_0_join5 rfl rfl rfl
private theorem rc_2_9_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 0) 0 1117 = 18749775912911604523698746316 :=
  phaseBlock_append rc_2_9_2360_0_join2 rc_2_9_2360_0_join6 rfl rfl rfl
private theorem rc_2_9_2360_0 : fastPhase (bank 2 9).shape 179808 2360 28 1 0 7 0 = 18749775912911604523698746316 :=
  phase_of_block (n := 1117) (by decide +kernel) rc_2_9_2360_0_join7
private theorem rc_2_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 0 128 = 4433643945221731679802104352 := by decide +kernel
private theorem rc_2_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 128 128 = 3746909393895764387509152288 := by decide +kernel
private theorem rc_2_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 256 128 = 3104656882841074092645890592 := by decide +kernel
private theorem rc_2_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 384 128 = 2505112176928219725317065248 := by decide +kernel
private theorem rc_2_9_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 512 128 = 1946537248772536507318927821 := by decide +kernel
private theorem rc_2_9_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 640 128 = 1427230845697990553571808747 := by decide +kernel
private theorem rc_2_9_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 768 128 = 945526987004127911692756065 := by decide +kernel
private theorem rc_2_9_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 896 128 = 499791709932670506599990748 := by decide +kernel
private theorem rc_2_9_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 1024 93 = 103206196289785493800505958 := by decide +kernel
private theorem rc_2_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 0 256 = 8180553339117496067311256640 :=
  phaseBlock_append rc_2_9_2360_1_part0 rc_2_9_2360_1_part1 rfl rfl rfl
private theorem rc_2_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 256 256 = 5609769059769293817962955840 :=
  phaseBlock_append rc_2_9_2360_1_part2 rc_2_9_2360_1_part3 rfl rfl rfl
private theorem rc_2_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 0 512 = 13790322398886789885274212480 :=
  phaseBlock_append rc_2_9_2360_1_join0 rc_2_9_2360_1_join1 rfl rfl rfl
private theorem rc_2_9_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 512 256 = 3373768094470527060890736568 :=
  phaseBlock_append rc_2_9_2360_1_part4 rc_2_9_2360_1_part5 rfl rfl rfl
private theorem rc_2_9_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 896 221 = 602997906222456000400496706 :=
  phaseBlock_append rc_2_9_2360_1_part7 rc_2_9_2360_1_part8 rfl rfl rfl
private theorem rc_2_9_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 768 349 = 1548524893226583912093252771 :=
  phaseBlock_append rc_2_9_2360_1_part6 rc_2_9_2360_1_join4 rfl rfl rfl
private theorem rc_2_9_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 512 605 = 4922292987697110972983989339 :=
  phaseBlock_append rc_2_9_2360_1_join3 rc_2_9_2360_1_join5 rfl rfl rfl
private theorem rc_2_9_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2360 28 1 0 7 1) 0 1117 = 18712615386583900858258201819 :=
  phaseBlock_append rc_2_9_2360_1_join2 rc_2_9_2360_1_join6 rfl rfl rfl
private theorem rc_2_9_2360_1 : fastPhase (bank 2 9).shape 179808 2360 28 1 0 7 1 = 18712615386583900858258201819 :=
  phase_of_block (n := 1117) (by decide +kernel) rc_2_9_2360_1_join7
private theorem rc_2_9_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 0 128 = 4439160049299223240022445792 := by decide +kernel
private theorem rc_2_9_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 128 128 = 3752072191940020656492601056 := by decide +kernel
private theorem rc_2_9_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 256 128 = 3109481090783173289554112224 := by decide +kernel
private theorem rc_2_9_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 384 128 = 2509612178164837500881960672 := by decide +kernel
private theorem rc_2_9_2361_0_part4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 512 128 = 1950727097233485857979951219 := by decide +kernel
private theorem rc_2_9_2361_0_part5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 640 128 = 1431124259856604704276905391 := by decide +kernel
private theorem rc_2_9_2361_0_part6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 768 128 = 949137386695038971010444235 := by decide +kernel
private theorem rc_2_9_2361_0_part7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 896 128 = 503132204265250401017501284 := by decide +kernel
private theorem rc_2_9_2361_0_part8 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 1024 93 = 105471285994771823901481277 := by decide +kernel
private theorem rc_2_9_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 0 256 = 8191232241239243896515046848 :=
  phaseBlock_append rc_2_9_2361_0_part0 rc_2_9_2361_0_part1 rfl rfl rfl
private theorem rc_2_9_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 256 256 = 5619093268948010790436072896 :=
  phaseBlock_append rc_2_9_2361_0_part2 rc_2_9_2361_0_part3 rfl rfl rfl
private theorem rc_2_9_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 0 512 = 13810325510187254686951119744 :=
  phaseBlock_append rc_2_9_2361_0_join0 rc_2_9_2361_0_join1 rfl rfl rfl
private theorem rc_2_9_2361_0_join3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 512 256 = 3381851357090090562256856610 :=
  phaseBlock_append rc_2_9_2361_0_part4 rc_2_9_2361_0_part5 rfl rfl rfl
private theorem rc_2_9_2361_0_join4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 896 221 = 608603490260022224918982561 :=
  phaseBlock_append rc_2_9_2361_0_part7 rc_2_9_2361_0_part8 rfl rfl rfl
private theorem rc_2_9_2361_0_join5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 768 349 = 1557740876955061195929426796 :=
  phaseBlock_append rc_2_9_2361_0_part6 rc_2_9_2361_0_join4 rfl rfl rfl
private theorem rc_2_9_2361_0_join6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 512 605 = 4939592234045151758186283406 :=
  phaseBlock_append rc_2_9_2361_0_join3 rc_2_9_2361_0_join5 rfl rfl rfl
private theorem rc_2_9_2361_0_join7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 0) 0 1117 = 18749917744232406445137403150 :=
  phaseBlock_append rc_2_9_2361_0_join2 rc_2_9_2361_0_join6 rfl rfl rfl
private theorem rc_2_9_2361_0 : fastPhase (bank 2 9).shape 179808 2361 28 1 0 7 0 = 18749917744232406445137403150 :=
  phase_of_block (n := 1117) (by decide +kernel) rc_2_9_2361_0_join7
private theorem rc_2_9_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 0 128 = 4433683758904580590042420320 := by decide +kernel
private theorem rc_2_9_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 128 128 = 3746940832703412703540569184 := by decide +kernel
private theorem rc_2_9_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 256 128 = 3104681037057542167637505120 := by decide +kernel
private theorem rc_2_9_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 384 128 = 2505130081748346884658234464 := by decide +kernel
private theorem rc_2_9_2361_1_part4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 512 128 = 1946549885004040769572261491 := by decide +kernel
private theorem rc_2_9_2361_1_part5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 640 128 = 1427239129103064476120292267 := by decide +kernel
private theorem rc_2_9_2361_1_part6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 768 128 = 945531800044812842284200958 := by decide +kernel
private theorem rc_2_9_2361_1_part7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 896 128 = 499793892065951726093518127 := by decide +kernel
private theorem rc_2_9_2361_1_part8 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 1024 93 = 103206582445126635919622217 := by decide +kernel
private theorem rc_2_9_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 0 256 = 8180624591607993293582989504 :=
  phaseBlock_append rc_2_9_2361_1_part0 rc_2_9_2361_1_part1 rfl rfl rfl
private theorem rc_2_9_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 256 256 = 5609811118805889052295739584 :=
  phaseBlock_append rc_2_9_2361_1_part2 rc_2_9_2361_1_part3 rfl rfl rfl
private theorem rc_2_9_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 0 512 = 13790435710413882345878729088 :=
  phaseBlock_append rc_2_9_2361_1_join0 rc_2_9_2361_1_join1 rfl rfl rfl
private theorem rc_2_9_2361_1_join3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 512 256 = 3373789014107105245692553758 :=
  phaseBlock_append rc_2_9_2361_1_part4 rc_2_9_2361_1_part5 rfl rfl rfl
private theorem rc_2_9_2361_1_join4 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 896 221 = 603000474511078362013140344 :=
  phaseBlock_append rc_2_9_2361_1_part7 rc_2_9_2361_1_part8 rfl rfl rfl
private theorem rc_2_9_2361_1_join5 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 768 349 = 1548532274555891204297341302 :=
  phaseBlock_append rc_2_9_2361_1_part6 rc_2_9_2361_1_join4 rfl rfl rfl
private theorem rc_2_9_2361_1_join6 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 512 605 = 4922321288662996449989895060 :=
  phaseBlock_append rc_2_9_2361_1_join3 rc_2_9_2361_1_join5 rfl rfl rfl
private theorem rc_2_9_2361_1_join7 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2361 28 1 0 7 1) 0 1117 = 18712756999076878795868624148 :=
  phaseBlock_append rc_2_9_2361_1_join2 rc_2_9_2361_1_join6 rfl rfl rfl
private theorem rc_2_9_2361_1 : fastPhase (bank 2 9).shape 179808 2361 28 1 0 7 1 = 18712756999076878795868624148 :=
  phase_of_block (n := 1117) (by decide +kernel) rc_2_9_2361_1_join7
private theorem receipt_2_9 : B1Checked (bank 2 9) 28 0 7 := by
  refine b1_checked_from_values (bank 2 9) 28 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_5265_1116)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_9_2360_0 rc_2_9_2360_1 rc_2_9_2361_0 rc_2_9_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_5447_1155_part0 :
    blockEstimate 5447 1155 1155 128 = 1914642080 := by decide +kernel
private theorem mom_5447_1155_part1 :
    blockEstimate 5447 1155 1283 128 = 12954168992 := by decide +kernel
private theorem mom_5447_1155_part2 :
    blockEstimate 5447 1155 1411 128 = 34205777568 := by decide +kernel
private theorem mom_5447_1155_part3 :
    blockEstimate 5447 1155 1539 128 = 64864161440 := by decide +kernel
private theorem mom_5447_1155_part4 :
    blockEstimate 5447 1155 1667 128 = 104124014240 := by decide +kernel
private theorem mom_5447_1155_part5 :
    blockEstimate 5447 1155 1795 128 = 151180029600 := by decide +kernel
private theorem mom_5447_1155_part6 :
    blockEstimate 5447 1155 1923 128 = 205226901152 := by decide +kernel
private theorem mom_5447_1155_part7 :
    blockEstimate 5447 1155 2051 128 = 265459322528 := by decide +kernel
private theorem mom_5447_1155_part8 :
    blockEstimate 5447 1155 2179 128 = 331071987360 := by decide +kernel
private theorem mom_5447_1155_part9 :
    blockEstimate 5447 1155 2307 128 = 399892896155 := by decide +kernel
private theorem mom_5447_1155_part10 :
    blockEstimate 5447 1155 2435 128 = 465510176384 := by decide +kernel
private theorem mom_5447_1155_part11 :
    blockEstimate 5447 1155 2563 128 = 526278858368 := by decide +kernel
private theorem mom_5447_1155_part12 :
    blockEstimate 5447 1155 2691 128 = 582198924928 := by decide +kernel
private theorem mom_5447_1155_part13 :
    blockEstimate 5447 1155 2819 128 = 633270376064 := by decide +kernel
private theorem mom_5447_1155_part14 :
    blockEstimate 5447 1155 2947 128 = 679493211776 := by decide +kernel
private theorem mom_5447_1155_part15 :
    blockEstimate 5447 1155 3075 128 = 720867432064 := by decide +kernel
private theorem mom_5447_1155_part16 :
    blockEstimate 5447 1155 3203 128 = 757393036928 := by decide +kernel
private theorem mom_5447_1155_part17 :
    blockEstimate 5447 1155 3331 128 = 789070026368 := by decide +kernel
private theorem mom_5447_1155_part18 :
    blockEstimate 5447 1155 3459 128 = 815898400384 := by decide +kernel
private theorem mom_5447_1155_part19 :
    blockEstimate 5447 1155 3587 128 = 837878158976 := by decide +kernel
private theorem mom_5447_1155_part20 :
    blockEstimate 5447 1155 3715 128 = 855009302144 := by decide +kernel
private theorem mom_5447_1155_part21 :
    blockEstimate 5447 1155 3843 128 = 867291829888 := by decide +kernel
private theorem mom_5447_1155_part22 :
    blockEstimate 5447 1155 3971 128 = 874725742208 := by decide +kernel
private theorem mom_5447_1155_part23 :
    blockEstimate 5447 1155 4099 128 = 877311039104 := by decide +kernel
private theorem mom_5447_1155_part24 :
    blockEstimate 5447 1155 4227 128 = 875047720576 := by decide +kernel
private theorem mom_5447_1155_part25 :
    blockEstimate 5447 1155 4355 128 = 867935786624 := by decide +kernel
private theorem mom_5447_1155_part26 :
    blockEstimate 5447 1155 4483 128 = 855975237248 := by decide +kernel
private theorem mom_5447_1155_part27 :
    blockEstimate 5447 1155 4611 128 = 839166072448 := by decide +kernel
private theorem mom_5447_1155_part28 :
    blockEstimate 5447 1155 4739 128 = 817508292224 := by decide +kernel
private theorem mom_5447_1155_part29 :
    blockEstimate 5447 1155 4867 128 = 791001896576 := by decide +kernel
private theorem mom_5447_1155_part30 :
    blockEstimate 5447 1155 4995 128 = 759646885504 := by decide +kernel
private theorem mom_5447_1155_part31 :
    blockEstimate 5447 1155 5123 128 = 723443259008 := by decide +kernel
private theorem mom_5447_1155_part32 :
    blockEstimate 5447 1155 5251 128 = 682391017088 := by decide +kernel
private theorem mom_5447_1155_part33 :
    blockEstimate 5447 1155 5379 128 = 636549258764 := by decide +kernel
private theorem mom_5447_1155_part34 :
    blockEstimate 5447 1155 5507 128 = 587549201722 := by decide +kernel
private theorem mom_5447_1155_part35 :
    blockEstimate 5447 1155 5635 128 = 537485127439 := by decide +kernel
private theorem mom_5447_1155_part36 :
    blockEstimate 5447 1155 5763 128 = 487006581021 := by decide +kernel
private theorem mom_5447_1155_part37 :
    blockEstimate 5447 1155 5891 128 = 436662421146 := by decide +kernel
private theorem mom_5447_1155_part38 :
    blockEstimate 5447 1155 6019 128 = 386979214294 := by decide +kernel
private theorem mom_5447_1155_part39 :
    blockEstimate 5447 1155 6147 128 = 338461234562 := by decide +kernel
private theorem mom_5447_1155_part40 :
    blockEstimate 5447 1155 6275 128 = 291590464447 := by decide +kernel
private theorem mom_5447_1155_part41 :
    blockEstimate 5447 1155 6403 128 = 246826593864 := by decide +kernel
private theorem mom_5447_1155_part42 :
    blockEstimate 5447 1155 6531 128 = 204544381647 := by decide +kernel
private theorem mom_5447_1155_part43 :
    blockEstimate 5447 1155 6659 128 = 164893036688 := by decide +kernel
private theorem mom_5447_1155_part44 :
    blockEstimate 5447 1155 6787 128 = 128801440912 := by decide +kernel
private theorem mom_5447_1155_part45 :
    blockEstimate 5447 1155 6915 128 = 96638662800 := by decide +kernel
private theorem mom_5447_1155_part46 :
    blockEstimate 5447 1155 7043 128 = 68656360592 := by decide +kernel
private theorem mom_5447_1155_part47 :
    blockEstimate 5447 1155 7171 128 = 45106192528 := by decide +kernel
private theorem mom_5447_1155_part48 :
    blockEstimate 5447 1155 7299 128 = 26239816848 := by decide +kernel
private theorem mom_5447_1155_part49 :
    blockEstimate 5447 1155 7427 128 = 12308891792 := by decide +kernel
private theorem mom_5447_1155_part50 :
    blockEstimate 5447 1155 7555 128 = 3565075600 := by decide +kernel
private theorem mom_5447_1155_part51 :
    blockEstimate 5447 1155 7683 74 = 194071415 := by decide +kernel
private theorem mom_5447_1155_join0 :
    blockEstimate 5447 1155 1283 256 = 47159946560 :=
  block_append mom_5447_1155_part1 mom_5447_1155_part2 rfl rfl rfl
private theorem mom_5447_1155_join1 :
    blockEstimate 5447 1155 1155 384 = 49074588640 :=
  block_append mom_5447_1155_part0 mom_5447_1155_join0 rfl rfl rfl
private theorem mom_5447_1155_join2 :
    blockEstimate 5447 1155 1667 256 = 255304043840 :=
  block_append mom_5447_1155_part4 mom_5447_1155_part5 rfl rfl rfl
private theorem mom_5447_1155_join3 :
    blockEstimate 5447 1155 1539 384 = 320168205280 :=
  block_append mom_5447_1155_part3 mom_5447_1155_join2 rfl rfl rfl
private theorem mom_5447_1155_join4 :
    blockEstimate 5447 1155 1155 768 = 369242793920 :=
  block_append mom_5447_1155_join1 mom_5447_1155_join3 rfl rfl rfl
private theorem mom_5447_1155_join5 :
    blockEstimate 5447 1155 2051 256 = 596531309888 :=
  block_append mom_5447_1155_part7 mom_5447_1155_part8 rfl rfl rfl
private theorem mom_5447_1155_join6 :
    blockEstimate 5447 1155 1923 384 = 801758211040 :=
  block_append mom_5447_1155_part6 mom_5447_1155_join5 rfl rfl rfl
private theorem mom_5447_1155_join7 :
    blockEstimate 5447 1155 2307 256 = 865403072539 :=
  block_append mom_5447_1155_part9 mom_5447_1155_part10 rfl rfl rfl
private theorem mom_5447_1155_join8 :
    blockEstimate 5447 1155 2563 256 = 1108477783296 :=
  block_append mom_5447_1155_part11 mom_5447_1155_part12 rfl rfl rfl
private theorem mom_5447_1155_join9 :
    blockEstimate 5447 1155 2307 512 = 1973880855835 :=
  block_append mom_5447_1155_join7 mom_5447_1155_join8 rfl rfl rfl
private theorem mom_5447_1155_join10 :
    blockEstimate 5447 1155 1923 896 = 2775639066875 :=
  block_append mom_5447_1155_join6 mom_5447_1155_join9 rfl rfl rfl
private theorem mom_5447_1155_join11 :
    blockEstimate 5447 1155 1155 1664 = 3144881860795 :=
  block_append mom_5447_1155_join4 mom_5447_1155_join10 rfl rfl rfl
private theorem mom_5447_1155_join12 :
    blockEstimate 5447 1155 2947 256 = 1400360643840 :=
  block_append mom_5447_1155_part14 mom_5447_1155_part15 rfl rfl rfl
private theorem mom_5447_1155_join13 :
    blockEstimate 5447 1155 2819 384 = 2033631019904 :=
  block_append mom_5447_1155_part13 mom_5447_1155_join12 rfl rfl rfl
private theorem mom_5447_1155_join14 :
    blockEstimate 5447 1155 3331 256 = 1604968426752 :=
  block_append mom_5447_1155_part17 mom_5447_1155_part18 rfl rfl rfl
private theorem mom_5447_1155_join15 :
    blockEstimate 5447 1155 3203 384 = 2362361463680 :=
  block_append mom_5447_1155_part16 mom_5447_1155_join14 rfl rfl rfl
private theorem mom_5447_1155_join16 :
    blockEstimate 5447 1155 2819 768 = 4395992483584 :=
  block_append mom_5447_1155_join13 mom_5447_1155_join15 rfl rfl rfl
private theorem mom_5447_1155_join17 :
    blockEstimate 5447 1155 3715 256 = 1722301132032 :=
  block_append mom_5447_1155_part20 mom_5447_1155_part21 rfl rfl rfl
private theorem mom_5447_1155_join18 :
    blockEstimate 5447 1155 3587 384 = 2560179291008 :=
  block_append mom_5447_1155_part19 mom_5447_1155_join17 rfl rfl rfl
private theorem mom_5447_1155_join19 :
    blockEstimate 5447 1155 3971 256 = 1752036781312 :=
  block_append mom_5447_1155_part22 mom_5447_1155_part23 rfl rfl rfl
private theorem mom_5447_1155_join20 :
    blockEstimate 5447 1155 4227 256 = 1742983507200 :=
  block_append mom_5447_1155_part24 mom_5447_1155_part25 rfl rfl rfl
private theorem mom_5447_1155_join21 :
    blockEstimate 5447 1155 3971 512 = 3495020288512 :=
  block_append mom_5447_1155_join19 mom_5447_1155_join20 rfl rfl rfl
private theorem mom_5447_1155_join22 :
    blockEstimate 5447 1155 3587 896 = 6055199579520 :=
  block_append mom_5447_1155_join18 mom_5447_1155_join21 rfl rfl rfl
private theorem mom_5447_1155_join23 :
    blockEstimate 5447 1155 2819 1664 = 10451192063104 :=
  block_append mom_5447_1155_join16 mom_5447_1155_join22 rfl rfl rfl
private theorem mom_5447_1155_join24 :
    blockEstimate 5447 1155 1155 3328 = 13596073923899 :=
  block_append mom_5447_1155_join11 mom_5447_1155_join23 rfl rfl rfl
private theorem mom_5447_1155_join25 :
    blockEstimate 5447 1155 4611 256 = 1656674364672 :=
  block_append mom_5447_1155_part27 mom_5447_1155_part28 rfl rfl rfl
private theorem mom_5447_1155_join26 :
    blockEstimate 5447 1155 4483 384 = 2512649601920 :=
  block_append mom_5447_1155_part26 mom_5447_1155_join25 rfl rfl rfl
private theorem mom_5447_1155_join27 :
    blockEstimate 5447 1155 4995 256 = 1483090144512 :=
  block_append mom_5447_1155_part30 mom_5447_1155_part31 rfl rfl rfl
private theorem mom_5447_1155_join28 :
    blockEstimate 5447 1155 4867 384 = 2274092041088 :=
  block_append mom_5447_1155_part29 mom_5447_1155_join27 rfl rfl rfl
private theorem mom_5447_1155_join29 :
    blockEstimate 5447 1155 4483 768 = 4786741643008 :=
  block_append mom_5447_1155_join26 mom_5447_1155_join28 rfl rfl rfl
private theorem mom_5447_1155_join30 :
    blockEstimate 5447 1155 5379 256 = 1224098460486 :=
  block_append mom_5447_1155_part33 mom_5447_1155_part34 rfl rfl rfl
private theorem mom_5447_1155_join31 :
    blockEstimate 5447 1155 5251 384 = 1906489477574 :=
  block_append mom_5447_1155_part32 mom_5447_1155_join30 rfl rfl rfl
private theorem mom_5447_1155_join32 :
    blockEstimate 5447 1155 5635 256 = 1024491708460 :=
  block_append mom_5447_1155_part35 mom_5447_1155_part36 rfl rfl rfl
private theorem mom_5447_1155_join33 :
    blockEstimate 5447 1155 5891 256 = 823641635440 :=
  block_append mom_5447_1155_part37 mom_5447_1155_part38 rfl rfl rfl
private theorem mom_5447_1155_join34 :
    blockEstimate 5447 1155 5635 512 = 1848133343900 :=
  block_append mom_5447_1155_join32 mom_5447_1155_join33 rfl rfl rfl
private theorem mom_5447_1155_join35 :
    blockEstimate 5447 1155 5251 896 = 3754622821474 :=
  block_append mom_5447_1155_join31 mom_5447_1155_join34 rfl rfl rfl
private theorem mom_5447_1155_join36 :
    blockEstimate 5447 1155 4483 1664 = 8541364464482 :=
  block_append mom_5447_1155_join29 mom_5447_1155_join35 rfl rfl rfl
private theorem mom_5447_1155_join37 :
    blockEstimate 5447 1155 6275 256 = 538417058311 :=
  block_append mom_5447_1155_part40 mom_5447_1155_part41 rfl rfl rfl
private theorem mom_5447_1155_join38 :
    blockEstimate 5447 1155 6147 384 = 876878292873 :=
  block_append mom_5447_1155_part39 mom_5447_1155_join37 rfl rfl rfl
private theorem mom_5447_1155_join39 :
    blockEstimate 5447 1155 6659 256 = 293694477600 :=
  block_append mom_5447_1155_part43 mom_5447_1155_part44 rfl rfl rfl
private theorem mom_5447_1155_join40 :
    blockEstimate 5447 1155 6531 384 = 498238859247 :=
  block_append mom_5447_1155_part42 mom_5447_1155_join39 rfl rfl rfl
private theorem mom_5447_1155_join41 :
    blockEstimate 5447 1155 6147 768 = 1375117152120 :=
  block_append mom_5447_1155_join38 mom_5447_1155_join40 rfl rfl rfl
private theorem mom_5447_1155_join42 :
    blockEstimate 5447 1155 7043 256 = 113762553120 :=
  block_append mom_5447_1155_part46 mom_5447_1155_part47 rfl rfl rfl
private theorem mom_5447_1155_join43 :
    blockEstimate 5447 1155 6915 384 = 210401215920 :=
  block_append mom_5447_1155_part45 mom_5447_1155_join42 rfl rfl rfl
private theorem mom_5447_1155_join44 :
    blockEstimate 5447 1155 7299 256 = 38548708640 :=
  block_append mom_5447_1155_part48 mom_5447_1155_part49 rfl rfl rfl
private theorem mom_5447_1155_join45 :
    blockEstimate 5447 1155 7555 202 = 3759147015 :=
  block_append mom_5447_1155_part50 mom_5447_1155_part51 rfl rfl rfl
private theorem mom_5447_1155_join46 :
    blockEstimate 5447 1155 7299 458 = 42307855655 :=
  block_append mom_5447_1155_join44 mom_5447_1155_join45 rfl rfl rfl
private theorem mom_5447_1155_join47 :
    blockEstimate 5447 1155 6915 842 = 252709071575 :=
  block_append mom_5447_1155_join43 mom_5447_1155_join46 rfl rfl rfl
private theorem mom_5447_1155_join48 :
    blockEstimate 5447 1155 6147 1610 = 1627826223695 :=
  block_append mom_5447_1155_join41 mom_5447_1155_join47 rfl rfl rfl
private theorem mom_5447_1155_join49 :
    blockEstimate 5447 1155 4483 3274 = 10169190688177 :=
  block_append mom_5447_1155_join36 mom_5447_1155_join48 rfl rfl rfl
private theorem mom_5447_1155_join50 :
    blockEstimate 5447 1155 1155 6602 = 23765264612076 :=
  block_append mom_5447_1155_join24 mom_5447_1155_join49 rfl rfl rfl
private theorem mom_5447_1155 : momentEstimate 5447 1155 = 23765264612076 := mom_5447_1155_join50
private theorem rc_2_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 0 128 = 16082231994375399601282035936 := by decide +kernel
private theorem rc_2_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 128 128 = 13725034172647029031963353312 := by decide +kernel
private theorem rc_2_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 256 128 = 11503145300234822523915047136 := by decide +kernel
private theorem rc_2_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 384 128 = 9412056794173625358843953376 := by decide +kernel
private theorem rc_2_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 512 128 = 7447320484214718417367451214 := by decide +kernel
private theorem rc_2_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 640 128 = 5604552640477614919609250853 := by decide +kernel
private theorem rc_2_10_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 768 128 = 3879425278882635358418743595 := by decide +kernel
private theorem rc_2_10_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 896 128 = 2267659524084455558175211418 := by decide +kernel
private theorem rc_2_10_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 1024 128 = 765035112558459936279265603 := by decide +kernel
private theorem rc_2_10_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 1152 4 = 851374345234645674670071 := by decide +kernel
private theorem rc_2_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 0 256 = 29807266167022428633245389248 :=
  phaseBlock_append rc_2_10_2360_0_part0 rc_2_10_2360_0_part1 rfl rfl rfl
private theorem rc_2_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 384 256 = 16859377278388343776211404590 :=
  phaseBlock_append rc_2_10_2360_0_part3 rc_2_10_2360_0_part4 rfl rfl rfl
private theorem rc_2_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 256 384 = 28362522578623166300126451726 :=
  phaseBlock_append rc_2_10_2360_0_part2 rc_2_10_2360_0_join1 rfl rfl rfl
private theorem rc_2_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 0 640 = 58169788745645594933371840974 :=
  phaseBlock_append rc_2_10_2360_0_join0 rc_2_10_2360_0_join2 rfl rfl rfl
private theorem rc_2_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 640 256 = 9483977919360250278027994448 :=
  phaseBlock_append rc_2_10_2360_0_part5 rc_2_10_2360_0_part6 rfl rfl rfl
private theorem rc_2_10_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 1024 132 = 765886486903694581953935674 :=
  phaseBlock_append rc_2_10_2360_0_part8 rc_2_10_2360_0_part9 rfl rfl rfl
private theorem rc_2_10_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 896 260 = 3033546010988150140129147092 :=
  phaseBlock_append rc_2_10_2360_0_part7 rc_2_10_2360_0_join5 rfl rfl rfl
private theorem rc_2_10_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 640 516 = 12517523930348400418157141540 :=
  phaseBlock_append rc_2_10_2360_0_join4 rc_2_10_2360_0_join6 rfl rfl rfl
private theorem rc_2_10_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 0) 0 1156 = 70687312675993995351528982514 :=
  phaseBlock_append rc_2_10_2360_0_join3 rc_2_10_2360_0_join7 rfl rfl rfl
private theorem rc_2_10_2360_0 : fastPhase (bank 2 10).shape 179808 2360 40 1 0 7 0 = 70687312675993995351528982514 :=
  phase_of_block (n := 1156) (by decide +kernel) rc_2_10_2360_0_join8
private theorem rc_2_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 0 128 = 16063520764432940461825764576 := by decide +kernel
private theorem rc_2_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 128 128 = 13707365698944002718119591136 := by decide +kernel
private theorem rc_2_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 256 128 = 11486485152014263318209252576 := by decide +kernel
private theorem rc_2_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 384 128 = 9396371001637081609401736416 := by decide +kernel
private theorem rc_2_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 512 128 = 7432575535929563025003545943 := by decide +kernel
private theorem rc_2_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 640 128 = 5590715470294893647357990431 := by decide +kernel
private theorem rc_2_10_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 768 128 = 3866463260059670430833527083 := by decide +kernel
private theorem rc_2_10_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 896 128 = 2255540481110917658994450930 := by decide +kernel
private theorem rc_2_10_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 1024 128 = 753727319824030375793670363 := by decide +kernel
private theorem rc_2_10_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 1152 4 = 510735303029277941906271 := by decide +kernel
private theorem rc_2_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 0 256 = 29770886463376943179945355712 :=
  phaseBlock_append rc_2_10_2360_1_part0 rc_2_10_2360_1_part1 rfl rfl rfl
private theorem rc_2_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 384 256 = 16828946537566644634405282359 :=
  phaseBlock_append rc_2_10_2360_1_part3 rc_2_10_2360_1_part4 rfl rfl rfl
private theorem rc_2_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 256 384 = 28315431689580907952614534935 :=
  phaseBlock_append rc_2_10_2360_1_part2 rc_2_10_2360_1_join1 rfl rfl rfl
private theorem rc_2_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 0 640 = 58086318152957851132559890647 :=
  phaseBlock_append rc_2_10_2360_1_join0 rc_2_10_2360_1_join2 rfl rfl rfl
private theorem rc_2_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 640 256 = 9457178730354564078191517514 :=
  phaseBlock_append rc_2_10_2360_1_part5 rc_2_10_2360_1_part6 rfl rfl rfl
private theorem rc_2_10_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 1024 132 = 754238055127059653735576634 :=
  phaseBlock_append rc_2_10_2360_1_part8 rc_2_10_2360_1_part9 rfl rfl rfl
private theorem rc_2_10_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 896 260 = 3009778536237977312730027564 :=
  phaseBlock_append rc_2_10_2360_1_part7 rc_2_10_2360_1_join5 rfl rfl rfl
private theorem rc_2_10_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 640 516 = 12466957266592541390921545078 :=
  phaseBlock_append rc_2_10_2360_1_join4 rc_2_10_2360_1_join6 rfl rfl rfl
private theorem rc_2_10_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2360 40 1 0 7 1) 0 1156 = 70553275419550392523481435725 :=
  phaseBlock_append rc_2_10_2360_1_join3 rc_2_10_2360_1_join7 rfl rfl rfl
private theorem rc_2_10_2360_1 : fastPhase (bank 2 10).shape 179808 2360 40 1 0 7 1 = 70553275419550392523481435725 :=
  phase_of_block (n := 1156) (by decide +kernel) rc_2_10_2360_1_join8
private theorem rc_2_10_2361_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 0 128 = 16082375506262091580469867744 := by decide +kernel
private theorem rc_2_10_2361_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 128 128 = 13725148821128149336030889184 := by decide +kernel
private theorem rc_2_10_2361_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 256 128 = 11503234598142012467723539680 := by decide +kernel
private theorem rc_2_10_2361_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 384 128 = 9412124108497481221028603104 := by decide +kernel
private theorem rc_2_10_2361_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 512 128 = 7447369031263111326340805291 := by decide +kernel
private theorem rc_2_10_2361_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 640 128 = 5604585448323348448111927203 := by decide +kernel
private theorem rc_2_10_2361_0_part6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 768 128 = 3879445319021215496948983107 := by decide +kernel
private theorem rc_2_10_2361_0_part7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 896 128 = 2267669645194753295348872365 := by decide +kernel
private theorem rc_2_10_2361_0_part8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 1024 128 = 765038017313458249713617298 := by decide +kernel
private theorem rc_2_10_2361_0_part9 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 1152 4 = 851377143536507026614242 := by decide +kernel
private theorem rc_2_10_2361_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 0 256 = 29807524327390240916500756928 :=
  phaseBlock_append rc_2_10_2361_0_part0 rc_2_10_2361_0_part1 rfl rfl rfl
private theorem rc_2_10_2361_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 384 256 = 16859493139760592547369408395 :=
  phaseBlock_append rc_2_10_2361_0_part3 rc_2_10_2361_0_part4 rfl rfl rfl
private theorem rc_2_10_2361_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 256 384 = 28362727737902605015092948075 :=
  phaseBlock_append rc_2_10_2361_0_part2 rc_2_10_2361_0_join1 rfl rfl rfl
private theorem rc_2_10_2361_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 0 640 = 58170252065292845931593705003 :=
  phaseBlock_append rc_2_10_2361_0_join0 rc_2_10_2361_0_join2 rfl rfl rfl
private theorem rc_2_10_2361_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 640 256 = 9484030767344563945060910310 :=
  phaseBlock_append rc_2_10_2361_0_part5 rc_2_10_2361_0_part6 rfl rfl rfl
private theorem rc_2_10_2361_0_join5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 1024 132 = 765889394456994756740231540 :=
  phaseBlock_append rc_2_10_2361_0_part8 rc_2_10_2361_0_part9 rfl rfl rfl
private theorem rc_2_10_2361_0_join6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 896 260 = 3033559039651748052089103905 :=
  phaseBlock_append rc_2_10_2361_0_part7 rc_2_10_2361_0_join5 rfl rfl rfl
private theorem rc_2_10_2361_0_join7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 640 516 = 12517589806996311997150014215 :=
  phaseBlock_append rc_2_10_2361_0_join4 rc_2_10_2361_0_join6 rfl rfl rfl
private theorem rc_2_10_2361_0_join8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 0) 0 1156 = 70687841872289157928743719218 :=
  phaseBlock_append rc_2_10_2361_0_join3 rc_2_10_2361_0_join7 rfl rfl rfl
private theorem rc_2_10_2361_0 : fastPhase (bank 2 10).shape 179808 2361 40 1 0 7 0 = 70687841872289157928743719218 :=
  phase_of_block (n := 1156) (by decide +kernel) rc_2_10_2361_0_join8
private theorem rc_2_10_2361_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 0 128 = 16063664138745283145375263392 := by decide +kernel
private theorem rc_2_10_2361_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 128 128 = 13707480224316715321233390240 := by decide +kernel
private theorem rc_2_10_2361_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 256 128 = 11486574340566758611062016672 := by decide +kernel
private theorem rc_2_10_2361_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 384 128 = 9396438219659108671985769120 := by decide +kernel
private theorem rc_2_10_2361_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 512 128 = 7432623999052724121687205037 := by decide +kernel
private theorem rc_2_10_2361_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 640 128 = 5590748206042070365939831536 := by decide +kernel
private theorem rc_2_10_2361_1_part6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 768 128 = 3866483239272450096840744348 := by decide +kernel
private theorem rc_2_10_2361_1_part7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 896 128 = 2255550551784363723308438890 := by decide +kernel
private theorem rc_2_10_2361_1_part8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 1024 128 = 753730183961383344954567407 := by decide +kernel
private theorem rc_2_10_2361_1_part9 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 1152 4 = 510736983385674348642630 := by decide +kernel
private theorem rc_2_10_2361_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 0 256 = 29771144363061998466608653632 :=
  phaseBlock_append rc_2_10_2361_1_part0 rc_2_10_2361_1_part1 rfl rfl rfl
private theorem rc_2_10_2361_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 384 256 = 16829062218711832793672974157 :=
  phaseBlock_append rc_2_10_2361_1_part3 rc_2_10_2361_1_part4 rfl rfl rfl
private theorem rc_2_10_2361_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 256 384 = 28315636559278591404734990829 :=
  phaseBlock_append rc_2_10_2361_1_part2 rc_2_10_2361_1_join1 rfl rfl rfl
private theorem rc_2_10_2361_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 0 640 = 58086780922340589871343644461 :=
  phaseBlock_append rc_2_10_2361_1_join0 rc_2_10_2361_1_join2 rfl rfl rfl
private theorem rc_2_10_2361_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 640 256 = 9457231445314520462780575884 :=
  phaseBlock_append rc_2_10_2361_1_part5 rc_2_10_2361_1_part6 rfl rfl rfl
private theorem rc_2_10_2361_1_join5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 1024 132 = 754240920944769019303210037 :=
  phaseBlock_append rc_2_10_2361_1_part8 rc_2_10_2361_1_part9 rfl rfl rfl
private theorem rc_2_10_2361_1_join6 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 896 260 = 3009791472729132742611648927 :=
  phaseBlock_append rc_2_10_2361_1_part7 rc_2_10_2361_1_join5 rfl rfl rfl
private theorem rc_2_10_2361_1_join7 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 640 516 = 12467022918043653205392224811 :=
  phaseBlock_append rc_2_10_2361_1_join4 rc_2_10_2361_1_join6 rfl rfl rfl
private theorem rc_2_10_2361_1_join8 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2361 40 1 0 7 1) 0 1156 = 70553803840384243076735869272 :=
  phaseBlock_append rc_2_10_2361_1_join3 rc_2_10_2361_1_join7 rfl rfl rfl
private theorem rc_2_10_2361_1 : fastPhase (bank 2 10).shape 179808 2361 40 1 0 7 1 = 70553803840384243076735869272 :=
  phase_of_block (n := 1156) (by decide +kernel) rc_2_10_2361_1_join8
private theorem receipt_2_10 : B1Checked (bank 2 10) 40 0 7 := by
  refine b1_checked_from_values (bank 2 10) 40 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_5447_1155)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_2_10_2360_0 rc_2_10_2360_1 rc_2_10_2361_0 rc_2_10_2361_1 (by decide +kernel) (by decide +kernel)

theorem rect2_checked (i : Fin 11) :
    B1Checked (bank 2 i) (reserve i) (excess 2) (seed 2) := by
  fin_cases i
  · exact receipt_2_0
  · exact receipt_2_1
  · exact receipt_2_2
  · exact receipt_2_3
  · exact receipt_2_4
  · exact receipt_2_5
  · exact receipt_2_6
  · exact receipt_2_7
  · exact receipt_2_8
  · exact receipt_2_9
  · exact receipt_2_10

#print axioms rect2_checked
end Lower6962.B1.RescueSource
