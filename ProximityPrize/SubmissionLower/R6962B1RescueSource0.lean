import ProximityPrize.SubmissionLower.R6962B1RescueSchedule

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Lower6962.B1.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase phaseBlock phaseBlock_append phase_of_block)

private theorem mom_1335_283_part0 :
    blockEstimate 1335 283 283 128 = 443532960 := by decide +kernel
private theorem mom_1335_283_part1 :
    blockEstimate 1335 283 411 128 = 2792199840 := by decide +kernel
private theorem mom_1335_283_part2 :
    blockEstimate 1335 283 539 128 = 6561751385 := by decide +kernel
private theorem mom_1335_283_part3 :
    blockEstimate 1335 283 667 128 = 9854927232 := by decide +kernel
private theorem mom_1335_283_part4 :
    blockEstimate 1335 283 795 128 = 11960435072 := by decide +kernel
private theorem mom_1335_283_part5 :
    blockEstimate 1335 283 923 128 = 12874760576 := by decide +kernel
private theorem mom_1335_283_part6 :
    blockEstimate 1335 283 1051 128 = 12597903744 := by decide +kernel
private theorem mom_1335_283_part7 :
    blockEstimate 1335 283 1179 128 = 11129864576 := by decide +kernel
private theorem mom_1335_283_part8 :
    blockEstimate 1335 283 1307 128 = 8544973654 := by decide +kernel
private theorem mom_1335_283_part9 :
    blockEstimate 1335 283 1435 128 = 5551785281 := by decide +kernel
private theorem mom_1335_283_part10 :
    blockEstimate 1335 283 1563 128 = 2857917767 := by decide +kernel
private theorem mom_1335_283_part11 :
    blockEstimate 1335 283 1691 128 = 912482768 := by decide +kernel
private theorem mom_1335_283_part12 :
    blockEstimate 1335 283 1819 82 = 62919374 := by decide +kernel
private theorem mom_1335_283_join0 :
    blockEstimate 1335 283 411 256 = 9353951225 :=
  block_append mom_1335_283_part1 mom_1335_283_part2 rfl rfl rfl
private theorem mom_1335_283_join1 :
    blockEstimate 1335 283 283 384 = 9797484185 :=
  block_append mom_1335_283_part0 mom_1335_283_join0 rfl rfl rfl
private theorem mom_1335_283_join2 :
    blockEstimate 1335 283 795 256 = 24835195648 :=
  block_append mom_1335_283_part4 mom_1335_283_part5 rfl rfl rfl
private theorem mom_1335_283_join3 :
    blockEstimate 1335 283 667 384 = 34690122880 :=
  block_append mom_1335_283_part3 mom_1335_283_join2 rfl rfl rfl
private theorem mom_1335_283_join4 :
    blockEstimate 1335 283 283 768 = 44487607065 :=
  block_append mom_1335_283_join1 mom_1335_283_join3 rfl rfl rfl
private theorem mom_1335_283_join5 :
    blockEstimate 1335 283 1179 256 = 19674838230 :=
  block_append mom_1335_283_part7 mom_1335_283_part8 rfl rfl rfl
private theorem mom_1335_283_join6 :
    blockEstimate 1335 283 1051 384 = 32272741974 :=
  block_append mom_1335_283_part6 mom_1335_283_join5 rfl rfl rfl
private theorem mom_1335_283_join7 :
    blockEstimate 1335 283 1435 256 = 8409703048 :=
  block_append mom_1335_283_part9 mom_1335_283_part10 rfl rfl rfl
private theorem mom_1335_283_join8 :
    blockEstimate 1335 283 1691 210 = 975402142 :=
  block_append mom_1335_283_part11 mom_1335_283_part12 rfl rfl rfl
private theorem mom_1335_283_join9 :
    blockEstimate 1335 283 1435 466 = 9385105190 :=
  block_append mom_1335_283_join7 mom_1335_283_join8 rfl rfl rfl
private theorem mom_1335_283_join10 :
    blockEstimate 1335 283 1051 850 = 41657847164 :=
  block_append mom_1335_283_join6 mom_1335_283_join9 rfl rfl rfl
private theorem mom_1335_283_join11 :
    blockEstimate 1335 283 283 1618 = 86145454229 :=
  block_append mom_1335_283_join4 mom_1335_283_join10 rfl rfl rfl
private theorem mom_1335_283 : momentEstimate 1335 283 = 86145454229 := mom_1335_283_join11
private theorem rc_0_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 0) 0 128 = 9555266801045160576210816 := by decide +kernel
private theorem rc_0_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 0) 128 128 = 3562932800200852486025508 := by decide +kernel
private theorem rc_0_0_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 0) 256 28 = 111577254474625413717978 := by decide +kernel
private theorem rc_0_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 0) 128 156 = 3674510054675477899743486 :=
  phaseBlock_append rc_0_0_2360_0_part1 rc_0_0_2360_0_part2 rfl rfl rfl
private theorem rc_0_0_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 0) 0 284 = 13229776855720638475954302 :=
  phaseBlock_append rc_0_0_2360_0_part0 rc_0_0_2360_0_join0 rfl rfl rfl
private theorem rc_0_0_2360_0 : fastPhase (bank 0 0).shape 179808 2360 0 1 0 1 0 = 13229776855720638475954302 :=
  phase_of_block (n := 284) (by decide +kernel) rc_0_0_2360_0_join1
private theorem rc_0_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 1) 0 128 = 9503607414281903041232832 := by decide +kernel
private theorem rc_0_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 1) 128 128 = 3521665359567442054571226 := by decide +kernel
private theorem rc_0_0_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 1) 256 28 = 103817328336259553797488 := by decide +kernel
private theorem rc_0_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 1) 128 156 = 3625482687903701608368714 :=
  phaseBlock_append rc_0_0_2360_1_part1 rc_0_0_2360_1_part2 rfl rfl rfl
private theorem rc_0_0_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2360 0 1 0 1 1) 0 284 = 13129090102185604649601546 :=
  phaseBlock_append rc_0_0_2360_1_part0 rc_0_0_2360_1_join0 rfl rfl rfl
private theorem rc_0_0_2360_1 : fastPhase (bank 0 0).shape 179808 2360 0 1 0 1 1 = 13129090102185604649601546 :=
  phase_of_block (n := 284) (by decide +kernel) rc_0_0_2360_1_join1
private theorem rc_0_0_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 0) 0 128 = 9555347174541137761656672 := by decide +kernel
private theorem rc_0_0_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 0) 128 128 = 3562954261644120192372512 := by decide +kernel
private theorem rc_0_0_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 0) 256 28 = 111577701026827372305633 := by decide +kernel
private theorem rc_0_0_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 0) 128 156 = 3674531962670947564678145 :=
  phaseBlock_append rc_0_0_2361_0_part1 rc_0_0_2361_0_part2 rfl rfl rfl
private theorem rc_0_0_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 0) 0 284 = 13229879137212085326334817 :=
  phaseBlock_append rc_0_0_2361_0_part0 rc_0_0_2361_0_join0 rfl rfl rfl
private theorem rc_0_0_2361_0 : fastPhase (bank 0 0).shape 179808 2361 0 1 0 1 0 = 13229879137212085326334817 :=
  phase_of_block (n := 284) (by decide +kernel) rc_0_0_2361_0_join1
private theorem rc_0_0_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 1) 0 128 = 9503687427622217078316512 := by decide +kernel
private theorem rc_0_0_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 1) 128 128 = 3521686607236475755881180 := by decide +kernel
private theorem rc_0_0_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 1) 256 28 = 103817745239381370572949 := by decide +kernel
private theorem rc_0_0_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 1) 128 156 = 3625504352475857126454129 :=
  phaseBlock_append rc_0_0_2361_1_part1 rc_0_0_2361_1_part2 rfl rfl rfl
private theorem rc_0_0_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179808 2361 0 1 0 1 1) 0 284 = 13129191780098074204770641 :=
  phaseBlock_append rc_0_0_2361_1_part0 rc_0_0_2361_1_join0 rfl rfl rfl
private theorem rc_0_0_2361_1 : fastPhase (bank 0 0).shape 179808 2361 0 1 0 1 1 = 13129191780098074204770641 :=
  phase_of_block (n := 284) (by decide +kernel) rc_0_0_2361_1_join1
private theorem receipt_0_0 : B1Checked (bank 0 0) 0 0 1 := by
  refine b1_checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1335_283)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_0_2360_0 rc_0_0_2360_1 rc_0_0_2361_0 rc_0_0_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1477_313_part0 :
    blockEstimate 1477 313 313 128 = 494334880 := by decide +kernel
private theorem mom_1477_313_part1 :
    blockEstimate 1477 313 441 128 = 3143123872 := by decide +kernel
private theorem mom_1477_313_part2 :
    blockEstimate 1477 313 569 128 = 7612026138 := by decide +kernel
private theorem mom_1477_313_part3 :
    blockEstimate 1477 313 697 128 = 12027405760 := by decide +kernel
private theorem mom_1477_313_part4 :
    blockEstimate 1477 313 825 128 = 15163024832 := by decide +kernel
private theorem mom_1477_313_part5 :
    blockEstimate 1477 313 953 128 = 16981632448 := by decide +kernel
private theorem mom_1477_313_part6 :
    blockEstimate 1477 313 1081 128 = 17483228608 := by decide +kernel
private theorem mom_1477_313_part7 :
    blockEstimate 1477 313 1209 128 = 16667813312 := by decide +kernel
private theorem mom_1477_313_part8 :
    blockEstimate 1477 313 1337 128 = 14535386560 := by decide +kernel
private theorem mom_1477_313_part9 :
    blockEstimate 1477 313 1465 128 = 11214836644 := by decide +kernel
private theorem mom_1477_313_part10 :
    blockEstimate 1477 313 1593 128 = 7544134968 := by decide +kernel
private theorem mom_1477_313_part11 :
    blockEstimate 1477 313 1721 128 = 4204261349 := by decide +kernel
private theorem mom_1477_313_part12 :
    blockEstimate 1477 313 1849 128 = 1643312592 := by decide +kernel
private theorem mom_1477_313_part13 :
    blockEstimate 1477 313 1977 126 = 244998608 := by decide +kernel
private theorem mom_1477_313_join0 :
    blockEstimate 1477 313 441 256 = 10755150010 :=
  block_append mom_1477_313_part1 mom_1477_313_part2 rfl rfl rfl
private theorem mom_1477_313_join1 :
    blockEstimate 1477 313 313 384 = 11249484890 :=
  block_append mom_1477_313_part0 mom_1477_313_join0 rfl rfl rfl
private theorem mom_1477_313_join2 :
    blockEstimate 1477 313 697 256 = 27190430592 :=
  block_append mom_1477_313_part3 mom_1477_313_part4 rfl rfl rfl
private theorem mom_1477_313_join3 :
    blockEstimate 1477 313 953 256 = 34464861056 :=
  block_append mom_1477_313_part5 mom_1477_313_part6 rfl rfl rfl
private theorem mom_1477_313_join4 :
    blockEstimate 1477 313 697 512 = 61655291648 :=
  block_append mom_1477_313_join2 mom_1477_313_join3 rfl rfl rfl
private theorem mom_1477_313_join5 :
    blockEstimate 1477 313 313 896 = 72904776538 :=
  block_append mom_1477_313_join1 mom_1477_313_join4 rfl rfl rfl
private theorem mom_1477_313_join6 :
    blockEstimate 1477 313 1337 256 = 25750223204 :=
  block_append mom_1477_313_part8 mom_1477_313_part9 rfl rfl rfl
private theorem mom_1477_313_join7 :
    blockEstimate 1477 313 1209 384 = 42418036516 :=
  block_append mom_1477_313_part7 mom_1477_313_join6 rfl rfl rfl
private theorem mom_1477_313_join8 :
    blockEstimate 1477 313 1593 256 = 11748396317 :=
  block_append mom_1477_313_part10 mom_1477_313_part11 rfl rfl rfl
private theorem mom_1477_313_join9 :
    blockEstimate 1477 313 1849 254 = 1888311200 :=
  block_append mom_1477_313_part12 mom_1477_313_part13 rfl rfl rfl
private theorem mom_1477_313_join10 :
    blockEstimate 1477 313 1593 510 = 13636707517 :=
  block_append mom_1477_313_join8 mom_1477_313_join9 rfl rfl rfl
private theorem mom_1477_313_join11 :
    blockEstimate 1477 313 1209 894 = 56054744033 :=
  block_append mom_1477_313_join7 mom_1477_313_join10 rfl rfl rfl
private theorem mom_1477_313_join12 :
    blockEstimate 1477 313 313 1790 = 128959520571 :=
  block_append mom_1477_313_join5 mom_1477_313_join11 rfl rfl rfl
private theorem mom_1477_313 : momentEstimate 1477 313 = 128959520571 := mom_1477_313_join12
private theorem rc_0_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 0) 0 128 = 15815564729153264287479456 := by decide +kernel
private theorem rc_0_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 0) 128 128 = 6937382142034778022406824 := by decide +kernel
private theorem rc_0_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 0) 256 58 = 693623801783970712779594 := by decide +kernel
private theorem rc_0_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 0) 128 186 = 7631005943818748735186418 :=
  phaseBlock_append rc_0_1_2360_0_part1 rc_0_1_2360_0_part2 rfl rfl rfl
private theorem rc_0_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 0) 0 314 = 23446570672972013022665874 :=
  phaseBlock_append rc_0_1_2360_0_part0 rc_0_1_2360_0_join0 rfl rfl rfl
private theorem rc_0_1_2360_0 : fastPhase (bank 0 1).shape 179808 2360 1 1 0 1 0 = 23446570672972013022665874 :=
  phase_of_block (n := 314) (by decide +kernel) rc_0_1_2360_0_join1
private theorem rc_0_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 1) 0 128 = 15739894158838290812501536 := by decide +kernel
private theorem rc_0_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 1) 128 128 = 6875491405962233226979684 := by decide +kernel
private theorem rc_0_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 1) 256 58 = 669733829320456682710549 := by decide +kernel
private theorem rc_0_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 1) 128 186 = 7545225235282689909690233 :=
  phaseBlock_append rc_0_1_2360_1_part1 rc_0_1_2360_1_part2 rfl rfl rfl
private theorem rc_0_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2360 1 1 0 1 1) 0 314 = 23285119394120980722191769 :=
  phaseBlock_append rc_0_1_2360_1_part0 rc_0_1_2360_1_join0 rfl rfl rfl
private theorem rc_0_1_2360_1 : fastPhase (bank 0 1).shape 179808 2360 1 1 0 1 1 = 23285119394120980722191769 :=
  phase_of_block (n := 314) (by decide +kernel) rc_0_1_2360_1_join1
private theorem rc_0_1_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 0) 0 128 = 15815698805437484443082752 := by decide +kernel
private theorem rc_0_1_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 0) 128 128 = 6937425785047597702229508 := by decide +kernel
private theorem rc_0_1_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 0) 256 58 = 693626830201301934311543 := by decide +kernel
private theorem rc_0_1_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 0) 128 186 = 7631052615248899636541051 :=
  phaseBlock_append rc_0_1_2361_0_part1 rc_0_1_2361_0_part2 rfl rfl rfl
private theorem rc_0_1_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 0) 0 314 = 23446751420686384079623803 :=
  phaseBlock_append rc_0_1_2361_0_part0 rc_0_1_2361_0_join0 rfl rfl rfl
private theorem rc_0_1_2361_0 : fastPhase (bank 0 1).shape 179808 2361 1 1 0 1 0 = 23446751420686384079623803 :=
  phase_of_block (n := 314) (by decide +kernel) rc_0_1_2361_0_join1
private theorem rc_0_1_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 1) 0 128 = 15740027703559880160168064 := by decide +kernel
private theorem rc_0_1_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 1) 128 128 = 6875534712288622609026662 := by decide +kernel
private theorem rc_0_1_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 1) 256 58 = 669736761613023260659366 := by decide +kernel
private theorem rc_0_1_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 1) 128 186 = 7545271473901645869686028 :=
  phaseBlock_append rc_0_1_2361_1_part1 rc_0_1_2361_1_part2 rfl rfl rfl
private theorem rc_0_1_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2361 1 1 0 1 1) 0 314 = 23285299177461526029854092 :=
  phaseBlock_append rc_0_1_2361_1_part0 rc_0_1_2361_1_join0 rfl rfl rfl
private theorem rc_0_1_2361_1 : fastPhase (bank 0 1).shape 179808 2361 1 1 0 1 1 = 23285299177461526029854092 :=
  phase_of_block (n := 314) (by decide +kernel) rc_0_1_2361_1_join1
private theorem receipt_0_1 : B1Checked (bank 0 1) 1 0 1 := by
  refine b1_checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1477_313)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_1_2360_0 rc_0_1_2360_1 rc_0_1_2361_0 rc_0_1_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1714_363_part0 :
    blockEstimate 1714 363 363 128 = 579124000 := by decide +kernel
private theorem mom_1714_363_part1 :
    blockEstimate 1714 363 491 128 = 3728821024 := by decide +kernel
private theorem mom_1714_363_part2 :
    blockEstimate 1714 363 619 128 = 9259874241 := by decide +kernel
private theorem mom_1714_363_part3 :
    blockEstimate 1714 363 747 128 = 15691731328 := by decide +kernel
private theorem mom_1714_363_part4 :
    blockEstimate 1714 363 875 128 = 20889162112 := by decide +kernel
private theorem mom_1714_363_part5 :
    blockEstimate 1714 363 1003 128 = 24559866240 := by decide +kernel
private theorem mom_1714_363_part6 :
    blockEstimate 1714 363 1131 128 = 26703843712 := by decide +kernel
private theorem mom_1714_363_part7 :
    blockEstimate 1714 363 1259 128 = 27321094528 := by decide +kernel
private theorem mom_1714_363_part8 :
    blockEstimate 1714 363 1387 128 = 26411618688 := by decide +kernel
private theorem mom_1714_363_part9 :
    blockEstimate 1714 363 1515 128 = 23975416192 := by decide +kernel
private theorem mom_1714_363_part10 :
    blockEstimate 1714 363 1643 128 = 20029135199 := by decide +kernel
private theorem mom_1714_363_part11 :
    blockEstimate 1714 363 1771 128 = 15138657136 := by decide +kernel
private theorem mom_1714_363_part12 :
    blockEstimate 1714 363 1899 128 = 10263009448 := by decide +kernel
private theorem mom_1714_363_part13 :
    blockEstimate 1714 363 2027 128 = 5921853704 := by decide +kernel
private theorem mom_1714_363_part14 :
    blockEstimate 1714 363 2155 128 = 2553881584 := by decide +kernel
private theorem mom_1714_363_part15 :
    blockEstimate 1714 363 2283 128 = 540493808 := by decide +kernel
private theorem mom_1714_363_part16 :
    blockEstimate 1714 363 2411 29 = 4014492 := by decide +kernel
private theorem mom_1714_363_join0 :
    blockEstimate 1714 363 363 256 = 4307945024 :=
  block_append mom_1714_363_part0 mom_1714_363_part1 rfl rfl rfl
private theorem mom_1714_363_join1 :
    blockEstimate 1714 363 619 256 = 24951605569 :=
  block_append mom_1714_363_part2 mom_1714_363_part3 rfl rfl rfl
private theorem mom_1714_363_join2 :
    blockEstimate 1714 363 363 512 = 29259550593 :=
  block_append mom_1714_363_join0 mom_1714_363_join1 rfl rfl rfl
private theorem mom_1714_363_join3 :
    blockEstimate 1714 363 875 256 = 45449028352 :=
  block_append mom_1714_363_part4 mom_1714_363_part5 rfl rfl rfl
private theorem mom_1714_363_join4 :
    blockEstimate 1714 363 1131 256 = 54024938240 :=
  block_append mom_1714_363_part6 mom_1714_363_part7 rfl rfl rfl
private theorem mom_1714_363_join5 :
    blockEstimate 1714 363 875 512 = 99473966592 :=
  block_append mom_1714_363_join3 mom_1714_363_join4 rfl rfl rfl
private theorem mom_1714_363_join6 :
    blockEstimate 1714 363 363 1024 = 128733517185 :=
  block_append mom_1714_363_join2 mom_1714_363_join5 rfl rfl rfl
private theorem mom_1714_363_join7 :
    blockEstimate 1714 363 1387 256 = 50387034880 :=
  block_append mom_1714_363_part8 mom_1714_363_part9 rfl rfl rfl
private theorem mom_1714_363_join8 :
    blockEstimate 1714 363 1643 256 = 35167792335 :=
  block_append mom_1714_363_part10 mom_1714_363_part11 rfl rfl rfl
private theorem mom_1714_363_join9 :
    blockEstimate 1714 363 1387 512 = 85554827215 :=
  block_append mom_1714_363_join7 mom_1714_363_join8 rfl rfl rfl
private theorem mom_1714_363_join10 :
    blockEstimate 1714 363 1899 256 = 16184863152 :=
  block_append mom_1714_363_part12 mom_1714_363_part13 rfl rfl rfl
private theorem mom_1714_363_join11 :
    blockEstimate 1714 363 2283 157 = 544508300 :=
  block_append mom_1714_363_part15 mom_1714_363_part16 rfl rfl rfl
private theorem mom_1714_363_join12 :
    blockEstimate 1714 363 2155 285 = 3098389884 :=
  block_append mom_1714_363_part14 mom_1714_363_join11 rfl rfl rfl
private theorem mom_1714_363_join13 :
    blockEstimate 1714 363 1899 541 = 19283253036 :=
  block_append mom_1714_363_join10 mom_1714_363_join12 rfl rfl rfl
private theorem mom_1714_363_join14 :
    blockEstimate 1714 363 1387 1053 = 104838080251 :=
  block_append mom_1714_363_join9 mom_1714_363_join13 rfl rfl rfl
private theorem mom_1714_363_join15 :
    blockEstimate 1714 363 363 2077 = 233571597436 :=
  block_append mom_1714_363_join6 mom_1714_363_join14 rfl rfl rfl
private theorem mom_1714_363 : momentEstimate 1714 363 = 233571597436 := mom_1714_363_join15
private theorem rc_0_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 0) 0 128 = 27861103321359175797650784 := by decide +kernel
private theorem rc_0_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 0) 128 128 = 14539717550090891136408549 := by decide +kernel
private theorem rc_0_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 0) 256 108 = 3558270806452272481906179 := by decide +kernel
private theorem rc_0_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 0) 128 236 = 18097988356543163618314728 :=
  phaseBlock_append rc_0_2_2360_0_part1 rc_0_2_2360_0_part2 rfl rfl rfl
private theorem rc_0_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 0) 0 364 = 45959091677902339415965512 :=
  phaseBlock_append rc_0_2_2360_0_part0 rc_0_2_2360_0_join0 rfl rfl rfl
private theorem rc_0_2_2360_0 : fastPhase (bank 0 2).shape 179808 2360 2 1 0 1 0 = 45959091677902339415965512 :=
  phase_of_block (n := 364) (by decide +kernel) rc_0_2_2360_0_join1
private theorem rc_0_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 1) 0 128 = 27749187229730444621366496 := by decide +kernel
private theorem rc_0_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 1) 128 128 = 14445435670756456564155983 := by decide +kernel
private theorem rc_0_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 1) 256 108 = 3491290388229423438828609 := by decide +kernel
private theorem rc_0_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 1) 128 236 = 17936726058985880002984592 :=
  phaseBlock_append rc_0_2_2360_1_part1 rc_0_2_2360_1_part2 rfl rfl rfl
private theorem rc_0_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2360 2 1 0 1 1) 0 364 = 45685913288716324624351088 :=
  phaseBlock_append rc_0_2_2360_1_part0 rc_0_2_2360_1_join0 rfl rfl rfl
private theorem rc_0_2_2360_1 : fastPhase (bank 0 2).shape 179808 2360 2 1 0 1 1 = 45685913288716324624351088 :=
  phase_of_block (n := 364) (by decide +kernel) rc_0_2_2360_1_join1
private theorem rc_0_2_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 0) 0 128 = 27861342501521238436513024 := by decide +kernel
private theorem rc_0_2_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 0) 128 128 = 14539814862350954434853406 := by decide +kernel
private theorem rc_0_2_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 0) 256 108 = 3558288047255208055194942 := by decide +kernel
private theorem rc_0_2_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 0) 128 236 = 18098102909606162490048348 :=
  phaseBlock_append rc_0_2_2361_0_part1 rc_0_2_2361_0_part2 rfl rfl rfl
private theorem rc_0_2_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 0) 0 364 = 45959445411127400926561372 :=
  phaseBlock_append rc_0_2_2361_0_part0 rc_0_2_2361_0_join0 rfl rfl rfl
private theorem rc_0_2_2361_0 : fastPhase (bank 0 2).shape 179808 2361 2 1 0 1 0 = 45959445411127400926561372 :=
  phase_of_block (n := 364) (by decide +kernel) rc_0_2_2361_0_join1
private theorem rc_0_2_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 1) 0 128 = 27749425614274996164292032 := by decide +kernel
private theorem rc_0_2_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 1) 128 128 = 14445532438056355510181972 := by decide +kernel
private theorem rc_0_2_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 1) 256 108 = 3491307341240477186499618 := by decide +kernel
private theorem rc_0_2_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 1) 128 236 = 17936839779296832696681590 :=
  phaseBlock_append rc_0_2_2361_1_part1 rc_0_2_2361_1_part2 rfl rfl rfl
private theorem rc_0_2_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2361 2 1 0 1 1) 0 364 = 45686265393571828860973622 :=
  phaseBlock_append rc_0_2_2361_1_part0 rc_0_2_2361_1_join0 rfl rfl rfl
private theorem rc_0_2_2361_1 : fastPhase (bank 0 2).shape 179808 2361 2 1 0 1 1 = 45686265393571828860973622 :=
  phase_of_block (n := 364) (by decide +kernel) rc_0_2_2361_1_join1
private theorem receipt_0_2 : B1Checked (bank 0 2) 2 0 1 := by
  refine b1_checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1714_363)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_2_2360_0 rc_0_2_2360_1 rc_0_2_2361_0 rc_0_2_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1830_388_part0 :
    blockEstimate 1830 388 388 128 = 620624160 := by decide +kernel
private theorem mom_1830_388_part1 :
    blockEstimate 1830 388 516 128 = 4015491360 := by decide +kernel
private theorem mom_1830_388_part2 :
    blockEstimate 1830 388 644 128 = 10037041440 := by decide +kernel
private theorem mom_1830_388_part3 :
    blockEstimate 1830 388 772 128 = 17451164407 := by decide +kernel
private theorem mom_1830_388_part4 :
    blockEstimate 1830 388 900 128 = 23824525952 := by decide +kernel
private theorem mom_1830_388_part5 :
    blockEstimate 1830 388 1028 128 = 28566317696 := by decide +kernel
private theorem mom_1830_388_part6 :
    blockEstimate 1830 388 1156 128 = 31676525184 := by decide +kernel
private theorem mom_1830_388_part7 :
    blockEstimate 1830 388 1284 128 = 33155148416 := by decide +kernel
private theorem mom_1830_388_part8 :
    blockEstimate 1830 388 1412 128 = 33002187392 := by decide +kernel
private theorem mom_1830_388_part9 :
    blockEstimate 1830 388 1540 128 = 31217642112 := by decide +kernel
private theorem mom_1830_388_part10 :
    blockEstimate 1830 388 1668 128 = 27801512576 := by decide +kernel
private theorem mom_1830_388_part11 :
    blockEstimate 1830 388 1796 128 = 22835223854 := by decide +kernel
private theorem mom_1830_388_part12 :
    blockEstimate 1830 388 1924 128 = 17181073042 := by decide +kernel
private theorem mom_1830_388_part13 :
    blockEstimate 1830 388 2052 128 = 11685664822 := by decide +kernel
private theorem mom_1830_388_part14 :
    blockEstimate 1830 388 2180 128 = 6829028205 := by decide +kernel
private theorem mom_1830_388_part15 :
    blockEstimate 1830 388 2308 128 = 3049663088 := by decide +kernel
private theorem mom_1830_388_part16 :
    blockEstimate 1830 388 2436 128 = 723570288 := by decide +kernel
private theorem mom_1830_388_part17 :
    blockEstimate 1830 388 2564 42 = 12410574 := by decide +kernel
private theorem mom_1830_388_join0 :
    blockEstimate 1830 388 388 256 = 4636115520 :=
  block_append mom_1830_388_part0 mom_1830_388_part1 rfl rfl rfl
private theorem mom_1830_388_join1 :
    blockEstimate 1830 388 644 256 = 27488205847 :=
  block_append mom_1830_388_part2 mom_1830_388_part3 rfl rfl rfl
private theorem mom_1830_388_join2 :
    blockEstimate 1830 388 388 512 = 32124321367 :=
  block_append mom_1830_388_join0 mom_1830_388_join1 rfl rfl rfl
private theorem mom_1830_388_join3 :
    blockEstimate 1830 388 900 256 = 52390843648 :=
  block_append mom_1830_388_part4 mom_1830_388_part5 rfl rfl rfl
private theorem mom_1830_388_join4 :
    blockEstimate 1830 388 1284 256 = 66157335808 :=
  block_append mom_1830_388_part7 mom_1830_388_part8 rfl rfl rfl
private theorem mom_1830_388_join5 :
    blockEstimate 1830 388 1156 384 = 97833860992 :=
  block_append mom_1830_388_part6 mom_1830_388_join4 rfl rfl rfl
private theorem mom_1830_388_join6 :
    blockEstimate 1830 388 900 640 = 150224704640 :=
  block_append mom_1830_388_join3 mom_1830_388_join5 rfl rfl rfl
private theorem mom_1830_388_join7 :
    blockEstimate 1830 388 388 1152 = 182349026007 :=
  block_append mom_1830_388_join2 mom_1830_388_join6 rfl rfl rfl
private theorem mom_1830_388_join8 :
    blockEstimate 1830 388 1540 256 = 59019154688 :=
  block_append mom_1830_388_part9 mom_1830_388_part10 rfl rfl rfl
private theorem mom_1830_388_join9 :
    blockEstimate 1830 388 1796 256 = 40016296896 :=
  block_append mom_1830_388_part11 mom_1830_388_part12 rfl rfl rfl
private theorem mom_1830_388_join10 :
    blockEstimate 1830 388 1540 512 = 99035451584 :=
  block_append mom_1830_388_join8 mom_1830_388_join9 rfl rfl rfl
private theorem mom_1830_388_join11 :
    blockEstimate 1830 388 2052 256 = 18514693027 :=
  block_append mom_1830_388_part13 mom_1830_388_part14 rfl rfl rfl
private theorem mom_1830_388_join12 :
    blockEstimate 1830 388 2436 170 = 735980862 :=
  block_append mom_1830_388_part16 mom_1830_388_part17 rfl rfl rfl
private theorem mom_1830_388_join13 :
    blockEstimate 1830 388 2308 298 = 3785643950 :=
  block_append mom_1830_388_part15 mom_1830_388_join12 rfl rfl rfl
private theorem mom_1830_388_join14 :
    blockEstimate 1830 388 2052 554 = 22300336977 :=
  block_append mom_1830_388_join11 mom_1830_388_join13 rfl rfl rfl
private theorem mom_1830_388_join15 :
    blockEstimate 1830 388 1540 1066 = 121335788561 :=
  block_append mom_1830_388_join10 mom_1830_388_join14 rfl rfl rfl
private theorem mom_1830_388_join16 :
    blockEstimate 1830 388 388 2218 = 303684814568 :=
  block_append mom_1830_388_join7 mom_1830_388_join15 rfl rfl rfl
private theorem mom_1830_388 : momentEstimate 1830 388 = 303684814568 := mom_1830_388_join16
private theorem rc_0_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 0 128 = 41068807737176072791099968 := by decide +kernel
private theorem rc_0_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 128 128 = 22786375246678142527691205 := by decide +kernel
private theorem rc_0_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 256 128 = 7364979495654098424845004 := by decide +kernel
private theorem rc_0_3_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 384 5 = 11638529399255340605589 := by decide +kernel
private theorem rc_0_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 0 256 = 63855182983854215318791173 :=
  phaseBlock_append rc_0_3_2360_0_part0 rc_0_3_2360_0_part1 rfl rfl rfl
private theorem rc_0_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 256 133 = 7376618025053353765450593 :=
  phaseBlock_append rc_0_3_2360_0_part2 rc_0_3_2360_0_part3 rfl rfl rfl
private theorem rc_0_3_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 0) 0 389 = 71231801008907569084241766 :=
  phaseBlock_append rc_0_3_2360_0_join0 rc_0_3_2360_0_join1 rfl rfl rfl
private theorem rc_0_3_2360_0 : fastPhase (bank 0 3).shape 179808 2360 3 1 0 1 0 = 71231801008907569084241766 :=
  phase_of_block (n := 389) (by decide +kernel) rc_0_3_2360_0_join2
private theorem rc_0_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 0 128 = 40916105363940880635289728 := by decide +kernel
private theorem rc_0_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 128 128 = 22656197668092301466330024 := by decide +kernel
private theorem rc_0_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 256 128 = 7255478940323313728392171 := by decide +kernel
private theorem rc_0_3_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 384 5 = 7755456921209870093109 := by decide +kernel
private theorem rc_0_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 0 256 = 63572303032033182101619752 :=
  phaseBlock_append rc_0_3_2360_1_part0 rc_0_3_2360_1_part1 rfl rfl rfl
private theorem rc_0_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 256 133 = 7263234397244523598485280 :=
  phaseBlock_append rc_0_3_2360_1_part2 rc_0_3_2360_1_part3 rfl rfl rfl
private theorem rc_0_3_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2360 3 1 0 1 1) 0 389 = 70835537429277705700105032 :=
  phaseBlock_append rc_0_3_2360_1_join0 rc_0_3_2360_1_join1 rfl rfl rfl
private theorem rc_0_3_2360_1 : fastPhase (bank 0 3).shape 179808 2360 3 1 0 1 1 = 70835537429277705700105032 :=
  phase_of_block (n := 389) (by decide +kernel) rc_0_3_2360_1_join2
private theorem rc_0_3_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 0 128 = 41069161314451327071423552 := by decide +kernel
private theorem rc_0_3_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 128 128 = 22786531199713395192670815 := by decide +kernel
private theorem rc_0_3_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 256 128 = 7365016501031646862309891 := by decide +kernel
private theorem rc_0_3_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 384 5 = 11638570741054514764784 := by decide +kernel
private theorem rc_0_3_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 0 256 = 63855692514164722264094367 :=
  phaseBlock_append rc_0_3_2361_0_part0 rc_0_3_2361_0_part1 rfl rfl rfl
private theorem rc_0_3_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 256 133 = 7376655071772701377074675 :=
  phaseBlock_append rc_0_3_2361_0_part2 rc_0_3_2361_0_part3 rfl rfl rfl
private theorem rc_0_3_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 0) 0 389 = 71232347585937423641169042 :=
  phaseBlock_append rc_0_3_2361_0_join0 rc_0_3_2361_0_join1 rfl rfl rfl
private theorem rc_0_3_2361_0 : fastPhase (bank 0 3).shape 179808 2361 3 1 0 1 0 = 71232347585937423641169042 :=
  phase_of_block (n := 389) (by decide +kernel) rc_0_3_2361_0_join2
private theorem rc_0_3_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 0 128 = 40916457853343757722244480 := by decide +kernel
private theorem rc_0_3_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 128 128 = 22656352853450019102159118 := by decide +kernel
private theorem rc_0_3_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 256 128 = 7255515461477000339372625 := by decide +kernel
private theorem rc_0_3_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 384 5 = 7755484545528145521986 := by decide +kernel
private theorem rc_0_3_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 0 256 = 63572810706793776824403598 :=
  phaseBlock_append rc_0_3_2361_1_part0 rc_0_3_2361_1_part1 rfl rfl rfl
private theorem rc_0_3_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 256 133 = 7263270946022528484894611 :=
  phaseBlock_append rc_0_3_2361_1_part2 rc_0_3_2361_1_part3 rfl rfl rfl
private theorem rc_0_3_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2361 3 1 0 1 1) 0 389 = 70836081652816305309298209 :=
  phaseBlock_append rc_0_3_2361_1_join0 rc_0_3_2361_1_join1 rfl rfl rfl
private theorem rc_0_3_2361_1 : fastPhase (bank 0 3).shape 179808 2361 3 1 0 1 1 = 70836081652816305309298209 :=
  phase_of_block (n := 389) (by decide +kernel) rc_0_3_2361_1_join2
private theorem receipt_0_3 : B1Checked (bank 0 3) 3 0 1 := by
  refine b1_checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1830_388)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_3_2360_0 rc_0_3_2360_1 rc_0_3_2361_0 rc_0_3_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2103_446_part0 :
    blockEstimate 2103 446 446 128 = 718292640 := by decide +kernel
private theorem mom_2103_446_part1 :
    blockEstimate 2103 446 574 128 = 4690155168 := by decide +kernel
private theorem mom_2103_446_part2 :
    blockEstimate 2103 446 702 128 = 11861223072 := by decide +kernel
private theorem mom_2103_446_part3 :
    blockEstimate 2103 446 830 128 = 21349158744 := by decide +kernel
private theorem mom_2103_446_part4 :
    blockEstimate 2103 446 958 128 = 30816880896 := by decide +kernel
private theorem mom_2103_446_part5 :
    blockEstimate 2103 446 1086 128 = 38477416704 := by decide +kernel
private theorem mom_2103_446_part6 :
    blockEstimate 2103 446 1214 128 = 44263098624 := by decide +kernel
private theorem mom_2103_446_part7 :
    blockEstimate 2103 446 1342 128 = 48173926656 := by decide +kernel
private theorem mom_2103_446_part8 :
    blockEstimate 2103 446 1470 128 = 50209900800 := by decide +kernel
private theorem mom_2103_446_part9 :
    blockEstimate 2103 446 1598 128 = 50371021056 := by decide +kernel
private theorem mom_2103_446_part10 :
    blockEstimate 2103 446 1726 128 = 48657287424 := by decide +kernel
private theorem mom_2103_446_part11 :
    blockEstimate 2103 446 1854 128 = 45068699904 := by decide +kernel
private theorem mom_2103_446_part12 :
    blockEstimate 2103 446 1982 128 = 39605299924 := by decide +kernel
private theorem mom_2103_446_part13 :
    blockEstimate 2103 446 2110 128 = 32548813137 := by decide +kernel
private theorem mom_2103_446_part14 :
    blockEstimate 2103 446 2238 128 = 25051597789 := by decide +kernel
private theorem mom_2103_446_part15 :
    blockEstimate 2103 446 2366 128 = 17812960486 := by decide +kernel
private theorem mom_2103_446_part16 :
    blockEstimate 2103 446 2494 128 = 11306108806 := by decide +kernel
private theorem mom_2103_446_part17 :
    blockEstimate 2103 446 2622 128 = 5960025616 := by decide +kernel
private theorem mom_2103_446_part18 :
    blockEstimate 2103 446 2750 128 = 2198227472 := by decide +kernel
private theorem mom_2103_446_part19 :
    blockEstimate 2103 446 2878 117 = 284069225 := by decide +kernel
private theorem mom_2103_446_join0 :
    blockEstimate 2103 446 446 256 = 5408447808 :=
  block_append mom_2103_446_part0 mom_2103_446_part1 rfl rfl rfl
private theorem mom_2103_446_join1 :
    blockEstimate 2103 446 830 256 = 52166039640 :=
  block_append mom_2103_446_part3 mom_2103_446_part4 rfl rfl rfl
private theorem mom_2103_446_join2 :
    blockEstimate 2103 446 702 384 = 64027262712 :=
  block_append mom_2103_446_part2 mom_2103_446_join1 rfl rfl rfl
private theorem mom_2103_446_join3 :
    blockEstimate 2103 446 446 640 = 69435710520 :=
  block_append mom_2103_446_join0 mom_2103_446_join2 rfl rfl rfl
private theorem mom_2103_446_join4 :
    blockEstimate 2103 446 1086 256 = 82740515328 :=
  block_append mom_2103_446_part5 mom_2103_446_part6 rfl rfl rfl
private theorem mom_2103_446_join5 :
    blockEstimate 2103 446 1470 256 = 100580921856 :=
  block_append mom_2103_446_part8 mom_2103_446_part9 rfl rfl rfl
private theorem mom_2103_446_join6 :
    blockEstimate 2103 446 1342 384 = 148754848512 :=
  block_append mom_2103_446_part7 mom_2103_446_join5 rfl rfl rfl
private theorem mom_2103_446_join7 :
    blockEstimate 2103 446 1086 640 = 231495363840 :=
  block_append mom_2103_446_join4 mom_2103_446_join6 rfl rfl rfl
private theorem mom_2103_446_join8 :
    blockEstimate 2103 446 446 1280 = 300931074360 :=
  block_append mom_2103_446_join3 mom_2103_446_join7 rfl rfl rfl
private theorem mom_2103_446_join9 :
    blockEstimate 2103 446 1726 256 = 93725987328 :=
  block_append mom_2103_446_part10 mom_2103_446_part11 rfl rfl rfl
private theorem mom_2103_446_join10 :
    blockEstimate 2103 446 2110 256 = 57600410926 :=
  block_append mom_2103_446_part13 mom_2103_446_part14 rfl rfl rfl
private theorem mom_2103_446_join11 :
    blockEstimate 2103 446 1982 384 = 97205710850 :=
  block_append mom_2103_446_part12 mom_2103_446_join10 rfl rfl rfl
private theorem mom_2103_446_join12 :
    blockEstimate 2103 446 1726 640 = 190931698178 :=
  block_append mom_2103_446_join9 mom_2103_446_join11 rfl rfl rfl
private theorem mom_2103_446_join13 :
    blockEstimate 2103 446 2366 256 = 29119069292 :=
  block_append mom_2103_446_part15 mom_2103_446_part16 rfl rfl rfl
private theorem mom_2103_446_join14 :
    blockEstimate 2103 446 2750 245 = 2482296697 :=
  block_append mom_2103_446_part18 mom_2103_446_part19 rfl rfl rfl
private theorem mom_2103_446_join15 :
    blockEstimate 2103 446 2622 373 = 8442322313 :=
  block_append mom_2103_446_part17 mom_2103_446_join14 rfl rfl rfl
private theorem mom_2103_446_join16 :
    blockEstimate 2103 446 2366 629 = 37561391605 :=
  block_append mom_2103_446_join13 mom_2103_446_join15 rfl rfl rfl
private theorem mom_2103_446_join17 :
    blockEstimate 2103 446 1726 1269 = 228493089783 :=
  block_append mom_2103_446_join12 mom_2103_446_join16 rfl rfl rfl
private theorem mom_2103_446_join18 :
    blockEstimate 2103 446 446 2549 = 529424164143 :=
  block_append mom_2103_446_join8 mom_2103_446_join17 rfl rfl rfl
private theorem mom_2103_446 : momentEstimate 2103 446 = 529424164143 := mom_2103_446_join18
private theorem rc_0_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 0 128 = 69664935242869620932893344 := by decide +kernel
private theorem rc_0_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 128 128 = 42914968183092718921615218 := by decide +kernel
private theorem rc_0_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 256 128 = 19801791983483924150848431 := by decide +kernel
private theorem rc_0_4_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 384 63 = 2296921946604699788459757 := by decide +kernel
private theorem rc_0_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 0 256 = 112579903425962339854508562 :=
  phaseBlock_append rc_0_4_2360_0_part0 rc_0_4_2360_0_part1 rfl rfl rfl
private theorem rc_0_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 256 191 = 22098713930088623939308188 :=
  phaseBlock_append rc_0_4_2360_0_part2 rc_0_4_2360_0_part3 rfl rfl rfl
private theorem rc_0_4_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 0) 0 447 = 134678617356050963793816750 :=
  phaseBlock_append rc_0_4_2360_0_join0 rc_0_4_2360_0_join1 rfl rfl rfl
private theorem rc_0_4_2360_0 : fastPhase (bank 0 4).shape 179808 2360 4 1 0 1 0 = 134678617356050963793816750 :=
  phase_of_block (n := 447) (by decide +kernel) rc_0_4_2360_0_join2
private theorem rc_0_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 0 128 = 69443888447398549038969120 := by decide +kernel
private theorem rc_0_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 128 128 = 42722395926121040560077678 := by decide +kernel
private theorem rc_0_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 256 128 = 19635668346090562478218590 := by decide +kernel
private theorem rc_0_4_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 384 63 = 2224256515998681550855653 := by decide +kernel
private theorem rc_0_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 0 256 = 112166284373519589599046798 :=
  phaseBlock_append rc_0_4_2360_1_part0 rc_0_4_2360_1_part1 rfl rfl rfl
private theorem rc_0_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 256 191 = 21859924862089244029074243 :=
  phaseBlock_append rc_0_4_2360_1_part2 rc_0_4_2360_1_part3 rfl rfl rfl
private theorem rc_0_4_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2360 4 1 0 1 1) 0 447 = 134026209235608833628121041 :=
  phaseBlock_append rc_0_4_2360_1_join0 rc_0_4_2360_1_join1 rfl rfl rfl
private theorem rc_0_4_2360_1 : fastPhase (bank 0 4).shape 179808 2360 4 1 0 1 1 = 134026209235608833628121041 :=
  phase_of_block (n := 447) (by decide +kernel) rc_0_4_2360_1_join2
private theorem rc_0_4_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 0 128 = 69665541267161378036189248 := by decide +kernel
private theorem rc_0_4_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 128 128 = 42915275894619843675804956 := by decide +kernel
private theorem rc_0_4_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 256 128 = 19801901410128308401885494 := by decide +kernel
private theorem rc_0_4_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 384 63 = 2296931416053211068854142 := by decide +kernel
private theorem rc_0_4_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 0 256 = 112580817161781221711994204 :=
  phaseBlock_append rc_0_4_2361_0_part0 rc_0_4_2361_0_part1 rfl rfl rfl
private theorem rc_0_4_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 256 191 = 22098832826181519470739636 :=
  phaseBlock_append rc_0_4_2361_0_part2 rc_0_4_2361_0_part3 rfl rfl rfl
private theorem rc_0_4_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 0) 0 447 = 134679649987962741182733840 :=
  phaseBlock_append rc_0_4_2361_0_join0 rc_0_4_2361_0_join1 rfl rfl rfl
private theorem rc_0_4_2361_0 : fastPhase (bank 0 4).shape 179808 2361 4 1 0 1 0 = 134679649987962741182733840 :=
  phase_of_block (n := 447) (by decide +kernel) rc_0_4_2361_0_join2
private theorem rc_0_4_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 0 128 = 69444492882218680284888192 := by decide +kernel
private theorem rc_0_4_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 128 128 = 42722702454410543463552548 := by decide +kernel
private theorem rc_0_4_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 256 128 = 19635776955705743978070882 := by decide +kernel
private theorem rc_0_4_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 384 63 = 2224265704940209375495554 := by decide +kernel
private theorem rc_0_4_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 0 256 = 112167195336629223748440740 :=
  phaseBlock_append rc_0_4_2361_1_part0 rc_0_4_2361_1_part1 rfl rfl rfl
private theorem rc_0_4_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 256 191 = 21860042660645953353566436 :=
  phaseBlock_append rc_0_4_2361_1_part2 rc_0_4_2361_1_part3 rfl rfl rfl
private theorem rc_0_4_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2361 4 1 0 1 1) 0 447 = 134027237997275177102007176 :=
  phaseBlock_append rc_0_4_2361_1_join0 rc_0_4_2361_1_join1 rfl rfl rfl
private theorem rc_0_4_2361_1 : fastPhase (bank 0 4).shape 179808 2361 4 1 0 1 1 = 134027237997275177102007176 :=
  phase_of_block (n := 447) (by decide +kernel) rc_0_4_2361_1_join2
private theorem receipt_0_4 : B1Checked (bank 0 4) 4 0 1 := by
  refine b1_checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2103_446)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_4_2360_0 rc_0_4_2360_1 rc_0_4_2361_0 rc_0_4_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2416_512_part0 :
    blockEstimate 2416 512 512 128 = 830271520 := by decide +kernel
private theorem mom_2416_512_part1 :
    blockEstimate 2416 512 640 128 = 5463670816 := by decide +kernel
private theorem mom_2416_512_part2 :
    blockEstimate 2416 512 768 128 = 13952684064 := by decide +kernel
private theorem mom_2416_512_part3 :
    blockEstimate 2416 512 896 128 = 25492004896 := by decide +kernel
private theorem mom_2416_512_part4 :
    blockEstimate 2416 512 1024 128 = 38644248960 := by decide +kernel
private theorem mom_2416_512_part5 :
    blockEstimate 2416 512 1152 128 = 50343997824 := by decide +kernel
private theorem mom_2416_512_part6 :
    blockEstimate 2416 512 1280 128 = 59892068736 := by decide +kernel
private theorem mom_2416_512_part7 :
    blockEstimate 2416 512 1408 128 = 67288461696 := by decide +kernel
private theorem mom_2416_512_part8 :
    blockEstimate 2416 512 1536 128 = 72533176704 := by decide +kernel
private theorem mom_2416_512_part9 :
    blockEstimate 2416 512 1664 128 = 75626213760 := by decide +kernel
private theorem mom_2416_512_part10 :
    blockEstimate 2416 512 1792 128 = 76567572864 := by decide +kernel
private theorem mom_2416_512_part11 :
    blockEstimate 2416 512 1920 128 = 75357254016 := by decide +kernel
private theorem mom_2416_512_part12 :
    blockEstimate 2416 512 2048 128 = 71995257216 := by decide +kernel
private theorem mom_2416_512_part13 :
    blockEstimate 2416 512 2176 128 = 66481582464 := by decide +kernel
private theorem mom_2416_512_part14 :
    blockEstimate 2416 512 2304 128 = 58816754124 := by decide +kernel
private theorem mom_2416_512_part15 :
    blockEstimate 2416 512 2432 128 = 49388611997 := by decide +kernel
private theorem mom_2416_512_part16 :
    blockEstimate 2416 512 2560 128 = 39485504494 := by decide +kernel
private theorem mom_2416_512_part17 :
    blockEstimate 2416 512 2688 128 = 29800716928 := by decide +kernel
private theorem mom_2416_512_part18 :
    blockEstimate 2416 512 2816 128 = 20830229855 := by decide +kernel
private theorem mom_2416_512_part19 :
    blockEstimate 2416 512 2944 128 = 12977688256 := by decide +kernel
private theorem mom_2416_512_part20 :
    blockEstimate 2416 512 3072 128 = 6729952960 := by decide +kernel
private theorem mom_2416_512_part21 :
    blockEstimate 2416 512 3200 128 = 2416381632 := by decide +kernel
private theorem mom_2416_512_part22 :
    blockEstimate 2416 512 3328 112 = 288021608 := by decide +kernel
private theorem mom_2416_512_join0 :
    blockEstimate 2416 512 512 256 = 6293942336 :=
  block_append mom_2416_512_part0 mom_2416_512_part1 rfl rfl rfl
private theorem mom_2416_512_join1 :
    blockEstimate 2416 512 896 256 = 64136253856 :=
  block_append mom_2416_512_part3 mom_2416_512_part4 rfl rfl rfl
private theorem mom_2416_512_join2 :
    blockEstimate 2416 512 768 384 = 78088937920 :=
  block_append mom_2416_512_part2 mom_2416_512_join1 rfl rfl rfl
private theorem mom_2416_512_join3 :
    blockEstimate 2416 512 512 640 = 84382880256 :=
  block_append mom_2416_512_join0 mom_2416_512_join2 rfl rfl rfl
private theorem mom_2416_512_join4 :
    blockEstimate 2416 512 1280 256 = 127180530432 :=
  block_append mom_2416_512_part6 mom_2416_512_part7 rfl rfl rfl
private theorem mom_2416_512_join5 :
    blockEstimate 2416 512 1152 384 = 177524528256 :=
  block_append mom_2416_512_part5 mom_2416_512_join4 rfl rfl rfl
private theorem mom_2416_512_join6 :
    blockEstimate 2416 512 1664 256 = 152193786624 :=
  block_append mom_2416_512_part9 mom_2416_512_part10 rfl rfl rfl
private theorem mom_2416_512_join7 :
    blockEstimate 2416 512 1536 384 = 224726963328 :=
  block_append mom_2416_512_part8 mom_2416_512_join6 rfl rfl rfl
private theorem mom_2416_512_join8 :
    blockEstimate 2416 512 1152 768 = 402251491584 :=
  block_append mom_2416_512_join5 mom_2416_512_join7 rfl rfl rfl
private theorem mom_2416_512_join9 :
    blockEstimate 2416 512 512 1408 = 486634371840 :=
  block_append mom_2416_512_join3 mom_2416_512_join8 rfl rfl rfl
private theorem mom_2416_512_join10 :
    blockEstimate 2416 512 2048 256 = 138476839680 :=
  block_append mom_2416_512_part12 mom_2416_512_part13 rfl rfl rfl
private theorem mom_2416_512_join11 :
    blockEstimate 2416 512 1920 384 = 213834093696 :=
  block_append mom_2416_512_part11 mom_2416_512_join10 rfl rfl rfl
private theorem mom_2416_512_join12 :
    blockEstimate 2416 512 2432 256 = 88874116491 :=
  block_append mom_2416_512_part15 mom_2416_512_part16 rfl rfl rfl
private theorem mom_2416_512_join13 :
    blockEstimate 2416 512 2304 384 = 147690870615 :=
  block_append mom_2416_512_part14 mom_2416_512_join12 rfl rfl rfl
private theorem mom_2416_512_join14 :
    blockEstimate 2416 512 1920 768 = 361524964311 :=
  block_append mom_2416_512_join11 mom_2416_512_join13 rfl rfl rfl
private theorem mom_2416_512_join15 :
    blockEstimate 2416 512 2816 256 = 33807918111 :=
  block_append mom_2416_512_part18 mom_2416_512_part19 rfl rfl rfl
private theorem mom_2416_512_join16 :
    blockEstimate 2416 512 2688 384 = 63608635039 :=
  block_append mom_2416_512_part17 mom_2416_512_join15 rfl rfl rfl
private theorem mom_2416_512_join17 :
    blockEstimate 2416 512 3200 240 = 2704403240 :=
  block_append mom_2416_512_part21 mom_2416_512_part22 rfl rfl rfl
private theorem mom_2416_512_join18 :
    blockEstimate 2416 512 3072 368 = 9434356200 :=
  block_append mom_2416_512_part20 mom_2416_512_join17 rfl rfl rfl
private theorem mom_2416_512_join19 :
    blockEstimate 2416 512 2688 752 = 73042991239 :=
  block_append mom_2416_512_join16 mom_2416_512_join18 rfl rfl rfl
private theorem mom_2416_512_join20 :
    blockEstimate 2416 512 1920 1520 = 434567955550 :=
  block_append mom_2416_512_join14 mom_2416_512_join19 rfl rfl rfl
private theorem mom_2416_512_join21 :
    blockEstimate 2416 512 512 2928 = 921202327390 :=
  block_append mom_2416_512_join9 mom_2416_512_join20 rfl rfl rfl
private theorem mom_2416_512 : momentEstimate 2416 512 = 921202327390 := mom_2416_512_join21
private theorem rc_0_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 0 128 = 139776649387837125754956672 := by decide +kernel
private theorem rc_0_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 128 128 = 93373503776448788177324928 := by decide +kernel
private theorem rc_0_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 256 128 = 52443434970409378155601409 := by decide +kernel
private theorem rc_0_5_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 384 128 = 16640949743122918685149951 := by decide +kernel
private theorem rc_0_5_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 512 1 = 1889296744415311685160 := by decide +kernel
private theorem rc_0_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 0 256 = 233150153164285913932281600 :=
  phaseBlock_append rc_0_5_2360_0_part0 rc_0_5_2360_0_part1 rfl rfl rfl
private theorem rc_0_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 384 129 = 16642839039867333996835111 :=
  phaseBlock_append rc_0_5_2360_0_part3 rc_0_5_2360_0_part4 rfl rfl rfl
private theorem rc_0_5_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 256 257 = 69086274010276712152436520 :=
  phaseBlock_append rc_0_5_2360_0_part2 rc_0_5_2360_0_join1 rfl rfl rfl
private theorem rc_0_5_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 0) 0 513 = 302236427174562626084718120 :=
  phaseBlock_append rc_0_5_2360_0_join0 rc_0_5_2360_0_join2 rfl rfl rfl
private theorem rc_0_5_2360_0 : fastPhase (bank 0 5).shape 179808 2360 6 1 0 1 0 = 302236427174562626084718120 :=
  phase_of_block (n := 513) (by decide +kernel) rc_0_5_2360_0_join3
private theorem rc_0_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 0 128 = 139396765607956891416230016 := by decide +kernel
private theorem rc_0_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 128 128 = 93036261405343466249230464 := by decide +kernel
private theorem rc_0_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 256 128 = 52146211492292355569432697 := by decide +kernel
private theorem rc_0_5_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 384 128 = 16381140318580515707115861 := by decide +kernel
private theorem rc_0_5_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 512 1 = 0 := by decide +kernel
private theorem rc_0_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 0 256 = 232433027013300357665460480 :=
  phaseBlock_append rc_0_5_2360_1_part0 rc_0_5_2360_1_part1 rfl rfl rfl
private theorem rc_0_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 384 129 = 16381140318580515707115861 :=
  phaseBlock_append rc_0_5_2360_1_part3 rc_0_5_2360_1_part4 rfl rfl rfl
private theorem rc_0_5_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 256 257 = 68527351810872871276548558 :=
  phaseBlock_append rc_0_5_2360_1_part2 rc_0_5_2360_1_join1 rfl rfl rfl
private theorem rc_0_5_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2360 6 1 0 1 1) 0 513 = 300960378824173228942009038 :=
  phaseBlock_append rc_0_5_2360_1_join0 rc_0_5_2360_1_join2 rfl rfl rfl
private theorem rc_0_5_2360_1 : fastPhase (bank 0 5).shape 179808 2360 6 1 0 1 1 = 300960378824173228942009038 :=
  phase_of_block (n := 513) (by decide +kernel) rc_0_5_2360_1_join3
private theorem rc_0_5_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 0 128 = 139777874090502078437140992 := by decide +kernel
private theorem rc_0_5_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 128 128 = 93374198369452235530398208 := by decide +kernel
private theorem rc_0_5_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 256 128 = 52443750427930355286454036 := by decide +kernel
private theorem rc_0_5_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 384 128 = 16641026258624745032995150 := by decide +kernel
private theorem rc_0_5_2361_0_part4 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 512 1 = 1889303301229477239120 := by decide +kernel
private theorem rc_0_5_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 0 256 = 233152072459954313967539200 :=
  phaseBlock_append rc_0_5_2361_0_part0 rc_0_5_2361_0_part1 rfl rfl rfl
private theorem rc_0_5_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 384 129 = 16642915561925974510234270 :=
  phaseBlock_append rc_0_5_2361_0_part3 rc_0_5_2361_0_part4 rfl rfl rfl
private theorem rc_0_5_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 256 257 = 69086665989856329796688306 :=
  phaseBlock_append rc_0_5_2361_0_part2 rc_0_5_2361_0_join1 rfl rfl rfl
private theorem rc_0_5_2361_0_join3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 0) 0 513 = 302238738449810643764227506 :=
  phaseBlock_append rc_0_5_2361_0_join0 rc_0_5_2361_0_join2 rfl rfl rfl
private theorem rc_0_5_2361_0 : fastPhase (bank 0 5).shape 179808 2361 6 1 0 1 0 = 302238738449810643764227506 :=
  phase_of_block (n := 513) (by decide +kernel) rc_0_5_2361_0_join3
private theorem rc_0_5_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 0 128 = 139397987562482930228634880 := by decide +kernel
private theorem rc_0_5_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 128 128 = 93036953860781249188816128 := by decide +kernel
private theorem rc_0_5_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 256 128 = 52146525369926800649200201 := by decide +kernel
private theorem rc_0_5_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 384 128 = 16381215759572474524710549 := by decide +kernel
private theorem rc_0_5_2361_1_part4 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 512 1 = 0 := by decide +kernel
private theorem rc_0_5_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 0 256 = 232434941423264179417451008 :=
  phaseBlock_append rc_0_5_2361_1_part0 rc_0_5_2361_1_part1 rfl rfl rfl
private theorem rc_0_5_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 384 129 = 16381215759572474524710549 :=
  phaseBlock_append rc_0_5_2361_1_part3 rc_0_5_2361_1_part4 rfl rfl rfl
private theorem rc_0_5_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 256 257 = 68527741129499275173910750 :=
  phaseBlock_append rc_0_5_2361_1_part2 rc_0_5_2361_1_join1 rfl rfl rfl
private theorem rc_0_5_2361_1_join3 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2361 6 1 0 1 1) 0 513 = 300962682552763454591361758 :=
  phaseBlock_append rc_0_5_2361_1_join0 rc_0_5_2361_1_join2 rfl rfl rfl
private theorem rc_0_5_2361_1 : fastPhase (bank 0 5).shape 179808 2361 6 1 0 1 1 = 300962682552763454591361758 :=
  phase_of_block (n := 513) (by decide +kernel) rc_0_5_2361_1_join3
private theorem receipt_0_5 : B1Checked (bank 0 5) 6 0 1 := by
  refine b1_checked_from_values (bank 0 5) 6 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2416_512)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_5_2360_0 rc_0_5_2360_1 rc_0_5_2361_0 rc_0_5_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_2886_612_part0 :
    blockEstimate 2886 612 612 128 = 998418720 := by decide +kernel
private theorem mom_2886_612_part1 :
    blockEstimate 2886 612 740 128 = 6625179936 := by decide +kernel
private theorem mom_2886_612_part2 :
    blockEstimate 2886 612 868 128 = 17093216544 := by decide +kernel
private theorem mom_2886_612_part3 :
    blockEstimate 2886 612 996 128 = 31597222176 := by decide +kernel
private theorem mom_2886_612_part4 :
    blockEstimate 2886 612 1124 128 = 49323656175 := by decide +kernel
private theorem mom_2886_612_part5 :
    blockEstimate 2886 612 1252 128 = 68135077504 := by decide +kernel
private theorem mom_2886_612_part6 :
    blockEstimate 2886 612 1380 128 = 84766934656 := by decide +kernel
private theorem mom_2886_612_part7 :
    blockEstimate 2886 612 1508 128 = 98827683456 := by decide +kernel
private theorem mom_2886_612_part8 :
    blockEstimate 2886 612 1636 128 = 110317323904 := by decide +kernel
private theorem mom_2886_612_part9 :
    blockEstimate 2886 612 1764 128 = 119235856000 := by decide +kernel
private theorem mom_2886_612_part10 :
    blockEstimate 2886 612 1892 128 = 125583279744 := by decide +kernel
private theorem mom_2886_612_part11 :
    blockEstimate 2886 612 2020 128 = 129359595136 := by decide +kernel
private theorem mom_2886_612_part12 :
    blockEstimate 2886 612 2148 128 = 130564802176 := by decide +kernel
private theorem mom_2886_612_part13 :
    blockEstimate 2886 612 2276 128 = 129198900864 := by decide +kernel
private theorem mom_2886_612_part14 :
    blockEstimate 2886 612 2404 128 = 125261891200 := by decide +kernel
private theorem mom_2886_612_part15 :
    blockEstimate 2886 612 2532 128 = 118753773184 := by decide +kernel
private theorem mom_2886_612_part16 :
    blockEstimate 2886 612 2660 128 = 109674546816 := by decide +kernel
private theorem mom_2886_612_part17 :
    blockEstimate 2886 612 2788 128 = 98028213056 := by decide +kernel
private theorem mom_2886_612_part18 :
    blockEstimate 2886 612 2916 128 = 84408191089 := by decide +kernel
private theorem mom_2886_612_part19 :
    blockEstimate 2886 612 3044 128 = 70268723987 := by decide +kernel
private theorem mom_2886_612_part20 :
    blockEstimate 2886 612 3172 128 = 56281477058 := by decide +kernel
private theorem mom_2886_612_part21 :
    blockEstimate 2886 612 3300 128 = 42956335232 := by decide +kernel
private theorem mom_2886_612_part22 :
    blockEstimate 2886 612 3428 128 = 30744505222 := by decide +kernel
private theorem mom_2886_612_part23 :
    blockEstimate 2886 612 3556 128 = 20031489648 := by decide +kernel
private theorem mom_2886_612_part24 :
    blockEstimate 2886 612 3684 128 = 11344210544 := by decide +kernel
private theorem mom_2886_612_part25 :
    blockEstimate 2886 612 3812 128 = 4969893488 := by decide +kernel
private theorem mom_2886_612_part26 :
    blockEstimate 2886 612 3940 128 = 1160196720 := by decide +kernel
private theorem mom_2886_612_part27 :
    blockEstimate 2886 612 4068 42 = 19647342 := by decide +kernel
private theorem mom_2886_612_join0 :
    blockEstimate 2886 612 740 256 = 23718396480 :=
  block_append mom_2886_612_part1 mom_2886_612_part2 rfl rfl rfl
private theorem mom_2886_612_join1 :
    blockEstimate 2886 612 612 384 = 24716815200 :=
  block_append mom_2886_612_part0 mom_2886_612_join0 rfl rfl rfl
private theorem mom_2886_612_join2 :
    blockEstimate 2886 612 996 256 = 80920878351 :=
  block_append mom_2886_612_part3 mom_2886_612_part4 rfl rfl rfl
private theorem mom_2886_612_join3 :
    blockEstimate 2886 612 1252 256 = 152902012160 :=
  block_append mom_2886_612_part5 mom_2886_612_part6 rfl rfl rfl
private theorem mom_2886_612_join4 :
    blockEstimate 2886 612 996 512 = 233822890511 :=
  block_append mom_2886_612_join2 mom_2886_612_join3 rfl rfl rfl
private theorem mom_2886_612_join5 :
    blockEstimate 2886 612 612 896 = 258539705711 :=
  block_append mom_2886_612_join1 mom_2886_612_join4 rfl rfl rfl
private theorem mom_2886_612_join6 :
    blockEstimate 2886 612 1636 256 = 229553179904 :=
  block_append mom_2886_612_part8 mom_2886_612_part9 rfl rfl rfl
private theorem mom_2886_612_join7 :
    blockEstimate 2886 612 1508 384 = 328380863360 :=
  block_append mom_2886_612_part7 mom_2886_612_join6 rfl rfl rfl
private theorem mom_2886_612_join8 :
    blockEstimate 2886 612 1892 256 = 254942874880 :=
  block_append mom_2886_612_part10 mom_2886_612_part11 rfl rfl rfl
private theorem mom_2886_612_join9 :
    blockEstimate 2886 612 2148 256 = 259763703040 :=
  block_append mom_2886_612_part12 mom_2886_612_part13 rfl rfl rfl
private theorem mom_2886_612_join10 :
    blockEstimate 2886 612 1892 512 = 514706577920 :=
  block_append mom_2886_612_join8 mom_2886_612_join9 rfl rfl rfl
private theorem mom_2886_612_join11 :
    blockEstimate 2886 612 1508 896 = 843087441280 :=
  block_append mom_2886_612_join7 mom_2886_612_join10 rfl rfl rfl
private theorem mom_2886_612_join12 :
    blockEstimate 2886 612 612 1792 = 1101627146991 :=
  block_append mom_2886_612_join5 mom_2886_612_join11 rfl rfl rfl
private theorem mom_2886_612_join13 :
    blockEstimate 2886 612 2532 256 = 228428320000 :=
  block_append mom_2886_612_part15 mom_2886_612_part16 rfl rfl rfl
private theorem mom_2886_612_join14 :
    blockEstimate 2886 612 2404 384 = 353690211200 :=
  block_append mom_2886_612_part14 mom_2886_612_join13 rfl rfl rfl
private theorem mom_2886_612_join15 :
    blockEstimate 2886 612 2788 256 = 182436404145 :=
  block_append mom_2886_612_part17 mom_2886_612_part18 rfl rfl rfl
private theorem mom_2886_612_join16 :
    blockEstimate 2886 612 3044 256 = 126550201045 :=
  block_append mom_2886_612_part19 mom_2886_612_part20 rfl rfl rfl
private theorem mom_2886_612_join17 :
    blockEstimate 2886 612 2788 512 = 308986605190 :=
  block_append mom_2886_612_join15 mom_2886_612_join16 rfl rfl rfl
private theorem mom_2886_612_join18 :
    blockEstimate 2886 612 2404 896 = 662676816390 :=
  block_append mom_2886_612_join14 mom_2886_612_join17 rfl rfl rfl
private theorem mom_2886_612_join19 :
    blockEstimate 2886 612 3428 256 = 50775994870 :=
  block_append mom_2886_612_part22 mom_2886_612_part23 rfl rfl rfl
private theorem mom_2886_612_join20 :
    blockEstimate 2886 612 3300 384 = 93732330102 :=
  block_append mom_2886_612_part21 mom_2886_612_join19 rfl rfl rfl
private theorem mom_2886_612_join21 :
    blockEstimate 2886 612 3684 256 = 16314104032 :=
  block_append mom_2886_612_part24 mom_2886_612_part25 rfl rfl rfl
private theorem mom_2886_612_join22 :
    blockEstimate 2886 612 3940 170 = 1179844062 :=
  block_append mom_2886_612_part26 mom_2886_612_part27 rfl rfl rfl
private theorem mom_2886_612_join23 :
    blockEstimate 2886 612 3684 426 = 17493948094 :=
  block_append mom_2886_612_join21 mom_2886_612_join22 rfl rfl rfl
private theorem mom_2886_612_join24 :
    blockEstimate 2886 612 3300 810 = 111226278196 :=
  block_append mom_2886_612_join20 mom_2886_612_join23 rfl rfl rfl
private theorem mom_2886_612_join25 :
    blockEstimate 2886 612 2404 1706 = 773903094586 :=
  block_append mom_2886_612_join18 mom_2886_612_join24 rfl rfl rfl
private theorem mom_2886_612_join26 :
    blockEstimate 2886 612 612 3498 = 1875530241577 :=
  block_append mom_2886_612_join12 mom_2886_612_join25 rfl rfl rfl
private theorem mom_2886_612 : momentEstimate 2886 612 = 1875530241577 := mom_2886_612_join26
private theorem rc_0_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 0 128 = 341682907043762832890526144 := by decide +kernel
private theorem rc_0_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 128 128 = 247524268689667773077928384 := by decide +kernel
private theorem rc_0_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 256 128 = 162627269332610927840330720 := by decide +kernel
private theorem rc_0_6_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 384 128 = 86508657633286071394570219 := by decide +kernel
private theorem rc_0_6_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 512 101 = 19994476899509818930826725 := by decide +kernel
private theorem rc_0_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 0 256 = 589207175733430605968454528 :=
  phaseBlock_append rc_0_6_2360_0_part0 rc_0_6_2360_0_part1 rfl rfl rfl
private theorem rc_0_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 384 229 = 106503134532795890325396944 :=
  phaseBlock_append rc_0_6_2360_0_part3 rc_0_6_2360_0_part4 rfl rfl rfl
private theorem rc_0_6_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 256 357 = 269130403865406818165727664 :=
  phaseBlock_append rc_0_6_2360_0_part2 rc_0_6_2360_0_join1 rfl rfl rfl
private theorem rc_0_6_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 0) 0 613 = 858337579598837424134182192 :=
  phaseBlock_append rc_0_6_2360_0_join0 rc_0_6_2360_0_join2 rfl rfl rfl
private theorem rc_0_6_2360_0 : fastPhase (bank 0 6).shape 179808 2360 9 1 0 1 0 = 858337579598837424134182192 :=
  phase_of_block (n := 613) (by decide +kernel) rc_0_6_2360_0_join3
private theorem rc_0_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 0 128 = 340919840150268544070407680 := by decide +kernel
private theorem rc_0_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 128 128 = 246832980363479596110943744 := by decide +kernel
private theorem rc_0_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 256 128 = 162004091767103998519465852 := by decide +kernel
private theorem rc_0_6_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 384 128 = 85949944358194213019597295 := by decide +kernel
private theorem rc_0_6_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 512 101 = 19596738926351348905590162 := by decide +kernel
private theorem rc_0_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 0 256 = 587752820513748140181351424 :=
  phaseBlock_append rc_0_6_2360_1_part0 rc_0_6_2360_1_part1 rfl rfl rfl
private theorem rc_0_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 384 229 = 105546683284545561925187457 :=
  phaseBlock_append rc_0_6_2360_1_part3 rc_0_6_2360_1_part4 rfl rfl rfl
private theorem rc_0_6_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 256 357 = 267550775051649560444653309 :=
  phaseBlock_append rc_0_6_2360_1_part2 rc_0_6_2360_1_join1 rfl rfl rfl
private theorem rc_0_6_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2360 9 1 0 1 1) 0 613 = 855303595565397700626004733 :=
  phaseBlock_append rc_0_6_2360_1_join0 rc_0_6_2360_1_join2 rfl rfl rfl
private theorem rc_0_6_2360_1 : fastPhase (bank 0 6).shape 179808 2360 9 1 0 1 1 = 855303595565397700626004733 :=
  phase_of_block (n := 613) (by decide +kernel) rc_0_6_2360_1_join3
private theorem rc_0_6_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 0 128 = 341685925323046688518031040 := by decide +kernel
private theorem rc_0_6_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 128 128 = 247526183214563932561385152 := by decide +kernel
private theorem rc_0_6_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 256 128 = 162628336952009678466473047 := by decide +kernel
private theorem rc_0_6_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 384 128 = 86509117719642913472024983 := by decide +kernel
private theorem rc_0_6_2361_0_part4 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 512 101 = 19994560604787077275142657 := by decide +kernel
private theorem rc_0_6_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 0 256 = 589212108537610621079416192 :=
  phaseBlock_append rc_0_6_2361_0_part0 rc_0_6_2361_0_part1 rfl rfl rfl
private theorem rc_0_6_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 384 229 = 106503678324429990747167640 :=
  phaseBlock_append rc_0_6_2361_0_part3 rc_0_6_2361_0_part4 rfl rfl rfl
private theorem rc_0_6_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 256 357 = 269132015276439669213640687 :=
  phaseBlock_append rc_0_6_2361_0_part2 rc_0_6_2361_0_join1 rfl rfl rfl
private theorem rc_0_6_2361_0_join3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 0) 0 613 = 858344123814050290293056879 :=
  phaseBlock_append rc_0_6_2361_0_join0 rc_0_6_2361_0_join2 rfl rfl rfl
private theorem rc_0_6_2361_0 : fastPhase (bank 0 6).shape 179808 2361 9 1 0 1 0 = 858344123814050290293056879 :=
  phase_of_block (n := 613) (by decide +kernel) rc_0_6_2361_0_join3
private theorem rc_0_6_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 0 128 = 340922852873943165313722624 := by decide +kernel
private theorem rc_0_6_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 128 128 = 246834890364719331205441792 := by decide +kernel
private theorem rc_0_6_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 256 128 = 162005155817582033931202034 := by decide +kernel
private theorem rc_0_6_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 384 128 = 85950401761986310216786512 := by decide +kernel
private theorem rc_0_6_2361_1_part4 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 512 101 = 19596821088875865373283469 := by decide +kernel
private theorem rc_0_6_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 0 256 = 587757743238662496519164416 :=
  phaseBlock_append rc_0_6_2361_1_part0 rc_0_6_2361_1_part1 rfl rfl rfl
private theorem rc_0_6_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 384 229 = 105547222850862175590069981 :=
  phaseBlock_append rc_0_6_2361_1_part3 rc_0_6_2361_1_part4 rfl rfl rfl
private theorem rc_0_6_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 256 357 = 267552378668444209521272015 :=
  phaseBlock_append rc_0_6_2361_1_part2 rc_0_6_2361_1_join1 rfl rfl rfl
private theorem rc_0_6_2361_1_join3 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2361 9 1 0 1 1) 0 613 = 855310121907106706040436431 :=
  phaseBlock_append rc_0_6_2361_1_join0 rc_0_6_2361_1_join2 rfl rfl rfl
private theorem rc_0_6_2361_1 : fastPhase (bank 0 6).shape 179808 2361 9 1 0 1 1 = 855310121907106706040436431 :=
  phase_of_block (n := 613) (by decide +kernel) rc_0_6_2361_1_join3
private theorem receipt_0_6 : B1Checked (bank 0 6) 9 0 1 := by
  refine b1_checked_from_values (bank 0 6) 9 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2886_612)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_6_2360_0 rc_0_6_2360_1 rc_0_6_2361_0 rc_0_6_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_3511_744_part0 :
    blockEstimate 3511 744 744 128 = 1222018720 := by decide +kernel
private theorem mom_3511_744_part1 :
    blockEstimate 3511 744 872 128 = 8169739936 := by decide +kernel
private theorem mom_3511_744_part2 :
    blockEstimate 3511 744 1000 128 = 21269456544 := by decide +kernel
private theorem mom_3511_744_part3 :
    blockEstimate 3511 744 1128 128 = 39715862176 := by decide +kernel
private theorem mom_3511_744_part4 :
    blockEstimate 3511 744 1256 128 = 62703650464 := by decide +kernel
private theorem mom_3511_744_part5 :
    blockEstimate 3511 744 1384 128 = 89421191190 := by decide +kernel
private theorem mom_3511_744_part6 :
    blockEstimate 3511 744 1512 128 = 117535443520 := by decide +kernel
private theorem mom_3511_744_part7 :
    blockEstimate 3511 744 1640 128 = 143058356800 := by decide +kernel
private theorem mom_3511_744_part8 :
    blockEstimate 3511 744 1768 128 = 165456513600 := by decide +kernel
private theorem mom_3511_744_part9 :
    blockEstimate 3511 744 1896 128 = 184729913920 := by decide +kernel
private theorem mom_3511_744_part10 :
    blockEstimate 3511 744 2024 128 = 200878557760 := by decide +kernel
private theorem mom_3511_744_part11 :
    blockEstimate 3511 744 2152 128 = 213902445120 := by decide +kernel
private theorem mom_3511_744_part12 :
    blockEstimate 3511 744 2280 128 = 223801576000 := by decide +kernel
private theorem mom_3511_744_part13 :
    blockEstimate 3511 744 2408 128 = 230575950400 := by decide +kernel
private theorem mom_3511_744_part14 :
    blockEstimate 3511 744 2536 128 = 234225568320 := by decide +kernel
private theorem mom_3511_744_part15 :
    blockEstimate 3511 744 2664 128 = 234750429760 := by decide +kernel
private theorem mom_3511_744_part16 :
    blockEstimate 3511 744 2792 128 = 232150534720 := by decide +kernel
private theorem mom_3511_744_part17 :
    blockEstimate 3511 744 2920 128 = 226425883200 := by decide +kernel
private theorem mom_3511_744_part18 :
    blockEstimate 3511 744 3048 128 = 217576475200 := by decide +kernel
private theorem mom_3511_744_part19 :
    blockEstimate 3511 744 3176 128 = 205602310720 := by decide +kernel
private theorem mom_3511_744_part20 :
    blockEstimate 3511 744 3304 128 = 190503389760 := by decide +kernel
private theorem mom_3511_744_part21 :
    blockEstimate 3511 744 3432 128 = 172300697020 := by decide +kernel
private theorem mom_3511_744_part22 :
    blockEstimate 3511 744 3560 128 = 151944354321 := by decide +kernel
private theorem mom_3511_744_part23 :
    blockEstimate 3511 744 3688 128 = 131023720657 := by decide +kernel
private theorem mom_3511_744_part24 :
    blockEstimate 3511 744 3816 128 = 110172726128 := by decide +kernel
private theorem mom_3511_744_part25 :
    blockEstimate 3511 744 3944 128 = 89912793186 := by decide +kernel
private theorem mom_3511_744_part26 :
    blockEstimate 3511 744 4072 128 = 70730753920 := by decide +kernel
private theorem mom_3511_744_part27 :
    blockEstimate 3511 744 4200 128 = 53040360277 := by decide +kernel
private theorem mom_3511_744_part28 :
    blockEstimate 3511 744 4328 128 = 37214452480 := by decide +kernel
private theorem mom_3511_744_part29 :
    blockEstimate 3511 744 4456 128 = 23845288704 := by decide +kernel
private theorem mom_3511_744_part30 :
    blockEstimate 3511 744 4584 128 = 13214415616 := by decide +kernel
private theorem mom_3511_744_part31 :
    blockEstimate 3511 744 4712 128 = 5573491456 := by decide +kernel
private theorem mom_3511_744_part32 :
    blockEstimate 3511 744 4840 128 = 1174174464 := by decide +kernel
private theorem mom_3511_744_part33 :
    blockEstimate 3511 744 4968 31 = 9987776 := by decide +kernel
private theorem mom_3511_744_join0 :
    blockEstimate 3511 744 744 256 = 9391758656 :=
  block_append mom_3511_744_part0 mom_3511_744_part1 rfl rfl rfl
private theorem mom_3511_744_join1 :
    blockEstimate 3511 744 1000 256 = 60985318720 :=
  block_append mom_3511_744_part2 mom_3511_744_part3 rfl rfl rfl
private theorem mom_3511_744_join2 :
    blockEstimate 3511 744 744 512 = 70377077376 :=
  block_append mom_3511_744_join0 mom_3511_744_join1 rfl rfl rfl
private theorem mom_3511_744_join3 :
    blockEstimate 3511 744 1256 256 = 152124841654 :=
  block_append mom_3511_744_part4 mom_3511_744_part5 rfl rfl rfl
private theorem mom_3511_744_join4 :
    blockEstimate 3511 744 1512 256 = 260593800320 :=
  block_append mom_3511_744_part6 mom_3511_744_part7 rfl rfl rfl
private theorem mom_3511_744_join5 :
    blockEstimate 3511 744 1256 512 = 412718641974 :=
  block_append mom_3511_744_join3 mom_3511_744_join4 rfl rfl rfl
private theorem mom_3511_744_join6 :
    blockEstimate 3511 744 744 1024 = 483095719350 :=
  block_append mom_3511_744_join2 mom_3511_744_join5 rfl rfl rfl
private theorem mom_3511_744_join7 :
    blockEstimate 3511 744 1768 256 = 350186427520 :=
  block_append mom_3511_744_part8 mom_3511_744_part9 rfl rfl rfl
private theorem mom_3511_744_join8 :
    blockEstimate 3511 744 2024 256 = 414781002880 :=
  block_append mom_3511_744_part10 mom_3511_744_part11 rfl rfl rfl
private theorem mom_3511_744_join9 :
    blockEstimate 3511 744 1768 512 = 764967430400 :=
  block_append mom_3511_744_join7 mom_3511_744_join8 rfl rfl rfl
private theorem mom_3511_744_join10 :
    blockEstimate 3511 744 2280 256 = 454377526400 :=
  block_append mom_3511_744_part12 mom_3511_744_part13 rfl rfl rfl
private theorem mom_3511_744_join11 :
    blockEstimate 3511 744 2664 256 = 466900964480 :=
  block_append mom_3511_744_part15 mom_3511_744_part16 rfl rfl rfl
private theorem mom_3511_744_join12 :
    blockEstimate 3511 744 2536 384 = 701126532800 :=
  block_append mom_3511_744_part14 mom_3511_744_join11 rfl rfl rfl
private theorem mom_3511_744_join13 :
    blockEstimate 3511 744 2280 640 = 1155504059200 :=
  block_append mom_3511_744_join10 mom_3511_744_join12 rfl rfl rfl
private theorem mom_3511_744_join14 :
    blockEstimate 3511 744 1768 1152 = 1920471489600 :=
  block_append mom_3511_744_join9 mom_3511_744_join13 rfl rfl rfl
private theorem mom_3511_744_join15 :
    blockEstimate 3511 744 744 2176 = 2403567208950 :=
  block_append mom_3511_744_join6 mom_3511_744_join14 rfl rfl rfl
private theorem mom_3511_744_join16 :
    blockEstimate 3511 744 2920 256 = 444002358400 :=
  block_append mom_3511_744_part17 mom_3511_744_part18 rfl rfl rfl
private theorem mom_3511_744_join17 :
    blockEstimate 3511 744 3176 256 = 396105700480 :=
  block_append mom_3511_744_part19 mom_3511_744_part20 rfl rfl rfl
private theorem mom_3511_744_join18 :
    blockEstimate 3511 744 2920 512 = 840108058880 :=
  block_append mom_3511_744_join16 mom_3511_744_join17 rfl rfl rfl
private theorem mom_3511_744_join19 :
    blockEstimate 3511 744 3432 256 = 324245051341 :=
  block_append mom_3511_744_part21 mom_3511_744_part22 rfl rfl rfl
private theorem mom_3511_744_join20 :
    blockEstimate 3511 744 3688 256 = 241196446785 :=
  block_append mom_3511_744_part23 mom_3511_744_part24 rfl rfl rfl
private theorem mom_3511_744_join21 :
    blockEstimate 3511 744 3432 512 = 565441498126 :=
  block_append mom_3511_744_join19 mom_3511_744_join20 rfl rfl rfl
private theorem mom_3511_744_join22 :
    blockEstimate 3511 744 2920 1024 = 1405549557006 :=
  block_append mom_3511_744_join18 mom_3511_744_join21 rfl rfl rfl
private theorem mom_3511_744_join23 :
    blockEstimate 3511 744 3944 256 = 160643547106 :=
  block_append mom_3511_744_part25 mom_3511_744_part26 rfl rfl rfl
private theorem mom_3511_744_join24 :
    blockEstimate 3511 744 4200 256 = 90254812757 :=
  block_append mom_3511_744_part27 mom_3511_744_part28 rfl rfl rfl
private theorem mom_3511_744_join25 :
    blockEstimate 3511 744 3944 512 = 250898359863 :=
  block_append mom_3511_744_join23 mom_3511_744_join24 rfl rfl rfl
private theorem mom_3511_744_join26 :
    blockEstimate 3511 744 4456 256 = 37059704320 :=
  block_append mom_3511_744_part29 mom_3511_744_part30 rfl rfl rfl
private theorem mom_3511_744_join27 :
    blockEstimate 3511 744 4840 159 = 1184162240 :=
  block_append mom_3511_744_part32 mom_3511_744_part33 rfl rfl rfl
private theorem mom_3511_744_join28 :
    blockEstimate 3511 744 4712 287 = 6757653696 :=
  block_append mom_3511_744_part31 mom_3511_744_join27 rfl rfl rfl
private theorem mom_3511_744_join29 :
    blockEstimate 3511 744 4456 543 = 43817358016 :=
  block_append mom_3511_744_join26 mom_3511_744_join28 rfl rfl rfl
private theorem mom_3511_744_join30 :
    blockEstimate 3511 744 3944 1055 = 294715717879 :=
  block_append mom_3511_744_join25 mom_3511_744_join29 rfl rfl rfl
private theorem mom_3511_744_join31 :
    blockEstimate 3511 744 2920 2079 = 1700265274885 :=
  block_append mom_3511_744_join22 mom_3511_744_join30 rfl rfl rfl
private theorem mom_3511_744_join32 :
    blockEstimate 3511 744 744 4255 = 4103832483835 :=
  block_append mom_3511_744_join15 mom_3511_744_join31 rfl rfl rfl
private theorem mom_3511_744 : momentEstimate 3511 744 = 4103832483835 := mom_3511_744_join32
private theorem rc_0_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 0 128 = 915753728034489702196552896 := by decide +kernel
private theorem rc_0_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 128 128 = 709650068119110355752494272 := by decide +kernel
private theorem rc_0_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 256 128 = 520148187880523742926316736 := by decide +kernel
private theorem rc_0_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 384 128 = 346543687834676418993662742 := by decide +kernel
private theorem rc_0_7_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 512 128 = 188136189016595850828604696 := by decide +kernel
private theorem rc_0_7_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 640 105 = 46259788445321697119006227 := by decide +kernel
private theorem rc_0_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 128 256 = 1229798255999634098678811008 :=
  phaseBlock_append rc_0_7_2360_0_part1 rc_0_7_2360_0_part2 rfl rfl rfl
private theorem rc_0_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 0 384 = 2145551984034123800875363904 :=
  phaseBlock_append rc_0_7_2360_0_part0 rc_0_7_2360_0_join0 rfl rfl rfl
private theorem rc_0_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 512 233 = 234395977461917547947610923 :=
  phaseBlock_append rc_0_7_2360_0_part4 rc_0_7_2360_0_part5 rfl rfl rfl
private theorem rc_0_7_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 384 361 = 580939665296593966941273665 :=
  phaseBlock_append rc_0_7_2360_0_part3 rc_0_7_2360_0_join2 rfl rfl rfl
private theorem rc_0_7_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 0) 0 745 = 2726491649330717767816637569 :=
  phaseBlock_append rc_0_7_2360_0_join1 rc_0_7_2360_0_join3 rfl rfl rfl
private theorem rc_0_7_2360_0 : fastPhase (bank 0 7).shape 179808 2360 13 1 0 1 0 = 2726491649330717767816637569 :=
  phase_of_block (n := 745) (by decide +kernel) rc_0_7_2360_0_join4
private theorem rc_0_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 0 128 = 914098677378691470669536256 := by decide +kernel
private theorem rc_0_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 128 128 = 708123074196651572097727488 := by decide +kernel
private theorem rc_0_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 256 128 = 518743909350510264115141632 := by decide +kernel
private theorem rc_0_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 384 128 = 345256811000634380540058630 := by decide +kernel
private theorem rc_0_7_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 512 128 = 186961424541208941740462483 := by decide +kernel
private theorem rc_0_7_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 640 105 = 45376123688183895205099612 := by decide +kernel
private theorem rc_0_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 128 256 = 1226866983547161836212869120 :=
  phaseBlock_append rc_0_7_2360_1_part1 rc_0_7_2360_1_part2 rfl rfl rfl
private theorem rc_0_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 0 384 = 2140965660925853306882405376 :=
  phaseBlock_append rc_0_7_2360_1_part0 rc_0_7_2360_1_join0 rfl rfl rfl
private theorem rc_0_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 512 233 = 232337548229392836945562095 :=
  phaseBlock_append rc_0_7_2360_1_part4 rc_0_7_2360_1_part5 rfl rfl rfl
private theorem rc_0_7_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 384 361 = 577594359230027217485620725 :=
  phaseBlock_append rc_0_7_2360_1_part3 rc_0_7_2360_1_join2 rfl rfl rfl
private theorem rc_0_7_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2360 13 1 0 1 1) 0 745 = 2718560020155880524368026101 :=
  phaseBlock_append rc_0_7_2360_1_join1 rc_0_7_2360_1_join3 rfl rfl rfl
private theorem rc_0_7_2360_1 : fastPhase (bank 0 7).shape 179808 2360 13 1 0 1 1 = 2718560020155880524368026101 :=
  phase_of_block (n := 745) (by decide +kernel) rc_0_7_2360_1_join4
private theorem rc_0_7_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 0 128 = 915761872755332912941622016 := by decide +kernel
private theorem rc_0_7_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 128 128 = 709655744315703448924414720 := by decide +kernel
private theorem rc_0_7_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 256 128 = 520151857773676831423521536 := by decide +kernel
private theorem rc_0_7_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 384 128 = 346545787806319290129864798 := by decide +kernel
private theorem rc_0_7_2361_0_part4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 512 128 = 188137131800929651026185594 := by decide +kernel
private theorem rc_0_7_2361_0_part5 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 640 105 = 46259976368151381955905232 := by decide +kernel
private theorem rc_0_7_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 128 256 = 1229807602089380280347936256 :=
  phaseBlock_append rc_0_7_2361_0_part1 rc_0_7_2361_0_part2 rfl rfl rfl
private theorem rc_0_7_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 0 384 = 2145569474844713193289558272 :=
  phaseBlock_append rc_0_7_2361_0_part0 rc_0_7_2361_0_join0 rfl rfl rfl
private theorem rc_0_7_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 512 233 = 234397108169081032982090826 :=
  phaseBlock_append rc_0_7_2361_0_part4 rc_0_7_2361_0_part5 rfl rfl rfl
private theorem rc_0_7_2361_0_join3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 384 361 = 580942895975400323111955624 :=
  phaseBlock_append rc_0_7_2361_0_part3 rc_0_7_2361_0_join2 rfl rfl rfl
private theorem rc_0_7_2361_0_join4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 0) 0 745 = 2726512370820113516401513896 :=
  phaseBlock_append rc_0_7_2361_0_join1 rc_0_7_2361_0_join3 rfl rfl rfl
private theorem rc_0_7_2361_0 : fastPhase (bank 0 7).shape 179808 2361 13 1 0 1 0 = 2726512370820113516401513896 :=
  phase_of_block (n := 745) (by decide +kernel) rc_0_7_2361_0_join4
private theorem rc_0_7_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 0 128 = 914106809985003849477199552 := by decide +kernel
private theorem rc_0_7_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 128 128 = 708128740126066731008718528 := by decide +kernel
private theorem rc_0_7_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 256 128 = 518747570709188519060494016 := by decide +kernel
private theorem rc_0_7_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 384 128 = 345258904062806237148330918 := by decide +kernel
private theorem rc_0_7_2361_1_part4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 512 128 = 186962361943234238735994626 := by decide +kernel
private theorem rc_0_7_2361_1_part5 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 640 105 = 45376308254053544930350166 := by decide +kernel
private theorem rc_0_7_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 128 256 = 1226876310835255250069212544 :=
  phaseBlock_append rc_0_7_2361_1_part1 rc_0_7_2361_1_part2 rfl rfl rfl
private theorem rc_0_7_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 0 384 = 2140983120820259099546412096 :=
  phaseBlock_append rc_0_7_2361_1_part0 rc_0_7_2361_1_join0 rfl rfl rfl
private theorem rc_0_7_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 512 233 = 232338670197287783666344792 :=
  phaseBlock_append rc_0_7_2361_1_part4 rc_0_7_2361_1_part5 rfl rfl rfl
private theorem rc_0_7_2361_1_join3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 384 361 = 577597574260094020814675710 :=
  phaseBlock_append rc_0_7_2361_1_part3 rc_0_7_2361_1_join2 rfl rfl rfl
private theorem rc_0_7_2361_1_join4 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2361 13 1 0 1 1) 0 745 = 2718580695080353120361087806 :=
  phaseBlock_append rc_0_7_2361_1_join1 rc_0_7_2361_1_join3 rfl rfl rfl
private theorem rc_0_7_2361_1 : fastPhase (bank 0 7).shape 179808 2361 13 1 0 1 1 = 2718580695080353120361087806 :=
  phase_of_block (n := 745) (by decide +kernel) rc_0_7_2361_1_join4
private theorem receipt_0_7 : B1Checked (bank 0 7) 13 0 1 := by
  refine b1_checked_from_values (bank 0 7) 13 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_3511_744)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_7_2360_0 rc_0_7_2360_1 rc_0_7_2361_0 rc_0_7_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_4022_853_part0 :
    blockEstimate 4022 853 853 128 = 1404834080 := by decide +kernel
private theorem mom_4022_853_part1 :
    blockEstimate 4022 853 981 128 = 9432572192 := by decide +kernel
private theorem mom_4022_853_part2 :
    blockEstimate 4022 853 1109 128 = 24683950368 := by decide +kernel
private theorem mom_4022_853_part3 :
    blockEstimate 4022 853 1237 128 = 46353662240 := by decide +kernel
private theorem mom_4022_853_part4 :
    blockEstimate 4022 853 1365 128 = 73636401440 := by decide +kernel
private theorem mom_4022_853_part5 :
    blockEstimate 4022 853 1493 128 = 105726861600 := by decide +kernel
private theorem mom_4022_853_part6 :
    blockEstimate 4022 853 1621 128 = 141778186613 := by decide +kernel
private theorem mom_4022_853_part7 :
    blockEstimate 4022 853 1749 128 = 178616873792 := by decide +kernel
private theorem mom_4022_853_part8 :
    blockEstimate 4022 853 1877 128 = 212204516160 := by decide +kernel
private theorem mom_4022_853_part9 :
    blockEstimate 4022 853 2005 128 = 242210222912 := by decide +kernel
private theorem mom_4022_853_part10 :
    blockEstimate 4022 853 2133 128 = 268633994048 := by decide +kernel
private theorem mom_4022_853_part11 :
    blockEstimate 4022 853 2261 128 = 291475829568 := by decide +kernel
private theorem mom_4022_853_part12 :
    blockEstimate 4022 853 2389 128 = 310735729472 := by decide +kernel
private theorem mom_4022_853_part13 :
    blockEstimate 4022 853 2517 128 = 326413693760 := by decide +kernel
private theorem mom_4022_853_part14 :
    blockEstimate 4022 853 2645 128 = 338509722432 := by decide +kernel
private theorem mom_4022_853_part15 :
    blockEstimate 4022 853 2773 128 = 347023815488 := by decide +kernel
private theorem mom_4022_853_part16 :
    blockEstimate 4022 853 2901 128 = 351955972928 := by decide +kernel
private theorem mom_4022_853_part17 :
    blockEstimate 4022 853 3029 128 = 353306194752 := by decide +kernel
private theorem mom_4022_853_part18 :
    blockEstimate 4022 853 3157 128 = 351074480960 := by decide +kernel
private theorem mom_4022_853_part19 :
    blockEstimate 4022 853 3285 128 = 345260831552 := by decide +kernel
private theorem mom_4022_853_part20 :
    blockEstimate 4022 853 3413 128 = 335865246528 := by decide +kernel
private theorem mom_4022_853_part21 :
    blockEstimate 4022 853 3541 128 = 322887725888 := by decide +kernel
private theorem mom_4022_853_part22 :
    blockEstimate 4022 853 3669 128 = 306328269632 := by decide +kernel
private theorem mom_4022_853_part23 :
    blockEstimate 4022 853 3797 128 = 286186877760 := by decide +kernel
private theorem mom_4022_853_part24 :
    blockEstimate 4022 853 3925 128 = 262469661432 := by decide +kernel
private theorem mom_4022_853_part25 :
    blockEstimate 4022 853 4053 128 = 235994998974 := by decide +kernel
private theorem mom_4022_853_part26 :
    blockEstimate 4022 853 4181 128 = 208639666086 := by decide +kernel
private theorem mom_4022_853_part27 :
    blockEstimate 4022 853 4309 128 = 181135208472 := by decide +kernel
private theorem mom_4022_853_part28 :
    blockEstimate 4022 853 4437 128 = 154017829623 := by decide +kernel
private theorem mom_4022_853_part29 :
    blockEstimate 4022 853 4565 128 = 127793556806 := by decide +kernel
private theorem mom_4022_853_part30 :
    blockEstimate 4022 853 4693 128 = 102938242626 := by decide +kernel
private theorem mom_4022_853_part31 :
    blockEstimate 4022 853 4821 128 = 79844384636 := by decide +kernel
private theorem mom_4022_853_part32 :
    blockEstimate 4022 853 4949 128 = 58856041408 := by decide +kernel
private theorem mom_4022_853_part33 :
    blockEstimate 4022 853 5077 128 = 40640754624 := by decide +kernel
private theorem mom_4022_853_part34 :
    blockEstimate 4022 853 5205 128 = 25487244224 := by decide +kernel
private theorem mom_4022_853_part35 :
    blockEstimate 4022 853 5333 128 = 13647168448 := by decide +kernel
private theorem mom_4022_853_part36 :
    blockEstimate 4022 853 5461 128 = 5372185536 := by decide +kernel
private theorem mom_4022_853_part37 :
    blockEstimate 4022 853 5589 128 = 913953728 := by decide +kernel
private theorem mom_4022_853_part38 :
    blockEstimate 4022 853 5717 11 = 646812 := by decide +kernel
private theorem mom_4022_853_join0 :
    blockEstimate 4022 853 853 256 = 10837406272 :=
  block_append mom_4022_853_part0 mom_4022_853_part1 rfl rfl rfl
private theorem mom_4022_853_join1 :
    blockEstimate 4022 853 1109 256 = 71037612608 :=
  block_append mom_4022_853_part2 mom_4022_853_part3 rfl rfl rfl
private theorem mom_4022_853_join2 :
    blockEstimate 4022 853 853 512 = 81875018880 :=
  block_append mom_4022_853_join0 mom_4022_853_join1 rfl rfl rfl
private theorem mom_4022_853_join3 :
    blockEstimate 4022 853 1365 256 = 179363263040 :=
  block_append mom_4022_853_part4 mom_4022_853_part5 rfl rfl rfl
private theorem mom_4022_853_join4 :
    blockEstimate 4022 853 1749 256 = 390821389952 :=
  block_append mom_4022_853_part7 mom_4022_853_part8 rfl rfl rfl
private theorem mom_4022_853_join5 :
    blockEstimate 4022 853 1621 384 = 532599576565 :=
  block_append mom_4022_853_part6 mom_4022_853_join4 rfl rfl rfl
private theorem mom_4022_853_join6 :
    blockEstimate 4022 853 1365 640 = 711962839605 :=
  block_append mom_4022_853_join3 mom_4022_853_join5 rfl rfl rfl
private theorem mom_4022_853_join7 :
    blockEstimate 4022 853 853 1152 = 793837858485 :=
  block_append mom_4022_853_join2 mom_4022_853_join6 rfl rfl rfl
private theorem mom_4022_853_join8 :
    blockEstimate 4022 853 2005 256 = 510844216960 :=
  block_append mom_4022_853_part9 mom_4022_853_part10 rfl rfl rfl
private theorem mom_4022_853_join9 :
    blockEstimate 4022 853 2389 256 = 637149423232 :=
  block_append mom_4022_853_part12 mom_4022_853_part13 rfl rfl rfl
private theorem mom_4022_853_join10 :
    blockEstimate 4022 853 2261 384 = 928625252800 :=
  block_append mom_4022_853_part11 mom_4022_853_join9 rfl rfl rfl
private theorem mom_4022_853_join11 :
    blockEstimate 4022 853 2005 640 = 1439469469760 :=
  block_append mom_4022_853_join8 mom_4022_853_join10 rfl rfl rfl
private theorem mom_4022_853_join12 :
    blockEstimate 4022 853 2645 256 = 685533537920 :=
  block_append mom_4022_853_part14 mom_4022_853_part15 rfl rfl rfl
private theorem mom_4022_853_join13 :
    blockEstimate 4022 853 3029 256 = 704380675712 :=
  block_append mom_4022_853_part17 mom_4022_853_part18 rfl rfl rfl
private theorem mom_4022_853_join14 :
    blockEstimate 4022 853 2901 384 = 1056336648640 :=
  block_append mom_4022_853_part16 mom_4022_853_join13 rfl rfl rfl
private theorem mom_4022_853_join15 :
    blockEstimate 4022 853 2645 640 = 1741870186560 :=
  block_append mom_4022_853_join12 mom_4022_853_join14 rfl rfl rfl
private theorem mom_4022_853_join16 :
    blockEstimate 4022 853 2005 1280 = 3181339656320 :=
  block_append mom_4022_853_join11 mom_4022_853_join15 rfl rfl rfl
private theorem mom_4022_853_join17 :
    blockEstimate 4022 853 853 2432 = 3975177514805 :=
  block_append mom_4022_853_join7 mom_4022_853_join16 rfl rfl rfl
private theorem mom_4022_853_join18 :
    blockEstimate 4022 853 3285 256 = 681126078080 :=
  block_append mom_4022_853_part19 mom_4022_853_part20 rfl rfl rfl
private theorem mom_4022_853_join19 :
    blockEstimate 4022 853 3669 256 = 592515147392 :=
  block_append mom_4022_853_part22 mom_4022_853_part23 rfl rfl rfl
private theorem mom_4022_853_join20 :
    blockEstimate 4022 853 3541 384 = 915402873280 :=
  block_append mom_4022_853_part21 mom_4022_853_join19 rfl rfl rfl
private theorem mom_4022_853_join21 :
    blockEstimate 4022 853 3285 640 = 1596528951360 :=
  block_append mom_4022_853_join18 mom_4022_853_join20 rfl rfl rfl
private theorem mom_4022_853_join22 :
    blockEstimate 4022 853 3925 256 = 498464660406 :=
  block_append mom_4022_853_part24 mom_4022_853_part25 rfl rfl rfl
private theorem mom_4022_853_join23 :
    blockEstimate 4022 853 4309 256 = 335153038095 :=
  block_append mom_4022_853_part27 mom_4022_853_part28 rfl rfl rfl
private theorem mom_4022_853_join24 :
    blockEstimate 4022 853 4181 384 = 543792704181 :=
  block_append mom_4022_853_part26 mom_4022_853_join23 rfl rfl rfl
private theorem mom_4022_853_join25 :
    blockEstimate 4022 853 3925 640 = 1042257364587 :=
  block_append mom_4022_853_join22 mom_4022_853_join24 rfl rfl rfl
private theorem mom_4022_853_join26 :
    blockEstimate 4022 853 3285 1280 = 2638786315947 :=
  block_append mom_4022_853_join21 mom_4022_853_join25 rfl rfl rfl
private theorem mom_4022_853_join27 :
    blockEstimate 4022 853 4565 256 = 230731799432 :=
  block_append mom_4022_853_part29 mom_4022_853_part30 rfl rfl rfl
private theorem mom_4022_853_join28 :
    blockEstimate 4022 853 4949 256 = 99496796032 :=
  block_append mom_4022_853_part32 mom_4022_853_part33 rfl rfl rfl
private theorem mom_4022_853_join29 :
    blockEstimate 4022 853 4821 384 = 179341180668 :=
  block_append mom_4022_853_part31 mom_4022_853_join28 rfl rfl rfl
private theorem mom_4022_853_join30 :
    blockEstimate 4022 853 4565 640 = 410072980100 :=
  block_append mom_4022_853_join27 mom_4022_853_join29 rfl rfl rfl
private theorem mom_4022_853_join31 :
    blockEstimate 4022 853 5205 256 = 39134412672 :=
  block_append mom_4022_853_part34 mom_4022_853_part35 rfl rfl rfl
private theorem mom_4022_853_join32 :
    blockEstimate 4022 853 5589 139 = 914600540 :=
  block_append mom_4022_853_part37 mom_4022_853_part38 rfl rfl rfl
private theorem mom_4022_853_join33 :
    blockEstimate 4022 853 5461 267 = 6286786076 :=
  block_append mom_4022_853_part36 mom_4022_853_join32 rfl rfl rfl
private theorem mom_4022_853_join34 :
    blockEstimate 4022 853 5205 523 = 45421198748 :=
  block_append mom_4022_853_join31 mom_4022_853_join33 rfl rfl rfl
private theorem mom_4022_853_join35 :
    blockEstimate 4022 853 4565 1163 = 455494178848 :=
  block_append mom_4022_853_join30 mom_4022_853_join34 rfl rfl rfl
private theorem mom_4022_853_join36 :
    blockEstimate 4022 853 3285 2443 = 3094280494795 :=
  block_append mom_4022_853_join26 mom_4022_853_join35 rfl rfl rfl
private theorem mom_4022_853_join37 :
    blockEstimate 4022 853 853 4875 = 7069458009600 :=
  block_append mom_4022_853_join17 mom_4022_853_join36 rfl rfl rfl
private theorem mom_4022_853 : momentEstimate 4022 853 = 7069458009600 := mom_4022_853_join37
private theorem rc_0_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 0 128 = 2389230687263171239941739744 := by decide +kernel
private theorem rc_0_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 128 128 = 1922315376626047007073461472 := by decide +kernel
private theorem rc_0_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 256 128 = 1488054086790429572972623072 := by decide +kernel
private theorem rc_0_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 384 128 = 1085254396098338014556742336 := by decide +kernel
private theorem rc_0_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 512 128 = 712729698290194252121696241 := by decide +kernel
private theorem rc_0_8_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 640 128 = 369296353488831486128774139 := by decide +kernel
private theorem rc_0_8_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 768 86 = 69242298528437002240097724 := by decide +kernel
private theorem rc_0_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 128 256 = 3410369463416476580046084544 :=
  phaseBlock_append rc_0_8_2360_0_part1 rc_0_8_2360_0_part2 rfl rfl rfl
private theorem rc_0_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 0 384 = 5799600150679647819987824288 :=
  phaseBlock_append rc_0_8_2360_0_part0 rc_0_8_2360_0_join0 rfl rfl rfl
private theorem rc_0_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 384 256 = 1797984094388532266678438577 :=
  phaseBlock_append rc_0_8_2360_0_part3 rc_0_8_2360_0_part4 rfl rfl rfl
private theorem rc_0_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 640 214 = 438538652017268488368871863 :=
  phaseBlock_append rc_0_8_2360_0_part5 rc_0_8_2360_0_part6 rfl rfl rfl
private theorem rc_0_8_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 384 470 = 2236522746405800755047310440 :=
  phaseBlock_append rc_0_8_2360_0_join2 rc_0_8_2360_0_join3 rfl rfl rfl
private theorem rc_0_8_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 0) 0 854 = 8036122897085448575035134728 :=
  phaseBlock_append rc_0_8_2360_0_join1 rc_0_8_2360_0_join4 rfl rfl rfl
private theorem rc_0_8_2360_0 : fastPhase (bank 0 8).shape 179808 2360 19 1 0 1 0 = 8036122897085448575035134728 :=
  phase_of_block (n := 854) (by decide +kernel) rc_0_8_2360_0_join5
private theorem rc_0_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 0 128 = 2385501751074510869985551712 := by decide +kernel
private theorem rc_0_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 128 128 = 1918837554726387690409604448 := by decide +kernel
private theorem rc_0_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 256 128 = 1484818344531653372303934816 := by decide +kernel
private theorem rc_0_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 384 128 = 1082251735252571544667329636 := by decide +kernel
private theorem rc_0_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 512 128 = 709951152848406253231484575 := by decide +kernel
private theorem rc_0_8_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 640 128 = 366732988299701204462080997 := by decide +kernel
private theorem rc_0_8_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 768 86 = 67636439613439788065973831 := by decide +kernel
private theorem rc_0_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 128 256 = 3403655899258041062713539264 :=
  phaseBlock_append rc_0_8_2360_1_part1 rc_0_8_2360_1_part2 rfl rfl rfl
private theorem rc_0_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 0 384 = 5789157650332551932699090976 :=
  phaseBlock_append rc_0_8_2360_1_part0 rc_0_8_2360_1_join0 rfl rfl rfl
private theorem rc_0_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 384 256 = 1792202888100977797898814211 :=
  phaseBlock_append rc_0_8_2360_1_part3 rc_0_8_2360_1_part4 rfl rfl rfl
private theorem rc_0_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 640 214 = 434369427913140992528054828 :=
  phaseBlock_append rc_0_8_2360_1_part5 rc_0_8_2360_1_part6 rfl rfl rfl
private theorem rc_0_8_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 384 470 = 2226572316014118790426869039 :=
  phaseBlock_append rc_0_8_2360_1_join2 rc_0_8_2360_1_join3 rfl rfl rfl
private theorem rc_0_8_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2360 19 1 0 1 1) 0 854 = 8015729966346670723125960015 :=
  phaseBlock_append rc_0_8_2360_1_join1 rc_0_8_2360_1_join4 rfl rfl rfl
private theorem rc_0_8_2360_1 : fastPhase (bank 0 8).shape 179808 2360 19 1 0 1 1 = 8015729966346670723125960015 :=
  phase_of_block (n := 854) (by decide +kernel) rc_0_8_2360_1_join5
private theorem rc_0_8_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 0 128 = 2389251988883583562138902144 := by decide +kernel
private theorem rc_0_8_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 128 128 = 1922331019063169022330986112 := by decide +kernel
private theorem rc_0_8_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 256 128 = 1488064982788332171829436032 := by decide +kernel
private theorem rc_0_8_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 384 128 = 1085261415958630476806829092 := by decide +kernel
private theorem rc_0_8_2361_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 512 128 = 712733664247176738510381900 := by decide +kernel
private theorem rc_0_8_2361_0_part5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 640 128 = 369298064912284975930428421 := by decide +kernel
private theorem rc_0_8_2361_0_part6 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 768 86 = 69242564158666252865433152 := by decide +kernel
private theorem rc_0_8_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 128 256 = 3410396001851501194160422144 :=
  phaseBlock_append rc_0_8_2361_0_part1 rc_0_8_2361_0_part2 rfl rfl rfl
private theorem rc_0_8_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 0 384 = 5799647990735084756299324288 :=
  phaseBlock_append rc_0_8_2361_0_part0 rc_0_8_2361_0_join0 rfl rfl rfl
private theorem rc_0_8_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 384 256 = 1797995080205807215317210992 :=
  phaseBlock_append rc_0_8_2361_0_part3 rc_0_8_2361_0_part4 rfl rfl rfl
private theorem rc_0_8_2361_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 640 214 = 438540629070951228795861573 :=
  phaseBlock_append rc_0_8_2361_0_part5 rc_0_8_2361_0_part6 rfl rfl rfl
private theorem rc_0_8_2361_0_join4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 384 470 = 2236535709276758444113072565 :=
  phaseBlock_append rc_0_8_2361_0_join2 rc_0_8_2361_0_join3 rfl rfl rfl
private theorem rc_0_8_2361_0_join5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 0) 0 854 = 8036183700011843200412396853 :=
  phaseBlock_append rc_0_8_2361_0_join1 rc_0_8_2361_0_join4 rfl rfl rfl
private theorem rc_0_8_2361_0 : fastPhase (bank 0 8).shape 179808 2361 19 1 0 1 0 = 8036183700011843200412396853 :=
  phase_of_block (n := 854) (by decide +kernel) rc_0_8_2361_0_join5
private theorem rc_0_8_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 0 128 = 2385523025379803901818267712 := by decide +kernel
private theorem rc_0_8_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 128 128 = 1918853173482268377142462528 := by decide +kernel
private theorem rc_0_8_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 256 128 = 1484829220287981065414027328 := by decide +kernel
private theorem rc_0_8_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 384 128 = 1082258738121576555685503227 := by decide +kernel
private theorem rc_0_8_2361_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 512 128 = 709955104906789352793006112 := by decide +kernel
private theorem rc_0_8_2361_1_part5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 640 128 = 366734688727308874964512617 := by decide +kernel
private theorem rc_0_8_2361_1_part6 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 768 86 = 67636699385893691305329560 := by decide +kernel
private theorem rc_0_8_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 128 256 = 3403682393770249442556489856 :=
  phaseBlock_append rc_0_8_2361_1_part1 rc_0_8_2361_1_part2 rfl rfl rfl
private theorem rc_0_8_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 0 384 = 5789205419150053344374757568 :=
  phaseBlock_append rc_0_8_2361_1_part0 rc_0_8_2361_1_join0 rfl rfl rfl
private theorem rc_0_8_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 384 256 = 1792213843028365908478509339 :=
  phaseBlock_append rc_0_8_2361_1_part3 rc_0_8_2361_1_part4 rfl rfl rfl
private theorem rc_0_8_2361_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 640 214 = 434371388113202566269842177 :=
  phaseBlock_append rc_0_8_2361_1_part5 rc_0_8_2361_1_part6 rfl rfl rfl
private theorem rc_0_8_2361_1_join4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 384 470 = 2226585231141568474748351516 :=
  phaseBlock_append rc_0_8_2361_1_join2 rc_0_8_2361_1_join3 rfl rfl rfl
private theorem rc_0_8_2361_1_join5 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2361 19 1 0 1 1) 0 854 = 8015790650291621819123109084 :=
  phaseBlock_append rc_0_8_2361_1_join1 rc_0_8_2361_1_join4 rfl rfl rfl
private theorem rc_0_8_2361_1 : fastPhase (bank 0 8).shape 179808 2361 19 1 0 1 1 = 8015790650291621819123109084 :=
  phase_of_block (n := 854) (by decide +kernel) rc_0_8_2361_1_join5
private theorem receipt_0_8 : B1Checked (bank 0 8) 19 0 1 := by
  refine b1_checked_from_values (bank 0 8) 19 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_4022_853)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_8_2360_0 rc_0_8_2360_1 rc_0_8_2361_0 rc_0_8_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_4969_1053_part0 :
    blockEstimate 4969 1053 1053 128 = 1743632800 := by decide +kernel
private theorem mom_4969_1053_part1 :
    blockEstimate 4969 1053 1181 128 = 11772889504 := by decide +kernel
private theorem mom_4969_1053_part2 :
    blockEstimate 4969 1053 1309 128 = 31011789216 := by decide +kernel
private theorem mom_4969_1053_part3 :
    blockEstimate 4969 1053 1437 128 = 58655025568 := by decide +kernel
private theorem mom_4969_1053_part4 :
    blockEstimate 4969 1053 1565 128 = 93897292192 := by decide +kernel
private theorem mom_4969_1053_part5 :
    blockEstimate 4969 1053 1693 128 = 135933282720 := by decide +kernel
private theorem mom_4969_1053_part6 :
    blockEstimate 4969 1053 1821 128 = 183957690784 := by decide +kernel
private theorem mom_4969_1053_part7 :
    blockEstimate 4969 1053 1949 128 = 237165210016 := by decide +kernel
private theorem mom_4969_1053_part8 :
    blockEstimate 4969 1053 2077 128 = 294129242223 := by decide +kernel
private theorem mom_4969_1053_part9 :
    blockEstimate 4969 1053 2205 128 = 349226423872 := by decide +kernel
private theorem mom_4969_1053_part10 :
    blockEstimate 4969 1053 2333 128 = 399918798400 := by decide +kernel
private theorem mom_4969_1053_part11 :
    blockEstimate 4969 1053 2461 128 = 446190376512 := by decide +kernel
private theorem mom_4969_1053_part12 :
    blockEstimate 4969 1053 2589 128 = 488041158208 := by decide +kernel
private theorem mom_4969_1053_part13 :
    blockEstimate 4969 1053 2717 128 = 525471143488 := by decide +kernel
private theorem mom_4969_1053_part14 :
    blockEstimate 4969 1053 2845 128 = 558480332352 := by decide +kernel
private theorem mom_4969_1053_part15 :
    blockEstimate 4969 1053 2973 128 = 587068724800 := by decide +kernel
private theorem mom_4969_1053_part16 :
    blockEstimate 4969 1053 3101 128 = 611236320832 := by decide +kernel
private theorem mom_4969_1053_part17 :
    blockEstimate 4969 1053 3229 128 = 630983120448 := by decide +kernel
private theorem mom_4969_1053_part18 :
    blockEstimate 4969 1053 3357 128 = 646309123648 := by decide +kernel
private theorem mom_4969_1053_part19 :
    blockEstimate 4969 1053 3485 128 = 657214330432 := by decide +kernel
private theorem mom_4969_1053_part20 :
    blockEstimate 4969 1053 3613 128 = 663698740800 := by decide +kernel
private theorem mom_4969_1053_part21 :
    blockEstimate 4969 1053 3741 128 = 665762354752 := by decide +kernel
private theorem mom_4969_1053_part22 :
    blockEstimate 4969 1053 3869 128 = 663405172288 := by decide +kernel
private theorem mom_4969_1053_part23 :
    blockEstimate 4969 1053 3997 128 = 656627193408 := by decide +kernel
private theorem mom_4969_1053_part24 :
    blockEstimate 4969 1053 4125 128 = 645428418112 := by decide +kernel
private theorem mom_4969_1053_part25 :
    blockEstimate 4969 1053 4253 128 = 629808846400 := by decide +kernel
private theorem mom_4969_1053_part26 :
    blockEstimate 4969 1053 4381 128 = 609768478272 := by decide +kernel
private theorem mom_4969_1053_part27 :
    blockEstimate 4969 1053 4509 128 = 585307313728 := by decide +kernel
private theorem mom_4969_1053_part28 :
    blockEstimate 4969 1053 4637 128 = 556425352768 := by decide +kernel
private theorem mom_4969_1053_part29 :
    blockEstimate 4969 1053 4765 128 = 523122595392 := by decide +kernel
private theorem mom_4969_1053_part30 :
    blockEstimate 4969 1053 4893 128 = 485434243390 := by decide +kernel
private theorem mom_4969_1053_part31 :
    blockEstimate 4969 1053 5021 128 = 444720572477 := by decide +kernel
private theorem mom_4969_1053_part32 :
    blockEstimate 4969 1053 5149 128 = 403024625209 := by decide +kernel
private theorem mom_4969_1053_part33 :
    blockEstimate 4969 1053 5277 128 = 361015465641 := by decide +kernel
private theorem mom_4969_1053_part34 :
    blockEstimate 4969 1053 5405 128 = 319238146213 := by decide +kernel
private theorem mom_4969_1053_part35 :
    blockEstimate 4969 1053 5533 128 = 278213270417 := by decide +kernel
private theorem mom_4969_1053_part36 :
    blockEstimate 4969 1053 5661 128 = 238436991255 := by decide +kernel
private theorem mom_4969_1053_part37 :
    blockEstimate 4969 1053 5789 128 = 200381013050 := by decide +kernel
private theorem mom_4969_1053_part38 :
    blockEstimate 4969 1053 5917 128 = 164483393524 := by decide +kernel
private theorem mom_4969_1053_part39 :
    blockEstimate 4969 1053 6045 128 = 130906741776 := by decide +kernel
private theorem mom_4969_1053_part40 :
    blockEstimate 4969 1053 6173 128 = 100408899600 := by decide +kernel
private theorem mom_4969_1053_part41 :
    blockEstimate 4969 1053 6301 128 = 73472349200 := by decide +kernel
private theorem mom_4969_1053_part42 :
    blockEstimate 4969 1053 6429 128 = 50348748816 := by decide +kernel
private theorem mom_4969_1053_part43 :
    blockEstimate 4969 1053 6557 128 = 31289756688 := by decide +kernel
private theorem mom_4969_1053_part44 :
    blockEstimate 4969 1053 6685 128 = 16547031056 := by decide +kernel
private theorem mom_4969_1053_part45 :
    blockEstimate 4969 1053 6813 128 = 6372230160 := by decide +kernel
private theorem mom_4969_1053_part46 :
    blockEstimate 4969 1053 6941 128 = 1017012240 := by decide +kernel
private theorem mom_4969_1053_part47 :
    blockEstimate 4969 1053 7069 6 = 168871 := by decide +kernel
private theorem mom_4969_1053_join0 :
    blockEstimate 4969 1053 1181 256 = 42784678720 :=
  block_append mom_4969_1053_part1 mom_4969_1053_part2 rfl rfl rfl
private theorem mom_4969_1053_join1 :
    blockEstimate 4969 1053 1053 384 = 44528311520 :=
  block_append mom_4969_1053_part0 mom_4969_1053_join0 rfl rfl rfl
private theorem mom_4969_1053_join2 :
    blockEstimate 4969 1053 1565 256 = 229830574912 :=
  block_append mom_4969_1053_part4 mom_4969_1053_part5 rfl rfl rfl
private theorem mom_4969_1053_join3 :
    blockEstimate 4969 1053 1437 384 = 288485600480 :=
  block_append mom_4969_1053_part3 mom_4969_1053_join2 rfl rfl rfl
private theorem mom_4969_1053_join4 :
    blockEstimate 4969 1053 1053 768 = 333013912000 :=
  block_append mom_4969_1053_join1 mom_4969_1053_join3 rfl rfl rfl
private theorem mom_4969_1053_join5 :
    blockEstimate 4969 1053 1949 256 = 531294452239 :=
  block_append mom_4969_1053_part7 mom_4969_1053_part8 rfl rfl rfl
private theorem mom_4969_1053_join6 :
    blockEstimate 4969 1053 1821 384 = 715252143023 :=
  block_append mom_4969_1053_part6 mom_4969_1053_join5 rfl rfl rfl
private theorem mom_4969_1053_join7 :
    blockEstimate 4969 1053 2333 256 = 846109174912 :=
  block_append mom_4969_1053_part10 mom_4969_1053_part11 rfl rfl rfl
private theorem mom_4969_1053_join8 :
    blockEstimate 4969 1053 2205 384 = 1195335598784 :=
  block_append mom_4969_1053_part9 mom_4969_1053_join7 rfl rfl rfl
private theorem mom_4969_1053_join9 :
    blockEstimate 4969 1053 1821 768 = 1910587741807 :=
  block_append mom_4969_1053_join6 mom_4969_1053_join8 rfl rfl rfl
private theorem mom_4969_1053_join10 :
    blockEstimate 4969 1053 1053 1536 = 2243601653807 :=
  block_append mom_4969_1053_join4 mom_4969_1053_join9 rfl rfl rfl
private theorem mom_4969_1053_join11 :
    blockEstimate 4969 1053 2717 256 = 1083951475840 :=
  block_append mom_4969_1053_part13 mom_4969_1053_part14 rfl rfl rfl
private theorem mom_4969_1053_join12 :
    blockEstimate 4969 1053 2589 384 = 1571992634048 :=
  block_append mom_4969_1053_part12 mom_4969_1053_join11 rfl rfl rfl
private theorem mom_4969_1053_join13 :
    blockEstimate 4969 1053 3101 256 = 1242219441280 :=
  block_append mom_4969_1053_part16 mom_4969_1053_part17 rfl rfl rfl
private theorem mom_4969_1053_join14 :
    blockEstimate 4969 1053 2973 384 = 1829288166080 :=
  block_append mom_4969_1053_part15 mom_4969_1053_join13 rfl rfl rfl
private theorem mom_4969_1053_join15 :
    blockEstimate 4969 1053 2589 768 = 3401280800128 :=
  block_append mom_4969_1053_join12 mom_4969_1053_join14 rfl rfl rfl
private theorem mom_4969_1053_join16 :
    blockEstimate 4969 1053 3485 256 = 1320913071232 :=
  block_append mom_4969_1053_part19 mom_4969_1053_part20 rfl rfl rfl
private theorem mom_4969_1053_join17 :
    blockEstimate 4969 1053 3357 384 = 1967222194880 :=
  block_append mom_4969_1053_part18 mom_4969_1053_join16 rfl rfl rfl
private theorem mom_4969_1053_join18 :
    blockEstimate 4969 1053 3869 256 = 1320032365696 :=
  block_append mom_4969_1053_part22 mom_4969_1053_part23 rfl rfl rfl
private theorem mom_4969_1053_join19 :
    blockEstimate 4969 1053 3741 384 = 1985794720448 :=
  block_append mom_4969_1053_part21 mom_4969_1053_join18 rfl rfl rfl
private theorem mom_4969_1053_join20 :
    blockEstimate 4969 1053 3357 768 = 3953016915328 :=
  block_append mom_4969_1053_join17 mom_4969_1053_join19 rfl rfl rfl
private theorem mom_4969_1053_join21 :
    blockEstimate 4969 1053 2589 1536 = 7354297715456 :=
  block_append mom_4969_1053_join15 mom_4969_1053_join20 rfl rfl rfl
private theorem mom_4969_1053_join22 :
    blockEstimate 4969 1053 1053 3072 = 9597899369263 :=
  block_append mom_4969_1053_join10 mom_4969_1053_join21 rfl rfl rfl
private theorem mom_4969_1053_join23 :
    blockEstimate 4969 1053 4253 256 = 1239577324672 :=
  block_append mom_4969_1053_part25 mom_4969_1053_part26 rfl rfl rfl
private theorem mom_4969_1053_join24 :
    blockEstimate 4969 1053 4125 384 = 1885005742784 :=
  block_append mom_4969_1053_part24 mom_4969_1053_join23 rfl rfl rfl
private theorem mom_4969_1053_join25 :
    blockEstimate 4969 1053 4637 256 = 1079547948160 :=
  block_append mom_4969_1053_part28 mom_4969_1053_part29 rfl rfl rfl
private theorem mom_4969_1053_join26 :
    blockEstimate 4969 1053 4509 384 = 1664855261888 :=
  block_append mom_4969_1053_part27 mom_4969_1053_join25 rfl rfl rfl
private theorem mom_4969_1053_join27 :
    blockEstimate 4969 1053 4125 768 = 3549861004672 :=
  block_append mom_4969_1053_join24 mom_4969_1053_join26 rfl rfl rfl
private theorem mom_4969_1053_join28 :
    blockEstimate 4969 1053 5021 256 = 847745197686 :=
  block_append mom_4969_1053_part31 mom_4969_1053_part32 rfl rfl rfl
private theorem mom_4969_1053_join29 :
    blockEstimate 4969 1053 4893 384 = 1333179441076 :=
  block_append mom_4969_1053_part30 mom_4969_1053_join28 rfl rfl rfl
private theorem mom_4969_1053_join30 :
    blockEstimate 4969 1053 5405 256 = 597451416630 :=
  block_append mom_4969_1053_part34 mom_4969_1053_part35 rfl rfl rfl
private theorem mom_4969_1053_join31 :
    blockEstimate 4969 1053 5277 384 = 958466882271 :=
  block_append mom_4969_1053_part33 mom_4969_1053_join30 rfl rfl rfl
private theorem mom_4969_1053_join32 :
    blockEstimate 4969 1053 4893 768 = 2291646323347 :=
  block_append mom_4969_1053_join29 mom_4969_1053_join31 rfl rfl rfl
private theorem mom_4969_1053_join33 :
    blockEstimate 4969 1053 4125 1536 = 5841507328019 :=
  block_append mom_4969_1053_join27 mom_4969_1053_join32 rfl rfl rfl
private theorem mom_4969_1053_join34 :
    blockEstimate 4969 1053 5789 256 = 364864406574 :=
  block_append mom_4969_1053_part37 mom_4969_1053_part38 rfl rfl rfl
private theorem mom_4969_1053_join35 :
    blockEstimate 4969 1053 5661 384 = 603301397829 :=
  block_append mom_4969_1053_part36 mom_4969_1053_join34 rfl rfl rfl
private theorem mom_4969_1053_join36 :
    blockEstimate 4969 1053 6173 256 = 173881248800 :=
  block_append mom_4969_1053_part40 mom_4969_1053_part41 rfl rfl rfl
private theorem mom_4969_1053_join37 :
    blockEstimate 4969 1053 6045 384 = 304787990576 :=
  block_append mom_4969_1053_part39 mom_4969_1053_join36 rfl rfl rfl
private theorem mom_4969_1053_join38 :
    blockEstimate 4969 1053 5661 768 = 908089388405 :=
  block_append mom_4969_1053_join35 mom_4969_1053_join37 rfl rfl rfl
private theorem mom_4969_1053_join39 :
    blockEstimate 4969 1053 6557 256 = 47836787744 :=
  block_append mom_4969_1053_part43 mom_4969_1053_part44 rfl rfl rfl
private theorem mom_4969_1053_join40 :
    blockEstimate 4969 1053 6429 384 = 98185536560 :=
  block_append mom_4969_1053_part42 mom_4969_1053_join39 rfl rfl rfl
private theorem mom_4969_1053_join41 :
    blockEstimate 4969 1053 6941 134 = 1017181111 :=
  block_append mom_4969_1053_part46 mom_4969_1053_part47 rfl rfl rfl
private theorem mom_4969_1053_join42 :
    blockEstimate 4969 1053 6813 262 = 7389411271 :=
  block_append mom_4969_1053_part45 mom_4969_1053_join41 rfl rfl rfl
private theorem mom_4969_1053_join43 :
    blockEstimate 4969 1053 6429 646 = 105574947831 :=
  block_append mom_4969_1053_join40 mom_4969_1053_join42 rfl rfl rfl
private theorem mom_4969_1053_join44 :
    blockEstimate 4969 1053 5661 1414 = 1013664336236 :=
  block_append mom_4969_1053_join38 mom_4969_1053_join43 rfl rfl rfl
private theorem mom_4969_1053_join45 :
    blockEstimate 4969 1053 4125 2950 = 6855171664255 :=
  block_append mom_4969_1053_join33 mom_4969_1053_join44 rfl rfl rfl
private theorem mom_4969_1053_join46 :
    blockEstimate 4969 1053 1053 6022 = 16453071033518 :=
  block_append mom_4969_1053_join22 mom_4969_1053_join45 rfl rfl rfl
private theorem mom_4969_1053 : momentEstimate 4969 1053 = 16453071033518 := mom_4969_1053_join46
private theorem rc_0_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 0 128 = 8479184280514496836930249152 := by decide +kernel
private theorem rc_0_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 128 128 = 7144544145180645118011220416 := by decide +kernel
private theorem rc_0_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 256 128 = 5885085613612043817884918208 := by decide +kernel
private theorem rc_0_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 384 128 = 4698616673706914637021618624 := by decide +kernel
private theorem rc_0_9_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 512 128 = 3582952622860042607218413261 := by decide +kernel
private theorem rc_0_9_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 640 128 = 2535917993720049828288410514 := by decide +kernel
private theorem rc_0_9_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 768 128 = 1555336075176899471946871554 := by decide +kernel
private theorem rc_0_9_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 896 128 = 639033529619750031881036895 := by decide +kernel
private theorem rc_0_9_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 1024 30 = 23963667519880209738131076 := by decide +kernel
private theorem rc_0_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 0 256 = 15623728425695141954941469568 :=
  phaseBlock_append rc_0_9_2360_0_part0 rc_0_9_2360_0_part1 rfl rfl rfl
private theorem rc_0_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 256 256 = 10583702287318958454906536832 :=
  phaseBlock_append rc_0_9_2360_0_part2 rc_0_9_2360_0_part3 rfl rfl rfl
private theorem rc_0_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 0 512 = 26207430713014100409848006400 :=
  phaseBlock_append rc_0_9_2360_0_join0 rc_0_9_2360_0_join1 rfl rfl rfl
private theorem rc_0_9_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 512 256 = 6118870616580092435506823775 :=
  phaseBlock_append rc_0_9_2360_0_part4 rc_0_9_2360_0_part5 rfl rfl rfl
private theorem rc_0_9_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 896 158 = 662997197139630241619167971 :=
  phaseBlock_append rc_0_9_2360_0_part7 rc_0_9_2360_0_part8 rfl rfl rfl
private theorem rc_0_9_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 768 286 = 2218333272316529713566039525 :=
  phaseBlock_append rc_0_9_2360_0_part6 rc_0_9_2360_0_join4 rfl rfl rfl
private theorem rc_0_9_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 512 542 = 8337203888896622149072863300 :=
  phaseBlock_append rc_0_9_2360_0_join3 rc_0_9_2360_0_join5 rfl rfl rfl
private theorem rc_0_9_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 0) 0 1054 = 34544634601910722558920869700 :=
  phaseBlock_append rc_0_9_2360_0_join2 rc_0_9_2360_0_join6 rfl rfl rfl
private theorem rc_0_9_2360_0 : fastPhase (bank 0 9).shape 179808 2360 28 1 0 1 0 = 34544634601910722558920869700 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_0_9_2360_0_join7
private theorem rc_0_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 0 128 = 8468599469548938617167999488 := by decide +kernel
private theorem rc_0_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 128 128 = 7134535360859982774010827264 := by decide +kernel
private theorem rc_0_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 256 128 = 5875636257992746688876818944 := by decide +kernel
private theorem rc_0_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 384 128 = 4689710198437429276542669312 := by decide +kernel
private theorem rc_0_9_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 512 128 = 3574572527299940535486499425 := by decide +kernel
private theorem rc_0_9_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 640 128 = 2528047814414372689284393750 := by decide +kernel
private theorem rc_0_9_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 768 128 = 1547959393244644479847716882 := by decide +kernel
private theorem rc_0_9_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 896 128 = 632133975672520406488700334 := by decide +kernel
private theorem rc_0_9_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 1024 30 = 22413843433987155147968544 := by decide +kernel
private theorem rc_0_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 0 256 = 15603134830408921391178826752 :=
  phaseBlock_append rc_0_9_2360_1_part0 rc_0_9_2360_1_part1 rfl rfl rfl
private theorem rc_0_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 256 256 = 10565346456430175965419488256 :=
  phaseBlock_append rc_0_9_2360_1_part2 rc_0_9_2360_1_part3 rfl rfl rfl
private theorem rc_0_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 0 512 = 26168481286839097356598315008 :=
  phaseBlock_append rc_0_9_2360_1_join0 rc_0_9_2360_1_join1 rfl rfl rfl
private theorem rc_0_9_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 512 256 = 6102620341714313224770893175 :=
  phaseBlock_append rc_0_9_2360_1_part4 rc_0_9_2360_1_part5 rfl rfl rfl
private theorem rc_0_9_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 896 158 = 654547819106507561636668878 :=
  phaseBlock_append rc_0_9_2360_1_part7 rc_0_9_2360_1_part8 rfl rfl rfl
private theorem rc_0_9_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 768 286 = 2202507212351152041484385760 :=
  phaseBlock_append rc_0_9_2360_1_part6 rc_0_9_2360_1_join4 rfl rfl rfl
private theorem rc_0_9_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 512 542 = 8305127554065465266255278935 :=
  phaseBlock_append rc_0_9_2360_1_join3 rc_0_9_2360_1_join5 rfl rfl rfl
private theorem rc_0_9_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2360 28 1 0 1 1) 0 1054 = 34473608840904562622853593943 :=
  phaseBlock_append rc_0_9_2360_1_join2 rc_0_9_2360_1_join6 rfl rfl rfl
private theorem rc_0_9_2360_1 : fastPhase (bank 0 9).shape 179808 2360 28 1 0 1 1 = 34473608840904562622853593943 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_0_9_2360_1_join7
private theorem rc_0_9_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 0 128 = 8479260225110930072897330784 := by decide +kernel
private theorem rc_0_9_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 128 128 = 7144603662796359391128473184 := by decide +kernel
private theorem rc_0_9_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 256 128 = 5885130813600347425702968928 := by decide +kernel
private theorem rc_0_9_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 384 128 = 4698649589857249675784924768 := by decide +kernel
private theorem rc_0_9_2361_0_part4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 512 128 = 3582975195400846144850254689 := by decide +kernel
private theorem rc_0_9_2361_0_part5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 640 128 = 2535932092214790211175690532 := by decide +kernel
private theorem rc_0_9_2361_0_part6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 768 128 = 1555343538178596496798467562 := by decide +kernel
private theorem rc_0_9_2361_0_part7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 896 128 = 639036116096054454022920612 := by decide +kernel
private theorem rc_0_9_2361_0_part8 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 1024 30 = 23963750763055774486044668 := by decide +kernel
private theorem rc_0_9_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 0 256 = 15623863887907289464025803968 :=
  phaseBlock_append rc_0_9_2361_0_part0 rc_0_9_2361_0_part1 rfl rfl rfl
private theorem rc_0_9_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 256 256 = 10583780403457597101487893696 :=
  phaseBlock_append rc_0_9_2361_0_part2 rc_0_9_2361_0_part3 rfl rfl rfl
private theorem rc_0_9_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 0 512 = 26207644291364886565513697664 :=
  phaseBlock_append rc_0_9_2361_0_join0 rc_0_9_2361_0_join1 rfl rfl rfl
private theorem rc_0_9_2361_0_join3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 512 256 = 6118907287615636356025945221 :=
  phaseBlock_append rc_0_9_2361_0_part4 rc_0_9_2361_0_part5 rfl rfl rfl
private theorem rc_0_9_2361_0_join4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 896 158 = 662999866859110228508965280 :=
  phaseBlock_append rc_0_9_2361_0_part7 rc_0_9_2361_0_part8 rfl rfl rfl
private theorem rc_0_9_2361_0_join5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 768 286 = 2218343405037706725307432842 :=
  phaseBlock_append rc_0_9_2361_0_part6 rc_0_9_2361_0_join4 rfl rfl rfl
private theorem rc_0_9_2361_0_join6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 512 542 = 8337250692653343081333378063 :=
  phaseBlock_append rc_0_9_2361_0_join3 rc_0_9_2361_0_join5 rfl rfl rfl
private theorem rc_0_9_2361_0_join7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 0) 0 1054 = 34544894984018229646847075727 :=
  phaseBlock_append rc_0_9_2361_0_join2 rc_0_9_2361_0_join6 rfl rfl rfl
private theorem rc_0_9_2361_0 : fastPhase (bank 0 9).shape 179808 2361 28 1 0 1 0 = 34544894984018229646847075727 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_0_9_2361_0_join7
private theorem rc_0_9_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 0 128 = 8468675336381347844772013920 := by decide +kernel
private theorem rc_0_9_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 128 128 = 7134594809076800754465560416 := by decide +kernel
private theorem rc_0_9_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 256 128 = 5875681396590118175037097824 := by decide +kernel
private theorem rc_0_9_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 384 128 = 4689743060848874913224865632 := by decide +kernel
private theorem rc_0_9_2361_1_part4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 512 128 = 3574595053439878176255832320 := by decide +kernel
private theorem rc_0_9_2361_1_part5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 640 128 = 2528061873558177736786348272 := by decide +kernel
private theorem rc_0_9_2361_1_part6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 768 128 = 1547966823579023776072376275 := by decide +kernel
private theorem rc_0_9_2361_1_part7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 896 128 = 632136535797053227034143127 := by decide +kernel
private theorem rc_0_9_2361_1_part8 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 1024 30 = 22413921374964531972611592 := by decide +kernel
private theorem rc_0_9_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 0 256 = 15603270145458148599237574336 :=
  phaseBlock_append rc_0_9_2361_1_part0 rc_0_9_2361_1_part1 rfl rfl rfl
private theorem rc_0_9_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 256 256 = 10565424457438993088261963456 :=
  phaseBlock_append rc_0_9_2361_1_part2 rc_0_9_2361_1_part3 rfl rfl rfl
private theorem rc_0_9_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 0 512 = 26168694602897141687499537792 :=
  phaseBlock_append rc_0_9_2361_1_join0 rc_0_9_2361_1_join1 rfl rfl rfl
private theorem rc_0_9_2361_1_join3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 512 256 = 6102656926998055913042180592 :=
  phaseBlock_append rc_0_9_2361_1_part4 rc_0_9_2361_1_part5 rfl rfl rfl
private theorem rc_0_9_2361_1_join4 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 896 158 = 654550457172017759006754719 :=
  phaseBlock_append rc_0_9_2361_1_part7 rc_0_9_2361_1_part8 rfl rfl rfl
private theorem rc_0_9_2361_1_join5 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 768 286 = 2202517280751041535079130994 :=
  phaseBlock_append rc_0_9_2361_1_part6 rc_0_9_2361_1_join4 rfl rfl rfl
private theorem rc_0_9_2361_1_join6 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 512 542 = 8305174207749097448121311586 :=
  phaseBlock_append rc_0_9_2361_1_join3 rc_0_9_2361_1_join5 rfl rfl rfl
private theorem rc_0_9_2361_1_join7 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2361 28 1 0 1 1) 0 1054 = 34473868810646239135620849378 :=
  phaseBlock_append rc_0_9_2361_1_join2 rc_0_9_2361_1_join6 rfl rfl rfl
private theorem rc_0_9_2361_1 : fastPhase (bank 0 9).shape 179808 2361 28 1 0 1 1 = 34473868810646239135620849378 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_0_9_2361_1_join7
private theorem receipt_0_9 : B1Checked (bank 0 9) 28 0 1 := by
  refine b1_checked_from_values (bank 0 9) 28 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_4969_1053)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_9_2360_0 rc_0_9_2360_1 rc_0_9_2361_0 rc_0_9_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_6190_1312_part0 :
    blockEstimate 6190 1312 1312 128 = 2180457760 := by decide +kernel
private theorem mom_6190_1312_part1 :
    blockEstimate 6190 1312 1440 128 = 14790341920 := by decide +kernel
private theorem mom_6190_1312_part2 :
    blockEstimate 6190 1312 1568 128 = 39170491680 := by decide +kernel
private theorem mom_6190_1312_part3 :
    blockEstimate 6190 1312 1696 128 = 74515600672 := by decide +kernel
private theorem mom_6190_1312_part4 :
    blockEstimate 6190 1312 1824 128 = 120020362528 := by decide +kernel
private theorem mom_6190_1312_part5 :
    blockEstimate 6190 1312 1952 128 = 174879470880 := by decide +kernel
private theorem mom_6190_1312_part6 :
    blockEstimate 6190 1312 2080 128 = 238287619360 := by decide +kernel
private theorem mom_6190_1312_part7 :
    blockEstimate 6190 1312 2208 128 = 309439501600 := by decide +kernel
private theorem mom_6190_1312_part8 :
    blockEstimate 6190 1312 2336 128 = 387529811232 := by decide +kernel
private theorem mom_6190_1312_part9 :
    blockEstimate 6190 1312 2464 128 = 471753241888 := by decide +kernel
private theorem mom_6190_1312_part10 :
    blockEstimate 6190 1312 2592 128 = 560595816840 := by decide +kernel
private theorem mom_6190_1312_part11 :
    blockEstimate 6190 1312 2720 128 = 647263202560 := by decide +kernel
private theorem mom_6190_1312_part12 :
    blockEstimate 6190 1312 2848 128 = 728450215168 := by decide +kernel
private theorem mom_6190_1312_part13 :
    blockEstimate 6190 1312 2976 128 = 804130106624 := by decide +kernel
private theorem mom_6190_1312_part14 :
    blockEstimate 6190 1312 3104 128 = 874302876928 := by decide +kernel
private theorem mom_6190_1312_part15 :
    blockEstimate 6190 1312 3232 128 = 938968526080 := by decide +kernel
private theorem mom_6190_1312_part16 :
    blockEstimate 6190 1312 3360 128 = 998127054080 := by decide +kernel
private theorem mom_6190_1312_part17 :
    blockEstimate 6190 1312 3488 128 = 1051778460928 := by decide +kernel
private theorem mom_6190_1312_part18 :
    blockEstimate 6190 1312 3616 128 = 1099922746624 := by decide +kernel
private theorem mom_6190_1312_part19 :
    blockEstimate 6190 1312 3744 128 = 1142559911168 := by decide +kernel
private theorem mom_6190_1312_part20 :
    blockEstimate 6190 1312 3872 128 = 1179689954560 := by decide +kernel
private theorem mom_6190_1312_part21 :
    blockEstimate 6190 1312 4000 128 = 1211312876800 := by decide +kernel
private theorem mom_6190_1312_part22 :
    blockEstimate 6190 1312 4128 128 = 1237428677888 := by decide +kernel
private theorem mom_6190_1312_part23 :
    blockEstimate 6190 1312 4256 128 = 1258037357824 := by decide +kernel
private theorem mom_6190_1312_part24 :
    blockEstimate 6190 1312 4384 128 = 1273138916608 := by decide +kernel
private theorem mom_6190_1312_part25 :
    blockEstimate 6190 1312 4512 128 = 1282733354240 := by decide +kernel
private theorem mom_6190_1312_part26 :
    blockEstimate 6190 1312 4640 128 = 1286820670720 := by decide +kernel
private theorem mom_6190_1312_part27 :
    blockEstimate 6190 1312 4768 128 = 1285400866048 := by decide +kernel
private theorem mom_6190_1312_part28 :
    blockEstimate 6190 1312 4896 128 = 1278473940224 := by decide +kernel
private theorem mom_6190_1312_part29 :
    blockEstimate 6190 1312 5024 128 = 1266039893248 := by decide +kernel
private theorem mom_6190_1312_part30 :
    blockEstimate 6190 1312 5152 128 = 1248098725120 := by decide +kernel
private theorem mom_6190_1312_part31 :
    blockEstimate 6190 1312 5280 128 = 1224650435840 := by decide +kernel
private theorem mom_6190_1312_part32 :
    blockEstimate 6190 1312 5408 128 = 1195695025408 := by decide +kernel
private theorem mom_6190_1312_part33 :
    blockEstimate 6190 1312 5536 128 = 1161232493824 := by decide +kernel
private theorem mom_6190_1312_part34 :
    blockEstimate 6190 1312 5664 128 = 1121262841088 := by decide +kernel
private theorem mom_6190_1312_part35 :
    blockEstimate 6190 1312 5792 128 = 1075786067200 := by decide +kernel
private theorem mom_6190_1312_part36 :
    blockEstimate 6190 1312 5920 128 = 1024802172160 := by decide +kernel
private theorem mom_6190_1312_part37 :
    blockEstimate 6190 1312 6048 128 = 968311155968 := by decide +kernel
private theorem mom_6190_1312_part38 :
    blockEstimate 6190 1312 6176 128 = 906774987896 := by decide +kernel
private theorem mom_6190_1312_part39 :
    blockEstimate 6190 1312 6304 128 = 842902999874 := by decide +kernel
private theorem mom_6190_1312_part40 :
    blockEstimate 6190 1312 6432 128 = 778082601925 := by decide +kernel
private theorem mom_6190_1312_part41 :
    blockEstimate 6190 1312 6560 128 = 712881308450 := by decide +kernel
private theorem mom_6190_1312_part42 :
    blockEstimate 6190 1312 6688 128 = 647846289068 := by decide +kernel
private theorem mom_6190_1312_part43 :
    blockEstimate 6190 1312 6816 128 = 583505087368 := by decide +kernel
private theorem mom_6190_1312_part44 :
    blockEstimate 6190 1312 6944 128 = 520365618915 := by decide +kernel
private theorem mom_6190_1312_part45 :
    blockEstimate 6190 1312 7072 128 = 458916174350 := by decide +kernel
private theorem mom_6190_1312_part46 :
    blockEstimate 6190 1312 7200 128 = 399625416578 := by decide +kernel
private theorem mom_6190_1312_part47 :
    blockEstimate 6190 1312 7328 128 = 342942382059 := by decide +kernel
private theorem mom_6190_1312_part48 :
    blockEstimate 6190 1312 7456 128 = 289134605868 := by decide +kernel
private theorem mom_6190_1312_part49 :
    blockEstimate 6190 1312 7584 128 = 238401544688 := by decide +kernel
private theorem mom_6190_1312_part50 :
    blockEstimate 6190 1312 7712 128 = 191805308400 := by decide +kernel
private theorem mom_6190_1312_part51 :
    blockEstimate 6190 1312 7840 128 = 149657459184 := by decide +kernel
private theorem mom_6190_1312_part52 :
    blockEstimate 6190 1312 7968 128 = 112209655280 := by decide +kernel
private theorem mom_6190_1312_part53 :
    blockEstimate 6190 1312 8096 128 = 79713554928 := by decide +kernel
private theorem mom_6190_1312_part54 :
    blockEstimate 6190 1312 8224 128 = 52420816368 := by decide +kernel
private theorem mom_6190_1312_part55 :
    blockEstimate 6190 1312 8352 128 = 30583097840 := by decide +kernel
private theorem mom_6190_1312_part56 :
    blockEstimate 6190 1312 8480 128 = 14452057584 := by decide +kernel
private theorem mom_6190_1312_part57 :
    blockEstimate 6190 1312 8608 128 = 4279353840 := by decide +kernel
private theorem mom_6190_1312_part58 :
    blockEstimate 6190 1312 8736 78 = 257610670 := by decide +kernel
private theorem mom_6190_1312_join0 :
    blockEstimate 6190 1312 1440 256 = 53960833600 :=
  block_append mom_6190_1312_part1 mom_6190_1312_part2 rfl rfl rfl
private theorem mom_6190_1312_join1 :
    blockEstimate 6190 1312 1312 384 = 56141291360 :=
  block_append mom_6190_1312_part0 mom_6190_1312_join0 rfl rfl rfl
private theorem mom_6190_1312_join2 :
    blockEstimate 6190 1312 1696 256 = 194535963200 :=
  block_append mom_6190_1312_part3 mom_6190_1312_part4 rfl rfl rfl
private theorem mom_6190_1312_join3 :
    blockEstimate 6190 1312 1952 256 = 413167090240 :=
  block_append mom_6190_1312_part5 mom_6190_1312_part6 rfl rfl rfl
private theorem mom_6190_1312_join4 :
    blockEstimate 6190 1312 1696 512 = 607703053440 :=
  block_append mom_6190_1312_join2 mom_6190_1312_join3 rfl rfl rfl
private theorem mom_6190_1312_join5 :
    blockEstimate 6190 1312 1312 896 = 663844344800 :=
  block_append mom_6190_1312_join1 mom_6190_1312_join4 rfl rfl rfl
private theorem mom_6190_1312_join6 :
    blockEstimate 6190 1312 2336 256 = 859283053120 :=
  block_append mom_6190_1312_part8 mom_6190_1312_part9 rfl rfl rfl
private theorem mom_6190_1312_join7 :
    blockEstimate 6190 1312 2208 384 = 1168722554720 :=
  block_append mom_6190_1312_part7 mom_6190_1312_join6 rfl rfl rfl
private theorem mom_6190_1312_join8 :
    blockEstimate 6190 1312 2592 256 = 1207859019400 :=
  block_append mom_6190_1312_part10 mom_6190_1312_part11 rfl rfl rfl
private theorem mom_6190_1312_join9 :
    blockEstimate 6190 1312 2848 256 = 1532580321792 :=
  block_append mom_6190_1312_part12 mom_6190_1312_part13 rfl rfl rfl
private theorem mom_6190_1312_join10 :
    blockEstimate 6190 1312 2592 512 = 2740439341192 :=
  block_append mom_6190_1312_join8 mom_6190_1312_join9 rfl rfl rfl
private theorem mom_6190_1312_join11 :
    blockEstimate 6190 1312 2208 896 = 3909161895912 :=
  block_append mom_6190_1312_join7 mom_6190_1312_join10 rfl rfl rfl
private theorem mom_6190_1312_join12 :
    blockEstimate 6190 1312 1312 1792 = 4573006240712 :=
  block_append mom_6190_1312_join5 mom_6190_1312_join11 rfl rfl rfl
private theorem mom_6190_1312_join13 :
    blockEstimate 6190 1312 3232 256 = 1937095580160 :=
  block_append mom_6190_1312_part15 mom_6190_1312_part16 rfl rfl rfl
private theorem mom_6190_1312_join14 :
    blockEstimate 6190 1312 3104 384 = 2811398457088 :=
  block_append mom_6190_1312_part14 mom_6190_1312_join13 rfl rfl rfl
private theorem mom_6190_1312_join15 :
    blockEstimate 6190 1312 3488 256 = 2151701207552 :=
  block_append mom_6190_1312_part17 mom_6190_1312_part18 rfl rfl rfl
private theorem mom_6190_1312_join16 :
    blockEstimate 6190 1312 3744 256 = 2322249865728 :=
  block_append mom_6190_1312_part19 mom_6190_1312_part20 rfl rfl rfl
private theorem mom_6190_1312_join17 :
    blockEstimate 6190 1312 3488 512 = 4473951073280 :=
  block_append mom_6190_1312_join15 mom_6190_1312_join16 rfl rfl rfl
private theorem mom_6190_1312_join18 :
    blockEstimate 6190 1312 3104 896 = 7285349530368 :=
  block_append mom_6190_1312_join14 mom_6190_1312_join17 rfl rfl rfl
private theorem mom_6190_1312_join19 :
    blockEstimate 6190 1312 4000 256 = 2448741554688 :=
  block_append mom_6190_1312_part21 mom_6190_1312_part22 rfl rfl rfl
private theorem mom_6190_1312_join20 :
    blockEstimate 6190 1312 4256 256 = 2531176274432 :=
  block_append mom_6190_1312_part23 mom_6190_1312_part24 rfl rfl rfl
private theorem mom_6190_1312_join21 :
    blockEstimate 6190 1312 4000 512 = 4979917829120 :=
  block_append mom_6190_1312_join19 mom_6190_1312_join20 rfl rfl rfl
private theorem mom_6190_1312_join22 :
    blockEstimate 6190 1312 4512 256 = 2569554024960 :=
  block_append mom_6190_1312_part25 mom_6190_1312_part26 rfl rfl rfl
private theorem mom_6190_1312_join23 :
    blockEstimate 6190 1312 4768 256 = 2563874806272 :=
  block_append mom_6190_1312_part27 mom_6190_1312_part28 rfl rfl rfl
private theorem mom_6190_1312_join24 :
    blockEstimate 6190 1312 4512 512 = 5133428831232 :=
  block_append mom_6190_1312_join22 mom_6190_1312_join23 rfl rfl rfl
private theorem mom_6190_1312_join25 :
    blockEstimate 6190 1312 4000 1024 = 10113346660352 :=
  block_append mom_6190_1312_join21 mom_6190_1312_join24 rfl rfl rfl
private theorem mom_6190_1312_join26 :
    blockEstimate 6190 1312 3104 1920 = 17398696190720 :=
  block_append mom_6190_1312_join18 mom_6190_1312_join25 rfl rfl rfl
private theorem mom_6190_1312_join27 :
    blockEstimate 6190 1312 1312 3712 = 21971702431432 :=
  block_append mom_6190_1312_join12 mom_6190_1312_join26 rfl rfl rfl
private theorem mom_6190_1312_join28 :
    blockEstimate 6190 1312 5152 256 = 2472749160960 :=
  block_append mom_6190_1312_part30 mom_6190_1312_part31 rfl rfl rfl
private theorem mom_6190_1312_join29 :
    blockEstimate 6190 1312 5024 384 = 3738789054208 :=
  block_append mom_6190_1312_part29 mom_6190_1312_join28 rfl rfl rfl
private theorem mom_6190_1312_join30 :
    blockEstimate 6190 1312 5408 256 = 2356927519232 :=
  block_append mom_6190_1312_part32 mom_6190_1312_part33 rfl rfl rfl
private theorem mom_6190_1312_join31 :
    blockEstimate 6190 1312 5664 256 = 2197048908288 :=
  block_append mom_6190_1312_part34 mom_6190_1312_part35 rfl rfl rfl
private theorem mom_6190_1312_join32 :
    blockEstimate 6190 1312 5408 512 = 4553976427520 :=
  block_append mom_6190_1312_join30 mom_6190_1312_join31 rfl rfl rfl
private theorem mom_6190_1312_join33 :
    blockEstimate 6190 1312 5024 896 = 8292765481728 :=
  block_append mom_6190_1312_join29 mom_6190_1312_join32 rfl rfl rfl
private theorem mom_6190_1312_join34 :
    blockEstimate 6190 1312 5920 256 = 1993113328128 :=
  block_append mom_6190_1312_part36 mom_6190_1312_part37 rfl rfl rfl
private theorem mom_6190_1312_join35 :
    blockEstimate 6190 1312 6176 256 = 1749677987770 :=
  block_append mom_6190_1312_part38 mom_6190_1312_part39 rfl rfl rfl
private theorem mom_6190_1312_join36 :
    blockEstimate 6190 1312 5920 512 = 3742791315898 :=
  block_append mom_6190_1312_join34 mom_6190_1312_join35 rfl rfl rfl
private theorem mom_6190_1312_join37 :
    blockEstimate 6190 1312 6432 256 = 1490963910375 :=
  block_append mom_6190_1312_part40 mom_6190_1312_part41 rfl rfl rfl
private theorem mom_6190_1312_join38 :
    blockEstimate 6190 1312 6688 256 = 1231351376436 :=
  block_append mom_6190_1312_part42 mom_6190_1312_part43 rfl rfl rfl
private theorem mom_6190_1312_join39 :
    blockEstimate 6190 1312 6432 512 = 2722315286811 :=
  block_append mom_6190_1312_join37 mom_6190_1312_join38 rfl rfl rfl
private theorem mom_6190_1312_join40 :
    blockEstimate 6190 1312 5920 1024 = 6465106602709 :=
  block_append mom_6190_1312_join36 mom_6190_1312_join39 rfl rfl rfl
private theorem mom_6190_1312_join41 :
    blockEstimate 6190 1312 5024 1920 = 14757872084437 :=
  block_append mom_6190_1312_join33 mom_6190_1312_join40 rfl rfl rfl
private theorem mom_6190_1312_join42 :
    blockEstimate 6190 1312 7072 256 = 858541590928 :=
  block_append mom_6190_1312_part45 mom_6190_1312_part46 rfl rfl rfl
private theorem mom_6190_1312_join43 :
    blockEstimate 6190 1312 6944 384 = 1378907209843 :=
  block_append mom_6190_1312_part44 mom_6190_1312_join42 rfl rfl rfl
private theorem mom_6190_1312_join44 :
    blockEstimate 6190 1312 7328 256 = 632076987927 :=
  block_append mom_6190_1312_part47 mom_6190_1312_part48 rfl rfl rfl
private theorem mom_6190_1312_join45 :
    blockEstimate 6190 1312 7584 256 = 430206853088 :=
  block_append mom_6190_1312_part49 mom_6190_1312_part50 rfl rfl rfl
private theorem mom_6190_1312_join46 :
    blockEstimate 6190 1312 7328 512 = 1062283841015 :=
  block_append mom_6190_1312_join44 mom_6190_1312_join45 rfl rfl rfl
private theorem mom_6190_1312_join47 :
    blockEstimate 6190 1312 6944 896 = 2441191050858 :=
  block_append mom_6190_1312_join43 mom_6190_1312_join46 rfl rfl rfl
private theorem mom_6190_1312_join48 :
    blockEstimate 6190 1312 7840 256 = 261867114464 :=
  block_append mom_6190_1312_part51 mom_6190_1312_part52 rfl rfl rfl
private theorem mom_6190_1312_join49 :
    blockEstimate 6190 1312 8096 256 = 132134371296 :=
  block_append mom_6190_1312_part53 mom_6190_1312_part54 rfl rfl rfl
private theorem mom_6190_1312_join50 :
    blockEstimate 6190 1312 7840 512 = 394001485760 :=
  block_append mom_6190_1312_join48 mom_6190_1312_join49 rfl rfl rfl
private theorem mom_6190_1312_join51 :
    blockEstimate 6190 1312 8352 256 = 45035155424 :=
  block_append mom_6190_1312_part55 mom_6190_1312_part56 rfl rfl rfl
private theorem mom_6190_1312_join52 :
    blockEstimate 6190 1312 8608 206 = 4536964510 :=
  block_append mom_6190_1312_part57 mom_6190_1312_part58 rfl rfl rfl
private theorem mom_6190_1312_join53 :
    blockEstimate 6190 1312 8352 462 = 49572119934 :=
  block_append mom_6190_1312_join51 mom_6190_1312_join52 rfl rfl rfl
private theorem mom_6190_1312_join54 :
    blockEstimate 6190 1312 7840 974 = 443573605694 :=
  block_append mom_6190_1312_join50 mom_6190_1312_join53 rfl rfl rfl
private theorem mom_6190_1312_join55 :
    blockEstimate 6190 1312 6944 1870 = 2884764656552 :=
  block_append mom_6190_1312_join47 mom_6190_1312_join54 rfl rfl rfl
private theorem mom_6190_1312_join56 :
    blockEstimate 6190 1312 5024 3790 = 17642636740989 :=
  block_append mom_6190_1312_join41 mom_6190_1312_join55 rfl rfl rfl
private theorem mom_6190_1312_join57 :
    blockEstimate 6190 1312 1312 7502 = 39614339172421 :=
  block_append mom_6190_1312_join27 mom_6190_1312_join56 rfl rfl rfl
private theorem mom_6190_1312 : momentEstimate 6190 1312 = 39614339172421 := mom_6190_1312_join57
private theorem rc_0_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 0 128 = 31974970385939049852869320416 := by decide +kernel
private theorem rc_0_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 128 128 = 27954670861966588909844287200 := by decide +kernel
private theorem rc_0_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 256 128 = 24115291754372572570868711136 := by decide +kernel
private theorem rc_0_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 384 128 = 20452651984038868681518231264 := by decide +kernel
private theorem rc_0_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 512 128 = 16962579472382406285578034912 := by decide +kernel
private theorem rc_0_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 640 128 = 13640912543957047158418040431 := by decide +kernel
private theorem rc_0_10_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 768 128 = 10483506767707098743200680849 := by decide +kernel
private theorem rc_0_10_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 896 128 = 7486211840074713586700335776 := by decide +kernel
private theorem rc_0_10_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 1024 128 = 4644877622652894584260876788 := by decide +kernel
private theorem rc_0_10_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 1152 128 = 1955362909442964683174152062 := by decide +kernel
private theorem rc_0_10_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 1280 33 = 86154662593336497414371337 := by decide +kernel
private theorem rc_0_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 0 256 = 59929641247905638762713607616 :=
  phaseBlock_append rc_0_10_2360_0_part0 rc_0_10_2360_0_part1 rfl rfl rfl
private theorem rc_0_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 384 256 = 37415231456421274967096266176 :=
  phaseBlock_append rc_0_10_2360_0_part3 rc_0_10_2360_0_part4 rfl rfl rfl
private theorem rc_0_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 256 384 = 61530523210793847537964977312 :=
  phaseBlock_append rc_0_10_2360_0_part2 rc_0_10_2360_0_join1 rfl rfl rfl
private theorem rc_0_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 0 640 = 121460164458699486300678584928 :=
  phaseBlock_append rc_0_10_2360_0_join0 rc_0_10_2360_0_join2 rfl rfl rfl
private theorem rc_0_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 768 256 = 17969718607781812329901016625 :=
  phaseBlock_append rc_0_10_2360_0_part6 rc_0_10_2360_0_part7 rfl rfl rfl
private theorem rc_0_10_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 640 384 = 31610631151738859488319057056 :=
  phaseBlock_append rc_0_10_2360_0_part5 rc_0_10_2360_0_join4 rfl rfl rfl
private theorem rc_0_10_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 1152 161 = 2041517572036301180588523399 :=
  phaseBlock_append rc_0_10_2360_0_part9 rc_0_10_2360_0_part10 rfl rfl rfl
private theorem rc_0_10_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 1024 289 = 6686395194689195764849400187 :=
  phaseBlock_append rc_0_10_2360_0_part8 rc_0_10_2360_0_join6 rfl rfl rfl
private theorem rc_0_10_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 640 673 = 38297026346428055253168457243 :=
  phaseBlock_append rc_0_10_2360_0_join5 rc_0_10_2360_0_join7 rfl rfl rfl
private theorem rc_0_10_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 0) 0 1313 = 159757190805127541553847042171 :=
  phaseBlock_append rc_0_10_2360_0_join3 rc_0_10_2360_0_join8 rfl rfl rfl
private theorem rc_0_10_2360_0 : fastPhase (bank 0 10).shape 179808 2360 40 1 0 1 0 = 159757190805127541553847042171 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_0_10_2360_0_join9
private theorem rc_0_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 0 128 = 31943270297357729267366174496 := by decide +kernel
private theorem rc_0_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 128 128 = 27924352737086969712034991904 := by decide +kernel
private theorem rc_0_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 256 128 = 24086323949195986451432308512 := by decide +kernel
private theorem rc_0_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 384 128 = 20425002923175019216010915616 := by decide +kernel
private theorem rc_0_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 512 128 = 16936217649001252587614756640 := by decide +kernel
private theorem rc_0_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 640 128 = 13615806517252999155046062810 := by decide +kernel
private theorem rc_0_10_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 768 128 = 10459625142860076116124587070 := by decide +kernel
private theorem rc_0_10_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 896 128 = 7463523279136484193773883210 := by decide +kernel
private theorem rc_0_10_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 1024 128 = 4623350856065898765636120822 := by decide +kernel
private theorem rc_0_10_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 1152 128 = 1934966736103773631413593778 := by decide +kernel
private theorem rc_0_10_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 1280 33 = 81075787842800365085098254 := by decide +kernel
private theorem rc_0_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 0 256 = 59867623034444698979401166400 :=
  phaseBlock_append rc_0_10_2360_1_part0 rc_0_10_2360_1_part1 rfl rfl rfl
private theorem rc_0_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 384 256 = 37361220572176271803625672256 :=
  phaseBlock_append rc_0_10_2360_1_part3 rc_0_10_2360_1_part4 rfl rfl rfl
private theorem rc_0_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 256 384 = 61447544521372258255057980768 :=
  phaseBlock_append rc_0_10_2360_1_part2 rc_0_10_2360_1_join1 rfl rfl rfl
private theorem rc_0_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 0 640 = 121315167555816957234459147168 :=
  phaseBlock_append rc_0_10_2360_1_join0 rc_0_10_2360_1_join2 rfl rfl rfl
private theorem rc_0_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 768 256 = 17923148421996560309898470280 :=
  phaseBlock_append rc_0_10_2360_1_part6 rc_0_10_2360_1_part7 rfl rfl rfl
private theorem rc_0_10_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 640 384 = 31538954939249559464944533090 :=
  phaseBlock_append rc_0_10_2360_1_part5 rc_0_10_2360_1_join4 rfl rfl rfl
private theorem rc_0_10_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 1152 161 = 2016042523946573996498692032 :=
  phaseBlock_append rc_0_10_2360_1_part9 rc_0_10_2360_1_part10 rfl rfl rfl
private theorem rc_0_10_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 1024 289 = 6639393380012472762134812854 :=
  phaseBlock_append rc_0_10_2360_1_part8 rc_0_10_2360_1_join6 rfl rfl rfl
private theorem rc_0_10_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 640 673 = 38178348319262032227079345944 :=
  phaseBlock_append rc_0_10_2360_1_join5 rc_0_10_2360_1_join7 rfl rfl rfl
private theorem rc_0_10_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2360 40 1 0 1 1) 0 1313 = 159493515875078989461538493112 :=
  phaseBlock_append rc_0_10_2360_1_join3 rc_0_10_2360_1_join8 rfl rfl rfl
private theorem rc_0_10_2360_1 : fastPhase (bank 0 10).shape 179808 2360 40 1 0 1 1 = 159493515875078989461538493112 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_0_10_2360_1_join9
private theorem rc_0_10_2361_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 0 128 = 31975257688093844016617270016 := by decide +kernel
private theorem rc_0_10_2361_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 128 128 = 27954908073874554549034412800 := by decide +kernel
private theorem rc_0_10_2361_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 256 128 = 24115483967523680023356582656 := by decide +kernel
private theorem rc_0_10_2361_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 384 128 = 20452804145583004457059511040 := by decide +kernel
private theorem rc_0_10_2361_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 512 128 = 16962696385443260442735127296 := by decide +kernel
private theorem rc_0_10_2361_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 640 128 = 13640998824153162251428260562 := by decide +kernel
private theorem rc_0_10_2361_0_part6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 768 128 = 10483566860157922164391138893 := by decide +kernel
private theorem rc_0_10_2361_0_part7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 896 128 = 7486250192625290131723612661 := by decide +kernel
private theorem rc_0_10_2361_0_part8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 1024 128 = 4644898531997523286068673980 := by decide +kernel
private theorem rc_0_10_2361_0_part9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 1152 128 = 1955370517769887593846583206 := by decide +kernel
private theorem rc_0_10_2361_0_part10 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 1280 33 = 86154957743486673259463766 := by decide +kernel
private theorem rc_0_10_2361_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 0 256 = 59930165761968398565651682816 :=
  phaseBlock_append rc_0_10_2361_0_part0 rc_0_10_2361_0_part1 rfl rfl rfl
private theorem rc_0_10_2361_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 384 256 = 37415500531026264899794638336 :=
  phaseBlock_append rc_0_10_2361_0_part3 rc_0_10_2361_0_part4 rfl rfl rfl
private theorem rc_0_10_2361_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 256 384 = 61530984498549944923151220992 :=
  phaseBlock_append rc_0_10_2361_0_part2 rc_0_10_2361_0_join1 rfl rfl rfl
private theorem rc_0_10_2361_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 0 640 = 121461150260518343488802903808 :=
  phaseBlock_append rc_0_10_2361_0_join0 rc_0_10_2361_0_join2 rfl rfl rfl
private theorem rc_0_10_2361_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 768 256 = 17969817052783212296114751554 :=
  phaseBlock_append rc_0_10_2361_0_part6 rc_0_10_2361_0_part7 rfl rfl rfl
private theorem rc_0_10_2361_0_join5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 640 384 = 31610815876936374547543012116 :=
  phaseBlock_append rc_0_10_2361_0_part5 rc_0_10_2361_0_join4 rfl rfl rfl
private theorem rc_0_10_2361_0_join6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 1152 161 = 2041525475513374267106046972 :=
  phaseBlock_append rc_0_10_2361_0_part9 rc_0_10_2361_0_part10 rfl rfl rfl
private theorem rc_0_10_2361_0_join7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 1024 289 = 6686424007510897553174720952 :=
  phaseBlock_append rc_0_10_2361_0_part8 rc_0_10_2361_0_join6 rfl rfl rfl
private theorem rc_0_10_2361_0_join8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 640 673 = 38297239884447272100717733068 :=
  phaseBlock_append rc_0_10_2361_0_join5 rc_0_10_2361_0_join7 rfl rfl rfl
private theorem rc_0_10_2361_0_join9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 0) 0 1313 = 159758390144965615589520636876 :=
  phaseBlock_append rc_0_10_2361_0_join3 rc_0_10_2361_0_join8 rfl rfl rfl
private theorem rc_0_10_2361_0 : fastPhase (bank 0 10).shape 179808 2361 40 1 0 1 0 = 159758390144965615589520636876 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_0_10_2361_0_join9
private theorem rc_0_10_2361_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 0 128 = 31943557366246134931099514368 := by decide +kernel
private theorem rc_0_10_2361_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 128 128 = 27924589735852072807328429568 := by decide +kernel
private theorem rc_0_10_2361_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 256 128 = 24086515968646163716837537280 := by decide +kernel
private theorem rc_0_10_2361_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 384 128 = 20425154909780282480906024448 := by decide +kernel
private theorem rc_0_10_2361_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 512 128 = 16936334405207134843440821760 := by decide +kernel
private theorem rc_0_10_2361_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 640 128 = 13615892658077743804861994347 := by decide +kernel
private theorem rc_0_10_2361_1_part6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 768 128 = 10459685112931534186079087102 := by decide +kernel
private theorem rc_0_10_2361_1_part7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 896 128 = 7463561525600491163845980798 := by decide +kernel
private theorem rc_0_10_2361_1_part8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 1024 128 = 4623371674913878793790907461 := by decide +kernel
private theorem rc_0_10_2361_1_part9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 1152 128 = 1934974268825104485927366271 := by decide +kernel
private theorem rc_0_10_2361_1_part10 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 1280 33 = 81076065828756273885690254 := by decide +kernel
private theorem rc_0_10_2361_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 0 256 = 59868147102098207738427943936 :=
  phaseBlock_append rc_0_10_2361_1_part0 rc_0_10_2361_1_part1 rfl rfl rfl
private theorem rc_0_10_2361_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 384 256 = 37361489314987417324346846208 :=
  phaseBlock_append rc_0_10_2361_1_part3 rc_0_10_2361_1_part4 rfl rfl rfl
private theorem rc_0_10_2361_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 256 384 = 61448005283633581041184383488 :=
  phaseBlock_append rc_0_10_2361_1_part2 rc_0_10_2361_1_join1 rfl rfl rfl
private theorem rc_0_10_2361_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 0 640 = 121316152385731788779612327424 :=
  phaseBlock_append rc_0_10_2361_1_join0 rc_0_10_2361_1_join2 rfl rfl rfl
private theorem rc_0_10_2361_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 768 256 = 17923246638532025349925067900 :=
  phaseBlock_append rc_0_10_2361_1_part6 rc_0_10_2361_1_part7 rfl rfl rfl
private theorem rc_0_10_2361_1_join5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 640 384 = 31539139296609769154787062247 :=
  phaseBlock_append rc_0_10_2361_1_part5 rc_0_10_2361_1_join4 rfl rfl rfl
private theorem rc_0_10_2361_1_join6 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 1152 161 = 2016050334653860759813056525 :=
  phaseBlock_append rc_0_10_2361_1_part9 rc_0_10_2361_1_part10 rfl rfl rfl
private theorem rc_0_10_2361_1_join7 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 1024 289 = 6639422009567739553603963986 :=
  phaseBlock_append rc_0_10_2361_1_part8 rc_0_10_2361_1_join6 rfl rfl rfl
private theorem rc_0_10_2361_1_join8 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 640 673 = 38178561306177508708391026233 :=
  phaseBlock_append rc_0_10_2361_1_join5 rc_0_10_2361_1_join7 rfl rfl rfl
private theorem rc_0_10_2361_1_join9 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2361 40 1 0 1 1) 0 1313 = 159494713691909297488003353657 :=
  phaseBlock_append rc_0_10_2361_1_join3 rc_0_10_2361_1_join8 rfl rfl rfl
private theorem rc_0_10_2361_1 : fastPhase (bank 0 10).shape 179808 2361 40 1 0 1 1 = 159494713691909297488003353657 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_0_10_2361_1_join9
private theorem receipt_0_10 : B1Checked (bank 0 10) 40 0 1 := by
  refine b1_checked_from_values (bank 0 10) 40 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_6190_1312)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_0_10_2360_0 rc_0_10_2360_1 rc_0_10_2361_0 rc_0_10_2361_1 (by decide +kernel) (by decide +kernel)

theorem rect0_checked (i : Fin 11) :
    B1Checked (bank 0 i) (reserve i) (excess 0) (seed 0) := by
  fin_cases i
  · exact receipt_0_0
  · exact receipt_0_1
  · exact receipt_0_2
  · exact receipt_0_3
  · exact receipt_0_4
  · exact receipt_0_5
  · exact receipt_0_6
  · exact receipt_0_7
  · exact receipt_0_8
  · exact receipt_0_9
  · exact receipt_0_10

#print axioms rect0_checked
end Lower6962.B1.RescueSource
