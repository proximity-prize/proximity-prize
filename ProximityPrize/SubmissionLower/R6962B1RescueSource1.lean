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
private theorem rc_1_0_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 0) 0 128 = 8571095377091695365090912 := by decide +kernel
private theorem rc_1_0_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 0) 128 128 = 3186250538028835629654255 := by decide +kernel
private theorem rc_1_0_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 0) 256 28 = 99553563024011536987161 := by decide +kernel
private theorem rc_1_0_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 0) 128 156 = 3285804101052847166641416 :=
  phaseBlock_append rc_1_0_2360_0_part1 rc_1_0_2360_0_part2 rfl rfl rfl
private theorem rc_1_0_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 0) 0 284 = 11856899478144542531732328 :=
  phaseBlock_append rc_1_0_2360_0_part0 rc_1_0_2360_0_join0 rfl rfl rfl
private theorem rc_1_0_2360_0 : fastPhase (bank 1 0).shape 179808 2360 0 1 0 2 0 = 11856899478144542531732328 :=
  phase_of_block (n := 284) (by decide +kernel) rc_1_0_2360_0_join1
private theorem rc_1_0_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 1) 0 128 = 8524546454901832231317792 := by decide +kernel
private theorem rc_1_0_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 1) 128 128 = 3149278279996196184141993 := by decide +kernel
private theorem rc_1_0_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 1) 256 28 = 92628268013108758821975 := by decide +kernel
private theorem rc_1_0_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 1) 128 156 = 3241906548009304942963968 :=
  phaseBlock_append rc_1_0_2360_1_part1 rc_1_0_2360_1_part2 rfl rfl rfl
private theorem rc_1_0_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2360 0 1 0 2 1) 0 284 = 11766453002911137174281760 :=
  phaseBlock_append rc_1_0_2360_1_part0 rc_1_0_2360_1_join0 rfl rfl rfl
private theorem rc_1_0_2360_1 : fastPhase (bank 1 0).shape 179808 2360 0 1 0 2 1 = 11766453002911137174281760 :=
  phase_of_block (n := 284) (by decide +kernel) rc_1_0_2360_1_join1
private theorem rc_1_0_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 0) 0 128 = 8571167477643960168080352 := by decide +kernel
private theorem rc_1_0_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 0) 128 128 = 3186269732516907812701514 := by decide +kernel
private theorem rc_1_0_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 0) 256 28 = 99553961457963166419885 := by decide +kernel
private theorem rc_1_0_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 0) 128 156 = 3285823693974870979121399 :=
  phaseBlock_append rc_1_0_2361_0_part1 rc_1_0_2361_0_part2 rfl rfl rfl
private theorem rc_1_0_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 0) 0 284 = 11856991171618831147201751 :=
  phaseBlock_append rc_1_0_2361_0_part0 rc_1_0_2361_0_join0 rfl rfl rfl
private theorem rc_1_0_2361_0 : fastPhase (bank 1 0).shape 179808 2361 0 1 0 2 0 = 11856991171618831147201751 :=
  phase_of_block (n := 284) (by decide +kernel) rc_1_0_2361_0_join1
private theorem rc_1_0_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 1) 0 128 = 8524618230594053607402080 := by decide +kernel
private theorem rc_1_0_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 1) 128 128 = 3149297282871097258196121 := by decide +kernel
private theorem rc_1_0_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 1) 256 28 = 92628639986257591101081 := by decide +kernel
private theorem rc_1_0_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 1) 128 156 = 3241925922857354849297202 :=
  phaseBlock_append rc_1_0_2361_1_part1 rc_1_0_2361_1_part2 rfl rfl rfl
private theorem rc_1_0_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179808 2361 0 1 0 2 1) 0 284 = 11766544153451408456699282 :=
  phaseBlock_append rc_1_0_2361_1_part0 rc_1_0_2361_1_join0 rfl rfl rfl
private theorem rc_1_0_2361_1 : fastPhase (bank 1 0).shape 179808 2361 0 1 0 2 1 = 11766544153451408456699282 :=
  phase_of_block (n := 284) (by decide +kernel) rc_1_0_2361_1_join1
private theorem receipt_1_0 : B1Checked (bank 1 0) 0 0 2 := by
  refine b1_checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1335_283)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_0_2360_0 rc_1_0_2360_1 rc_1_0_2361_0 rc_1_0_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 0) 0 128 = 14190072796757402236891968 := by decide +kernel
private theorem rc_1_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 0) 128 128 = 6206605469445339303565077 := by decide +kernel
private theorem rc_1_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 0) 256 58 = 619168973945084224692779 := by decide +kernel
private theorem rc_1_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 0) 128 186 = 6825774443390423528257856 :=
  phaseBlock_append rc_1_1_2360_0_part1 rc_1_1_2360_0_part2 rfl rfl rfl
private theorem rc_1_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 0) 0 314 = 21015847240147825765149824 :=
  phaseBlock_append rc_1_1_2360_0_part0 rc_1_1_2360_0_join0 rfl rfl rfl
private theorem rc_1_1_2360_0 : fastPhase (bank 1 1).shape 179808 2360 1 1 0 2 0 = 21015847240147825765149824 :=
  phase_of_block (n := 314) (by decide +kernel) rc_1_1_2360_0_join1
private theorem rc_1_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 1) 0 128 = 14121857440103942676143808 := by decide +kernel
private theorem rc_1_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 1) 128 128 = 6151103218319266433513121 := by decide +kernel
private theorem rc_1_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 1) 256 58 = 597833950922650593642712 := by decide +kernel
private theorem rc_1_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 1) 128 186 = 6748937169241917027155833 :=
  phaseBlock_append rc_1_1_2360_1_part1 rc_1_1_2360_1_part2 rfl rfl rfl
private theorem rc_1_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2360 1 1 0 2 1) 0 314 = 20870794609345859703299641 :=
  phaseBlock_append rc_1_1_2360_1_part0 rc_1_1_2360_1_join0 rfl rfl rfl
private theorem rc_1_1_2360_1 : fastPhase (bank 1 1).shape 179808 2360 1 1 0 2 1 = 20870794609345859703299641 :=
  phase_of_block (n := 314) (by decide +kernel) rc_1_1_2360_1_join1
private theorem rc_1_1_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 0) 0 128 = 14190193100321668513433952 := by decide +kernel
private theorem rc_1_1_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 0) 128 128 = 6206644518598948702445164 := by decide +kernel
private theorem rc_1_1_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 0) 256 58 = 619171677345176449225502 := by decide +kernel
private theorem rc_1_1_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 0) 128 186 = 6825816195944125151670666 :=
  phaseBlock_append rc_1_1_2361_0_part1 rc_1_1_2361_0_part2 rfl rfl rfl
private theorem rc_1_1_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 0) 0 314 = 21016009296265793665104618 :=
  phaseBlock_append rc_1_1_2361_0_part0 rc_1_1_2361_0_join0 rfl rfl rfl
private theorem rc_1_1_2361_0 : fastPhase (bank 1 1).shape 179808 2361 1 1 0 2 0 = 21016009296265793665104618 :=
  phase_of_block (n := 314) (by decide +kernel) rc_1_1_2361_0_join1
private theorem rc_1_1_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 1) 0 128 = 14121977263971516986434080 := by decide +kernel
private theorem rc_1_1_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 1) 128 128 = 6151141965391705942583686 := by decide +kernel
private theorem rc_1_1_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 1) 256 58 = 597836568470919040779431 := by decide +kernel
private theorem rc_1_1_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 1) 128 186 = 6748978533862624983363117 :=
  phaseBlock_append rc_1_1_2361_1_part1 rc_1_1_2361_1_part2 rfl rfl rfl
private theorem rc_1_1_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2361 1 1 0 2 1) 0 314 = 20870955797834141969797197 :=
  phaseBlock_append rc_1_1_2361_1_part0 rc_1_1_2361_1_join0 rfl rfl rfl
private theorem rc_1_1_2361_1 : fastPhase (bank 1 1).shape 179808 2361 1 1 0 2 1 = 20870955797834141969797197 :=
  phase_of_block (n := 314) (by decide +kernel) rc_1_1_2361_1_join1
private theorem receipt_1_1 : B1Checked (bank 1 1) 1 0 2 := by
  refine b1_checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1477_313)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_1_2360_0 rc_1_1_2360_1 rc_1_1_2361_0 rc_1_1_2361_1 (by decide +kernel) (by decide +kernel)
private theorem mom_1610_341_part0 :
    blockEstimate 1610 341 341 128 = 541916960 := by decide +kernel
private theorem mom_1610_341_part1 :
    blockEstimate 1610 341 469 128 = 3471806240 := by decide +kernel
private theorem mom_1610_341_part2 :
    blockEstimate 1610 341 597 128 = 8550618821 := by decide +kernel
private theorem mom_1610_341_part3 :
    blockEstimate 1610 341 725 128 = 14087543616 := by decide +kernel
private theorem mom_1610_341_part4 :
    blockEstimate 1610 341 853 128 = 18326461248 := by decide +kernel
private theorem mom_1610_341_part5 :
    blockEstimate 1610 341 981 128 = 21130926912 := by decide +kernel
private theorem mom_1610_341_part6 :
    blockEstimate 1610 341 1109 128 = 22500940608 := by decide +kernel
private theorem mom_1610_341_part7 :
    blockEstimate 1610 341 1237 128 = 22436502336 := by decide +kernel
private theorem mom_1610_341_part8 :
    blockEstimate 1610 341 1365 128 = 20937612096 := by decide +kernel
private theorem mom_1610_341_part9 :
    blockEstimate 1610 341 1493 128 = 18004387383 := by decide +kernel
private theorem mom_1610_341_part10 :
    blockEstimate 1610 341 1621 128 = 13880694800 := by decide +kernel
private theorem mom_1610_341_part11 :
    blockEstimate 1610 341 1749 128 = 9524300037 := by decide +kernel
private theorem mom_1610_341_part12 :
    blockEstimate 1610 341 1877 128 = 5557648257 := by decide +kernel
private theorem mom_1610_341_part13 :
    blockEstimate 1610 341 2005 128 = 2424522976 := by decide +kernel
private theorem mom_1610_341_part14 :
    blockEstimate 1610 341 2133 128 = 524671200 := by decide +kernel
private theorem mom_1610_341_part15 :
    blockEstimate 1610 341 2261 31 = 4558520 := by decide +kernel
private theorem mom_1610_341_join0 :
    blockEstimate 1610 341 341 256 = 4013723200 :=
  block_append mom_1610_341_part0 mom_1610_341_part1 rfl rfl rfl
private theorem mom_1610_341_join1 :
    blockEstimate 1610 341 597 256 = 22638162437 :=
  block_append mom_1610_341_part2 mom_1610_341_part3 rfl rfl rfl
private theorem mom_1610_341_join2 :
    blockEstimate 1610 341 341 512 = 26651885637 :=
  block_append mom_1610_341_join0 mom_1610_341_join1 rfl rfl rfl
private theorem mom_1610_341_join3 :
    blockEstimate 1610 341 853 256 = 39457388160 :=
  block_append mom_1610_341_part4 mom_1610_341_part5 rfl rfl rfl
private theorem mom_1610_341_join4 :
    blockEstimate 1610 341 1109 256 = 44937442944 :=
  block_append mom_1610_341_part6 mom_1610_341_part7 rfl rfl rfl
private theorem mom_1610_341_join5 :
    blockEstimate 1610 341 853 512 = 84394831104 :=
  block_append mom_1610_341_join3 mom_1610_341_join4 rfl rfl rfl
private theorem mom_1610_341_join6 :
    blockEstimate 1610 341 341 1024 = 111046716741 :=
  block_append mom_1610_341_join2 mom_1610_341_join5 rfl rfl rfl
private theorem mom_1610_341_join7 :
    blockEstimate 1610 341 1365 256 = 38941999479 :=
  block_append mom_1610_341_part8 mom_1610_341_part9 rfl rfl rfl
private theorem mom_1610_341_join8 :
    blockEstimate 1610 341 1621 256 = 23404994837 :=
  block_append mom_1610_341_part10 mom_1610_341_part11 rfl rfl rfl
private theorem mom_1610_341_join9 :
    blockEstimate 1610 341 1365 512 = 62346994316 :=
  block_append mom_1610_341_join7 mom_1610_341_join8 rfl rfl rfl
private theorem mom_1610_341_join10 :
    blockEstimate 1610 341 1877 256 = 7982171233 :=
  block_append mom_1610_341_part12 mom_1610_341_part13 rfl rfl rfl
private theorem mom_1610_341_join11 :
    blockEstimate 1610 341 2133 159 = 529229720 :=
  block_append mom_1610_341_part14 mom_1610_341_part15 rfl rfl rfl
private theorem mom_1610_341_join12 :
    blockEstimate 1610 341 1877 415 = 8511400953 :=
  block_append mom_1610_341_join10 mom_1610_341_join11 rfl rfl rfl
private theorem mom_1610_341_join13 :
    blockEstimate 1610 341 1365 927 = 70858395269 :=
  block_append mom_1610_341_join9 mom_1610_341_join12 rfl rfl rfl
private theorem mom_1610_341_join14 :
    blockEstimate 1610 341 341 1951 = 181905112010 :=
  block_append mom_1610_341_join6 mom_1610_341_join13 rfl rfl rfl
private theorem mom_1610_341 : momentEstimate 1610 341 = 181905112010 := mom_1610_341_join14
private theorem rc_1_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 0) 0 128 = 22308468314838255355066272 := by decide +kernel
private theorem rc_1_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 0) 128 128 = 10872096284047896337982097 := by decide +kernel
private theorem rc_1_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 0) 256 86 = 1933309299913890661742244 := by decide +kernel
private theorem rc_1_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 0) 128 214 = 12805405583961786999724341 :=
  phaseBlock_append rc_1_2_2360_0_part1 rc_1_2_2360_0_part2 rfl rfl rfl
private theorem rc_1_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 0) 0 342 = 35113873898800042354790613 :=
  phaseBlock_append rc_1_2_2360_0_part0 rc_1_2_2360_0_join0 rfl rfl rfl
private theorem rc_1_2_2360_0 : fastPhase (bank 1 2).shape 179808 2360 2 1 0 2 0 = 35113873898800042354790613 :=
  phase_of_block (n := 342) (by decide +kernel) rc_1_2_2360_0_join1
private theorem rc_1_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 1) 0 128 = 22211625364185566666992800 := by decide +kernel
private theorem rc_1_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 1) 128 128 = 10791824394339044805726422 := by decide +kernel
private theorem rc_1_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 1) 256 86 = 1887865841941526605986011 := by decide +kernel
private theorem rc_1_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 1) 128 214 = 12679690236280571411712433 :=
  phaseBlock_append rc_1_2_2360_1_part1 rc_1_2_2360_1_part2 rfl rfl rfl
private theorem rc_1_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2360 2 1 0 2 1) 0 342 = 34891315600466138078705233 :=
  phaseBlock_append rc_1_2_2360_1_part0 rc_1_2_2360_1_join0 rfl rfl rfl
private theorem rc_1_2_2360_1 : fastPhase (bank 1 2).shape 179808 2360 2 1 0 2 1 = 34891315600466138078705233 :=
  phase_of_block (n := 342) (by decide +kernel) rc_1_2_2360_1_join1
private theorem rc_1_2_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 0) 0 128 = 22308658421144962060049280 := by decide +kernel
private theorem rc_1_2_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 0) 128 128 = 10872167098706945720373027 := by decide +kernel
private theorem rc_1_2_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 0) 256 86 = 1933318280714533106480091 := by decide +kernel
private theorem rc_1_2_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 0) 128 214 = 12805485379421478826853118 :=
  phaseBlock_append rc_1_2_2361_0_part1 rc_1_2_2361_0_part2 rfl rfl rfl
private theorem rc_1_2_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 0) 0 342 = 35114143800566440886902398 :=
  phaseBlock_append rc_1_2_2361_0_part0 rc_1_2_2361_0_join0 rfl rfl rfl
private theorem rc_1_2_2361_0 : fastPhase (bank 1 2).shape 179808 2361 2 1 0 2 0 = 35114143800566440886902398 :=
  phase_of_block (n := 342) (by decide +kernel) rc_1_2_2361_0_join1
private theorem rc_1_2_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 1) 0 128 = 22211814786201435484640448 := by decide +kernel
private theorem rc_1_2_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 1) 128 128 = 10791894756622788625495510 := by decide +kernel
private theorem rc_1_2_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 1) 256 86 = 1887874632776280891232187 := by decide +kernel
private theorem rc_1_2_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 1) 128 214 = 12679769389399069516727697 :=
  phaseBlock_append rc_1_2_2361_1_part1 rc_1_2_2361_1_part2 rfl rfl rfl
private theorem rc_1_2_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2361 2 1 0 2 1) 0 342 = 34891584175600505001368145 :=
  phaseBlock_append rc_1_2_2361_1_part0 rc_1_2_2361_1_join0 rfl rfl rfl
private theorem rc_1_2_2361_1 : fastPhase (bank 1 2).shape 179808 2361 2 1 0 2 1 = 34891584175600505001368145 :=
  phase_of_block (n := 342) (by decide +kernel) rc_1_2_2361_1_join1
private theorem receipt_1_2 : B1Checked (bank 1 2) 2 0 2 := by
  refine b1_checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1610_341)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_2_2360_0 rc_1_2_2360_1 rc_1_2_2361_0 rc_1_2_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 0 128 = 36852475729368653301164256 := by decide +kernel
private theorem rc_1_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 128 128 = 20394420117112791195911370 := by decide +kernel
private theorem rc_1_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 256 128 = 6576168637214161093590774 := by decide +kernel
private theorem rc_1_3_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 384 5 = 10373491624630573608375 := by decide +kernel
private theorem rc_1_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 0 256 = 57246895846481444497075626 :=
  phaseBlock_append rc_1_3_2360_0_part0 rc_1_3_2360_0_part1 rfl rfl rfl
private theorem rc_1_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 256 133 = 6586542128838791667199149 :=
  phaseBlock_append rc_1_3_2360_0_part2 rc_1_3_2360_0_part3 rfl rfl rfl
private theorem rc_1_3_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 0) 0 389 = 63833437975320236164274775 :=
  phaseBlock_append rc_1_3_2360_0_join0 rc_1_3_2360_0_join1 rfl rfl rfl
private theorem rc_1_3_2360_0 : fastPhase (bank 1 3).shape 179808 2360 3 1 0 2 0 = 63833437975320236164274775 :=
  phase_of_block (n := 389) (by decide +kernel) rc_1_3_2360_0_join2
private theorem rc_1_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 0 128 = 36714706963532405555773536 := by decide +kernel
private theorem rc_1_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 128 128 = 20277504682292241690198627 := by decide +kernel
private theorem rc_1_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 256 128 = 6478299323731353478121406 := by decide +kernel
private theorem rc_1_3_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 384 5 = 6912390123639590512155 := by decide +kernel
private theorem rc_1_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 0 256 = 56992211645824647245972163 :=
  phaseBlock_append rc_1_3_2360_1_part0 rc_1_3_2360_1_part1 rfl rfl rfl
private theorem rc_1_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 256 133 = 6485211713854993068633561 :=
  phaseBlock_append rc_1_3_2360_1_part2 rc_1_3_2360_1_part3 rfl rfl rfl
private theorem rc_1_3_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2360 3 1 0 2 1) 0 389 = 63477423359679640314605724 :=
  phaseBlock_append rc_1_3_2360_1_join0 rc_1_3_2360_1_join1 rfl rfl rfl
private theorem rc_1_3_2360_1 : fastPhase (bank 1 3).shape 179808 2360 3 1 0 2 1 = 63477423359679640314605724 :=
  phase_of_block (n := 389) (by decide +kernel) rc_1_3_2360_1_join2
private theorem rc_1_3_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 0 128 = 36852793020215557015480512 := by decide +kernel
private theorem rc_1_3_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 128 128 = 20394559707496293411394080 := by decide +kernel
private theorem rc_1_3_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 256 128 = 6576201681402356192416144 := by decide +kernel
private theorem rc_1_3_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 384 5 = 10373528472831992308640 := by decide +kernel
private theorem rc_1_3_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 0 256 = 57247352727711850426874592 :=
  phaseBlock_append rc_1_3_2361_0_part0 rc_1_3_2361_0_part1 rfl rfl rfl
private theorem rc_1_3_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 256 133 = 6586575209875188184724784 :=
  phaseBlock_append rc_1_3_2361_0_part2 rc_1_3_2361_0_part3 rfl rfl rfl
private theorem rc_1_3_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 0) 0 389 = 63833927937587038611599376 :=
  phaseBlock_append rc_1_3_2361_0_join0 rc_1_3_2361_0_join1 rfl rfl rfl
private theorem rc_1_3_2361_0 : fastPhase (bank 1 3).shape 179808 2361 3 1 0 2 0 = 63833927937587038611599376 :=
  phase_of_block (n := 389) (by decide +kernel) rc_1_3_2361_0_join2
private theorem rc_1_3_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 0 128 = 36715023271738912214820096 := by decide +kernel
private theorem rc_1_3_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 128 128 = 20277643582775290401581577 := by decide +kernel
private theorem rc_1_3_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 256 128 = 6478331935013766405048397 := by decide +kernel
private theorem rc_1_3_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 384 5 = 6912414745023756937178 := by decide +kernel
private theorem rc_1_3_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 0 256 = 56992666854514202616401673 :=
  phaseBlock_append rc_1_3_2361_1_part0 rc_1_3_2361_1_part1 rfl rfl rfl
private theorem rc_1_3_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 256 133 = 6485244349758790161985575 :=
  phaseBlock_append rc_1_3_2361_1_part2 rc_1_3_2361_1_part3 rfl rfl rfl
private theorem rc_1_3_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2361 3 1 0 2 1) 0 389 = 63477911204272992778387248 :=
  phaseBlock_append rc_1_3_2361_1_join0 rc_1_3_2361_1_join1 rfl rfl rfl
private theorem rc_1_3_2361_1 : fastPhase (bank 1 3).shape 179808 2361 3 1 0 2 1 = 63477911204272992778387248 :=
  phase_of_block (n := 389) (by decide +kernel) rc_1_3_2361_1_join2
private theorem receipt_1_3 : B1Checked (bank 1 3) 3 0 2 := by
  refine b1_checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_1830_388)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_3_2360_0 rc_1_3_2360_1 rc_1_3_2361_0 rc_1_3_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 0 128 = 62517198411427414569280160 := by decide +kernel
private theorem rc_1_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 128 128 = 38416058221830705309171836 := by decide +kernel
private theorem rc_1_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 256 128 = 17682916658577301649060247 := by decide +kernel
private theorem rc_1_4_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 384 63 = 2047213950953802245307882 := by decide +kernel
private theorem rc_1_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 0 256 = 100933256633258119878451996 :=
  phaseBlock_append rc_1_4_2360_0_part0 rc_1_4_2360_0_part1 rfl rfl rfl
private theorem rc_1_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 256 191 = 19730130609531103894368129 :=
  phaseBlock_append rc_1_4_2360_0_part2 rc_1_4_2360_0_part3 rfl rfl rfl
private theorem rc_1_4_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 0) 0 447 = 120663387242789223772820125 :=
  phaseBlock_append rc_1_4_2360_0_join0 rc_1_4_2360_0_join1 rfl rfl rfl
private theorem rc_1_4_2360_0 : fastPhase (bank 1 4).shape 179808 2360 4 1 0 2 0 = 120663387242789223772820125 :=
  phase_of_block (n := 447) (by decide +kernel) rc_1_4_2360_0_join2
private theorem rc_1_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 0 128 = 62317615678905628031104480 := by decide +kernel
private theorem rc_1_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 128 128 = 38242934020671729697178554 := by decide +kernel
private theorem rc_1_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 256 128 = 17534250324407037491375877 := by decide +kernel
private theorem rc_1_4_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 384 63 = 1982421825675840403429983 := by decide +kernel
private theorem rc_1_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 0 256 = 100560549699577357728283034 :=
  phaseBlock_append rc_1_4_2360_1_part0 rc_1_4_2360_1_part1 rfl rfl rfl
private theorem rc_1_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 256 191 = 19516672150082877894805860 :=
  phaseBlock_append rc_1_4_2360_1_part2 rc_1_4_2360_1_part3 rfl rfl rfl
private theorem rc_1_4_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2360 4 1 0 2 1) 0 447 = 120077221849660235623088894 :=
  phaseBlock_append rc_1_4_2360_1_join0 rc_1_4_2360_1_join1 rfl rfl rfl
private theorem rc_1_4_2360_1 : fastPhase (bank 1 4).shape 179808 2360 4 1 0 2 1 = 120077221849660235623088894 :=
  phase_of_block (n := 447) (by decide +kernel) rc_1_4_2360_1_join2
private theorem rc_1_4_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 0 128 = 62517742275888976944702496 := by decide +kernel
private theorem rc_1_4_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 128 128 = 38416333687843711287082857 := by decide +kernel
private theorem rc_1_4_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 256 128 = 17683014382271199127246766 := by decide +kernel
private theorem rc_1_4_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 384 63 = 2047222391075581615144991 := by decide +kernel
private theorem rc_1_4_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 0 256 = 100934075963732688231785353 :=
  phaseBlock_append rc_1_4_2361_0_part0 rc_1_4_2361_0_part1 rfl rfl rfl
private theorem rc_1_4_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 256 191 = 19730236773346780742391757 :=
  phaseBlock_append rc_1_4_2361_0_part2 rc_1_4_2361_0_part3 rfl rfl rfl
private theorem rc_1_4_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 0) 0 447 = 120664312737079468974177110 :=
  phaseBlock_append rc_1_4_2361_0_join0 rc_1_4_2361_0_join1 rfl rfl rfl
private theorem rc_1_4_2361_0 : fastPhase (bank 1 4).shape 179808 2361 4 1 0 2 0 = 120664312737079468974177110 :=
  phase_of_block (n := 447) (by decide +kernel) rc_1_4_2361_0_join2
private theorem rc_1_4_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 0 128 = 62318158106338503325049632 := by decide +kernel
private theorem rc_1_4_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 128 128 = 38243208422123908499568902 := by decide +kernel
private theorem rc_1_4_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 256 128 = 17534347316675421671655780 := by decide +kernel
private theorem rc_1_4_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 384 63 = 1982430015667958277718710 := by decide +kernel
private theorem rc_1_4_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 0 256 = 100561366528462411824618534 :=
  phaseBlock_append rc_1_4_2361_1_part0 rc_1_4_2361_1_part1 rfl rfl rfl
private theorem rc_1_4_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 256 191 = 19516777332343379949374490 :=
  phaseBlock_append rc_1_4_2361_1_part2 rc_1_4_2361_1_part3 rfl rfl rfl
private theorem rc_1_4_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2361 4 1 0 2 1) 0 447 = 120078143860805791773993024 :=
  phaseBlock_append rc_1_4_2361_1_join0 rc_1_4_2361_1_join1 rfl rfl rfl
private theorem rc_1_4_2361_1 : fastPhase (bank 1 4).shape 179808 2361 4 1 0 2 1 = 120078143860805791773993024 :=
  phase_of_block (n := 447) (by decide +kernel) rc_1_4_2361_1_join2
private theorem receipt_1_4 : B1Checked (bank 1 4) 4 0 2 := by
  refine b1_checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2103_446)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_4_2360_0 rc_1_4_2360_1 rc_1_4_2361_0 rc_1_4_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 0 128 = 125479702592382219299280672 := by decide +kernel
private theorem rc_1_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 128 128 = 83638689450435287185245984 := by decide +kernel
private theorem rc_1_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 256 128 = 46873616914101630970986950 := by decide +kernel
private theorem rc_1_5_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 384 128 = 14843904157910807847675244 := by decide +kernel
private theorem rc_1_5_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 512 1 = 1682742578637557521728 := by decide +kernel
private theorem rc_1_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 0 256 = 209118392042817506484526656 :=
  phaseBlock_append rc_1_5_2360_0_part0 rc_1_5_2360_0_part1 rfl rfl rfl
private theorem rc_1_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 384 129 = 14845586900489445405196972 :=
  phaseBlock_append rc_1_5_2360_0_part3 rc_1_5_2360_0_part4 rfl rfl rfl
private theorem rc_1_5_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 256 257 = 61719203814591076376183922 :=
  phaseBlock_append rc_1_5_2360_0_part2 rc_1_5_2360_0_join1 rfl rfl rfl
private theorem rc_1_5_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 0) 0 513 = 270837595857408582860710578 :=
  phaseBlock_append rc_1_5_2360_0_join0 rc_1_5_2360_0_join2 rfl rfl rfl
private theorem rc_1_5_2360_0 : fastPhase (bank 1 5).shape 179808 2360 6 1 0 2 0 = 270837595857408582860710578 :=
  phase_of_block (n := 513) (by decide +kernel) rc_1_5_2360_0_join3
private theorem rc_1_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 0 128 = 125136521965692155967716640 := by decide +kernel
private theorem rc_1_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 128 128 = 83335177987571862978211104 := by decide +kernel
private theorem rc_1_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 256 128 = 46607177667721624957871385 := by decide +kernel
private theorem rc_1_5_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 384 128 = 14611976572423193400374220 := by decide +kernel
private theorem rc_1_5_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 512 1 = 0 := by decide +kernel
private theorem rc_1_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 0 256 = 208471699953264018945927744 :=
  phaseBlock_append rc_1_5_2360_1_part0 rc_1_5_2360_1_part1 rfl rfl rfl
private theorem rc_1_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 384 129 = 14611976572423193400374220 :=
  phaseBlock_append rc_1_5_2360_1_part3 rc_1_5_2360_1_part4 rfl rfl rfl
private theorem rc_1_5_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 256 257 = 61219154240144818358245605 :=
  phaseBlock_append rc_1_5_2360_1_part2 rc_1_5_2360_1_join1 rfl rfl rfl
private theorem rc_1_5_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2360 6 1 0 2 1) 0 513 = 269690854193408837304173349 :=
  phaseBlock_append rc_1_5_2360_1_join0 rc_1_5_2360_1_join2 rfl rfl rfl
private theorem rc_1_5_2360_1 : fastPhase (bank 1 5).shape 179808 2360 6 1 0 2 1 = 269690854193408837304173349 :=
  phase_of_block (n := 513) (by decide +kernel) rc_1_5_2360_1_join3
private theorem rc_1_5_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 0 128 = 125480802056829219781576128 := by decide +kernel
private theorem rc_1_5_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 128 128 = 83639311648674875208213952 := by decide +kernel
private theorem rc_1_5_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 256 128 = 46873898880919655149084276 := by decide +kernel
private theorem rc_1_5_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 384 128 = 14843972413636599918780139 := by decide +kernel
private theorem rc_1_5_2361_0_part4 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 512 1 = 1682748418604417786496 := by decide +kernel
private theorem rc_1_5_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 0 256 = 209120113705504094989790080 :=
  phaseBlock_append rc_1_5_2361_0_part0 rc_1_5_2361_0_part1 rfl rfl rfl
private theorem rc_1_5_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 384 129 = 14845655162055204336566635 :=
  phaseBlock_append rc_1_5_2361_0_part3 rc_1_5_2361_0_part4 rfl rfl rfl
private theorem rc_1_5_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 256 257 = 61719554042974859485650911 :=
  phaseBlock_append rc_1_5_2361_0_part2 rc_1_5_2361_0_join1 rfl rfl rfl
private theorem rc_1_5_2361_0_join3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 0) 0 513 = 270839667748478954475440991 :=
  phaseBlock_append rc_1_5_2361_0_join0 rc_1_5_2361_0_join2 rfl rfl rfl
private theorem rc_1_5_2361_0 : fastPhase (bank 1 5).shape 179808 2361 6 1 0 2 0 = 270839667748478954475440991 :=
  phase_of_block (n := 513) (by decide +kernel) rc_1_5_2361_0_join3
private theorem rc_1_5_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 0 128 = 125137618944142709715168640 := by decide +kernel
private theorem rc_1_5_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 128 128 = 83335798260392114031308160 := by decide +kernel
private theorem rc_1_5_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 256 128 = 46607458217660011780471024 := by decide +kernel
private theorem rc_1_5_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 384 128 = 14612043868777437061418142 := by decide +kernel
private theorem rc_1_5_2361_1_part4 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 512 1 = 0 := by decide +kernel
private theorem rc_1_5_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 0 256 = 208473417204534823746476800 :=
  phaseBlock_append rc_1_5_2361_1_part0 rc_1_5_2361_1_part1 rfl rfl rfl
private theorem rc_1_5_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 384 129 = 14612043868777437061418142 :=
  phaseBlock_append rc_1_5_2361_1_part3 rc_1_5_2361_1_part4 rfl rfl rfl
private theorem rc_1_5_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 256 257 = 61219502086437448841889166 :=
  phaseBlock_append rc_1_5_2361_1_part2 rc_1_5_2361_1_join1 rfl rfl rfl
private theorem rc_1_5_2361_1_join3 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2361 6 1 0 2 1) 0 513 = 269692919290972272588365966 :=
  phaseBlock_append rc_1_5_2361_1_join0 rc_1_5_2361_1_join2 rfl rfl rfl
private theorem rc_1_5_2361_1 : fastPhase (bank 1 5).shape 179808 2361 6 1 0 2 1 = 269692919290972272588365966 :=
  phase_of_block (n := 513) (by decide +kernel) rc_1_5_2361_1_join3
private theorem receipt_1_5 : B1Checked (bank 1 5) 6 0 2 := by
  refine b1_checked_from_values (bank 1 5) 6 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2416_512)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_5_2360_0 rc_1_5_2360_1 rc_1_5_2361_0 rc_1_5_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 0 128 = 306746507990080871028910944 := by decide +kernel
private theorem rc_1_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 128 128 = 221800549533442530621045600 := by decide +kernel
private theorem rc_1_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 256 128 = 145455024286755862243999827 := by decide +kernel
private theorem rc_1_6_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 384 128 = 77231996344743539889805173 := by decide +kernel
private theorem rc_1_6_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 512 101 = 17822302104181854887055054 := by decide +kernel
private theorem rc_1_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 0 256 = 528547057523523401649956544 :=
  phaseBlock_append rc_1_6_2360_0_part0 rc_1_6_2360_0_part1 rfl rfl rfl
private theorem rc_1_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 384 229 = 95054298448925394776860227 :=
  phaseBlock_append rc_1_6_2360_0_part3 rc_1_6_2360_0_part4 rfl rfl rfl
private theorem rc_1_6_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 256 357 = 240509322735681257020860054 :=
  phaseBlock_append rc_1_6_2360_0_part2 rc_1_6_2360_0_join1 rfl rfl rfl
private theorem rc_1_6_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 0) 0 613 = 769056380259204658670816598 :=
  phaseBlock_append rc_1_6_2360_0_join0 rc_1_6_2360_0_join2 rfl rfl rfl
private theorem rc_1_6_2360_0 : fastPhase (bank 1 6).shape 179808 2360 9 1 0 2 0 = 769056380259204658670816598 :=
  phase_of_block (n := 613) (by decide +kernel) rc_1_6_2360_0_join3
private theorem rc_1_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 0 128 = 306056994721856228585338080 := by decide +kernel
private theorem rc_1_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 128 128 = 221177875293161138815354080 := by decide +kernel
private theorem rc_1_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 256 128 = 144895547312759244245029107 := by decide +kernel
private theorem rc_1_6_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 384 128 = 76732118331076326635713209 := by decide +kernel
private theorem rc_1_6_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 512 101 = 17467599984998798599521984 := by decide +kernel
private theorem rc_1_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 0 256 = 527234870015017367400692160 :=
  phaseBlock_append rc_1_6_2360_1_part0 rc_1_6_2360_1_part1 rfl rfl rfl
private theorem rc_1_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 384 229 = 94199718316075125235235193 :=
  phaseBlock_append rc_1_6_2360_1_part3 rc_1_6_2360_1_part4 rfl rfl rfl
private theorem rc_1_6_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 256 357 = 239095265628834369480264300 :=
  phaseBlock_append rc_1_6_2360_1_part2 rc_1_6_2360_1_join1 rfl rfl rfl
private theorem rc_1_6_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2360 9 1 0 2 1) 0 613 = 766330135643851736880956460 :=
  phaseBlock_append rc_1_6_2360_1_join0 rc_1_6_2360_1_join2 rfl rfl rfl
private theorem rc_1_6_2360_1 : fastPhase (bank 1 6).shape 179808 2360 9 1 0 2 1 = 766330135643851736880956460 :=
  phase_of_block (n := 613) (by decide +kernel) rc_1_6_2360_1_join3
private theorem rc_1_6_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 0 128 = 306749217707369528705443392 := by decide +kernel
private theorem rc_1_6_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 128 128 = 221802265132597033491023424 := by decide +kernel
private theorem rc_1_6_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 256 128 = 145455979201071980470114204 := by decide +kernel
private theorem rc_1_6_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 384 128 = 77232407109577683759439557 := by decide +kernel
private theorem rc_1_6_2361_0_part4 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 512 101 = 17822376717471645882577767 := by decide +kernel
private theorem rc_1_6_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 0 256 = 528551482839966562196466816 :=
  phaseBlock_append rc_1_6_2361_0_part0 rc_1_6_2361_0_part1 rfl rfl rfl
private theorem rc_1_6_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 384 229 = 95054783827049329642017324 :=
  phaseBlock_append rc_1_6_2361_0_part3 rc_1_6_2361_0_part4 rfl rfl rfl
private theorem rc_1_6_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 256 357 = 240510763028121310112131528 :=
  phaseBlock_append rc_1_6_2361_0_part2 rc_1_6_2361_0_join1 rfl rfl rfl
private theorem rc_1_6_2361_0_join3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 0) 0 613 = 769062245868087872308598344 :=
  phaseBlock_append rc_1_6_2361_0_join0 rc_1_6_2361_0_join2 rfl rfl rfl
private theorem rc_1_6_2361_0 : fastPhase (bank 1 6).shape 179808 2361 9 1 0 2 0 = 769062245868087872308598344 :=
  phase_of_block (n := 613) (by decide +kernel) rc_1_6_2361_0_join3
private theorem rc_1_6_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 0 128 = 306059699411990658525855360 := by decide +kernel
private theorem rc_1_6_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 128 128 = 221179586813697108529790592 := by decide +kernel
private theorem rc_1_6_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 256 128 = 144896499021093385633568209 := by decide +kernel
private theorem rc_1_6_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 384 128 = 76732526695165737821917244 := by decide +kernel
private theorem rc_1_6_2361_1_part4 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 512 101 = 17467673222345119351134474 := by decide +kernel
private theorem rc_1_6_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 0 256 = 527239286225687767055645952 :=
  phaseBlock_append rc_1_6_2361_1_part0 rc_1_6_2361_1_part1 rfl rfl rfl
private theorem rc_1_6_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 384 229 = 94200199917510857173051718 :=
  phaseBlock_append rc_1_6_2361_1_part3 rc_1_6_2361_1_part4 rfl rfl rfl
private theorem rc_1_6_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 256 357 = 239096698938604242806619927 :=
  phaseBlock_append rc_1_6_2361_1_part2 rc_1_6_2361_1_join1 rfl rfl rfl
private theorem rc_1_6_2361_1_join3 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2361 9 1 0 2 1) 0 613 = 766335985164292009862265879 :=
  phaseBlock_append rc_1_6_2361_1_join0 rc_1_6_2361_1_join2 rfl rfl rfl
private theorem rc_1_6_2361_1 : fastPhase (bank 1 6).shape 179808 2361 9 1 0 2 1 = 766335985164292009862265879 :=
  phase_of_block (n := 613) (by decide +kernel) rc_1_6_2361_1_join3
private theorem receipt_1_6 : B1Checked (bank 1 6) 9 0 2 := by
  refine b1_checked_from_values (bank 1 6) 9 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_2886_612)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_6_2360_0 rc_1_6_2360_1 rc_1_6_2361_0 rc_1_6_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 0 128 = 822403834530698636744237696 := by decide +kernel
private theorem rc_1_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 128 128 = 636320875266323973018247808 := by decide +kernel
private theorem rc_1_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 256 128 = 465676700752132490590429824 := by decide +kernel
private theorem rc_1_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 384 128 = 309772473971827171132641527 := by decide +kernel
private theorem rc_1_7_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 512 128 = 167916807765688105047030388 := by decide +kernel
private theorem rc_1_7_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 640 105 = 41233684910300865040477193 := by decide +kernel
private theorem rc_1_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 128 256 = 1101997576018456463608677632 :=
  phaseBlock_append rc_1_7_2360_0_part1 rc_1_7_2360_0_part2 rfl rfl rfl
private theorem rc_1_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 0 384 = 1924401410549155100352915328 :=
  phaseBlock_append rc_1_7_2360_0_part0 rc_1_7_2360_0_join0 rfl rfl rfl
private theorem rc_1_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 512 233 = 209150492675988970087507581 :=
  phaseBlock_append rc_1_7_2360_0_part4 rc_1_7_2360_0_part5 rfl rfl rfl
private theorem rc_1_7_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 384 361 = 518922966647816141220149108 :=
  phaseBlock_append rc_1_7_2360_0_part3 rc_1_7_2360_0_join2 rfl rfl rfl
private theorem rc_1_7_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 0) 0 745 = 2443324377196971241573064436 :=
  phaseBlock_append rc_1_7_2360_0_join1 rc_1_7_2360_0_join3 rfl rfl rfl
private theorem rc_1_7_2360_0 : fastPhase (bank 1 7).shape 179808 2360 13 1 0 2 0 = 2443324377196971241573064436 :=
  phase_of_block (n := 745) (by decide +kernel) rc_1_7_2360_0_join4
private theorem rc_1_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 0 128 = 820907539279073037988554624 := by decide +kernel
private theorem rc_1_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 128 128 = 634943961651898442127304576 := by decide +kernel
private theorem rc_1_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 256 128 = 464413851218263687484368768 := by decide +kernel
private theorem rc_1_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 384 128 = 308618425148597098154978082 := by decide +kernel
private theorem rc_1_7_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 512 128 = 166866347386878072805792139 := by decide +kernel
private theorem rc_1_7_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 640 105 = 40445696145207252277684056 := by decide +kernel
private theorem rc_1_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 128 256 = 1099357812870162129611673344 :=
  phaseBlock_append rc_1_7_2360_1_part1 rc_1_7_2360_1_part2 rfl rfl rfl
private theorem rc_1_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 0 384 = 1920265352149235167600227968 :=
  phaseBlock_append rc_1_7_2360_1_part0 rc_1_7_2360_1_join0 rfl rfl rfl
private theorem rc_1_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 512 233 = 207312043532085325083476195 :=
  phaseBlock_append rc_1_7_2360_1_part4 rc_1_7_2360_1_part5 rfl rfl rfl
private theorem rc_1_7_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 384 361 = 515930468680682423238454277 :=
  phaseBlock_append rc_1_7_2360_1_part3 rc_1_7_2360_1_join2 rfl rfl rfl
private theorem rc_1_7_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2360 13 1 0 2 1) 0 745 = 2436195820829917590838682245 :=
  phaseBlock_append rc_1_7_2360_1_join1 rc_1_7_2360_1_join3 rfl rfl rfl
private theorem rc_1_7_2360_1 : fastPhase (bank 1 7).shape 179808 2360 13 1 0 2 1 = 2436195820829917590838682245 :=
  phase_of_block (n := 745) (by decide +kernel) rc_1_7_2360_1_join4
private theorem rc_1_7_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 0 128 = 822411149089895632300361376 := by decide +kernel
private theorem rc_1_7_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 128 128 = 636325965009122094919841440 := by decide +kernel
private theorem rc_1_7_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 256 128 = 465679986381672790538364576 := by decide +kernel
private theorem rc_1_7_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 384 128 = 309774351160372269480239667 := by decide +kernel
private theorem rc_1_7_2361_0_part4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 512 128 = 167917649250187726657230401 := by decide +kernel
private theorem rc_1_7_2361_0_part5 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 640 105 = 41233852418232538467355147 := by decide +kernel
private theorem rc_1_7_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 128 256 = 1102005951390794885458206016 :=
  phaseBlock_append rc_1_7_2361_0_part1 rc_1_7_2361_0_part2 rfl rfl rfl
private theorem rc_1_7_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 0 384 = 1924417100480690517758567392 :=
  phaseBlock_append rc_1_7_2361_0_part0 rc_1_7_2361_0_join0 rfl rfl rfl
private theorem rc_1_7_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 512 233 = 209151501668420265124585548 :=
  phaseBlock_append rc_1_7_2361_0_part4 rc_1_7_2361_0_part5 rfl rfl rfl
private theorem rc_1_7_2361_0_join3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 384 361 = 518925852828792534604825215 :=
  phaseBlock_append rc_1_7_2361_0_part3 rc_1_7_2361_0_join2 rfl rfl rfl
private theorem rc_1_7_2361_0_join4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 0) 0 745 = 2443342953309483052363392607 :=
  phaseBlock_append rc_1_7_2361_0_join1 rc_1_7_2361_0_join3 rfl rfl rfl
private theorem rc_1_7_2361_0 : fastPhase (bank 1 7).shape 179808 2361 13 1 0 2 0 = 2443342953309483052363392607 :=
  phase_of_block (n := 745) (by decide +kernel) rc_1_7_2361_0_join4
private theorem rc_1_7_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 0 128 = 820914842869926223112466144 := by decide +kernel
private theorem rc_1_7_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 128 128 = 634949042126626443037818592 := by decide +kernel
private theorem rc_1_7_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 256 128 = 464417129167186386259742432 := by decide +kernel
private theorem rc_1_7_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 384 128 = 308620296138116455069071633 := by decide +kernel
private theorem rc_1_7_2361_1_part4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 512 128 = 166867184057583564357286814 := by decide +kernel
private theorem rc_1_7_2361_1_part5 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 640 105 = 40445860659447277291706194 := by decide +kernel
private theorem rc_1_7_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 128 256 = 1099366171293812829297561024 :=
  phaseBlock_append rc_1_7_2361_1_part1 rc_1_7_2361_1_part2 rfl rfl rfl
private theorem rc_1_7_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 0 384 = 1920281014163739052410027168 :=
  phaseBlock_append rc_1_7_2361_1_part0 rc_1_7_2361_1_join0 rfl rfl rfl
private theorem rc_1_7_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 512 233 = 207313044717030841648993008 :=
  phaseBlock_append rc_1_7_2361_1_part4 rc_1_7_2361_1_part5 rfl rfl rfl
private theorem rc_1_7_2361_1_join3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 384 361 = 515933340855147296718064641 :=
  phaseBlock_append rc_1_7_2361_1_part3 rc_1_7_2361_1_join2 rfl rfl rfl
private theorem rc_1_7_2361_1_join4 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2361 13 1 0 2 1) 0 745 = 2436214355018886349128091809 :=
  phaseBlock_append rc_1_7_2361_1_join1 rc_1_7_2361_1_join3 rfl rfl rfl
private theorem rc_1_7_2361_1 : fastPhase (bank 1 7).shape 179808 2361 13 1 0 2 1 = 2436214355018886349128091809 :=
  phase_of_block (n := 745) (by decide +kernel) rc_1_7_2361_1_join4
private theorem receipt_1_7 : B1Checked (bank 1 7) 13 0 2 := by
  refine b1_checked_from_values (bank 1 7) 13 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_3511_744)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_7_2360_0 rc_1_7_2360_1 rc_1_7_2361_0 rc_1_7_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 0 128 = 2145619158667007814241732896 := by decide +kernel
private theorem rc_1_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 128 128 = 1724261269471348141993777440 := by decide +kernel
private theorem rc_1_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 256 128 = 1333155522855672039664970016 := by decide +kernel
private theorem rc_1_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 384 128 = 971130776276544647829773298 := by decide +kernel
private theorem rc_1_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 512 128 = 637026092624431591033765050 := by decide +kernel
private theorem rc_1_8_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 640 128 = 329688172650653443529360064 := by decide +kernel
private theorem rc_1_8_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 768 86 = 61756586924892967316687758 := by decide +kernel
private theorem rc_1_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 128 256 = 3057416792327020181658747456 :=
  phaseBlock_append rc_1_8_2360_0_part1 rc_1_8_2360_0_part2 rfl rfl rfl
private theorem rc_1_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 0 384 = 5203035950994027995900480352 :=
  phaseBlock_append rc_1_8_2360_0_part0 rc_1_8_2360_0_join0 rfl rfl rfl
private theorem rc_1_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 384 256 = 1608156868900976238863538348 :=
  phaseBlock_append rc_1_8_2360_0_part3 rc_1_8_2360_0_part4 rfl rfl rfl
private theorem rc_1_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 640 214 = 391444759575546410846047822 :=
  phaseBlock_append rc_1_8_2360_0_part5 rc_1_8_2360_0_part6 rfl rfl rfl
private theorem rc_1_8_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 384 470 = 1999601628476522649709586170 :=
  phaseBlock_append rc_1_8_2360_0_join2 rc_1_8_2360_0_join3 rfl rfl rfl
private theorem rc_1_8_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 0) 0 854 = 7202637579470550645610066522 :=
  phaseBlock_append rc_1_8_2360_0_join1 rc_1_8_2360_0_join4 rfl rfl rfl
private theorem rc_1_8_2360_0 : fastPhase (bank 1 8).shape 179808 2360 19 1 0 2 0 = 7202637579470550645610066522 :=
  phase_of_block (n := 854) (by decide +kernel) rc_1_8_2360_0_join5
private theorem rc_1_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 0 128 = 2142250551710840510724385056 := by decide +kernel
private theorem rc_1_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 128 128 = 1721125778703441092920752416 := by decide +kernel
private theorem rc_1_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 256 128 = 1330244249616286668163991840 := by decide +kernel
private theorem rc_1_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 384 128 = 968434892707169612592714948 := by decide +kernel
private theorem rc_1_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 512 128 = 634536837755881554251389619 := by decide +kernel
private theorem rc_1_8_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 640 128 = 327396851070648277084888821 := by decide +kernel
private theorem rc_1_8_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 768 86 = 60323956184685258095558745 := by decide +kernel
private theorem rc_1_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 128 256 = 3051370028319727761084744256 :=
  phaseBlock_append rc_1_8_2360_1_part1 rc_1_8_2360_1_part2 rfl rfl rfl
private theorem rc_1_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 0 384 = 5193620580030568271809129312 :=
  phaseBlock_append rc_1_8_2360_1_part0 rc_1_8_2360_1_join0 rfl rfl rfl
private theorem rc_1_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 384 256 = 1602971730463051166844104567 :=
  phaseBlock_append rc_1_8_2360_1_part3 rc_1_8_2360_1_part4 rfl rfl rfl
private theorem rc_1_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 640 214 = 387720807255333535180447566 :=
  phaseBlock_append rc_1_8_2360_1_part5 rc_1_8_2360_1_part6 rfl rfl rfl
private theorem rc_1_8_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 384 470 = 1990692537718384702024552133 :=
  phaseBlock_append rc_1_8_2360_1_join2 rc_1_8_2360_1_join3 rfl rfl rfl
private theorem rc_1_8_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2360 19 1 0 2 1) 0 854 = 7184313117748952973833681445 :=
  phaseBlock_append rc_1_8_2360_1_join1 rc_1_8_2360_1_join4 rfl rfl rfl
private theorem rc_1_8_2360_1 : fastPhase (bank 1 8).shape 179808 2360 19 1 0 2 1 = 7184313117748952973833681445 :=
  phase_of_block (n := 854) (by decide +kernel) rc_1_8_2360_1_join5
private theorem rc_1_8_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 0 128 = 2145638288486427553059773376 := by decide +kernel
private theorem rc_1_8_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 128 128 = 1724275300421245616807066560 := by decide +kernel
private theorem rc_1_8_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 256 128 = 1333165284748381990705454016 := by decide +kernel
private theorem rc_1_8_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 384 128 = 971137058024472494890356881 := by decide +kernel
private theorem rc_1_8_2361_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 512 128 = 637029637390305761276821947 := by decide +kernel
private theorem rc_1_8_2361_0_part5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 640 128 = 329689700549021747533230444 := by decide +kernel
private theorem rc_1_8_2361_0_part6 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 768 86 = 61756823840036619547369811 := by decide +kernel
private theorem rc_1_8_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 128 256 = 3057440585169627607512520576 :=
  phaseBlock_append rc_1_8_2361_0_part1 rc_1_8_2361_0_part2 rfl rfl rfl
private theorem rc_1_8_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 0 384 = 5203078873656055160572293952 :=
  phaseBlock_append rc_1_8_2361_0_part0 rc_1_8_2361_0_join0 rfl rfl rfl
private theorem rc_1_8_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 384 256 = 1608166695414778256167178828 :=
  phaseBlock_append rc_1_8_2361_0_part3 rc_1_8_2361_0_part4 rfl rfl rfl
private theorem rc_1_8_2361_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 640 214 = 391446524389058367080600255 :=
  phaseBlock_append rc_1_8_2361_0_part5 rc_1_8_2361_0_part6 rfl rfl rfl
private theorem rc_1_8_2361_0_join4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 384 470 = 1999613219803836623247779083 :=
  phaseBlock_append rc_1_8_2361_0_join2 rc_1_8_2361_0_join3 rfl rfl rfl
private theorem rc_1_8_2361_0_join5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 0) 0 854 = 7202692093459891783820073035 :=
  phaseBlock_append rc_1_8_2361_0_join1 rc_1_8_2361_0_join4 rfl rfl rfl
private theorem rc_1_8_2361_0 : fastPhase (bank 1 8).shape 179808 2361 19 1 0 2 0 = 7202692093459891783820073035 :=
  phase_of_block (n := 854) (by decide +kernel) rc_1_8_2361_0_join5
private theorem rc_1_8_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 0 128 = 2142269656822709187750850944 := by decide +kernel
private theorem rc_1_8_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 128 128 = 1721139788281603544178995584 := by decide +kernel
private theorem rc_1_8_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 256 128 = 1330253993283740128134066560 := by decide +kernel
private theorem rc_1_8_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 384 128 = 968441159192266854276999093 := by decide +kernel
private theorem rc_1_8_2361_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 512 128 = 634540370066696641486919487 := by decide +kernel
private theorem rc_1_8_2361_1_part5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 640 128 = 327398369138897596414015625 := by decide +kernel
private theorem rc_1_8_2361_1_part6 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 768 86 = 60324187873786387663133247 := by decide +kernel
private theorem rc_1_8_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 128 256 = 3051393781565343672313062144 :=
  phaseBlock_append rc_1_8_2361_1_part1 rc_1_8_2361_1_part2 rfl rfl rfl
private theorem rc_1_8_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 0 384 = 5193663438388052860063913088 :=
  phaseBlock_append rc_1_8_2361_1_part0 rc_1_8_2361_1_join0 rfl rfl rfl
private theorem rc_1_8_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 384 256 = 1602981529258963495763918580 :=
  phaseBlock_append rc_1_8_2361_1_part3 rc_1_8_2361_1_part4 rfl rfl rfl
private theorem rc_1_8_2361_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 640 214 = 387722557012683984077148872 :=
  phaseBlock_append rc_1_8_2361_1_part5 rc_1_8_2361_1_part6 rfl rfl rfl
private theorem rc_1_8_2361_1_join4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 384 470 = 1990704086271647479841067452 :=
  phaseBlock_append rc_1_8_2361_1_join2 rc_1_8_2361_1_join3 rfl rfl rfl
private theorem rc_1_8_2361_1_join5 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2361 19 1 0 2 1) 0 854 = 7184367524659700339904980540 :=
  phaseBlock_append rc_1_8_2361_1_join1 rc_1_8_2361_1_join4 rfl rfl rfl
private theorem rc_1_8_2361_1 : fastPhase (bank 1 8).shape 179808 2361 19 1 0 2 1 = 7184367524659700339904980540 :=
  phase_of_block (n := 854) (by decide +kernel) rc_1_8_2361_1_join5
private theorem receipt_1_8 : B1Checked (bank 1 8) 19 0 2 := by
  refine b1_checked_from_values (bank 1 8) 19 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_4022_853)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_8_2360_0 rc_1_8_2360_1 rc_1_8_2361_0 rc_1_8_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 0 128 = 7617340115275287633707099808 := by decide +kernel
private theorem rc_1_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 128 128 = 6412747889841981171064551072 := by decide +kernel
private theorem rc_1_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 256 128 = 5277673794243113834814244512 := by decide +kernel
private theorem rc_1_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 384 128 = 4209977462934886635346155168 := by decide +kernel
private theorem rc_1_9_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 512 128 = 3207531849890089120820657973 := by decide +kernel
private theorem rc_1_9_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 640 128 = 2268224928818279052439042572 := by decide +kernel
private theorem rc_1_9_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 768 128 = 1389950298687514938516181692 := by decide +kernel
private theorem rc_1_9_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 896 128 = 570611316154038401842176384 := by decide +kernel
private theorem rc_1_9_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 1024 30 = 21384724817097579912919866 := by decide +kernel
private theorem rc_1_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 0 256 = 14030088005117268804771650880 :=
  phaseBlock_append rc_1_9_2360_0_part0 rc_1_9_2360_0_part1 rfl rfl rfl
private theorem rc_1_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 256 256 = 9487651257178000470160399680 :=
  phaseBlock_append rc_1_9_2360_0_part2 rc_1_9_2360_0_part3 rfl rfl rfl
private theorem rc_1_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 0 512 = 23517739262295269274932050560 :=
  phaseBlock_append rc_1_9_2360_0_join0 rc_1_9_2360_0_join1 rfl rfl rfl
private theorem rc_1_9_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 512 256 = 5475756778708368173259700545 :=
  phaseBlock_append rc_1_9_2360_0_part4 rc_1_9_2360_0_part5 rfl rfl rfl
private theorem rc_1_9_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 896 158 = 591996040971135981755096250 :=
  phaseBlock_append rc_1_9_2360_0_part7 rc_1_9_2360_0_part8 rfl rfl rfl
private theorem rc_1_9_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 768 286 = 1981946339658650920271277942 :=
  phaseBlock_append rc_1_9_2360_0_part6 rc_1_9_2360_0_join4 rfl rfl rfl
private theorem rc_1_9_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 512 542 = 7457703118367019093530978487 :=
  phaseBlock_append rc_1_9_2360_0_join3 rc_1_9_2360_0_join5 rfl rfl rfl
private theorem rc_1_9_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 0) 0 1054 = 30975442380662288368463029047 :=
  phaseBlock_append rc_1_9_2360_0_join2 rc_1_9_2360_0_join6 rfl rfl rfl
private theorem rc_1_9_2360_0 : fastPhase (bank 1 9).shape 179808 2360 28 1 0 2 0 = 30975442380662288368463029047 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_1_9_2360_0_join7
private theorem rc_1_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 0 128 = 7607779235105324258436877152 := by decide +kernel
private theorem rc_1_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 128 128 = 6403720529302170881876958048 := by decide +kernel
private theorem rc_1_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 256 128 = 5269163709359789027948735328 := by decide +kernel
private theorem rc_1_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 384 128 = 4201968505855712593191451488 := by decide +kernel
private theorem rc_1_9_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 512 128 = 3200007967046419485333872106 := by decide +kernel
private theorem rc_1_9_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 640 128 = 2261170151350410021335969622 := by decide +kernel
private theorem rc_1_9_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 768 128 = 1383348748982855398452778851 := by decide +kernel
private theorem rc_1_9_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 896 128 = 564447212124528482948993835 := by decide +kernel
private theorem rc_1_9_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 1024 30 = 20001598901217543893303265 := by decide +kernel
private theorem rc_1_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 0 256 = 14011499764407495140313835200 :=
  phaseBlock_append rc_1_9_2360_1_part0 rc_1_9_2360_1_part1 rfl rfl rfl
private theorem rc_1_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 256 256 = 9471132215215501621140186816 :=
  phaseBlock_append rc_1_9_2360_1_part2 rc_1_9_2360_1_part3 rfl rfl rfl
private theorem rc_1_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 0 512 = 23482631979622996761454022016 :=
  phaseBlock_append rc_1_9_2360_1_join0 rc_1_9_2360_1_join1 rfl rfl rfl
private theorem rc_1_9_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 512 256 = 5461178118396829506669841728 :=
  phaseBlock_append rc_1_9_2360_1_part4 rc_1_9_2360_1_part5 rfl rfl rfl
private theorem rc_1_9_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 896 158 = 584448811025746026842297100 :=
  phaseBlock_append rc_1_9_2360_1_part7 rc_1_9_2360_1_part8 rfl rfl rfl
private theorem rc_1_9_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 768 286 = 1967797560008601425295075951 :=
  phaseBlock_append rc_1_9_2360_1_part6 rc_1_9_2360_1_join4 rfl rfl rfl
private theorem rc_1_9_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 512 542 = 7428975678405430931964917679 :=
  phaseBlock_append rc_1_9_2360_1_join3 rc_1_9_2360_1_join5 rfl rfl rfl
private theorem rc_1_9_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2360 28 1 0 2 1) 0 1054 = 30911607658028427693418939695 :=
  phaseBlock_append rc_1_9_2360_1_join2 rc_1_9_2360_1_join6 rfl rfl rfl
private theorem rc_1_9_2360_1 : fastPhase (bank 1 9).shape 179808 2360 28 1 0 2 1 = 30911607658028427693418939695 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_1_9_2360_1_join7
private theorem rc_1_9_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 0 128 = 7617408341026127068556890464 := by decide +kernel
private theorem rc_1_9_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 128 128 = 6412801311528525995176903008 := by decide +kernel
private theorem rc_1_9_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 256 128 = 5277714329302887895631229280 := by decide +kernel
private theorem rc_1_9_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 384 128 = 4210006956135929472530686304 := by decide +kernel
private theorem rc_1_9_2361_0_part4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 512 128 = 3207552057457368883388546310 := by decide +kernel
private theorem rc_1_9_2361_0_part5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 640 128 = 2268237539192326691236713300 := by decide +kernel
private theorem rc_1_9_2361_0_part6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 768 128 = 1389956968193401339435875433 := by decide +kernel
private theorem rc_1_9_2361_0_part7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 896 128 = 570613625721694304818526847 := by decide +kernel
private theorem rc_1_9_2361_0_part8 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 1024 30 = 21384799101787226278801568 := by decide +kernel
private theorem rc_1_9_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 0 256 = 14030209652554653063733793472 :=
  phaseBlock_append rc_1_9_2361_0_part0 rc_1_9_2361_0_part1 rfl rfl rfl
private theorem rc_1_9_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 256 256 = 9487721285438817368161915584 :=
  phaseBlock_append rc_1_9_2361_0_part2 rc_1_9_2361_0_part3 rfl rfl rfl
private theorem rc_1_9_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 0 512 = 23517930937993470431895709056 :=
  phaseBlock_append rc_1_9_2361_0_join0 rc_1_9_2361_0_join1 rfl rfl rfl
private theorem rc_1_9_2361_0_join3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 512 256 = 5475789596649695574625259610 :=
  phaseBlock_append rc_1_9_2361_0_part4 rc_1_9_2361_0_part5 rfl rfl rfl
private theorem rc_1_9_2361_0_join4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 896 158 = 591998424823481531097328415 :=
  phaseBlock_append rc_1_9_2361_0_part7 rc_1_9_2361_0_part8 rfl rfl rfl
private theorem rc_1_9_2361_0_join5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 768 286 = 1981955393016882870533203848 :=
  phaseBlock_append rc_1_9_2361_0_part6 rc_1_9_2361_0_join4 rfl rfl rfl
private theorem rc_1_9_2361_0_join6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 512 542 = 7457744989666578445158463458 :=
  phaseBlock_append rc_1_9_2361_0_join3 rc_1_9_2361_0_join5 rfl rfl rfl
private theorem rc_1_9_2361_0_join7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 0) 0 1054 = 30975675927660048877054172514 :=
  phaseBlock_append rc_1_9_2361_0_join2 rc_1_9_2361_0_join6 rfl rfl rfl
private theorem rc_1_9_2361_0 : fastPhase (bank 1 9).shape 179808 2361 28 1 0 2 0 = 30975675927660048877054172514 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_1_9_2361_0_join7
private theorem rc_1_9_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 0 128 = 7607847390530602613000221920 := by decide +kernel
private theorem rc_1_9_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 128 128 = 6403773888333232605522953440 := by decide +kernel
private theorem rc_1_9_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 256 128 = 5269204189087835499326756064 := by decide +kernel
private theorem rc_1_9_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 384 128 = 4201997950704860781510829280 := by decide +kernel
private theorem rc_1_9_2361_1_part4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 512 128 = 3200028132936614458964790567 := by decide +kernel
private theorem rc_1_9_2361_1_part5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 640 128 = 2261182726441520803337948175 := by decide +kernel
private theorem rc_1_9_2361_1_part6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 768 128 = 1383355389250238220036487930 := by decide +kernel
private theorem rc_1_9_2361_1_part7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 896 128 = 564449498148166654666356620 := by decide +kernel
private theorem rc_1_9_2361_1_part8 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 1024 30 = 20001668453998884771538257 := by decide +kernel
private theorem rc_1_9_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 0 256 = 14011621278863835218523175360 :=
  phaseBlock_append rc_1_9_2361_1_part0 rc_1_9_2361_1_part1 rfl rfl rfl
private theorem rc_1_9_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 256 256 = 9471202139792696280837585344 :=
  phaseBlock_append rc_1_9_2361_1_part2 rc_1_9_2361_1_part3 rfl rfl rfl
private theorem rc_1_9_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 0 512 = 23482823418656531499360760704 :=
  phaseBlock_append rc_1_9_2361_1_join0 rc_1_9_2361_1_join1 rfl rfl rfl
private theorem rc_1_9_2361_1_join3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 512 256 = 5461210859378135262302738742 :=
  phaseBlock_append rc_1_9_2361_1_part4 rc_1_9_2361_1_part5 rfl rfl rfl
private theorem rc_1_9_2361_1_join4 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 896 158 = 584451166602165539437894877 :=
  phaseBlock_append rc_1_9_2361_1_part7 rc_1_9_2361_1_part8 rfl rfl rfl
private theorem rc_1_9_2361_1_join5 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 768 286 = 1967806555852403759474382807 :=
  phaseBlock_append rc_1_9_2361_1_part6 rc_1_9_2361_1_join4 rfl rfl rfl
private theorem rc_1_9_2361_1_join6 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 512 542 = 7429017415230539021777121549 :=
  phaseBlock_append rc_1_9_2361_1_join3 rc_1_9_2361_1_join5 rfl rfl rfl
private theorem rc_1_9_2361_1_join7 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2361 28 1 0 2 1) 0 1054 = 30911840833887070521137882253 :=
  phaseBlock_append rc_1_9_2361_1_join2 rc_1_9_2361_1_join6 rfl rfl rfl
private theorem rc_1_9_2361_1 : fastPhase (bank 1 9).shape 179808 2361 28 1 0 2 1 = 30911840833887070521137882253 :=
  phase_of_block (n := 1054) (by decide +kernel) rc_1_9_2361_1_join7
private theorem receipt_1_9 : B1Checked (bank 1 9) 28 0 2 := by
  refine b1_checked_from_values (bank 1 9) 28 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_4969_1053)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_9_2360_0 rc_1_9_2360_1 rc_1_9_2361_0 rc_1_9_2361_1 (by decide +kernel) (by decide +kernel)
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
private theorem rc_1_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 0 128 = 28726866512227382535863841888 := by decide +kernel
private theorem rc_1_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 128 128 = 25099117241545701227177100384 := by decide +kernel
private theorem rc_1_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 256 128 = 21638261735084617247206069344 := by decide +kernel
private theorem rc_1_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 384 128 = 18340244453301004949248730208 := by decide +kernel
private theorem rc_1_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 512 128 = 15201027260953086614658806880 := by decide +kernel
private theorem rc_1_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 640 128 = 12216590663476250125556379279 := by decide +kernel
private theorem rc_1_10_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 768 128 = 9382939906831020489440728740 := by decide +kernel
private theorem rc_1_10_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 896 128 = 6696084258877510193707044950 := by decide +kernel
private theorem rc_1_10_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 1024 128 = 4152042426828963306218087793 := by decide +kernel
private theorem rc_1_10_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 1152 128 = 1746850395549431683368344327 := by decide +kernel
private theorem rc_1_10_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 1280 33 = 76933237549711387435017835 := by decide +kernel
private theorem rc_1_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 0 256 = 53825983753773083763040942272 :=
  phaseBlock_append rc_1_10_2360_0_part0 rc_1_10_2360_0_part1 rfl rfl rfl
private theorem rc_1_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 384 256 = 33541271714254091563907537088 :=
  phaseBlock_append rc_1_10_2360_0_part3 rc_1_10_2360_0_part4 rfl rfl rfl
private theorem rc_1_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 256 384 = 55179533449338708811113606432 :=
  phaseBlock_append rc_1_10_2360_0_part2 rc_1_10_2360_0_join1 rfl rfl rfl
private theorem rc_1_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 0 640 = 109005517203111792574154548704 :=
  phaseBlock_append rc_1_10_2360_0_join0 rc_1_10_2360_0_join2 rfl rfl rfl
private theorem rc_1_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 768 256 = 16079024165708530683147773690 :=
  phaseBlock_append rc_1_10_2360_0_part6 rc_1_10_2360_0_part7 rfl rfl rfl
private theorem rc_1_10_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 640 384 = 28295614829184780808704152969 :=
  phaseBlock_append rc_1_10_2360_0_part5 rc_1_10_2360_0_join4 rfl rfl rfl
private theorem rc_1_10_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 1152 161 = 1823783633099143070803362162 :=
  phaseBlock_append rc_1_10_2360_0_part9 rc_1_10_2360_0_part10 rfl rfl rfl
private theorem rc_1_10_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 1024 289 = 5975826059928106377021449955 :=
  phaseBlock_append rc_1_10_2360_0_part8 rc_1_10_2360_0_join6 rfl rfl rfl
private theorem rc_1_10_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 640 673 = 34271440889112887185725602924 :=
  phaseBlock_append rc_1_10_2360_0_join5 rc_1_10_2360_0_join7 rfl rfl rfl
private theorem rc_1_10_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 0) 0 1313 = 143276958092224679759880151628 :=
  phaseBlock_append rc_1_10_2360_0_join3 rc_1_10_2360_0_join8 rfl rfl rfl
private theorem rc_1_10_2360_0 : fastPhase (bank 1 10).shape 179808 2360 40 1 0 2 0 = 143276958092224679759880151628 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_1_10_2360_0_join9
private theorem rc_1_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 0 128 = 28698245177427336357093153504 := by decide +kernel
private theorem rc_1_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 128 128 = 25071772457314679268331662048 := by decide +kernel
private theorem rc_1_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 256 128 = 21612162751223699997720296160 := by decide +kernel
private theorem rc_1_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 384 128 = 18315360652349270619744684768 := by decide +kernel
private theorem rc_1_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 512 128 = 15177328157995145749672614624 := by decide +kernel
private theorem rc_1_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 640 128 = 12194045903716080498287519502 := by decide +kernel
private theorem rc_1_10_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 768 128 = 9361519247477069440899507660 := by decide +kernel
private theorem rc_1_10_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 896 128 = 6675757578845279966021382816 := by decide +kernel
private theorem rc_1_10_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 1024 128 = 4132779736954459604111560809 := by decide +kernel
private theorem rc_1_10_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 1152 128 = 1728621838496596700346984432 := by decide +kernel
private theorem rc_1_10_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 1280 33 = 72397731551795022988412667 := by decide +kernel
private theorem rc_1_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 0 256 = 53770017634742015625424815552 :=
  phaseBlock_append rc_1_10_2360_1_part0 rc_1_10_2360_1_part1 rfl rfl rfl
private theorem rc_1_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 384 256 = 33492688810344416369417299392 :=
  phaseBlock_append rc_1_10_2360_1_part3 rc_1_10_2360_1_part4 rfl rfl rfl
private theorem rc_1_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 256 384 = 55104851561568116367137595552 :=
  phaseBlock_append rc_1_10_2360_1_part2 rc_1_10_2360_1_join1 rfl rfl rfl
private theorem rc_1_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 0 640 = 108874869196310131992562411104 :=
  phaseBlock_append rc_1_10_2360_1_join0 rc_1_10_2360_1_join2 rfl rfl rfl
private theorem rc_1_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 768 256 = 16037276826322349406920890476 :=
  phaseBlock_append rc_1_10_2360_1_part6 rc_1_10_2360_1_part7 rfl rfl rfl
private theorem rc_1_10_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 640 384 = 28231322730038429905208409978 :=
  phaseBlock_append rc_1_10_2360_1_part5 rc_1_10_2360_1_join4 rfl rfl rfl
private theorem rc_1_10_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 1152 161 = 1801019570048391723335397099 :=
  phaseBlock_append rc_1_10_2360_1_part9 rc_1_10_2360_1_part10 rfl rfl rfl
private theorem rc_1_10_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 1024 289 = 5933799307002851327446957908 :=
  phaseBlock_append rc_1_10_2360_1_part8 rc_1_10_2360_1_join6 rfl rfl rfl
private theorem rc_1_10_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 640 673 = 34165122037041281232655367886 :=
  phaseBlock_append rc_1_10_2360_1_join5 rc_1_10_2360_1_join7 rfl rfl rfl
private theorem rc_1_10_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2360 40 1 0 2 1) 0 1313 = 143039991233351413225217778990 :=
  phaseBlock_append rc_1_10_2360_1_join3 rc_1_10_2360_1_join8 rfl rfl rfl
private theorem rc_1_10_2360_1 : fastPhase (bank 1 10).shape 179808 2360 40 1 0 2 1 = 143039991233351413225217778990 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_1_10_2360_1_join9
private theorem rc_1_10_2361_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 0 128 = 28727124630196795964843107968 := by decide +kernel
private theorem rc_1_10_2361_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 128 128 = 25099330223063382496633710208 := by decide +kernel
private theorem rc_1_10_2361_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 256 128 = 21638434205436294008445118080 := by decide +kernel
private theorem rc_1_10_2361_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 384 128 = 18340380899693455394689574528 := by decide +kernel
private theorem rc_1_10_2361_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 512 128 = 15201132033118818646309545600 := by decide +kernel
private theorem rc_1_10_2361_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 640 128 = 12216667935063899432481616834 := by decide +kernel
private theorem rc_1_10_2361_0_part6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 768 128 = 9382993691026917557777620921 := by decide +kernel
private theorem rc_1_10_2361_0_part7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 896 128 = 6696118563750371295164066760 := by decide +kernel
private theorem rc_1_10_2361_0_part8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 1024 128 = 4152061117767814732050865662 := by decide +kernel
private theorem rc_1_10_2361_0_part9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 1152 128 = 1746857192605370908758030334 := by decide +kernel
private theorem rc_1_10_2361_0_part10 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 1280 33 = 76933501109068185367667303 := by decide +kernel
private theorem rc_1_10_2361_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 0 256 = 53826454853260178461476818176 :=
  phaseBlock_append rc_1_10_2361_0_part0 rc_1_10_2361_0_part1 rfl rfl rfl
private theorem rc_1_10_2361_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 384 256 = 33541512932812274040999120128 :=
  phaseBlock_append rc_1_10_2361_0_part3 rc_1_10_2361_0_part4 rfl rfl rfl
private theorem rc_1_10_2361_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 256 384 = 55179947138248568049444238208 :=
  phaseBlock_append rc_1_10_2361_0_part2 rc_1_10_2361_0_join1 rfl rfl rfl
private theorem rc_1_10_2361_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 0 640 = 109006401991508746510921056384 :=
  phaseBlock_append rc_1_10_2361_0_join0 rc_1_10_2361_0_join2 rfl rfl rfl
private theorem rc_1_10_2361_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 768 256 = 16079112254777288852941687681 :=
  phaseBlock_append rc_1_10_2361_0_part6 rc_1_10_2361_0_part7 rfl rfl rfl
private theorem rc_1_10_2361_0_join5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 640 384 = 28295780189841188285423304515 :=
  phaseBlock_append rc_1_10_2361_0_part5 rc_1_10_2361_0_join4 rfl rfl rfl
private theorem rc_1_10_2361_0_join6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 1152 161 = 1823790693714439094125697637 :=
  phaseBlock_append rc_1_10_2361_0_part9 rc_1_10_2361_0_part10 rfl rfl rfl
private theorem rc_1_10_2361_0_join7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 1024 289 = 5975851811482253826176563299 :=
  phaseBlock_append rc_1_10_2361_0_part8 rc_1_10_2361_0_join6 rfl rfl rfl
private theorem rc_1_10_2361_0_join8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 640 673 = 34271632001323442111599867814 :=
  phaseBlock_append rc_1_10_2361_0_join5 rc_1_10_2361_0_join7 rfl rfl rfl
private theorem rc_1_10_2361_0_join9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 0) 0 1313 = 143278033992832188622520924198 :=
  phaseBlock_append rc_1_10_2361_0_join3 rc_1_10_2361_0_join8 rfl rfl rfl
private theorem rc_1_10_2361_0 : fastPhase (bank 1 10).shape 179808 2361 40 1 0 2 0 = 143278033992832188622520924198 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_1_10_2361_0_join9
private theorem rc_1_10_2361_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 0 128 = 28698503084554525614659686848 := by decide +kernel
private theorem rc_1_10_2361_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 128 128 = 25071985246411899376574558656 := by decide +kernel
private theorem rc_1_10_2361_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 256 128 = 21612335046919837952907907520 := by decide +kernel
private theorem rc_1_10_2361_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 384 128 = 18315496941197580187797598656 := by decide +kernel
private theorem rc_1_10_2361_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 512 128 = 15177432789077921411957903808 := by decide +kernel
private theorem rc_1_10_2361_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 640 128 = 12194123050103423811122117314 := by decide +kernel
private theorem rc_1_10_2361_1_part6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 768 128 = 9361572921875843074282192287 := by decide +kernel
private theorem rc_1_10_2361_1_part7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 896 128 = 6675791788659831729679474655 := by decide +kernel
private theorem rc_1_10_2361_1_part8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 1024 128 = 4132798346908010520868333188 := by decide +kernel
private theorem rc_1_10_2361_1_part9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 1152 128 = 1728628567979884215668963172 := by decide +kernel
private theorem rc_1_10_2361_1_part10 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 1280 33 = 72397979783260799266297554 := by decide +kernel
private theorem rc_1_10_2361_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 0 256 = 53770488330966424991234245504 :=
  phaseBlock_append rc_1_10_2361_1_part0 rc_1_10_2361_1_part1 rfl rfl rfl
private theorem rc_1_10_2361_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 384 256 = 33492929730275501599755502464 :=
  phaseBlock_append rc_1_10_2361_1_part3 rc_1_10_2361_1_part4 rfl rfl rfl
private theorem rc_1_10_2361_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 256 384 = 55105264777195339552663409984 :=
  phaseBlock_append rc_1_10_2361_1_part2 rc_1_10_2361_1_join1 rfl rfl rfl
private theorem rc_1_10_2361_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 0 640 = 108875753108161764543897655488 :=
  phaseBlock_append rc_1_10_2361_1_join0 rc_1_10_2361_1_join2 rfl rfl rfl
private theorem rc_1_10_2361_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 768 256 = 16037364710535674803961666942 :=
  phaseBlock_append rc_1_10_2361_1_part6 rc_1_10_2361_1_part7 rfl rfl rfl
private theorem rc_1_10_2361_1_join5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 640 384 = 28231487760639098615083784256 :=
  phaseBlock_append rc_1_10_2361_1_part5 rc_1_10_2361_1_join4 rfl rfl rfl
private theorem rc_1_10_2361_1_join6 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 1152 161 = 1801026547763145014935260726 :=
  phaseBlock_append rc_1_10_2361_1_part9 rc_1_10_2361_1_part10 rfl rfl rfl
private theorem rc_1_10_2361_1_join7 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 1024 289 = 5933824894671155535803593914 :=
  phaseBlock_append rc_1_10_2361_1_part8 rc_1_10_2361_1_join6 rfl rfl rfl
private theorem rc_1_10_2361_1_join8 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 640 673 = 34165312655310254150887378170 :=
  phaseBlock_append rc_1_10_2361_1_join5 rc_1_10_2361_1_join7 rfl rfl rfl
private theorem rc_1_10_2361_1_join9 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2361 40 1 0 2 1) 0 1313 = 143041065763472018694785033658 :=
  phaseBlock_append rc_1_10_2361_1_join3 rc_1_10_2361_1_join8 rfl rfl rfl
private theorem rc_1_10_2361_1 : fastPhase (bank 1 10).shape 179808 2361 40 1 0 2 1 = 143041065763472018694785033658 :=
  phase_of_block (n := 1313) (by decide +kernel) rc_1_10_2361_1_join9
private theorem receipt_1_10 : B1Checked (bank 1 10) 40 0 2 := by
  refine b1_checked_from_values (bank 1 10) 40 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) mom_6190_1312)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rc_1_10_2360_0 rc_1_10_2360_1 rc_1_10_2361_0 rc_1_10_2361_1 (by decide +kernel) (by decide +kernel)

theorem rect1_checked (i : Fin 11) :
    B1Checked (bank 1 i) (reserve i) (excess 1) (seed 1) := by
  fin_cases i
  · exact receipt_1_0
  · exact receipt_1_1
  · exact receipt_1_2
  · exact receipt_1_3
  · exact receipt_1_4
  · exact receipt_1_5
  · exact receipt_1_6
  · exact receipt_1_7
  · exact receipt_1_8
  · exact receipt_1_9
  · exact receipt_1_10

#print axioms rect1_checked
end Lower6962.B1.RescueSource
