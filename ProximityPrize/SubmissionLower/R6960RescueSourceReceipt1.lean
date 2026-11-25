import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_977_207_part0 :
    blockEstimate 977 207 207 128 = 315454880 := by decide +kernel
private theorem moment_977_207_part1 :
    blockEstimate 977 207 335 128 = 1893094372 := by decide +kernel
private theorem moment_977_207_part2 :
    blockEstimate 977 207 463 128 = 3762297344 := by decide +kernel
private theorem moment_977_207_part3 :
    blockEstimate 977 207 591 128 = 4827257344 := by decide +kernel
private theorem moment_977_207_part4 :
    blockEstimate 977 207 719 128 = 5019802112 := by decide +kernel
private theorem moment_977_207_part5 :
    blockEstimate 977 207 847 128 = 4339931648 := by decide +kernel
private theorem moment_977_207_part6 :
    blockEstimate 977 207 975 128 = 2905553180 := by decide +kernel
private theorem moment_977_207_part7 :
    blockEstimate 977 207 1103 128 = 1377948994 := by decide +kernel
private theorem moment_977_207_part8 :
    blockEstimate 977 207 1231 128 = 313825184 := by decide +kernel
private theorem moment_977_207_part9 :
    blockEstimate 977 207 1359 32 = 3011176 := by decide +kernel
private theorem moment_977_207_join0 :
    blockEstimate 977 207 207 256 = 2208549252 :=
  block_append moment_977_207_part0 moment_977_207_part1 rfl rfl rfl
private theorem moment_977_207_join1 :
    blockEstimate 977 207 591 256 = 9847059456 :=
  block_append moment_977_207_part3 moment_977_207_part4 rfl rfl rfl
private theorem moment_977_207_join2 :
    blockEstimate 977 207 463 384 = 13609356800 :=
  block_append moment_977_207_part2 moment_977_207_join1 rfl rfl rfl
private theorem moment_977_207_join3 :
    blockEstimate 977 207 207 640 = 15817906052 :=
  block_append moment_977_207_join0 moment_977_207_join2 rfl rfl rfl
private theorem moment_977_207_join4 :
    blockEstimate 977 207 847 256 = 7245484828 :=
  block_append moment_977_207_part5 moment_977_207_part6 rfl rfl rfl
private theorem moment_977_207_join5 :
    blockEstimate 977 207 1231 160 = 316836360 :=
  block_append moment_977_207_part8 moment_977_207_part9 rfl rfl rfl
private theorem moment_977_207_join6 :
    blockEstimate 977 207 1103 288 = 1694785354 :=
  block_append moment_977_207_part7 moment_977_207_join5 rfl rfl rfl
private theorem moment_977_207_join7 :
    blockEstimate 977 207 847 544 = 8940270182 :=
  block_append moment_977_207_join4 moment_977_207_join6 rfl rfl rfl
private theorem moment_977_207_join8 :
    blockEstimate 977 207 207 1184 = 24758176234 :=
  block_append moment_977_207_join3 moment_977_207_join7 rfl rfl rfl

theorem moment_977_207 : momentEstimate 977 207 = 24758176234 := moment_977_207_join8

private theorem moment_1047_222_part0 :
    blockEstimate 1047 222 222 128 = 340498080 := by decide +kernel
private theorem moment_1047_222_part1 :
    blockEstimate 1047 222 350 128 = 2075230592 := by decide +kernel
private theorem moment_1047_222_part2 :
    blockEstimate 1047 222 478 128 = 4311457024 := by decide +kernel
private theorem moment_1047_222_part3 :
    blockEstimate 1047 222 606 128 = 5736373504 := by decide +kernel
private theorem moment_1047_222_part4 :
    blockEstimate 1047 222 734 128 = 6225960192 := by decide +kernel
private theorem moment_1047_222_part5 :
    blockEstimate 1047 222 862 128 = 5780217088 := by decide +kernel
private theorem moment_1047_222_part6 :
    blockEstimate 1047 222 990 128 = 4419886184 := by decide +kernel
private theorem moment_1047_222_part7 :
    blockEstimate 1047 222 1118 128 = 2600283532 := by decide +kernel
private theorem moment_1047_222_part8 :
    blockEstimate 1047 222 1246 128 = 1026138287 := by decide +kernel
private theorem moment_1047_222_part9 :
    blockEstimate 1047 222 1374 117 = 137654825 := by decide +kernel
private theorem moment_1047_222_join0 :
    blockEstimate 1047 222 222 256 = 2415728672 :=
  block_append moment_1047_222_part0 moment_1047_222_part1 rfl rfl rfl
private theorem moment_1047_222_join1 :
    blockEstimate 1047 222 606 256 = 11962333696 :=
  block_append moment_1047_222_part3 moment_1047_222_part4 rfl rfl rfl
private theorem moment_1047_222_join2 :
    blockEstimate 1047 222 478 384 = 16273790720 :=
  block_append moment_1047_222_part2 moment_1047_222_join1 rfl rfl rfl
private theorem moment_1047_222_join3 :
    blockEstimate 1047 222 222 640 = 18689519392 :=
  block_append moment_1047_222_join0 moment_1047_222_join2 rfl rfl rfl
private theorem moment_1047_222_join4 :
    blockEstimate 1047 222 862 256 = 10200103272 :=
  block_append moment_1047_222_part5 moment_1047_222_part6 rfl rfl rfl
private theorem moment_1047_222_join5 :
    blockEstimate 1047 222 1246 245 = 1163793112 :=
  block_append moment_1047_222_part8 moment_1047_222_part9 rfl rfl rfl
private theorem moment_1047_222_join6 :
    blockEstimate 1047 222 1118 373 = 3764076644 :=
  block_append moment_1047_222_part7 moment_1047_222_join5 rfl rfl rfl
private theorem moment_1047_222_join7 :
    blockEstimate 1047 222 862 629 = 13964179916 :=
  block_append moment_1047_222_join4 moment_1047_222_join6 rfl rfl rfl
private theorem moment_1047_222_join8 :
    blockEstimate 1047 222 222 1269 = 32653699308 :=
  block_append moment_1047_222_join3 moment_1047_222_join7 rfl rfl rfl

theorem moment_1047_222 : momentEstimate 1047 222 = 32653699308 := moment_1047_222_join8

private theorem moment_1117_237_part0 :
    blockEstimate 1117 237 237 128 = 365541280 := by decide +kernel
private theorem moment_1117_237_part1 :
    blockEstimate 1117 237 365 128 = 2252469787 := by decide +kernel
private theorem moment_1117_237_part2 :
    blockEstimate 1117 237 493 128 = 4866007104 := by decide +kernel
private theorem moment_1117_237_part3 :
    blockEstimate 1117 237 621 128 = 6688972864 := by decide +kernel
private theorem moment_1117_237_part4 :
    blockEstimate 1117 237 749 128 = 7513694272 := by decide +kernel
private theorem moment_1117_237_part5 :
    blockEstimate 1117 237 877 128 = 7340171328 := by decide +kernel
private theorem moment_1117_237_part6 :
    blockEstimate 1117 237 1005 128 = 6168649768 := by decide +kernel
private theorem moment_1117_237_part7 :
    blockEstimate 1117 237 1133 128 = 4198892547 := by decide +kernel
private theorem moment_1117_237_part8 :
    blockEstimate 1117 237 1261 128 = 2189402175 := by decide +kernel
private theorem moment_1117_237_part9 :
    blockEstimate 1117 237 1389 128 = 679563600 := by decide +kernel
private theorem moment_1117_237_part10 :
    blockEstimate 1117 237 1517 74 = 38827925 := by decide +kernel
private theorem moment_1117_237_join0 :
    blockEstimate 1117 237 237 256 = 2618011067 :=
  block_append moment_1117_237_part0 moment_1117_237_part1 rfl rfl rfl
private theorem moment_1117_237_join1 :
    blockEstimate 1117 237 621 256 = 14202667136 :=
  block_append moment_1117_237_part3 moment_1117_237_part4 rfl rfl rfl
private theorem moment_1117_237_join2 :
    blockEstimate 1117 237 493 384 = 19068674240 :=
  block_append moment_1117_237_part2 moment_1117_237_join1 rfl rfl rfl
private theorem moment_1117_237_join3 :
    blockEstimate 1117 237 237 640 = 21686685307 :=
  block_append moment_1117_237_join0 moment_1117_237_join2 rfl rfl rfl
private theorem moment_1117_237_join4 :
    blockEstimate 1117 237 1005 256 = 10367542315 :=
  block_append moment_1117_237_part6 moment_1117_237_part7 rfl rfl rfl
private theorem moment_1117_237_join5 :
    blockEstimate 1117 237 877 384 = 17707713643 :=
  block_append moment_1117_237_part5 moment_1117_237_join4 rfl rfl rfl
private theorem moment_1117_237_join6 :
    blockEstimate 1117 237 1389 202 = 718391525 :=
  block_append moment_1117_237_part9 moment_1117_237_part10 rfl rfl rfl
private theorem moment_1117_237_join7 :
    blockEstimate 1117 237 1261 330 = 2907793700 :=
  block_append moment_1117_237_part8 moment_1117_237_join6 rfl rfl rfl
private theorem moment_1117_237_join8 :
    blockEstimate 1117 237 877 714 = 20615507343 :=
  block_append moment_1117_237_join5 moment_1117_237_join7 rfl rfl rfl
private theorem moment_1117_237_join9 :
    blockEstimate 1117 237 237 1354 = 42302192650 :=
  block_append moment_1117_237_join3 moment_1117_237_join8 rfl rfl rfl

theorem moment_1117_237 : momentEstimate 1117 237 = 42302192650 := moment_1117_237_join9

private theorem moment_1326_281_part0 :
    blockEstimate 1326 281 281 128 = 440313120 := by decide +kernel
private theorem moment_1326_281_part1 :
    blockEstimate 1326 281 409 128 = 2769958176 := by decide +kernel
private theorem moment_1326_281_part2 :
    blockEstimate 1326 281 537 128 = 6492999306 := by decide +kernel
private theorem moment_1326_281_part3 :
    blockEstimate 1326 281 665 128 = 9717503424 := by decide +kernel
private theorem moment_1326_281_part4 :
    blockEstimate 1326 281 793 128 = 11761980864 := by decide +kernel
private theorem moment_1326_281_part5 :
    blockEstimate 1326 281 921 128 = 12623664576 := by decide +kernel
private theorem moment_1326_281_part6 :
    blockEstimate 1326 281 1049 128 = 12302554560 := by decide +kernel
private theorem moment_1326_281_part7 :
    blockEstimate 1326 281 1177 128 = 10798650816 := by decide +kernel
private theorem moment_1326_281_part8 :
    blockEstimate 1326 281 1305 128 = 8203180395 := by decide +kernel
private theorem moment_1326_281_part9 :
    blockEstimate 1326 281 1433 128 = 5254501290 := by decide +kernel
private theorem moment_1326_281_part10 :
    blockEstimate 1326 281 1561 128 = 2634292110 := by decide +kernel
private theorem moment_1326_281_part11 :
    blockEstimate 1326 281 1689 128 = 787344864 := by decide +kernel
private theorem moment_1326_281_part12 :
    blockEstimate 1326 281 1817 71 = 41059686 := by decide +kernel
private theorem moment_1326_281_join0 :
    blockEstimate 1326 281 409 256 = 9262957482 :=
  block_append moment_1326_281_part1 moment_1326_281_part2 rfl rfl rfl
private theorem moment_1326_281_join1 :
    blockEstimate 1326 281 281 384 = 9703270602 :=
  block_append moment_1326_281_part0 moment_1326_281_join0 rfl rfl rfl
private theorem moment_1326_281_join2 :
    blockEstimate 1326 281 793 256 = 24385645440 :=
  block_append moment_1326_281_part4 moment_1326_281_part5 rfl rfl rfl
private theorem moment_1326_281_join3 :
    blockEstimate 1326 281 665 384 = 34103148864 :=
  block_append moment_1326_281_part3 moment_1326_281_join2 rfl rfl rfl
private theorem moment_1326_281_join4 :
    blockEstimate 1326 281 281 768 = 43806419466 :=
  block_append moment_1326_281_join1 moment_1326_281_join3 rfl rfl rfl
private theorem moment_1326_281_join5 :
    blockEstimate 1326 281 1177 256 = 19001831211 :=
  block_append moment_1326_281_part7 moment_1326_281_part8 rfl rfl rfl
private theorem moment_1326_281_join6 :
    blockEstimate 1326 281 1049 384 = 31304385771 :=
  block_append moment_1326_281_part6 moment_1326_281_join5 rfl rfl rfl
private theorem moment_1326_281_join7 :
    blockEstimate 1326 281 1433 256 = 7888793400 :=
  block_append moment_1326_281_part9 moment_1326_281_part10 rfl rfl rfl
private theorem moment_1326_281_join8 :
    blockEstimate 1326 281 1689 199 = 828404550 :=
  block_append moment_1326_281_part11 moment_1326_281_part12 rfl rfl rfl
private theorem moment_1326_281_join9 :
    blockEstimate 1326 281 1433 455 = 8717197950 :=
  block_append moment_1326_281_join7 moment_1326_281_join8 rfl rfl rfl
private theorem moment_1326_281_join10 :
    blockEstimate 1326 281 1049 839 = 40021583721 :=
  block_append moment_1326_281_join6 moment_1326_281_join9 rfl rfl rfl
private theorem moment_1326_281_join11 :
    blockEstimate 1326 281 281 1607 = 83828003187 :=
  block_append moment_1326_281_join4 moment_1326_281_join10 rfl rfl rfl

theorem moment_1326_281 : momentEstimate 1326 281 = 83828003187 := moment_1326_281_join11

private theorem moment_1327_281_part0 :
    blockEstimate 1327 281 281 128 = 440670880 := by decide +kernel
private theorem moment_1327_281_part1 :
    blockEstimate 1327 281 409 128 = 2772429472 := by decide +kernel
private theorem moment_1327_281_part2 :
    blockEstimate 1327 281 537 128 = 6499499186 := by decide +kernel
private theorem moment_1327_281_part3 :
    blockEstimate 1327 281 665 128 = 9728620992 := by decide +kernel
private theorem moment_1327_281_part4 :
    blockEstimate 1327 281 793 128 = 11777718720 := by decide +kernel
private theorem moment_1327_281_part5 :
    blockEstimate 1327 281 921 128 = 12644022720 := by decide +kernel
private theorem moment_1327_281_part6 :
    blockEstimate 1327 281 1049 128 = 12327532992 := by decide +kernel
private theorem moment_1327_281_part7 :
    blockEstimate 1327 281 1177 128 = 10828249536 := by decide +kernel
private theorem moment_1327_281_part8 :
    blockEstimate 1327 281 1305 128 = 8234870103 := by decide +kernel
private theorem moment_1327_281_part9 :
    blockEstimate 1327 281 1433 128 = 5281874916 := by decide +kernel
private theorem moment_1327_281_part10 :
    blockEstimate 1327 281 1561 128 = 2654626290 := by decide +kernel
private theorem moment_1327_281_part11 :
    blockEstimate 1327 281 1689 128 = 798423904 := by decide +kernel
private theorem moment_1327_281_part12 :
    blockEstimate 1327 281 1817 72 = 42800046 := by decide +kernel
private theorem moment_1327_281_join0 :
    blockEstimate 1327 281 409 256 = 9271928658 :=
  block_append moment_1327_281_part1 moment_1327_281_part2 rfl rfl rfl
private theorem moment_1327_281_join1 :
    blockEstimate 1327 281 281 384 = 9712599538 :=
  block_append moment_1327_281_part0 moment_1327_281_join0 rfl rfl rfl
private theorem moment_1327_281_join2 :
    blockEstimate 1327 281 793 256 = 24421741440 :=
  block_append moment_1327_281_part4 moment_1327_281_part5 rfl rfl rfl
private theorem moment_1327_281_join3 :
    blockEstimate 1327 281 665 384 = 34150362432 :=
  block_append moment_1327_281_part3 moment_1327_281_join2 rfl rfl rfl
private theorem moment_1327_281_join4 :
    blockEstimate 1327 281 281 768 = 43862961970 :=
  block_append moment_1327_281_join1 moment_1327_281_join3 rfl rfl rfl
private theorem moment_1327_281_join5 :
    blockEstimate 1327 281 1177 256 = 19063119639 :=
  block_append moment_1327_281_part7 moment_1327_281_part8 rfl rfl rfl
private theorem moment_1327_281_join6 :
    blockEstimate 1327 281 1049 384 = 31390652631 :=
  block_append moment_1327_281_part6 moment_1327_281_join5 rfl rfl rfl
private theorem moment_1327_281_join7 :
    blockEstimate 1327 281 1433 256 = 7936501206 :=
  block_append moment_1327_281_part9 moment_1327_281_part10 rfl rfl rfl
private theorem moment_1327_281_join8 :
    blockEstimate 1327 281 1689 200 = 841223950 :=
  block_append moment_1327_281_part11 moment_1327_281_part12 rfl rfl rfl
private theorem moment_1327_281_join9 :
    blockEstimate 1327 281 1433 456 = 8777725156 :=
  block_append moment_1327_281_join7 moment_1327_281_join8 rfl rfl rfl
private theorem moment_1327_281_join10 :
    blockEstimate 1327 281 1049 840 = 40168377787 :=
  block_append moment_1327_281_join6 moment_1327_281_join9 rfl rfl rfl
private theorem moment_1327_281_join11 :
    blockEstimate 1327 281 281 1608 = 84031339757 :=
  block_append moment_1327_281_join4 moment_1327_281_join10 rfl rfl rfl

theorem moment_1327_281 : momentEstimate 1327 281 = 84031339757 := moment_1327_281_join11

private theorem moment_1341_282_part0 :
    blockEstimate 1341 282 282 128 = 445679520 := by decide +kernel
private theorem moment_1341_282_part1 :
    blockEstimate 1341 282 410 128 = 2807027616 := by decide +kernel
private theorem moment_1341_282_part2 :
    blockEstimate 1341 282 538 128 = 6595706731 := by decide +kernel
private theorem moment_1341_282_part3 :
    blockEstimate 1341 282 666 128 = 9903134464 := by decide +kernel
private theorem moment_1341_282_part4 :
    blockEstimate 1341 282 794 128 = 12026730240 := by decide +kernel
private theorem moment_1341_282_part5 :
    blockEstimate 1341 282 922 128 = 12963337984 := by decide +kernel
private theorem moment_1341_282_part6 :
    blockEstimate 1341 282 1050 128 = 12712957696 := by decide +kernel
private theorem moment_1341_282_part7 :
    blockEstimate 1341 282 1178 128 = 11275589376 := by decide +kernel
private theorem moment_1341_282_part8 :
    blockEstimate 1341 282 1306 128 = 8711118963 := by decide +kernel
private theorem moment_1341_282_part9 :
    blockEstimate 1341 282 1434 128 = 5697061300 := by decide +kernel
private theorem moment_1341_282_part10 :
    blockEstimate 1341 282 1562 128 = 2967083923 := by decide +kernel
private theorem moment_1341_282_part11 :
    blockEstimate 1341 282 1690 128 = 974195776 := by decide +kernel
private theorem moment_1341_282_part12 :
    blockEstimate 1341 282 1818 87 = 75125996 := by decide +kernel
private theorem moment_1341_282_join0 :
    blockEstimate 1341 282 410 256 = 9402734347 :=
  block_append moment_1341_282_part1 moment_1341_282_part2 rfl rfl rfl
private theorem moment_1341_282_join1 :
    blockEstimate 1341 282 282 384 = 9848413867 :=
  block_append moment_1341_282_part0 moment_1341_282_join0 rfl rfl rfl
private theorem moment_1341_282_join2 :
    blockEstimate 1341 282 794 256 = 24990068224 :=
  block_append moment_1341_282_part4 moment_1341_282_part5 rfl rfl rfl
private theorem moment_1341_282_join3 :
    blockEstimate 1341 282 666 384 = 34893202688 :=
  block_append moment_1341_282_part3 moment_1341_282_join2 rfl rfl rfl
private theorem moment_1341_282_join4 :
    blockEstimate 1341 282 282 768 = 44741616555 :=
  block_append moment_1341_282_join1 moment_1341_282_join3 rfl rfl rfl
private theorem moment_1341_282_join5 :
    blockEstimate 1341 282 1178 256 = 19986708339 :=
  block_append moment_1341_282_part7 moment_1341_282_part8 rfl rfl rfl
private theorem moment_1341_282_join6 :
    blockEstimate 1341 282 1050 384 = 32699666035 :=
  block_append moment_1341_282_part6 moment_1341_282_join5 rfl rfl rfl
private theorem moment_1341_282_join7 :
    blockEstimate 1341 282 1434 256 = 8664145223 :=
  block_append moment_1341_282_part9 moment_1341_282_part10 rfl rfl rfl
private theorem moment_1341_282_join8 :
    blockEstimate 1341 282 1690 215 = 1049321772 :=
  block_append moment_1341_282_part11 moment_1341_282_part12 rfl rfl rfl
private theorem moment_1341_282_join9 :
    blockEstimate 1341 282 1434 471 = 9713466995 :=
  block_append moment_1341_282_join7 moment_1341_282_join8 rfl rfl rfl
private theorem moment_1341_282_join10 :
    blockEstimate 1341 282 1050 855 = 42413133030 :=
  block_append moment_1341_282_join6 moment_1341_282_join9 rfl rfl rfl
private theorem moment_1341_282_join11 :
    blockEstimate 1341 282 282 1623 = 87154749585 :=
  block_append moment_1341_282_join4 moment_1341_282_join10 rfl rfl rfl

theorem moment_1341_282 : momentEstimate 1341 282 = 87154749585 := moment_1341_282_join11

private theorem moment_1387_302_part0 :
    blockEstimate 1387 302 302 128 = 462136480 := by decide +kernel
private theorem moment_1387_302_part1 :
    blockEstimate 1387 302 430 128 = 2920707232 := by decide +kernel
private theorem moment_1387_302_part2 :
    blockEstimate 1387 302 558 128 = 6982836384 := by decide +kernel
private theorem moment_1387_302_part3 :
    blockEstimate 1387 302 686 128 = 10787226624 := by decide +kernel
private theorem moment_1387_302_part4 :
    blockEstimate 1387 302 814 128 = 13338903552 := by decide +kernel
private theorem moment_1387_302_part5 :
    blockEstimate 1387 302 942 128 = 14619706368 := by decide +kernel
private theorem moment_1387_302_part6 :
    blockEstimate 1387 302 1070 128 = 14629635072 := by decide +kernel
private theorem moment_1387_302_part7 :
    blockEstimate 1387 302 1198 128 = 13368689664 := by decide +kernel
private theorem moment_1387_302_part8 :
    blockEstimate 1387 302 1326 128 = 10858832125 := by decide +kernel
private theorem moment_1387_302_part9 :
    blockEstimate 1387 302 1454 128 = 7630480965 := by decide +kernel
private theorem moment_1387_302_part10 :
    blockEstimate 1387 302 1582 128 = 4503008202 := by decide +kernel
private theorem moment_1387_302_part11 :
    blockEstimate 1387 302 1710 128 = 1955193296 := by decide +kernel
private theorem moment_1387_302_part12 :
    blockEstimate 1387 302 1838 128 = 402271696 := by decide +kernel
private theorem moment_1387_302_part13 :
    blockEstimate 1387 302 1966 25 = 2128560 := by decide +kernel
private theorem moment_1387_302_join0 :
    blockEstimate 1387 302 430 256 = 9903543616 :=
  block_append moment_1387_302_part1 moment_1387_302_part2 rfl rfl rfl
private theorem moment_1387_302_join1 :
    blockEstimate 1387 302 302 384 = 10365680096 :=
  block_append moment_1387_302_part0 moment_1387_302_join0 rfl rfl rfl
private theorem moment_1387_302_join2 :
    blockEstimate 1387 302 686 256 = 24126130176 :=
  block_append moment_1387_302_part3 moment_1387_302_part4 rfl rfl rfl
private theorem moment_1387_302_join3 :
    blockEstimate 1387 302 942 256 = 29249341440 :=
  block_append moment_1387_302_part5 moment_1387_302_part6 rfl rfl rfl
private theorem moment_1387_302_join4 :
    blockEstimate 1387 302 686 512 = 53375471616 :=
  block_append moment_1387_302_join2 moment_1387_302_join3 rfl rfl rfl
private theorem moment_1387_302_join5 :
    blockEstimate 1387 302 302 896 = 63741151712 :=
  block_append moment_1387_302_join1 moment_1387_302_join4 rfl rfl rfl
private theorem moment_1387_302_join6 :
    blockEstimate 1387 302 1326 256 = 18489313090 :=
  block_append moment_1387_302_part8 moment_1387_302_part9 rfl rfl rfl
private theorem moment_1387_302_join7 :
    blockEstimate 1387 302 1198 384 = 31858002754 :=
  block_append moment_1387_302_part7 moment_1387_302_join6 rfl rfl rfl
private theorem moment_1387_302_join8 :
    blockEstimate 1387 302 1582 256 = 6458201498 :=
  block_append moment_1387_302_part10 moment_1387_302_part11 rfl rfl rfl
private theorem moment_1387_302_join9 :
    blockEstimate 1387 302 1838 153 = 404400256 :=
  block_append moment_1387_302_part12 moment_1387_302_part13 rfl rfl rfl
private theorem moment_1387_302_join10 :
    blockEstimate 1387 302 1582 409 = 6862601754 :=
  block_append moment_1387_302_join8 moment_1387_302_join9 rfl rfl rfl
private theorem moment_1387_302_join11 :
    blockEstimate 1387 302 1198 793 = 38720604508 :=
  block_append moment_1387_302_join7 moment_1387_302_join10 rfl rfl rfl
private theorem moment_1387_302_join12 :
    blockEstimate 1387 302 302 1689 = 102461756220 :=
  block_append moment_1387_302_join5 moment_1387_302_join11 rfl rfl rfl

theorem moment_1387_302 : momentEstimate 1387 302 = 102461756220 := moment_1387_302_join12

private theorem moment_1392_291_part0 :
    blockEstimate 1392 291 291 128 = 463925280 := by decide +kernel
private theorem moment_1392_291_part1 :
    blockEstimate 1392 291 419 128 = 2933063712 := by decide +kernel
private theorem moment_1392_291_part2 :
    blockEstimate 1392 291 547 128 = 6972032551 := by decide +kernel
private theorem moment_1392_291_part3 :
    blockEstimate 1392 291 675 128 = 10645366912 := by decide +kernel
private theorem moment_1392_291_part4 :
    blockEstimate 1392 291 803 128 = 13102016640 := by decide +kernel
private theorem moment_1392_291_part5 :
    blockEstimate 1392 291 931 128 = 14333929600 := by decide +kernel
private theorem moment_1392_291_part6 :
    blockEstimate 1392 291 1059 128 = 14341105792 := by decide +kernel
private theorem moment_1392_291_part7 :
    blockEstimate 1392 291 1187 128 = 13123545216 := by decide +kernel
private theorem moment_1392_291_part8 :
    blockEstimate 1392 291 1315 128 = 10691106230 := by decide +kernel
private theorem moment_1392_291_part9 :
    blockEstimate 1392 291 1443 128 = 7487810802 := by decide +kernel
private theorem moment_1392_291_part10 :
    blockEstimate 1392 291 1571 128 = 4379387141 := by decide +kernel
private theorem moment_1392_291_part11 :
    blockEstimate 1392 291 1699 128 = 1864956928 := by decide +kernel
private theorem moment_1392_291_part12 :
    blockEstimate 1392 291 1827 128 = 360231936 := by decide +kernel
private theorem moment_1392_291_part13 :
    blockEstimate 1392 291 1955 19 = 989370 := by decide +kernel
private theorem moment_1392_291_join0 :
    blockEstimate 1392 291 419 256 = 9905096263 :=
  block_append moment_1392_291_part1 moment_1392_291_part2 rfl rfl rfl
private theorem moment_1392_291_join1 :
    blockEstimate 1392 291 291 384 = 10369021543 :=
  block_append moment_1392_291_part0 moment_1392_291_join0 rfl rfl rfl
private theorem moment_1392_291_join2 :
    blockEstimate 1392 291 675 256 = 23747383552 :=
  block_append moment_1392_291_part3 moment_1392_291_part4 rfl rfl rfl
private theorem moment_1392_291_join3 :
    blockEstimate 1392 291 931 256 = 28675035392 :=
  block_append moment_1392_291_part5 moment_1392_291_part6 rfl rfl rfl
private theorem moment_1392_291_join4 :
    blockEstimate 1392 291 675 512 = 52422418944 :=
  block_append moment_1392_291_join2 moment_1392_291_join3 rfl rfl rfl
private theorem moment_1392_291_join5 :
    blockEstimate 1392 291 291 896 = 62791440487 :=
  block_append moment_1392_291_join1 moment_1392_291_join4 rfl rfl rfl
private theorem moment_1392_291_join6 :
    blockEstimate 1392 291 1315 256 = 18178917032 :=
  block_append moment_1392_291_part8 moment_1392_291_part9 rfl rfl rfl
private theorem moment_1392_291_join7 :
    blockEstimate 1392 291 1187 384 = 31302462248 :=
  block_append moment_1392_291_part7 moment_1392_291_join6 rfl rfl rfl
private theorem moment_1392_291_join8 :
    blockEstimate 1392 291 1571 256 = 6244344069 :=
  block_append moment_1392_291_part10 moment_1392_291_part11 rfl rfl rfl
private theorem moment_1392_291_join9 :
    blockEstimate 1392 291 1827 147 = 361221306 :=
  block_append moment_1392_291_part12 moment_1392_291_part13 rfl rfl rfl
private theorem moment_1392_291_join10 :
    blockEstimate 1392 291 1571 403 = 6605565375 :=
  block_append moment_1392_291_join8 moment_1392_291_join9 rfl rfl rfl
private theorem moment_1392_291_join11 :
    blockEstimate 1392 291 1187 787 = 37908027623 :=
  block_append moment_1392_291_join7 moment_1392_291_join10 rfl rfl rfl
private theorem moment_1392_291_join12 :
    blockEstimate 1392 291 291 1683 = 100699468110 :=
  block_append moment_1392_291_join5 moment_1392_291_join11 rfl rfl rfl

theorem moment_1392_291 : momentEstimate 1392 291 = 100699468110 := moment_1392_291_join12

private theorem receipt_0_1_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 0) 0 128 = 6941878633893392629836037 := by decide +kernel
private theorem receipt_0_1_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 0) 128 128 = 2551588781823814687211609 := by decide +kernel
private theorem receipt_0_1_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 0) 256 26 = 70529709740769286790004 := by decide +kernel
private theorem receipt_0_1_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 0) 128 154 = 2622118491564583974001613 :=
  phaseBlock_append receipt_0_1_2402_0_part1 receipt_0_1_2402_0_part2 rfl rfl rfl
private theorem receipt_0_1_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 0) 0 282 = 9563997125457976603837650 :=
  phaseBlock_append receipt_0_1_2402_0_part0 receipt_0_1_2402_0_join0 rfl rfl rfl

private theorem receipt_0_1_2402_0 : fastPhase (bank 0 1).shape 179798 2402 1 1 0 1 0 = 9563997125457976603837650 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2402_0_join1

private theorem receipt_0_1_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 1) 0 128 = 6903975578089992810796899 := by decide +kernel
private theorem receipt_0_1_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 1) 128 128 = 2521415377664691119225172 := by decide +kernel
private theorem receipt_0_1_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 1) 256 26 = 65263869225972675180000 := by decide +kernel
private theorem receipt_0_1_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 1) 128 154 = 2586679246890663794405172 :=
  phaseBlock_append receipt_0_1_2402_1_part1 receipt_0_1_2402_1_part2 rfl rfl rfl
private theorem receipt_0_1_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2402 1 1 0 1 1) 0 282 = 9490654824980656605202071 :=
  phaseBlock_append receipt_0_1_2402_1_part0 receipt_0_1_2402_1_join0 rfl rfl rfl

private theorem receipt_0_1_2402_1 : fastPhase (bank 0 1).shape 179798 2402 1 1 0 1 1 = 9490654824980656605202071 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2402_1_join1

private theorem receipt_0_1_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 0) 0 128 = 6941937175473557905211018 := by decide +kernel
private theorem receipt_0_1_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 0) 128 128 = 2551604020256952130633468 := by decide +kernel
private theorem receipt_0_1_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 0) 256 26 = 70529986744627815236496 := by decide +kernel
private theorem receipt_0_1_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 0) 128 154 = 2622134007001579945869964 :=
  phaseBlock_append receipt_0_1_2403_0_part1 receipt_0_1_2403_0_part2 rfl rfl rfl
private theorem receipt_0_1_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 0) 0 282 = 9564071182475137851080982 :=
  phaseBlock_append receipt_0_1_2403_0_part0 receipt_0_1_2403_0_join0 rfl rfl rfl

private theorem receipt_0_1_2403_0 : fastPhase (bank 0 1).shape 179798 2403 1 1 0 1 0 = 9564071182475137851080982 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2403_0_join1

private theorem receipt_0_1_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 1) 0 128 = 6904033855060479049784715 := by decide +kernel
private theorem receipt_0_1_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 1) 128 128 = 2521430461468719807662088 := by decide +kernel
private theorem receipt_0_1_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 1) 256 26 = 65264126434006483996740 := by decide +kernel
private theorem receipt_0_1_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 1) 128 154 = 2586694587902726291658828 :=
  phaseBlock_append receipt_0_1_2403_1_part1 receipt_0_1_2403_1_part2 rfl rfl rfl
private theorem receipt_0_1_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179798 2403 1 1 0 1 1) 0 282 = 9490728442963205341443543 :=
  phaseBlock_append receipt_0_1_2403_1_part0 receipt_0_1_2403_1_join0 rfl rfl rfl

private theorem receipt_0_1_2403_1 : fastPhase (bank 0 1).shape 179798 2403 1 1 0 1 1 = 9490728442963205341443543 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2403_1_join1

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2402_0 receipt_0_1_2402_1 receipt_0_1_2403_0 receipt_0_1_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 0) 0 128 = 6230203781426665533139441 := by decide +kernel
private theorem receipt_1_1_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 0) 128 128 = 2281988093606741271743052 := by decide +kernel
private theorem receipt_1_1_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 0) 256 26 = 62912026689287814310977 := by decide +kernel
private theorem receipt_1_1_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 0) 128 154 = 2344900120296029086054029 :=
  phaseBlock_append receipt_1_1_2402_0_part1 receipt_1_1_2402_0_part2 rfl rfl rfl
private theorem receipt_1_1_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 0) 0 282 = 8575103901722694619193470 :=
  phaseBlock_append receipt_1_1_2402_0_part0 receipt_1_1_2402_0_join0 rfl rfl rfl

private theorem receipt_1_1_2402_0 : fastPhase (bank 1 1).shape 179798 2402 1 1 0 2 0 = 8575103901722694619193470 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2402_0_join1

private theorem receipt_1_1_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 1) 0 128 = 6196010099993661906817974 := by decide +kernel
private theorem receipt_1_1_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 1) 128 128 = 2254947250670125846979418 := by decide +kernel
private theorem receipt_1_1_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 1) 256 26 = 58213779676717030737930 := by decide +kernel
private theorem receipt_1_1_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 1) 128 154 = 2313161030346842877717348 :=
  phaseBlock_append receipt_1_1_2402_1_part1 receipt_1_1_2402_1_part2 rfl rfl rfl
private theorem receipt_1_1_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2402 1 1 0 2 1) 0 282 = 8509171130340504784535322 :=
  phaseBlock_append receipt_1_1_2402_1_part0 receipt_1_1_2402_1_join0 rfl rfl rfl

private theorem receipt_1_1_2402_1 : fastPhase (bank 1 1).shape 179798 2402 1 1 0 2 1 = 8509171130340504784535322 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2402_1_join1

private theorem receipt_1_1_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 0) 0 128 = 6230256326052490022628269 := by decide +kernel
private theorem receipt_1_1_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 0) 128 128 = 2282001723617914794426813 := by decide +kernel
private theorem receipt_1_1_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 0) 256 26 = 62912273776588068731073 := by decide +kernel
private theorem receipt_1_1_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 0) 128 154 = 2344913997394502863157886 :=
  phaseBlock_append receipt_1_1_2403_0_part1 receipt_1_1_2403_0_part2 rfl rfl rfl
private theorem receipt_1_1_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 0) 0 282 = 8575170323446992885786155 :=
  phaseBlock_append receipt_1_1_2403_0_part0 receipt_1_1_2403_0_join0 rfl rfl rfl

private theorem receipt_1_1_2403_0 : fastPhase (bank 1 1).shape 179798 2403 1 1 0 2 0 = 8575170323446992885786155 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2403_0_join1

private theorem receipt_1_1_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 1) 0 128 = 6196062405622950891255741 := by decide +kernel
private theorem receipt_1_1_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 1) 128 128 = 2254960742031056762072292 := by decide +kernel
private theorem receipt_1_1_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 1) 256 26 = 58214009101484425024290 := by decide +kernel
private theorem receipt_1_1_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 1) 128 154 = 2313174751132541187096582 :=
  phaseBlock_append receipt_1_1_2403_1_part1 receipt_1_1_2403_1_part2 rfl rfl rfl
private theorem receipt_1_1_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179798 2403 1 1 0 2 1) 0 282 = 8509237156755492078352323 :=
  phaseBlock_append receipt_1_1_2403_1_part0 receipt_1_1_2403_1_join0 rfl rfl rfl

private theorem receipt_1_1_2403_1 : fastPhase (bank 1 1).shape 179798 2403 1 1 0 2 1 = 8509237156755492078352323 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2403_1_join1

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2402_0 receipt_1_1_2402_1 receipt_1_1_2403_0 receipt_1_1_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 0) 0 128 = 3272293812363101743653421 := by decide +kernel
private theorem receipt_2_1_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 0) 128 128 = 1168163576996661583914177 := by decide +kernel
private theorem receipt_2_1_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 0) 256 26 = 31582486004512676420052 := by decide +kernel
private theorem receipt_2_1_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 0) 128 154 = 1199746063001174260334229 :=
  phaseBlock_append receipt_2_1_2402_0_part1 receipt_2_1_2402_0_part2 rfl rfl rfl
private theorem receipt_2_1_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 0) 0 282 = 4472039875364276003987650 :=
  phaseBlock_append receipt_2_1_2402_0_part0 receipt_2_1_2402_0_join0 rfl rfl rfl

private theorem receipt_2_1_2402_0 : fastPhase (bank 2 1).shape 179798 2402 1 1 0 7 0 = 4472039875364276003987650 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2402_0_join1

private theorem receipt_2_1_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 1) 0 128 = 3253660129027369914983039 := by decide +kernel
private theorem receipt_2_1_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 1) 128 128 = 1154111167070550021203448 := by decide +kernel
private theorem receipt_2_1_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 1) 256 26 = 29219596864556518247880 := by decide +kernel
private theorem receipt_2_1_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 1) 128 154 = 1183330763935106539451328 :=
  phaseBlock_append receipt_2_1_2402_1_part1 receipt_2_1_2402_1_part2 rfl rfl rfl
private theorem receipt_2_1_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2402 1 1 0 7 1) 0 282 = 4436990892962476454434367 :=
  phaseBlock_append receipt_2_1_2402_1_part0 receipt_2_1_2402_1_join0 rfl rfl rfl

private theorem receipt_2_1_2402_1 : fastPhase (bank 2 1).shape 179798 2402 1 1 0 7 1 = 4436990892962476454434367 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2402_1_join1

private theorem receipt_2_1_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 0) 0 128 = 3272321428257864039585394 := by decide +kernel
private theorem receipt_2_1_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 0) 128 128 = 1168170560585985578628948 := by decide +kernel
private theorem receipt_2_1_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 0) 256 26 = 31582610051335214186448 := by decide +kernel
private theorem receipt_2_1_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 0) 128 154 = 1199753170637320792815396 :=
  phaseBlock_append receipt_2_1_2403_0_part1 receipt_2_1_2403_0_part2 rfl rfl rfl
private theorem receipt_2_1_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 0) 0 282 = 4472074598895184832400790 :=
  phaseBlock_append receipt_2_1_2403_0_part0 receipt_2_1_2403_0_join0 rfl rfl rfl

private theorem receipt_2_1_2403_0 : fastPhase (bank 2 1).shape 179798 2403 1 1 0 7 0 = 4472074598895184832400790 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2403_0_join1

private theorem receipt_2_1_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 1) 0 128 = 3253687613604858835895431 := by decide +kernel
private theorem receipt_2_1_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 1) 128 128 = 1154118078325354933793492 := by decide +kernel
private theorem receipt_2_1_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 1) 256 26 = 29219712026649491478040 := by decide +kernel
private theorem receipt_2_1_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 1) 128 154 = 1183337790352004425271532 :=
  phaseBlock_append receipt_2_1_2403_1_part1 receipt_2_1_2403_1_part2 rfl rfl rfl
private theorem receipt_2_1_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179798 2403 1 1 0 7 1) 0 282 = 4437025403956863261166963 :=
  phaseBlock_append receipt_2_1_2403_1_part0 receipt_2_1_2403_1_join0 rfl rfl rfl

private theorem receipt_2_1_2403_1 : fastPhase (bank 2 1).shape 179798 2403 1 1 0 7 1 = 4437025403956863261166963 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2403_1_join1

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2402_0 receipt_2_1_2402_1 receipt_2_1_2403_0 receipt_2_1_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2402 1 1 1 1 0) 0 128 = 303128186021976240801984 := by decide +kernel
private theorem receipt_3_1_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2402 1 1 1 1 0) 128 80 = 44656901655808480341624 := by decide +kernel
private theorem receipt_3_1_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2402 1 1 1 1 0) 0 208 = 347785087677784721143608 :=
  phaseBlock_append receipt_3_1_2402_0_part0 receipt_3_1_2402_0_part1 rfl rfl rfl

private theorem receipt_3_1_2402_0 : fastPhase (bank 3 1).shape 179798 2402 1 1 1 1 0 = 347785087677784721143608 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2402_0_join0

private theorem receipt_3_1_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2402 1 1 1 1 1) 0 128 = 300626502698691203647104 := by decide +kernel
private theorem receipt_3_1_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2402 1 1 1 1 1) 128 80 = 43500773926662652078416 := by decide +kernel
private theorem receipt_3_1_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2402 1 1 1 1 1) 0 208 = 344127276625353855725520 :=
  phaseBlock_append receipt_3_1_2402_1_part0 receipt_3_1_2402_1_part1 rfl rfl rfl

private theorem receipt_3_1_2402_1 : fastPhase (bank 3 1).shape 179798 2402 1 1 1 1 1 = 344127276625353855725520 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2402_1_join0

private theorem receipt_3_1_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2403 1 1 1 1 0) 0 128 = 303130389136016046063936 := by decide +kernel
private theorem receipt_3_1_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2403 1 1 1 1 0) 128 80 = 44657043764505868468296 := by decide +kernel
private theorem receipt_3_1_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2403 1 1 1 1 0) 0 208 = 347787432900521914532232 :=
  phaseBlock_append receipt_3_1_2403_0_part0 receipt_3_1_2403_0_part1 rfl rfl rfl

private theorem receipt_3_1_2403_0 : fastPhase (bank 3 1).shape 179798 2403 1 1 1 1 0 = 347787432900521914532232 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2403_0_join0

private theorem receipt_3_1_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2403 1 1 1 1 1) 0 128 = 300628686109027965674304 := by decide +kernel
private theorem receipt_3_1_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2403 1 1 1 1 1) 128 80 = 43500912633813824978184 := by decide +kernel
private theorem receipt_3_1_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179798 2403 1 1 1 1 1) 0 208 = 344129598742841790652488 :=
  phaseBlock_append receipt_3_1_2403_1_part0 receipt_3_1_2403_1_part1 rfl rfl rfl

private theorem receipt_3_1_2403_1 : fastPhase (bank 3 1).shape 179798 2403 1 1 1 1 1 = 344129598742841790652488 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2403_1_join0

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2402_0 receipt_3_1_2402_1 receipt_3_1_2403_0 receipt_3_1_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 0) 0 128 = 9834305600009392000836480 := by decide +kernel
private theorem receipt_0_2_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 0) 128 128 = 3646887273665794972515996 := by decide +kernel
private theorem receipt_0_2_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 0) 256 27 = 107571428323557715705792 := by decide +kernel
private theorem receipt_0_2_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 0) 128 155 = 3754458701989352688221788 :=
  phaseBlock_append receipt_0_2_2402_0_part1 receipt_0_2_2402_0_part2 rfl rfl rfl
private theorem receipt_0_2_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 0) 0 283 = 13588764301998744689058268 :=
  phaseBlock_append receipt_0_2_2402_0_part0 receipt_0_2_2402_0_join0 rfl rfl rfl

private theorem receipt_0_2_2402_0 : fastPhase (bank 0 2).shape 179798 2402 2 1 0 1 0 = 13588764301998744689058268 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2402_0_join1

private theorem receipt_0_2_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 1) 0 128 = 9780996683978580582575424 := by decide +kernel
private theorem receipt_0_2_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 1) 128 128 = 3604250651835039575482209 := by decide +kernel
private theorem receipt_0_2_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 1) 256 27 = 99825822896630329700438 := by decide +kernel
private theorem receipt_0_2_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 1) 128 155 = 3704076474731669905182647 :=
  phaseBlock_append receipt_0_2_2402_1_part1 receipt_0_2_2402_1_part2 rfl rfl rfl
private theorem receipt_0_2_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2402 2 1 0 1 1) 0 283 = 13485073158710250487758071 :=
  phaseBlock_append receipt_0_2_2402_1_part0 receipt_0_2_2402_1_join0 rfl rfl rfl

private theorem receipt_0_2_2402_1 : fastPhase (bank 0 2).shape 179798 2402 2 1 0 1 1 = 13485073158710250487758071 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2402_1_join1

private theorem receipt_0_2_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 0) 0 128 = 9834387571820821779423360 := by decide +kernel
private theorem receipt_0_2_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 0) 128 128 = 3646909049353321127918840 := by decide +kernel
private theorem receipt_0_2_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 0) 256 27 = 107571855604716829444286 := by decide +kernel
private theorem receipt_0_2_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 0) 128 155 = 3754480904958037957363126 :=
  phaseBlock_append receipt_0_2_2403_0_part1 receipt_0_2_2403_0_part2 rfl rfl rfl
private theorem receipt_0_2_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 0) 0 283 = 13588868476778859736786486 :=
  phaseBlock_append receipt_0_2_2403_0_part0 receipt_0_2_2403_0_join0 rfl rfl rfl

private theorem receipt_0_2_2403_0 : fastPhase (bank 0 2).shape 179798 2403 2 1 0 1 0 = 13588868476778859736786486 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2403_0_join1

private theorem receipt_0_2_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 1) 0 128 = 9781078287108955129758656 := by decide +kernel
private theorem receipt_0_2_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 1) 128 128 = 3604272208404080102147952 := by decide +kernel
private theorem receipt_0_2_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 1) 256 27 = 99826220748932530880168 := by decide +kernel
private theorem receipt_0_2_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 1) 128 155 = 3704098429153012633028120 :=
  phaseBlock_append receipt_0_2_2403_1_part1 receipt_0_2_2403_1_part2 rfl rfl rfl
private theorem receipt_0_2_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179798 2403 2 1 0 1 1) 0 283 = 13485176716261967762786776 :=
  phaseBlock_append receipt_0_2_2403_1_part0 receipt_0_2_2403_1_join0 rfl rfl rfl

private theorem receipt_0_2_2403_1 : fastPhase (bank 0 2).shape 179798 2403 2 1 0 1 1 = 13485176716261967762786776 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2403_1_join1

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2402_0 receipt_0_2_2402_1 receipt_0_2_2403_0 receipt_0_2_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 0) 0 128 = 8837780768691070179309984 := by decide +kernel
private theorem receipt_1_2_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 0) 128 128 = 3267517161465724757520591 := by decide +kernel
private theorem receipt_1_2_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 0) 256 27 = 96164595645241951693975 := by decide +kernel
private theorem receipt_1_2_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 0) 128 155 = 3363681757110966709214566 :=
  phaseBlock_append receipt_1_2_2402_0_part1 receipt_1_2_2402_0_part2 rfl rfl rfl
private theorem receipt_1_2_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 0) 0 283 = 12201462525802036888524550 :=
  phaseBlock_append receipt_1_2_2402_0_part0 receipt_1_2_2402_0_join0 rfl rfl rfl

private theorem receipt_1_2_2402_0 : fastPhase (bank 1 2).shape 179798 2402 2 1 0 2 0 = 12201462525802036888524550 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2402_0_join1

private theorem receipt_1_2_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 1) 0 128 = 8789659491737410930674144 := by decide +kernel
private theorem receipt_1_2_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 1) 128 128 = 3229247522646784323386481 := by decide +kernel
private theorem receipt_1_2_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 1) 256 27 = 89238820710312554594567 := by decide +kernel
private theorem receipt_1_2_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 1) 128 155 = 3318486343357096877981048 :=
  phaseBlock_append receipt_1_2_2402_1_part1 receipt_1_2_2402_1_part2 rfl rfl rfl
private theorem receipt_1_2_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2402 2 1 0 2 1) 0 283 = 12108145835094507808655192 :=
  phaseBlock_append receipt_1_2_2402_1_part0 receipt_1_2_2402_1_join0 rfl rfl rfl

private theorem receipt_1_2_2402_1 : fastPhase (bank 1 2).shape 179798 2402 2 1 0 2 1 = 12108145835094507808655192 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2402_1_join1

private theorem receipt_1_2_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 0) 0 128 = 8837854439596041525804384 := by decide +kernel
private theorem receipt_1_2_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 0) 128 128 = 3267536673914269927036730 := by decide +kernel
private theorem receipt_1_2_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 0) 256 27 = 96164977620055857702185 := by decide +kernel
private theorem receipt_1_2_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 0) 128 155 = 3363701651534325784738915 :=
  phaseBlock_append receipt_1_2_2403_0_part1 receipt_1_2_2403_0_part2 rfl rfl rfl
private theorem receipt_1_2_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 0) 0 283 = 12201556091130367310543299 :=
  phaseBlock_append receipt_1_2_2403_0_part0 receipt_1_2_2403_0_join0 rfl rfl rfl

private theorem receipt_1_2_2403_0 : fastPhase (bank 1 2).shape 179798 2403 2 1 0 2 0 = 12201556091130367310543299 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2403_0_join1

private theorem receipt_1_2_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 1) 0 128 = 8789732829503766462458336 := by decide +kernel
private theorem receipt_1_2_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 1) 128 128 = 3229266838330611000722268 := by decide +kernel
private theorem receipt_1_2_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 1) 256 27 = 89239176370541464945931 := by decide +kernel
private theorem receipt_1_2_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 1) 128 155 = 3318506014701152465668199 :=
  phaseBlock_append receipt_1_2_2403_1_part1 receipt_1_2_2403_1_part2 rfl rfl rfl
private theorem receipt_1_2_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179798 2403 2 1 0 2 1) 0 283 = 12108238844204918928126535 :=
  phaseBlock_append receipt_1_2_2403_1_part0 receipt_1_2_2403_1_join0 rfl rfl rfl

private theorem receipt_1_2_2403_1 : fastPhase (bank 1 2).shape 179798 2403 2 1 0 2 1 = 12108238844204918928126535 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2403_1_join1

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2402_0 receipt_1_2_2402_1 receipt_1_2_2403_0 receipt_1_2_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 0) 0 128 = 4680656377597572586189920 := by decide +kernel
private theorem receipt_2_2_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 0) 128 128 = 1693083508743016930998906 := by decide +kernel
private theorem receipt_2_2_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 0) 256 27 = 49008497741906558586997 := by decide +kernel
private theorem receipt_2_2_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 0) 128 155 = 1742092006484923489585903 :=
  phaseBlock_append receipt_2_2_2402_0_part1 receipt_2_2_2402_0_part2 rfl rfl rfl
private theorem receipt_2_2_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 0) 0 283 = 6422748384082496075775823 :=
  phaseBlock_append receipt_2_2_2402_0_part0 receipt_2_2_2402_0_join0 rfl rfl rfl

private theorem receipt_2_2_2402_0 : fastPhase (bank 2 2).shape 179798 2402 2 1 0 7 0 = 6422748384082496075775823 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2402_0_join1

private theorem receipt_2_2_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 1) 0 128 = 4654348781116837416423264 := by decide +kernel
private theorem receipt_2_2_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 1) 128 128 = 1672994210802290329339470 := by decide +kernel
private theorem receipt_2_2_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 1) 256 27 = 45473206066995446857229 := by decide +kernel
private theorem receipt_2_2_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 1) 128 155 = 1718467416869285776196699 :=
  phaseBlock_append receipt_2_2_2402_1_part1 receipt_2_2_2402_1_part2 rfl rfl rfl
private theorem receipt_2_2_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2402 2 1 0 7 1) 0 283 = 6372816197986123192619963 :=
  phaseBlock_append receipt_2_2_2402_1_part0 receipt_2_2_2402_1_join0 rfl rfl rfl

private theorem receipt_2_2_2402_1 : fastPhase (bank 2 2).shape 179798 2402 2 1 0 7 1 = 6372816197986123192619963 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2402_1_join1

private theorem receipt_2_2_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 0) 0 128 = 4680695415881868617129280 := by decide +kernel
private theorem receipt_2_2_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 0) 128 128 = 1693093626799221811755311 := by decide +kernel
private theorem receipt_2_2_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 0) 256 27 = 49008692417257089796286 := by decide +kernel
private theorem receipt_2_2_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 0) 128 155 = 1742102319216478901551597 :=
  phaseBlock_append receipt_2_2_2403_0_part1 receipt_2_2_2403_0_part2 rfl rfl rfl
private theorem receipt_2_2_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 0) 0 283 = 6422797735098347518680877 :=
  phaseBlock_append receipt_2_2_2403_0_part0 receipt_2_2_2403_0_join0 rfl rfl rfl

private theorem receipt_2_2_2403_0 : fastPhase (bank 2 2).shape 179798 2403 2 1 0 7 0 = 6422797735098347518680877 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2403_0_join1

private theorem receipt_2_2_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 1) 0 128 = 4654387635995415514594496 := by decide +kernel
private theorem receipt_2_2_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 1) 128 128 = 1673004225230200519323030 := by decide +kernel
private theorem receipt_2_2_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 1) 256 27 = 45473387307637937970602 := by decide +kernel
private theorem receipt_2_2_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 1) 128 155 = 1718477612537838457293632 :=
  phaseBlock_append receipt_2_2_2403_1_part1 receipt_2_2_2403_1_part2 rfl rfl rfl
private theorem receipt_2_2_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179798 2403 2 1 0 7 1) 0 283 = 6372865248533253971888128 :=
  phaseBlock_append receipt_2_2_2403_1_part0 receipt_2_2_2403_1_join0 rfl rfl rfl

private theorem receipt_2_2_2403_1 : fastPhase (bank 2 2).shape 179798 2403 2 1 0 7 1 = 6372865248533253971888128 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2403_1_join1

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2402_0 receipt_2_2_2402_1 receipt_2_2_2403_0 receipt_2_2_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2402 2 1 1 1 0) 0 128 = 462787962960945987835392 := by decide +kernel
private theorem receipt_3_2_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2402 2 1 1 1 0) 128 95 = 87523600423745355227520 := by decide +kernel
private theorem receipt_3_2_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2402 2 1 1 1 0) 0 223 = 550311563384691343062912 :=
  phaseBlock_append receipt_3_2_2402_0_part0 receipt_3_2_2402_0_part1 rfl rfl rfl

private theorem receipt_3_2_2402_0 : fastPhase (bank 3 2).shape 179798 2402 2 1 1 1 0 = 550311563384691343062912 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2402_0_join0

private theorem receipt_3_2_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2402 2 1 1 1 1) 0 128 = 459307673112163448953344 := by decide +kernel
private theorem receipt_3_2_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2402 2 1 1 1 1) 128 95 = 85603742945521022168448 := by decide +kernel
private theorem receipt_3_2_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2402 2 1 1 1 1) 0 223 = 544911416057684471121792 :=
  phaseBlock_append receipt_3_2_2402_1_part0 receipt_3_2_2402_1_part1 rfl rfl rfl

private theorem receipt_3_2_2402_1 : fastPhase (bank 3 2).shape 179798 2402 2 1 1 1 1 = 544911416057684471121792 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2402_1_join0

private theorem receipt_3_2_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2403 2 1 1 1 0) 0 128 = 462791362987766735569984 := by decide +kernel
private theorem receipt_3_2_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2403 2 1 1 1 0) 128 95 = 87523896325847456174384 := by decide +kernel
private theorem receipt_3_2_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2403 2 1 1 1 0) 0 223 = 550315259313614191744368 :=
  phaseBlock_append receipt_3_2_2403_0_part0 receipt_3_2_2403_0_part1 rfl rfl rfl

private theorem receipt_3_2_2403_0 : fastPhase (bank 3 2).shape 179798 2403 2 1 1 1 0 = 550315259313614191744368 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2403_0_join0

private theorem receipt_3_2_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2403 2 1 1 1 1) 0 128 = 459311045174294144580736 := by decide +kernel
private theorem receipt_3_2_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2403 2 1 1 1 1) 128 95 = 85604032857507488457776 := by decide +kernel
private theorem receipt_3_2_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179798 2403 2 1 1 1 1) 0 223 = 544915078031801633038512 :=
  phaseBlock_append receipt_3_2_2403_1_part0 receipt_3_2_2403_1_part1 rfl rfl rfl

private theorem receipt_3_2_2403_1 : fastPhase (bank 3 2).shape 179798 2403 2 1 1 1 1 = 544915078031801633038512 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2403_1_join0

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2402_0 receipt_3_2_2402_1 receipt_3_2_2403_0 receipt_3_2_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 0) 0 128 = 14794623185661270883034028 := by decide +kernel
private theorem receipt_0_3_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 0) 128 128 = 5443338995101052082024223 := by decide +kernel
private theorem receipt_0_3_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 0) 256 26 = 150572812626945374794997 := by decide +kernel
private theorem receipt_0_3_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 0) 128 154 = 5593911807727997456819220 :=
  phaseBlock_append receipt_0_3_2402_0_part1 receipt_0_3_2402_0_part2 rfl rfl rfl
private theorem receipt_0_3_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 0) 0 282 = 20388534993389268339853248 :=
  phaseBlock_append receipt_0_3_2402_0_part0 receipt_0_3_2402_0_join0 rfl rfl rfl

private theorem receipt_0_3_2402_0 : fastPhase (bank 0 3).shape 179798 2402 3 1 0 1 0 = 20388534993389268339853248 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2402_0_join1

private theorem receipt_0_3_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 1) 0 128 = 14713961632936485648359911 := by decide +kernel
private theorem receipt_0_3_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 1) 128 128 = 5379006867399635943360218 := by decide +kernel
private theorem receipt_0_3_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 1) 256 26 = 139331622298332328215073 := by decide +kernel
private theorem receipt_0_3_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 1) 128 154 = 5518338489697968271575291 :=
  phaseBlock_append receipt_0_3_2402_1_part1 receipt_0_3_2402_1_part2 rfl rfl rfl
private theorem receipt_0_3_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2402 3 1 0 1 1) 0 282 = 20232300122634453919935202 :=
  phaseBlock_append receipt_0_3_2402_1_part0 receipt_0_3_2402_1_join0 rfl rfl rfl

private theorem receipt_0_3_2402_1 : fastPhase (bank 0 3).shape 179798 2402 3 1 0 1 1 = 20232300122634453919935202 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2402_1_join1

private theorem receipt_0_3_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 0) 0 128 = 14794747130138468007801153 := by decide +kernel
private theorem receipt_0_3_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 0) 128 128 = 5443371192516815465719294 := by decide +kernel
private theorem receipt_0_3_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 0) 256 26 = 150573395103522173170524 := by decide +kernel
private theorem receipt_0_3_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 0) 128 154 = 5593944587620337638889818 :=
  phaseBlock_append receipt_0_3_2403_0_part1 receipt_0_3_2403_0_part2 rfl rfl rfl
private theorem receipt_0_3_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 0) 0 282 = 20388691717758805646690971 :=
  phaseBlock_append receipt_0_3_2403_0_part0 receipt_0_3_2403_0_join0 rfl rfl rfl

private theorem receipt_0_3_2403_0 : fastPhase (bank 0 3).shape 179798 2403 3 1 0 1 0 = 20388691717758805646690971 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2403_0_join1

private theorem receipt_0_3_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 1) 0 128 = 14714085018554731984373777 := by decide +kernel
private theorem receipt_0_3_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 1) 128 128 = 5379038738734856543765733 := by decide +kernel
private theorem receipt_0_3_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 1) 256 26 = 139332163185543999121779 := by decide +kernel
private theorem receipt_0_3_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 1) 128 154 = 5518370901920400542887512 :=
  phaseBlock_append receipt_0_3_2403_1_part1 receipt_0_3_2403_1_part2 rfl rfl rfl
private theorem receipt_0_3_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179798 2403 3 1 0 1 1) 0 282 = 20232455920475132527261289 :=
  phaseBlock_append receipt_0_3_2403_1_part0 receipt_0_3_2403_1_join0 rfl rfl rfl

private theorem receipt_0_3_2403_1 : fastPhase (bank 0 3).shape 179798 2403 3 1 0 1 1 = 20232455920475132527261289 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2403_1_join1

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2402_0 receipt_0_3_2402_1 receipt_0_3_2403_0 receipt_0_3_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 0) 0 128 = 13279837518804238073820895 := by decide +kernel
private theorem receipt_1_3_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 0) 128 128 = 4874300832547178792962542 := by decide +kernel
private theorem receipt_1_3_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 0) 256 26 = 134590292312777168564940 := by decide +kernel
private theorem receipt_1_3_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 0) 128 154 = 5008891124859955961527482 :=
  phaseBlock_append receipt_1_3_2402_0_part1 receipt_1_3_2402_0_part2 rfl rfl rfl
private theorem receipt_1_3_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 0) 0 282 = 18288728643664194035348377 :=
  phaseBlock_append receipt_1_3_2402_0_part0 receipt_1_3_2402_0_join0 rfl rfl rfl

private theorem receipt_1_3_2402_0 : fastPhase (bank 1 3).shape 179798 2402 3 1 0 2 0 = 18288728643664194035348377 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2402_0_join1

private theorem receipt_1_3_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 1) 0 128 = 13207177183990277123332124 := by decide +kernel
private theorem receipt_1_3_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 1) 128 128 = 4816612740130772002837733 := by decide +kernel
private theorem receipt_1_3_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 1) 256 26 = 124540611574831567881749 := by decide +kernel
private theorem receipt_1_3_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 1) 128 154 = 4941153351705603570719482 :=
  phaseBlock_append receipt_1_3_2402_1_part1 receipt_1_3_2402_1_part2 rfl rfl rfl
private theorem receipt_1_3_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2402 3 1 0 2 1) 0 282 = 18148330535695880694051606 :=
  phaseBlock_append receipt_1_3_2402_1_part0 receipt_1_3_2402_1_join0 rfl rfl rfl

private theorem receipt_1_3_2402_1 : fastPhase (bank 1 3).shape 179798 2402 3 1 0 2 1 = 18148330535695880694051606 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2402_1_join1

private theorem receipt_1_3_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 0) 0 128 = 13279948779716171562409586 := by decide +kernel
private theorem receipt_1_3_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 0) 128 128 = 4874329666538319139613090 := by decide +kernel
private theorem receipt_1_3_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 0) 256 26 = 134590812965022912021196 := by decide +kernel
private theorem receipt_1_3_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 0) 128 154 = 5008920479503342051634286 :=
  phaseBlock_append receipt_1_3_2403_0_part1 receipt_1_3_2403_0_part2 rfl rfl rfl
private theorem receipt_1_3_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 0) 0 282 = 18288869259219513614043872 :=
  phaseBlock_append receipt_1_3_2403_0_part0 receipt_1_3_2403_0_join0 rfl rfl rfl

private theorem receipt_1_3_2403_0 : fastPhase (bank 1 3).shape 179798 2403 3 1 0 2 0 = 18288869259219513614043872 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2403_0_join1

private theorem receipt_1_3_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 1) 0 128 = 13207287941067136924109131 := by decide +kernel
private theorem receipt_1_3_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 1) 128 128 = 4816641281609227868948773 := by decide +kernel
private theorem receipt_1_3_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 1) 256 26 = 124541095045303847353163 := by decide +kernel
private theorem receipt_1_3_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 1) 128 154 = 4941182376654531716301936 :=
  phaseBlock_append receipt_1_3_2403_1_part1 receipt_1_3_2403_1_part2 rfl rfl rfl
private theorem receipt_1_3_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179798 2403 3 1 0 2 1) 0 282 = 18148470317721668640411067 :=
  phaseBlock_append receipt_1_3_2403_1_part0 receipt_1_3_2403_1_join0 rfl rfl rfl

private theorem receipt_1_3_2403_1 : fastPhase (bank 1 3).shape 179798 2403 3 1 0 2 1 = 18148470317721668640411067 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2403_1_join1

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2402_0 receipt_1_3_2402_1 receipt_1_3_2403_0 receipt_1_3_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 0) 0 128 = 6966916901188679903667948 := by decide +kernel
private theorem receipt_2_3_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 0) 128 128 = 2512668028140300307325377 := by decide +kernel
private theorem receipt_2_3_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 0) 256 26 = 68466331680638634534722 := by decide +kernel
private theorem receipt_2_3_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 0) 128 154 = 2581134359820938941860099 :=
  phaseBlock_append receipt_2_3_2402_0_part1 receipt_2_3_2402_0_part2 rfl rfl rfl
private theorem receipt_2_3_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 0) 0 282 = 9548051261009618845528047 :=
  phaseBlock_append receipt_2_3_2402_0_part0 receipt_2_3_2402_0_join0 rfl rfl rfl

private theorem receipt_2_3_2402_0 : fastPhase (bank 2 3).shape 179798 2402 3 1 0 7 0 = 9548051261009618845528047 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2402_0_join1

private theorem receipt_2_3_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 1) 0 128 = 6927813842422206644771749 := by decide +kernel
private theorem receipt_2_3_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 1) 128 128 = 2482622513264748554026439 := by decide +kernel
private theorem receipt_2_3_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 1) 256 26 = 63347690563231822075951 := by decide +kernel
private theorem receipt_2_3_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 1) 128 154 = 2545970203827980376102390 :=
  phaseBlock_append receipt_2_3_2402_1_part1 receipt_2_3_2402_1_part2 rfl rfl rfl
private theorem receipt_2_3_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2402 3 1 0 7 1) 0 282 = 9473784046250187020874139 :=
  phaseBlock_append receipt_2_3_2402_1_part0 receipt_2_3_2402_1_join0 rfl rfl rfl

private theorem receipt_2_3_2402_1 : fastPhase (bank 2 3).shape 179798 2402 3 1 0 7 1 = 9473784046250187020874139 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2402_1_join1

private theorem receipt_2_3_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 0) 0 128 = 6966975297298557219094395 := by decide +kernel
private theorem receipt_2_3_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 0) 128 128 = 2512682901116302734339394 := by decide +kernel
private theorem receipt_2_3_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 0) 256 26 = 68466596546922480767826 := by decide +kernel
private theorem receipt_2_3_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 0) 128 154 = 2581149497663225215107220 :=
  phaseBlock_append receipt_2_3_2403_0_part1 receipt_2_3_2403_0_part2 rfl rfl rfl
private theorem receipt_2_3_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 0) 0 282 = 9548124794961782434201615 :=
  phaseBlock_append receipt_2_3_2403_0_part0 receipt_2_3_2403_0_join0 rfl rfl rfl

private theorem receipt_2_3_2403_0 : fastPhase (bank 2 3).shape 179798 2403 3 1 0 7 0 = 9548124794961782434201615 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2403_0_join1

private theorem receipt_2_3_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 1) 0 128 = 6927871965816291543195149 := by decide +kernel
private theorem receipt_2_3_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 1) 128 128 = 2482637233479747346713459 := by decide +kernel
private theorem receipt_2_3_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 1) 256 26 = 63347936489053313540205 := by decide +kernel
private theorem receipt_2_3_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 1) 128 154 = 2545985169968800660253664 :=
  phaseBlock_append receipt_2_3_2403_1_part1 receipt_2_3_2403_1_part2 rfl rfl rfl
private theorem receipt_2_3_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179798 2403 3 1 0 7 1) 0 282 = 9473857135785092203448813 :=
  phaseBlock_append receipt_2_3_2403_1_part0 receipt_2_3_2403_1_join0 rfl rfl rfl

private theorem receipt_2_3_2403_1 : fastPhase (bank 2 3).shape 179798 2403 3 1 0 7 1 = 9473857135785092203448813 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2403_1_join1

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2402_0 receipt_2_3_2402_1 receipt_2_3_2403_0 receipt_2_3_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2402 3 1 1 1 0) 0 128 = 684682548052377912608736 := by decide +kernel
private theorem receipt_3_3_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2402 3 1 1 1 0) 128 110 = 159353614437779087807316 := by decide +kernel
private theorem receipt_3_3_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2402 3 1 1 1 0) 0 238 = 844036162490157000416052 :=
  phaseBlock_append receipt_3_3_2402_0_part0 receipt_3_3_2402_0_part1 rfl rfl rfl

private theorem receipt_3_3_2402_0 : fastPhase (bank 3 3).shape 179798 2402 3 1 1 1 0 = 844036162490157000416052 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2402_0_join0

private theorem receipt_3_3_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2402 3 1 1 1 1) 0 128 = 679953846412110964429920 := by decide +kernel
private theorem receipt_3_3_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2402 3 1 1 1 1) 128 110 = 156319888541441682055955 := by decide +kernel
private theorem receipt_3_3_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2402 3 1 1 1 1) 0 238 = 836273734953552646485875 :=
  phaseBlock_append receipt_3_3_2402_1_part0 receipt_3_3_2402_1_part1 rfl rfl rfl

private theorem receipt_3_3_2402_1 : fastPhase (bank 3 3).shape 179798 2402 3 1 1 1 1 = 836273734953552646485875 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2402_1_join0

private theorem receipt_3_3_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2403 3 1 1 1 0) 0 128 = 684687629866779538286880 := by decide +kernel
private theorem receipt_3_3_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2403 3 1 1 1 0) 128 110 = 159354181090577587869106 := by decide +kernel
private theorem receipt_3_3_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2403 3 1 1 1 0) 0 238 = 844041810957357126155986 :=
  phaseBlock_append receipt_3_3_2403_0_part0 receipt_3_3_2403_0_part1 rfl rfl rfl

private theorem receipt_3_3_2403_0 : fastPhase (bank 3 3).shape 179798 2403 3 1 1 1 0 = 844041810957357126155986 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2403_0_join0

private theorem receipt_3_3_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2403 3 1 1 1 1) 0 128 = 679958889559291128283680 := by decide +kernel
private theorem receipt_3_3_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2403 3 1 1 1 1) 128 110 = 156320445249903629763277 := by decide +kernel
private theorem receipt_3_3_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179798 2403 3 1 1 1 1) 0 238 = 836279334809194758046957 :=
  phaseBlock_append receipt_3_3_2403_1_part0 receipt_3_3_2403_1_part1 rfl rfl rfl

private theorem receipt_3_3_2403_1 : fastPhase (bank 3 3).shape 179798 2403 3 1 1 1 1 = 836279334809194758046957 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2403_1_join0

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2402_0 receipt_3_3_2402_1 receipt_3_3_2403_0 receipt_3_3_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 0) 0 128 = 22152144065102908439842161 := by decide +kernel
private theorem receipt_0_4_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 0) 128 128 = 8699534720375142218491761 := by decide +kernel
private theorem receipt_0_4_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 0) 256 36 = 412488424546456994955726 := by decide +kernel
private theorem receipt_0_4_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 0) 128 164 = 9112023144921599213447487 :=
  phaseBlock_append receipt_0_4_2402_0_part1 receipt_0_4_2402_0_part2 rfl rfl rfl
private theorem receipt_0_4_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 0) 0 292 = 31264167210024507653289648 :=
  phaseBlock_append receipt_0_4_2402_0_part0 receipt_0_4_2402_0_join0 rfl rfl rfl

private theorem receipt_0_4_2402_0 : fastPhase (bank 0 4).shape 179798 2402 4 1 0 1 0 = 31264167210024507653289648 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2402_0_join1

private theorem receipt_0_4_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 1) 0 128 = 22036767255741714635205876 := by decide +kernel
private theorem receipt_0_4_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 1) 128 128 = 8606377788615351003639519 := by decide +kernel
private theorem receipt_0_4_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 1) 256 36 = 389959810984508437327960 := by decide +kernel
private theorem receipt_0_4_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 1) 128 164 = 8996337599599859440967479 :=
  phaseBlock_append receipt_0_4_2402_1_part1 receipt_0_4_2402_1_part2 rfl rfl rfl
private theorem receipt_0_4_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2402 4 1 0 1 1) 0 292 = 31033104855341574076173355 :=
  phaseBlock_append receipt_0_4_2402_1_part0 receipt_0_4_2402_1_join0 rfl rfl rfl

private theorem receipt_0_4_2402_1 : fastPhase (bank 0 4).shape 179798 2402 4 1 0 1 1 = 31033104855341574076173355 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2402_1_join1

private theorem receipt_0_4_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 0) 0 128 = 22152329535406961155875250 := by decide +kernel
private theorem receipt_0_4_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 0) 128 128 = 8699587110755091824256004 := by decide +kernel
private theorem receipt_0_4_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 0) 256 36 = 412490096361026814012805 := by decide +kernel
private theorem receipt_0_4_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 0) 128 164 = 9112077207116118638268809 :=
  phaseBlock_append receipt_0_4_2403_0_part1 receipt_0_4_2403_0_part2 rfl rfl rfl
private theorem receipt_0_4_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 0) 0 292 = 31264406742523079794144059 :=
  phaseBlock_append receipt_0_4_2403_0_part0 receipt_0_4_2403_0_join0 rfl rfl rfl

private theorem receipt_0_4_2403_0 : fastPhase (bank 0 4).shape 179798 2403 4 1 0 1 0 = 31264406742523079794144059 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2403_0_join1

private theorem receipt_0_4_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 1) 0 128 = 22036951924988364814080305 := by decide +kernel
private theorem receipt_0_4_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 1) 128 128 = 8606429695234165054882616 := by decide +kernel
private theorem receipt_0_4_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 1) 256 36 = 389961396545727197921761 := by decide +kernel
private theorem receipt_0_4_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 1) 128 164 = 8996391091779892252804377 :=
  phaseBlock_append receipt_0_4_2403_1_part1 receipt_0_4_2403_1_part2 rfl rfl rfl
private theorem receipt_0_4_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179798 2403 4 1 0 1 1) 0 292 = 31033343016768257066884682 :=
  phaseBlock_append receipt_0_4_2403_1_part0 receipt_0_4_2403_1_join0 rfl rfl rfl

private theorem receipt_0_4_2403_1 : fastPhase (bank 0 4).shape 179798 2403 4 1 0 1 1 = 31033343016768257066884682 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2403_1_join1

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2402_0 receipt_0_4_2402_1 receipt_0_4_2403_0 receipt_0_4_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 0) 0 128 = 19947254922885707072781633 := by decide +kernel
private theorem receipt_1_4_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 0) 128 128 = 7816997374227920565585642 := by decide +kernel
private theorem receipt_1_4_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 0) 256 36 = 370047887585749414893987 := by decide +kernel
private theorem receipt_1_4_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 0) 128 164 = 8187045261813669980479629 :=
  phaseBlock_append receipt_1_4_2402_0_part1 receipt_1_4_2402_0_part2 rfl rfl rfl
private theorem receipt_1_4_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 0) 0 292 = 28134300184699377053261262 :=
  phaseBlock_append receipt_1_4_2402_0_part0 receipt_1_4_2402_0_join0 rfl rfl rfl

private theorem receipt_1_4_2402_0 : fastPhase (bank 1 4).shape 179798 2402 4 1 0 2 0 = 28134300184699377053261262 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2402_0_join1

private theorem receipt_1_4_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 1) 0 128 = 19843021552008496062143271 := by decide +kernel
private theorem receipt_1_4_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 1) 128 128 = 7733172417710420512654110 := by decide +kernel
private theorem receipt_1_4_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 1) 256 36 = 349833065668204380055945 := by decide +kernel
private theorem receipt_1_4_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 1) 128 164 = 8083005483378624892710055 :=
  phaseBlock_append receipt_1_4_2402_1_part1 receipt_1_4_2402_1_part2 rfl rfl rfl
private theorem receipt_1_4_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2402 4 1 0 2 1) 0 292 = 27926027035387120954853326 :=
  phaseBlock_append receipt_1_4_2402_1_part0 receipt_1_4_2402_1_join0 rfl rfl rfl

private theorem receipt_1_4_2402_1 : fastPhase (bank 1 4).shape 179798 2402 4 1 0 2 1 = 27926027035387120954853326 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2402_1_join1

private theorem receipt_1_4_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 0) 0 128 = 19947421941087189785068519 := by decide +kernel
private theorem receipt_1_4_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 0) 128 128 = 7817044453159193087126896 := by decide +kernel
private theorem receipt_1_4_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 0) 256 36 = 370049387399908189845355 := by decide +kernel
private theorem receipt_1_4_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 0) 128 164 = 8187093840559101276972251 :=
  phaseBlock_append receipt_1_4_2403_0_part1 receipt_1_4_2403_0_part2 rfl rfl rfl
private theorem receipt_1_4_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 0) 0 292 = 28134515781646291062040770 :=
  phaseBlock_append receipt_1_4_2403_0_part0 receipt_1_4_2403_0_join0 rfl rfl rfl

private theorem receipt_1_4_2403_0 : fastPhase (bank 1 4).shape 179798 2403 4 1 0 2 0 = 28134515781646291062040770 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2403_0_join1

private theorem receipt_1_4_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 1) 0 128 = 19843187845988146029326192 := by decide +kernel
private theorem receipt_1_4_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 1) 128 128 = 7733219061195944175552494 := by decide +kernel
private theorem receipt_1_4_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 1) 256 36 = 349834488085472547875707 := by decide +kernel
private theorem receipt_1_4_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 1) 128 164 = 8083053549281416723428201 :=
  phaseBlock_append receipt_1_4_2403_1_part1 receipt_1_4_2403_1_part2 rfl rfl rfl
private theorem receipt_1_4_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179798 2403 4 1 0 2 1) 0 292 = 27926241395269562752754393 :=
  phaseBlock_append receipt_1_4_2403_1_part0 receipt_1_4_2403_1_join0 rfl rfl rfl

private theorem receipt_1_4_2403_1 : fastPhase (bank 1 4).shape 179798 2403 4 1 0 2 1 = 27926241395269562752754393 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2403_1_join1

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2402_0 receipt_1_4_2402_1 receipt_1_4_2403_0 receipt_1_4_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 0) 0 128 = 10700514776738309875406649 := by decide +kernel
private theorem receipt_2_4_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 0) 128 128 = 4129453300436652564366109 := by decide +kernel
private theorem receipt_2_4_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 0) 256 36 = 193210306281657265620110 := by decide +kernel
private theorem receipt_2_4_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 0) 128 164 = 4322663606718309829986219 :=
  phaseBlock_append receipt_2_4_2402_0_part1 receipt_2_4_2402_0_part2 rfl rfl rfl
private theorem receipt_2_4_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 0) 0 292 = 15023178383456619705392868 :=
  phaseBlock_append receipt_2_4_2402_0_part0 receipt_2_4_2402_0_join0 rfl rfl rfl

private theorem receipt_2_4_2402_0 : fastPhase (bank 2 4).shape 179798 2402 4 1 0 7 0 = 15023178383456619705392868 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2402_0_join1

private theorem receipt_2_4_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 1) 0 128 = 10643286614884427911880760 := by decide +kernel
private theorem receipt_2_4_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 1) 128 128 = 4084717443248267255574039 := by decide +kernel
private theorem receipt_2_4_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 1) 256 36 = 182639847924077992512232 := by decide +kernel
private theorem receipt_2_4_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 1) 128 164 = 4267357291172345248086271 :=
  phaseBlock_append receipt_2_4_2402_1_part1 receipt_2_4_2402_1_part2 rfl rfl rfl
private theorem receipt_2_4_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2402 4 1 0 7 1) 0 292 = 14910643906056773159967031 :=
  phaseBlock_append receipt_2_4_2402_1_part0 receipt_2_4_2402_1_join0 rfl rfl rfl

private theorem receipt_2_4_2402_1 : fastPhase (bank 2 4).shape 179798 2402 4 1 0 7 1 = 14910643906056773159967031 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2402_1_join1

private theorem receipt_2_4_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 0) 0 128 = 10700604404753183827397778 := by decide +kernel
private theorem receipt_2_4_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 0) 128 128 = 4129478183544051960848548 := by decide +kernel
private theorem receipt_2_4_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 0) 256 36 = 193211089410141825830745 := by decide +kernel
private theorem receipt_2_4_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 0) 128 164 = 4322689272954193786679293 :=
  phaseBlock_append receipt_2_4_2403_0_part1 receipt_2_4_2403_0_part2 rfl rfl rfl
private theorem receipt_2_4_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 0) 0 292 = 15023293677707377614077071 :=
  phaseBlock_append receipt_2_4_2403_0_part0 receipt_2_4_2403_0_join0 rfl rfl rfl

private theorem receipt_2_4_2403_0 : fastPhase (bank 2 4).shape 179798 2403 4 1 0 7 0 = 15023293677707377614077071 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2403_0_join1

private theorem receipt_2_4_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 1) 0 128 = 10643375843222275718127997 := by decide +kernel
private theorem receipt_2_4_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 1) 128 128 = 4084742093409511641939496 := by decide +kernel
private theorem receipt_2_4_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 1) 256 36 = 182640590573029923286365 := by decide +kernel
private theorem receipt_2_4_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 1) 128 164 = 4267382683982541565225861 :=
  phaseBlock_append receipt_2_4_2403_1_part1 receipt_2_4_2403_1_part2 rfl rfl rfl
private theorem receipt_2_4_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179798 2403 4 1 0 7 1) 0 292 = 14910758527204817283353858 :=
  phaseBlock_append receipt_2_4_2403_1_part0 receipt_2_4_2403_1_join0 rfl rfl rfl

private theorem receipt_2_4_2403_1 : fastPhase (bank 2 4).shape 179798 2403 4 1 0 7 1 = 14910758527204817283353858 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2403_1_join1

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2402_0 receipt_2_4_2402_1 receipt_2_4_2403_0 receipt_2_4_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 0) 0 128 = 1611496270264620995420256 := by decide +kernel
private theorem receipt_3_4_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 0) 128 128 = 650628453626827737378912 := by decide +kernel
private theorem receipt_3_4_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 0) 256 47 = 45112138796373586969668 := by decide +kernel
private theorem receipt_3_4_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 0) 128 175 = 695740592423201324348580 :=
  phaseBlock_append receipt_3_4_2402_0_part1 receipt_3_4_2402_0_part2 rfl rfl rfl
private theorem receipt_3_4_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 0) 0 303 = 2307236862687822319768836 :=
  phaseBlock_append receipt_3_4_2402_0_part0 receipt_3_4_2402_0_join0 rfl rfl rfl

private theorem receipt_3_4_2402_0 : fastPhase (bank 3 4).shape 179798 2402 4 1 1 1 0 = 2307236862687822319768836 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2402_0_join1

private theorem receipt_3_4_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 1) 0 128 = 1603207779837242970958560 := by decide +kernel
private theorem receipt_3_4_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 1) 128 128 = 644081994710939905932000 := by decide +kernel
private theorem receipt_3_4_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 1) 256 47 = 43189919761530116090250 := by decide +kernel
private theorem receipt_3_4_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 1) 128 175 = 687271914472470022022250 :=
  phaseBlock_append receipt_3_4_2402_1_part1 receipt_3_4_2402_1_part2 rfl rfl rfl
private theorem receipt_3_4_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2402 4 1 1 1 1) 0 303 = 2290479694309712992980810 :=
  phaseBlock_append receipt_3_4_2402_1_part0 receipt_3_4_2402_1_join0 rfl rfl rfl

private theorem receipt_3_4_2402_1 : fastPhase (bank 3 4).shape 179798 2402 4 1 1 1 1 = 2290479694309712992980810 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2402_1_join1

private theorem receipt_3_4_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 0) 0 128 = 1611508662506181507376672 := by decide +kernel
private theorem receipt_3_4_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 0) 128 128 = 650631206168625668003360 := by decide +kernel
private theorem receipt_3_4_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 0) 256 47 = 45112216278421391871660 := by decide +kernel
private theorem receipt_3_4_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 0) 128 175 = 695743422447047059875020 :=
  phaseBlock_append receipt_3_4_2403_0_part1 receipt_3_4_2403_0_part2 rfl rfl rfl
private theorem receipt_3_4_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 0) 0 303 = 2307252084953228567251692 :=
  phaseBlock_append receipt_3_4_2403_0_part0 receipt_3_4_2403_0_join0 rfl rfl rfl

private theorem receipt_3_4_2403_0 : fastPhase (bank 3 4).shape 179798 2403 4 1 1 1 0 = 2307252084953228567251692 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2403_0_join1

private theorem receipt_3_4_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 1) 0 128 = 1603220100450232539185568 := by decide +kernel
private theorem receipt_3_4_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 1) 128 128 = 644084718690956803559840 := by decide +kernel
private theorem receipt_3_4_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 1) 256 47 = 43189994158928656072185 := by decide +kernel
private theorem receipt_3_4_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 1) 128 175 = 687274712849885459632025 :=
  phaseBlock_append receipt_3_4_2403_1_part1 receipt_3_4_2403_1_part2 rfl rfl rfl
private theorem receipt_3_4_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179798 2403 4 1 1 1 1) 0 303 = 2290494813300117998817593 :=
  phaseBlock_append receipt_3_4_2403_1_part0 receipt_3_4_2403_1_join0 rfl rfl rfl

private theorem receipt_3_4_2403_1 : fastPhase (bank 3 4).shape 179798 2403 4 1 1 1 1 = 2290494813300117998817593 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2403_1_join1

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2402_0 receipt_3_4_2402_1 receipt_3_4_2403_0 receipt_3_4_2403_1 (by decide +kernel) (by decide +kernel)

def group1_stage (i : Fin 4) : Fin 17 :=
  ⟨1+i.val, by have := i.isLt; omega⟩

theorem group1_checked (rect : Fin 4) (i : Fin 4) :
    Checked (bank rect (group1_stage i)) (reserve (group1_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_1
    · exact receipt_1_1
    · exact receipt_2_1
    · exact receipt_3_1
  · fin_cases rect
    · exact receipt_0_2
    · exact receipt_1_2
    · exact receipt_2_2
    · exact receipt_3_2
  · fin_cases rect
    · exact receipt_0_3
    · exact receipt_1_3
    · exact receipt_2_3
    · exact receipt_3_3
  · fin_cases rect
    · exact receipt_0_4
    · exact receipt_1_4
    · exact receipt_2_4
    · exact receipt_3_4

theorem group1_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 4) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group1_stage i)).shape
      (cutoff h rect (group1_stage i)), ¬ G∣Q :=
  (group1_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group1_avoids

end Lower6960.RescueSource
