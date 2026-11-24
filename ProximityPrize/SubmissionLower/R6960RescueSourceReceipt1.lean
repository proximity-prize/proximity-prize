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

private theorem receipt_0_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 0) 0 128 = 7285840994773281543400382 := by decide +kernel
private theorem receipt_0_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 0) 128 128 = 2678391533525416428385335 := by decide +kernel
private theorem receipt_0_1_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 0) 256 26 = 74042847336633793794354 := by decide +kernel
private theorem receipt_0_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 0) 128 154 = 2752434380862050222179689 :=
  phaseBlock_append receipt_0_1_2359_0_part1 receipt_0_1_2359_0_part2 rfl rfl rfl
private theorem receipt_0_1_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 0) 0 282 = 10038275375635331765580071 :=
  phaseBlock_append receipt_0_1_2359_0_part0 receipt_0_1_2359_0_join0 rfl rfl rfl

private theorem receipt_0_1_2359_0 : fastPhase (bank 0 1).shape 179808 2379 1 1 0 1 0 = 10038275375635331765580071 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2359_0_join1

private theorem receipt_0_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 1) 0 128 = 7246063406748166324530582 := by decide +kernel
private theorem receipt_0_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 1) 128 128 = 2646719566385034704428161 := by decide +kernel
private theorem receipt_0_1_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 1) 256 26 = 68514721987573784670477 := by decide +kernel
private theorem receipt_0_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 1) 128 154 = 2715234288372608489098638 :=
  phaseBlock_append receipt_0_1_2359_1_part1 receipt_0_1_2359_1_part2 rfl rfl rfl
private theorem receipt_0_1_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2379 1 1 0 1 1) 0 282 = 9961297695120774813629220 :=
  phaseBlock_append receipt_0_1_2359_1_part0 receipt_0_1_2359_1_join0 rfl rfl rfl

private theorem receipt_0_1_2359_1 : fastPhase (bank 0 1).shape 179808 2379 1 1 0 1 1 = 9961297695120774813629220 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2359_1_join1

private theorem receipt_0_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 0) 0 128 = 7285902426308608057860265 := by decide +kernel
private theorem receipt_0_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 0) 128 128 = 2678407525954775923071876 := by decide +kernel
private theorem receipt_0_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 0) 256 26 = 74043138112079282842650 := by decide +kernel
private theorem receipt_0_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 0) 128 154 = 2752450664066855205914526 :=
  phaseBlock_append receipt_0_1_2360_0_part1 receipt_0_1_2360_0_part2 rfl rfl rfl
private theorem receipt_0_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 0) 0 282 = 10038353090375463263774791 :=
  phaseBlock_append receipt_0_1_2360_0_part0 receipt_0_1_2360_0_join0 rfl rfl rfl

private theorem receipt_0_1_2360_0 : fastPhase (bank 0 1).shape 179808 2380 1 1 0 1 0 = 10038353090375463263774791 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2360_0_join1

private theorem receipt_0_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 1) 0 128 = 7246124560647623095082175 := by decide +kernel
private theorem receipt_0_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 1) 128 128 = 2646735396544961363264103 := by decide +kernel
private theorem receipt_0_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 1) 256 26 = 68514991986862661197395 := by decide +kernel
private theorem receipt_0_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 1) 128 154 = 2715250388531824024461498 :=
  phaseBlock_append receipt_0_1_2360_1_part1 receipt_0_1_2360_1_part2 rfl rfl rfl
private theorem receipt_0_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2380 1 1 0 1 1) 0 282 = 9961374949179447119543673 :=
  phaseBlock_append receipt_0_1_2360_1_part0 receipt_0_1_2360_1_join0 rfl rfl rfl

private theorem receipt_0_1_2360_1 : fastPhase (bank 0 1).shape 179808 2380 1 1 0 1 1 = 9961374949179447119543673 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2360_1_join1

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2359_0 receipt_0_1_2359_1 receipt_0_1_2360_0 receipt_0_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 0) 0 128 = 6539225794982783602511781 := by decide +kernel
private theorem receipt_1_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 0) 128 128 = 2395712751003378997664168 := by decide +kernel
private theorem receipt_1_1_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 0) 256 26 = 66058731036455106514930 := by decide +kernel
private theorem receipt_1_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 0) 128 154 = 2461771482039834104179098 :=
  phaseBlock_append receipt_1_1_2359_0_part1 receipt_1_1_2359_0_part2 rfl rfl rfl
private theorem receipt_1_1_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 0) 0 282 = 9000997277022617706690879 :=
  phaseBlock_append receipt_1_1_2359_0_part0 receipt_1_1_2359_0_join0 rfl rfl rfl

private theorem receipt_1_1_2359_0 : fastPhase (bank 1 1).shape 179808 2379 1 1 0 2 0 = 9000997277022617706690879 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2359_0_join1

private theorem receipt_1_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 1) 0 128 = 6503343684599974771193727 := by decide +kernel
private theorem receipt_1_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 1) 128 128 = 2367326536871923080373721 := by decide +kernel
private theorem receipt_1_1_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 1) 256 26 = 61125528034702470480292 := by decide +kernel
private theorem receipt_1_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 1) 128 154 = 2428452064906625550854013 :=
  phaseBlock_append receipt_1_1_2359_1_part1 receipt_1_1_2359_1_part2 rfl rfl rfl
private theorem receipt_1_1_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2379 1 1 0 2 1) 0 282 = 8931795749506600322047740 :=
  phaseBlock_append receipt_1_1_2359_1_part0 receipt_1_1_2359_1_join0 rfl rfl rfl

private theorem receipt_1_1_2359_1 : fastPhase (bank 1 1).shape 179808 2379 1 1 0 2 1 = 8931795749506600322047740 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2359_1_join1

private theorem receipt_1_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 0) 0 128 = 6539280936120175785087054 := by decide +kernel
private theorem receipt_1_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 0) 128 128 = 2395727057294775254670109 := by decide +kernel
private theorem receipt_1_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 0) 256 26 = 66058990459054130187529 := by decide +kernel
private theorem receipt_1_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 0) 128 154 = 2461786047753829384857638 :=
  phaseBlock_append receipt_1_1_2360_0_part1 receipt_1_1_2360_0_part2 rfl rfl rfl
private theorem receipt_1_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 0) 0 282 = 9001066983874005169944692 :=
  phaseBlock_append receipt_1_1_2360_0_part0 receipt_1_1_2360_0_join0 rfl rfl rfl

private theorem receipt_1_1_2360_0 : fastPhase (bank 1 1).shape 179808 2380 1 1 0 2 0 = 9001066983874005169944692 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2360_0_join1

private theorem receipt_1_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 1) 0 128 = 6503398575001042387793545 := by decide +kernel
private theorem receipt_1_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 1) 128 128 = 2367340697651898449753686 := by decide +kernel
private theorem receipt_1_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 1) 256 26 = 61125768916549447096508 := by decide +kernel
private theorem receipt_1_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 1) 128 154 = 2428466466568447896850194 :=
  phaseBlock_append receipt_1_1_2360_1_part1 receipt_1_1_2360_1_part2 rfl rfl rfl
private theorem receipt_1_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2380 1 1 0 2 1) 0 282 = 8931865041569490284643739 :=
  phaseBlock_append receipt_1_1_2360_1_part0 receipt_1_1_2360_1_join0 rfl rfl rfl

private theorem receipt_1_1_2360_1 : fastPhase (bank 1 1).shape 179808 2380 1 1 0 2 1 = 8931865041569490284643739 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2360_1_join1

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2359_0 receipt_1_1_2359_1 receipt_1_1_2360_0 receipt_1_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 0) 0 128 = 3435118389693022102842629 := by decide +kernel
private theorem receipt_2_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 0) 128 128 = 1227329678482545430626426 := by decide +kernel
private theorem receipt_2_1_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 0) 256 26 = 33203855541549690115614 := by decide +kernel
private theorem receipt_2_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 0) 128 154 = 1260533534024095120742040 :=
  phaseBlock_append receipt_2_1_2359_0_part1 receipt_2_1_2359_0_part2 rfl rfl rfl
private theorem receipt_2_1_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 0) 0 282 = 4695651923717117223584669 :=
  phaseBlock_append receipt_2_1_2359_0_part0 receipt_2_1_2359_0_join0 rfl rfl rfl

private theorem receipt_2_1_2359_0 : fastPhase (bank 2 1).shape 179808 2379 1 1 0 7 0 = 4695651923717117223584669 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2359_0_join1

private theorem receipt_2_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 1) 0 128 = 3415578523767764668268831 := by decide +kernel
private theorem receipt_2_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 1) 128 128 = 1212572082604884024128613 := by decide +kernel
private theorem receipt_2_1_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 1) 256 26 = 30719793710802217873206 := by decide +kernel
private theorem receipt_2_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 1) 128 154 = 1243291876315686242001819 :=
  phaseBlock_append receipt_2_1_2359_1_part1 receipt_2_1_2359_1_part2 rfl rfl rfl
private theorem receipt_2_1_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2379 1 1 0 7 1) 0 282 = 4658870400083450910270650 :=
  phaseBlock_append receipt_2_1_2359_1_part0 receipt_2_1_2359_1_join0 rfl rfl rfl

private theorem receipt_2_1_2359_1 : fastPhase (bank 2 1).shape 179808 2379 1 1 0 7 1 = 4658870400083450910270650 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2359_1_join1

private theorem receipt_2_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 0) 0 128 = 3435147374149508905179838 := by decide +kernel
private theorem receipt_2_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 0) 128 128 = 1227337014093537960010159 := by decide +kernel
private theorem receipt_2_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 0) 256 26 = 33203985944727773774198 := by decide +kernel
private theorem receipt_2_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 0) 128 154 = 1260541000038265733784357 :=
  phaseBlock_append receipt_2_1_2360_0_part1 receipt_2_1_2360_0_part2 rfl rfl rfl
private theorem receipt_2_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 0) 0 282 = 4695688374187774638964195 :=
  phaseBlock_append receipt_2_1_2360_0_part0 receipt_2_1_2360_0_join0 rfl rfl rfl

private theorem receipt_2_1_2360_0 : fastPhase (bank 2 1).shape 179808 2380 1 1 0 7 0 = 4695688374187774638964195 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2360_0_join1

private theorem receipt_2_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 1) 0 128 = 3415607370580175388660490 := by decide +kernel
private theorem receipt_2_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 1) 128 128 = 1212579342277836722653885 := by decide +kernel
private theorem receipt_2_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 1) 256 26 = 30719914776216420674366 := by decide +kernel
private theorem receipt_2_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 1) 128 154 = 1243299257054053143328251 :=
  phaseBlock_append receipt_2_1_2360_1_part1 receipt_2_1_2360_1_part2 rfl rfl rfl
private theorem receipt_2_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2380 1 1 0 7 1) 0 282 = 4658906627634228531988741 :=
  phaseBlock_append receipt_2_1_2360_1_part0 receipt_2_1_2360_1_join0 rfl rfl rfl

private theorem receipt_2_1_2360_1 : fastPhase (bank 2 1).shape 179808 2380 1 1 0 7 1 = 4658906627634228531988741 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2360_1_join1

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2359_0 receipt_2_1_2359_1 receipt_2_1_2360_0 receipt_2_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2379 1 1 1 1 0) 0 128 = 312400312126227180693600 := by decide +kernel
private theorem receipt_3_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2379 1 1 1 1 0) 128 80 = 46032213602463323772060 := by decide +kernel
private theorem receipt_3_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2379 1 1 1 1 0) 0 208 = 358432525728690504465660 :=
  phaseBlock_append receipt_3_1_2359_0_part0 receipt_3_1_2359_0_part1 rfl rfl rfl

private theorem receipt_3_1_2359_0 : fastPhase (bank 3 1).shape 179808 2379 1 1 1 1 0 = 358432525728690504465660 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2359_0_join0

private theorem receipt_3_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2379 1 1 1 1 1) 0 128 = 309822448192386218687904 := by decide +kernel
private theorem receipt_3_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2379 1 1 1 1 1) 128 80 = 44840506308479003775204 := by decide +kernel
private theorem receipt_3_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2379 1 1 1 1 1) 0 208 = 354662954500865222463108 :=
  phaseBlock_append receipt_3_1_2359_1_part0 receipt_3_1_2359_1_part1 rfl rfl rfl

private theorem receipt_3_1_2359_1 : fastPhase (bank 3 1).shape 179808 2379 1 1 1 1 1 = 354662954500865222463108 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2359_1_join0

private theorem receipt_3_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2380 1 1 1 1 0) 0 128 = 312402582716334935830752 := by decide +kernel
private theorem receipt_3_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2380 1 1 1 1 0) 128 80 = 46032360080816475627372 := by decide +kernel
private theorem receipt_3_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2380 1 1 1 1 0) 0 208 = 358434942797151411458124 :=
  phaseBlock_append receipt_3_1_2360_0_part0 receipt_3_1_2360_0_part1 rfl rfl rfl

private theorem receipt_3_1_2360_0 : fastPhase (bank 3 1).shape 179808 2380 1 1 1 1 0 = 358434942797151411458124 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2360_0_join0

private theorem receipt_3_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2380 1 1 1 1 1) 0 128 = 309824698477681187909472 := by decide +kernel
private theorem receipt_3_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2380 1 1 1 1 1) 128 80 = 44840649280821287446332 := by decide +kernel
private theorem receipt_3_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2380 1 1 1 1 1) 0 208 = 354665347758502475355804 :=
  phaseBlock_append receipt_3_1_2360_1_part0 receipt_3_1_2360_1_part1 rfl rfl rfl

private theorem receipt_3_1_2360_1 : fastPhase (bank 3 1).shape 179808 2380 1 1 1 1 1 = 354665347758502475355804 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2360_1_join0

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2359_0 receipt_3_1_2359_1 receipt_3_1_2360_0 receipt_3_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 0) 0 128 = 10420389537922630355954400 := by decide +kernel
private theorem receipt_0_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 0) 128 128 = 3864766336842722463304586 := by decide +kernel
private theorem receipt_0_2_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 0) 256 27 = 114010695975814004602151 := by decide +kernel
private theorem receipt_0_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 0) 128 155 = 3978777032818536467906737 :=
  phaseBlock_append receipt_0_2_2359_0_part1 receipt_0_2_2359_0_part2 rfl rfl rfl
private theorem receipt_0_2_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 0) 0 283 = 14399166570741166823861137 :=
  phaseBlock_append receipt_0_2_2359_0_part0 receipt_0_2_2359_0_join0 rfl rfl rfl

private theorem receipt_0_2_2359_0 : fastPhase (bank 0 2).shape 179808 2379 2 1 0 1 0 = 14399166570741166823861137 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2359_0_join1

private theorem receipt_0_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 1) 0 128 = 10363908855302535786284960 := by decide +kernel
private theorem receipt_0_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 1) 128 128 = 3819583846524901690777662 := by decide +kernel
private theorem receipt_0_2_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 1) 256 27 = 105801453413743549591361 := by decide +kernel
private theorem receipt_0_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 1) 128 155 = 3925385299938645240369023 :=
  phaseBlock_append receipt_0_2_2359_1_part1 receipt_0_2_2359_1_part2 rfl rfl rfl
private theorem receipt_0_2_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2379 2 1 0 1 1) 0 283 = 14289294155241181026653983 :=
  phaseBlock_append receipt_0_2_2359_1_part0 receipt_0_2_2359_1_join0 rfl rfl rfl

private theorem receipt_0_2_2359_1 : fastPhase (bank 0 2).shape 179808 2379 2 1 0 1 1 = 14289294155241181026653983 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2359_1_join1

private theorem receipt_0_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 0) 0 128 = 10420476400416481218387360 := by decide +kernel
private theorem receipt_0_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 0) 128 128 = 3864789412048286423546398 := by decide +kernel
private theorem receipt_0_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 0) 256 27 = 114011148776387059531831 := by decide +kernel
private theorem receipt_0_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 0) 128 155 = 3978800560824673483078229 :=
  phaseBlock_append receipt_0_2_2360_0_part1 receipt_0_2_2360_0_part2 rfl rfl rfl
private theorem receipt_0_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 0) 0 283 = 14399276961241154701465589 :=
  phaseBlock_append receipt_0_2_2360_0_part0 receipt_0_2_2360_0_join0 rfl rfl rfl

private theorem receipt_0_2_2360_0 : fastPhase (bank 0 2).shape 179808 2380 2 1 0 1 0 = 14399276961241154701465589 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2360_0_join1

private theorem receipt_0_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 1) 0 128 = 10363995327173106838072480 := by decide +kernel
private theorem receipt_0_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 1) 128 128 = 3819606689556955155583623 := by decide +kernel
private theorem receipt_0_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 1) 256 27 = 105801875032000502531795 := by decide +kernel
private theorem receipt_0_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 1) 128 155 = 3925408564588955658115418 :=
  phaseBlock_append receipt_0_2_2360_1_part1 receipt_0_2_2360_1_part2 rfl rfl rfl
private theorem receipt_0_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2380 2 1 0 1 1) 0 283 = 14289403891762062496187898 :=
  phaseBlock_append receipt_0_2_2360_1_part0 receipt_0_2_2360_1_join0 rfl rfl rfl

private theorem receipt_0_2_2360_1 : fastPhase (bank 0 2).shape 179808 2380 2 1 0 1 1 = 14289403891762062496187898 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2360_1_join1

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2359_0 receipt_0_2_2359_1 receipt_0_2_2360_0 receipt_0_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 0) 0 128 = 9364540880885980431115680 := by decide +kernel
private theorem receipt_1_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 0) 128 128 = 3463052847734615364508526 := by decide +kernel
private theorem receipt_1_2_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 0) 256 27 = 101937105506190845057930 := by decide +kernel
private theorem receipt_1_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 0) 128 155 = 3564989953240806209566456 :=
  phaseBlock_append receipt_1_2_2359_0_part1 receipt_1_2_2359_0_part2 rfl rfl rfl
private theorem receipt_1_2_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 0) 0 283 = 12929530834126786640682136 :=
  phaseBlock_append receipt_1_2_2359_0_part0 receipt_1_2_2359_0_join0 rfl rfl rfl

private theorem receipt_1_2_2359_0 : fastPhase (bank 1 2).shape 179808 2379 2 1 0 2 0 = 12929530834126786640682136 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2359_0_join1

private theorem receipt_1_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 1) 0 128 = 9313562600973108393331424 := by decide +kernel
private theorem receipt_1_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 1) 128 128 = 3422496404720387360587608 := by decide +kernel
private theorem receipt_1_2_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 1) 256 27 = 94595656380256784866295 := by decide +kernel
private theorem receipt_1_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 1) 128 155 = 3517092061100644145453903 :=
  phaseBlock_append receipt_1_2_2359_1_part1 receipt_1_2_2359_1_part2 rfl rfl rfl
private theorem receipt_1_2_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2379 2 1 0 2 1) 0 283 = 12830654662073752538785327 :=
  phaseBlock_append receipt_1_2_2359_1_part0 receipt_1_2_2359_1_join0 rfl rfl rfl

private theorem receipt_1_2_2359_1 : fastPhase (bank 1 2).shape 179808 2379 2 1 0 2 1 = 12830654662073752538785327 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2359_1_join1

private theorem receipt_1_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 0) 0 128 = 9364618947595093762874880 := by decide +kernel
private theorem receipt_1_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 0) 128 128 = 3463073526498573206086810 := by decide +kernel
private theorem receipt_1_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 0) 256 27 = 101937510358212334543717 := by decide +kernel
private theorem receipt_1_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 0) 128 155 = 3565011036856785540630527 :=
  phaseBlock_append receipt_1_2_2360_0_part1 receipt_1_2_2360_0_part2 rfl rfl rfl
private theorem receipt_1_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 0) 0 283 = 12929629984451879303505407 :=
  phaseBlock_append receipt_1_2_2360_0_part0 receipt_1_2_2360_0_join0 rfl rfl rfl

private theorem receipt_1_2_2360_0 : fastPhase (bank 1 2).shape 179808 2380 2 1 0 2 0 = 12929629984451879303505407 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2360_0_join1

private theorem receipt_1_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 1) 0 128 = 9313640314768976683479040 := by decide +kernel
private theorem receipt_1_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 1) 128 128 = 3422516874990383214885126 := by decide +kernel
private theorem receipt_1_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 1) 256 27 = 94596033345589398593264 := by decide +kernel
private theorem receipt_1_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 1) 128 155 = 3517112908335972613478390 :=
  phaseBlock_append receipt_1_2_2360_1_part1 receipt_1_2_2360_1_part2 rfl rfl rfl
private theorem receipt_1_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2380 2 1 0 2 1) 0 283 = 12830753223104949296957430 :=
  phaseBlock_append receipt_1_2_2360_1_part0 receipt_1_2_2360_1_join0 rfl rfl rfl

private theorem receipt_1_2_2360_1 : fastPhase (bank 1 2).shape 179808 2380 2 1 0 2 1 = 12830753223104949296957430 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2360_1_join1

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2359_0 receipt_1_2_2359_1 receipt_1_2_2360_0 receipt_1_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 0) 0 128 = 4960009912533811460943072 := by decide +kernel
private theorem receipt_2_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 0) 128 128 = 1795668870456763152133634 := by decide +kernel
private theorem receipt_2_2_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 0) 256 27 = 52012301482578202727381 := by decide +kernel
private theorem receipt_2_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 0) 128 155 = 1847681171939341354861015 :=
  phaseBlock_append receipt_2_2_2359_0_part1 receipt_2_2_2359_0_part2 rfl rfl rfl
private theorem receipt_2_2_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 0) 0 283 = 6807691084473152815804087 :=
  phaseBlock_append receipt_2_2_2359_0_part0 receipt_2_2_2359_0_join0 rfl rfl rfl

private theorem receipt_2_2_2359_0 : fastPhase (bank 2 2).shape 179808 2379 2 1 0 7 0 = 6807691084473152815804087 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2359_0_join1

private theorem receipt_2_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 1) 0 128 = 4932163041920966366082080 := by decide +kernel
private theorem receipt_2_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 1) 128 128 = 1774372086375211246196502 := by decide +kernel
private theorem receipt_2_2_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 1) 256 27 = 48260536234747348236401 := by decide +kernel
private theorem receipt_2_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 1) 128 155 = 1822632622609958594432903 :=
  phaseBlock_append receipt_2_2_2359_1_part1 receipt_2_2_2359_1_part2 rfl rfl rfl
private theorem receipt_2_2_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2379 2 1 0 7 1) 0 283 = 6754795664530924960514983 :=
  phaseBlock_append receipt_2_2_2359_1_part0 receipt_2_2_2359_1_join0 rfl rfl rfl

private theorem receipt_2_2_2359_1 : fastPhase (bank 2 2).shape 179808 2379 2 1 0 7 1 = 6754795664530924960514983 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2359_1_join1

private theorem receipt_2_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 0) 0 128 = 4960051282632002270468832 := by decide +kernel
private theorem receipt_2_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 0) 128 128 = 1795679600645246521846396 := by decide +kernel
private theorem receipt_2_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 0) 256 27 = 52012508063226016699099 := by decide +kernel
private theorem receipt_2_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 0) 128 155 = 1847692108708472538545495 :=
  phaseBlock_append receipt_2_2_2360_0_part1 receipt_2_2_2360_0_part2 rfl rfl rfl
private theorem receipt_2_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 0) 0 283 = 6807743391340474809014327 :=
  phaseBlock_append receipt_2_2_2360_0_part0 receipt_2_2_2360_0_join0 rfl rfl rfl

private theorem receipt_2_2_2360_0 : fastPhase (bank 2 2).shape 179808 2380 2 1 0 7 0 = 6807743391340474809014327 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2360_0_join1

private theorem receipt_2_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 1) 0 128 = 4932204217921352348994400 := by decide +kernel
private theorem receipt_2_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 1) 128 128 = 1774382706731778010879929 := by decide +kernel
private theorem receipt_2_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 1) 256 27 = 48260728561822124324453 := by decide +kernel
private theorem receipt_2_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 1) 128 155 = 1822643435293600135204382 :=
  phaseBlock_append receipt_2_2_2360_1_part1 receipt_2_2_2360_1_part2 rfl rfl rfl
private theorem receipt_2_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2380 2 1 0 7 1) 0 283 = 6754847653214952484198782 :=
  phaseBlock_append receipt_2_2_2360_1_part0 receipt_2_2_2360_1_join0 rfl rfl rfl

private theorem receipt_2_2_2360_1 : fastPhase (bank 2 2).shape 179808 2380 2 1 0 7 1 = 6754847653214952484198782 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2360_1_join1

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2359_0 receipt_2_2_2359_1 receipt_2_2_2360_0 receipt_2_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2379 2 1 1 1 0) 0 128 = 476627980338370294803136 := by decide +kernel
private theorem receipt_3_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2379 2 1 1 1 0) 128 95 = 90158357341956127501328 := by decide +kernel
private theorem receipt_3_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2379 2 1 1 1 0) 0 223 = 566786337680326422304464 :=
  phaseBlock_append receipt_3_2_2359_0_part0 receipt_3_2_2359_0_part1 rfl rfl rfl

private theorem receipt_3_2_2359_0 : fastPhase (bank 3 2).shape 179808 2379 2 1 1 1 0 = 566786337680326422304464 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2359_0_join0

private theorem receipt_3_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2379 2 1 1 1 1) 0 128 = 473044086700877049880768 := by decide +kernel
private theorem receipt_3_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2379 2 1 1 1 1) 128 95 = 88180750994697486564134 := by decide +kernel
private theorem receipt_3_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2379 2 1 1 1 1) 0 223 = 561224837695574536444902 :=
  phaseBlock_append receipt_3_2_2359_1_part0 receipt_3_2_2359_1_part1 rfl rfl rfl

private theorem receipt_3_2_2359_1 : fastPhase (bank 3 2).shape 179808 2379 2 1 1 1 1 = 561224837695574536444902 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2359_1_join0

private theorem receipt_3_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2380 2 1 1 1 0) 0 128 = 476631482189787280784288 := by decide +kernel
private theorem receipt_3_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2380 2 1 1 1 0) 128 95 = 90158662138474051867192 := by decide +kernel
private theorem receipt_3_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2380 2 1 1 1 0) 0 223 = 566790144328261332651480 :=
  phaseBlock_append receipt_3_2_2360_0_part0 receipt_3_2_2360_0_part1 rfl rfl rfl

private theorem receipt_3_2_2360_0 : fastPhase (bank 3 2).shape 179808 2380 2 1 1 1 0 = 566790144328261332651480 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2360_0_join0

private theorem receipt_3_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2380 2 1 1 1 1) 0 128 = 473047559753406644779040 := by decide +kernel
private theorem receipt_3_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2380 2 1 1 1 1) 128 95 = 88181049621286441148812 := by decide +kernel
private theorem receipt_3_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2380 2 1 1 1 1) 0 223 = 561228609374693085927852 :=
  phaseBlock_append receipt_3_2_2360_1_part0 receipt_3_2_2360_1_part1 rfl rfl rfl

private theorem receipt_3_2_2360_1 : fastPhase (bank 3 2).shape 179808 2380 2 1 1 1 1 = 561228609374693085927852 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2360_1_join0

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2359_0 receipt_3_2_2359_1 receipt_3_2_2360_0 receipt_3_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 0) 0 128 = 15883955674924198267685003 := by decide +kernel
private theorem receipt_0_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 0) 128 128 = 5844950797896266189940786 := by decide +kernel
private theorem receipt_0_3_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 0) 256 26 = 161699868937747562953377 := by decide +kernel
private theorem receipt_0_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 0) 128 154 = 6006650666834013752894163 :=
  phaseBlock_append receipt_0_3_2359_0_part1 receipt_0_3_2359_0_part2 rfl rfl rfl
private theorem receipt_0_3_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 0) 0 282 = 21890606341758212020579166 :=
  phaseBlock_append receipt_0_3_2359_0_part0 receipt_0_3_2359_0_join0 rfl rfl rfl

private theorem receipt_0_3_2359_0 : fastPhase (bank 0 3).shape 179808 2379 3 1 0 1 0 = 21890606341758212020579166 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2359_0_join1

private theorem receipt_0_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 1) 0 128 = 15797362677012139143993012 := by decide +kernel
private theorem receipt_0_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 1) 128 128 = 5775874232623271027764743 := by decide +kernel
private theorem receipt_0_3_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 1) 256 26 = 149627998209448752591270 := by decide +kernel
private theorem receipt_0_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 1) 128 154 = 5925502230832719780356013 :=
  phaseBlock_append receipt_0_3_2359_1_part1 receipt_0_3_2359_1_part2 rfl rfl rfl
private theorem receipt_0_3_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2379 3 1 0 1 1) 0 282 = 21722864907844858924349025 :=
  phaseBlock_append receipt_0_3_2359_1_part0 receipt_0_3_2359_1_join0 rfl rfl rfl

private theorem receipt_0_3_2359_1 : fastPhase (bank 0 3).shape 179808 2379 3 1 0 1 1 = 21722864907844858924349025 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2359_1_join1

private theorem receipt_0_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 0) 0 128 = 15884088730985179452822007 := by decide +kernel
private theorem receipt_0_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 0) 128 128 = 5844985363475760838012656 := by decide +kernel
private theorem receipt_0_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 0) 256 26 = 161700494380909634634330 := by decide +kernel
private theorem receipt_0_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 0) 128 154 = 6006685857856670472646986 :=
  phaseBlock_append receipt_0_3_2360_0_part1 receipt_0_3_2360_0_part2 rfl rfl rfl
private theorem receipt_0_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 0) 0 282 = 21890774588841849925468993 :=
  phaseBlock_append receipt_0_3_2360_0_part0 receipt_0_3_2360_0_join0 rfl rfl rfl

private theorem receipt_0_3_2360_0 : fastPhase (bank 0 3).shape 179808 2380 3 1 0 1 0 = 21890774588841849925468993 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2360_0_join1

private theorem receipt_0_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 1) 0 128 = 15797495133216219174482265 := by decide +kernel
private theorem receipt_0_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 1) 128 128 = 5775908448160259333882148 := by decide +kernel
private theorem receipt_0_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 1) 256 26 = 149628579002367694325136 := by decide +kernel
private theorem receipt_0_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 1) 128 154 = 5925537027162627028207284 :=
  phaseBlock_append receipt_0_3_2360_1_part1 receipt_0_3_2360_1_part2 rfl rfl rfl
private theorem receipt_0_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2380 3 1 0 1 1) 0 282 = 21723032160378846202689549 :=
  phaseBlock_append receipt_0_3_2360_1_part0 receipt_0_3_2360_1_join0 rfl rfl rfl

private theorem receipt_0_3_2360_1 : fastPhase (bank 0 3).shape 179808 2380 3 1 0 1 1 = 21723032160378846202689549 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2360_1_join1

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2359_0 receipt_0_3_2359_1 receipt_0_3_2360_0 receipt_0_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 0) 0 128 = 14258322886215548992834313 := by decide +kernel
private theorem receipt_1_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 0) 128 128 = 5234620888499586283612236 := by decide +kernel
private theorem receipt_1_3_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 0) 256 26 = 144564504392189443002327 := by decide +kernel
private theorem receipt_1_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 0) 128 154 = 5379185392891775726614563 :=
  phaseBlock_append receipt_1_3_2359_0_part1 receipt_1_3_2359_0_part2 rfl rfl rfl
private theorem receipt_1_3_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 0) 0 282 = 19637508279107324719448876 :=
  phaseBlock_append receipt_1_3_2359_0_part0 receipt_1_3_2359_0_join0 rfl rfl rfl

private theorem receipt_1_3_2359_0 : fastPhase (bank 1 3).shape 179808 2379 3 1 0 2 0 = 19637508279107324719448876 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2359_0_join1

private theorem receipt_1_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 1) 0 128 = 14180325362952370797908138 := by decide +kernel
private theorem receipt_1_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 1) 128 128 = 5172673214779558487156055 := by decide +kernel
private theorem receipt_1_3_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 1) 256 26 = 133770146573820574879800 := by decide +kernel
private theorem receipt_1_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 1) 128 154 = 5306443361353379062035855 :=
  phaseBlock_append receipt_1_3_2359_1_part1 receipt_1_3_2359_1_part2 rfl rfl rfl
private theorem receipt_1_3_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2379 3 1 0 2 1) 0 282 = 19486768724305749859943993 :=
  phaseBlock_append receipt_1_3_2359_1_part0 receipt_1_3_2359_1_join0 rfl rfl rfl

private theorem receipt_1_3_2359_1 : fastPhase (bank 1 3).shape 179808 2379 3 1 0 2 1 = 19486768724305749859943993 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2359_1_join1

private theorem receipt_1_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 0) 0 128 = 14258442331805289048584060 := by decide +kernel
private theorem receipt_1_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 0) 128 128 = 5234651847272037228263833 := by decide +kernel
private theorem receipt_1_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 0) 256 26 = 144565063559653606202873 := by decide +kernel
private theorem receipt_1_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 0) 128 154 = 5379216910831690834466706 :=
  phaseBlock_append receipt_1_3_2360_0_part1 receipt_1_3_2360_0_part2 rfl rfl rfl
private theorem receipt_1_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 0) 0 282 = 19637659242636979883050766 :=
  phaseBlock_append receipt_1_3_2360_0_part0 receipt_1_3_2360_0_join0 rfl rfl rfl

private theorem receipt_1_3_2360_0 : fastPhase (bank 1 3).shape 179808 2380 3 1 0 2 0 = 19637659242636979883050766 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2360_0_join1

private theorem receipt_1_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 1) 0 128 = 14180444267801689906041853 := by decide +kernel
private theorem receipt_1_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 1) 128 128 = 5172703859522117969242854 := by decide +kernel
private theorem receipt_1_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 1) 256 26 = 133770665815480953200409 := by decide +kernel
private theorem receipt_1_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 1) 128 154 = 5306474525337598922443263 :=
  phaseBlock_append receipt_1_3_2360_1_part1 receipt_1_3_2360_1_part2 rfl rfl rfl
private theorem receipt_1_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2380 3 1 0 2 1) 0 282 = 19486918793139288828485116 :=
  phaseBlock_append receipt_1_3_2360_1_part0 receipt_1_3_2360_1_join0 rfl rfl rfl

private theorem receipt_1_3_2360_1 : fastPhase (bank 1 3).shape 179808 2380 3 1 0 2 1 = 19486918793139288828485116 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2360_1_join1

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2359_0 receipt_1_3_2359_1 receipt_1_3_2360_0 receipt_1_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 0) 0 128 = 7481214639131125297066145 := by decide +kernel
private theorem receipt_2_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 0) 128 128 = 2700428535939094567867065 := by decide +kernel
private theorem receipt_2_3_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 0) 256 26 = 73630067645870076463695 := by decide +kernel
private theorem receipt_2_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 0) 128 154 = 2774058603584964644330760 :=
  phaseBlock_append receipt_2_3_2359_0_part1 receipt_2_3_2359_0_part2 rfl rfl rfl
private theorem receipt_2_3_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 0) 0 282 = 10255273242716089941396905 :=
  phaseBlock_append receipt_2_3_2359_0_part0 receipt_2_3_2359_0_join0 rfl rfl rfl

private theorem receipt_2_3_2359_0 : fastPhase (bank 2 3).shape 179808 2379 3 1 0 7 0 = 10255273242716089941396905 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2359_0_join1

private theorem receipt_2_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 1) 0 128 = 7439270693121533240076713 := by decide +kernel
private theorem receipt_2_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 1) 128 128 = 2668152100410868369715346 := by decide +kernel
private theorem receipt_2_3_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 1) 256 26 = 68125665872129098350615 := by decide +kernel
private theorem receipt_2_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 1) 128 154 = 2736277766282997468065961 :=
  phaseBlock_append receipt_2_3_2359_1_part1 receipt_2_3_2359_1_part2 rfl rfl rfl
private theorem receipt_2_3_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2379 3 1 0 7 1) 0 282 = 10175548459404530708142674 :=
  phaseBlock_append receipt_2_3_2359_1_part0 receipt_2_3_2359_1_join0 rfl rfl rfl

private theorem receipt_2_3_2359_1 : fastPhase (bank 2 3).shape 179808 2379 3 1 0 7 1 = 10175548459404530708142674 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2359_1_join1

private theorem receipt_2_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 0) 0 128 = 7481277338134009174680929 := by decide +kernel
private theorem receipt_2_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 0) 128 128 = 2700444516499562240921971 := by decide +kernel
private theorem receipt_2_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 0) 256 26 = 73630352452787000033384 := by decide +kernel
private theorem receipt_2_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 0) 128 154 = 2774074868952349240955355 :=
  phaseBlock_append receipt_2_3_2360_0_part1 receipt_2_3_2360_0_part2 rfl rfl rfl
private theorem receipt_2_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 0) 0 282 = 10255352207086358415636284 :=
  phaseBlock_append receipt_2_3_2360_0_part0 receipt_2_3_2360_0_join0 rfl rfl rfl

private theorem receipt_2_3_2360_0 : fastPhase (bank 2 3).shape 179808 2380 3 1 0 7 0 = 10255352207086358415636284 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2360_0_join1

private theorem receipt_2_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 1) 0 128 = 7439333099707854147509884 := by decide +kernel
private theorem receipt_2_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 1) 128 128 = 2668167916925563821061293 := by decide +kernel
private theorem receipt_2_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 1) 256 26 = 68125930316914681212909 := by decide +kernel
private theorem receipt_2_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 1) 128 154 = 2736293847242478502274202 :=
  phaseBlock_append receipt_2_3_2360_1_part1 receipt_2_3_2360_1_part2 rfl rfl rfl
private theorem receipt_2_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2380 3 1 0 7 1) 0 282 = 10175626946950332649784086 :=
  phaseBlock_append receipt_2_3_2360_1_part0 receipt_2_3_2360_1_join0 rfl rfl rfl

private theorem receipt_2_3_2360_1 : fastPhase (bank 2 3).shape 179808 2380 3 1 0 7 1 = 10175626946950332649784086 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2360_1_join1

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2359_0 receipt_2_3_2359_1 receipt_2_3_2360_0 receipt_2_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2379 3 1 1 1 0) 0 128 = 704702781283292379620480 := by decide +kernel
private theorem receipt_3_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2379 3 1 1 1 0) 128 110 = 164043088031244107845698 := by decide +kernel
private theorem receipt_3_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2379 3 1 1 1 0) 0 238 = 868745869314536487466178 :=
  phaseBlock_append receipt_3_3_2359_0_part0 receipt_3_3_2359_0_part1 rfl rfl rfl

private theorem receipt_3_3_2359_0 : fastPhase (bank 3 3).shape 179808 2379 3 1 1 1 0 = 868745869314536487466178 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2359_0_join0

private theorem receipt_3_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2379 3 1 1 1 1) 0 128 = 699836458592598941944832 := by decide +kernel
private theorem receipt_3_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2379 3 1 1 1 1) 128 110 = 160920159069492132779436 := by decide +kernel
private theorem receipt_3_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2379 3 1 1 1 1) 0 238 = 860756617662091074724268 :=
  phaseBlock_append receipt_3_3_2359_1_part0 receipt_3_3_2359_1_part1 rfl rfl rfl

private theorem receipt_3_3_2359_1 : fastPhase (bank 3 3).shape 179808 2379 3 1 1 1 1 = 860756617662091074724268 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2359_1_join0

private theorem receipt_3_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2380 3 1 1 1 0) 0 128 = 704708011919908427992384 := by decide +kernel
private theorem receipt_3_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2380 3 1 1 1 0) 128 110 = 164043671336164646114748 := by decide +kernel
private theorem receipt_3_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2380 3 1 1 1 0) 0 238 = 868751683256073074107132 :=
  phaseBlock_append receipt_3_3_2360_0_part0 receipt_3_3_2360_0_part1 rfl rfl rfl

private theorem receipt_3_3_2360_0 : fastPhase (bank 3 3).shape 179808 2380 3 1 1 1 0 = 868751683256073074107132 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2360_0_join0

private theorem receipt_3_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2380 3 1 1 1 1) 0 128 = 699841649434074346353664 := by decide +kernel
private theorem receipt_3_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2380 3 1 1 1 1) 128 110 = 160920732138262758404688 := by decide +kernel
private theorem receipt_3_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2380 3 1 1 1 1) 0 238 = 860762381572337104758352 :=
  phaseBlock_append receipt_3_3_2360_1_part0 receipt_3_3_2360_1_part1 rfl rfl rfl

private theorem receipt_3_3_2360_1 : fastPhase (bank 3 3).shape 179808 2380 3 1 1 1 1 = 860762381572337104758352 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2360_1_join0

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2359_0 receipt_3_3_2359_1 receipt_3_3_2360_0 receipt_3_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 0) 0 128 = 24025473186265658899015532 := by decide +kernel
private theorem receipt_0_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 0) 128 128 = 9436525133082389594763334 := by decide +kernel
private theorem receipt_0_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 0) 256 36 = 447481569935240874118190 := by decide +kernel
private theorem receipt_0_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 0) 128 164 = 9884006703017630468881524 :=
  phaseBlock_append receipt_0_4_2359_0_part1 receipt_0_4_2359_0_part2 rfl rfl rfl
private theorem receipt_0_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 0) 0 292 = 33909479889283289367897056 :=
  phaseBlock_append receipt_0_4_2359_0_part0 receipt_0_4_2359_0_join0 rfl rfl rfl

private theorem receipt_0_4_2359_0 : fastPhase (bank 0 4).shape 179808 2379 4 1 0 1 0 = 33909479889283289367897056 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2359_0_join1

private theorem receipt_0_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 1) 0 128 = 23900351265617590204049502 := by decide +kernel
private theorem receipt_0_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 1) 128 128 = 9335479998469596910643242 := by decide +kernel
private theorem receipt_0_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 1) 256 36 = 423041829913857417541586 := by decide +kernel
private theorem receipt_0_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 1) 128 164 = 9758521828383454328184828 :=
  phaseBlock_append receipt_0_4_2359_1_part1 receipt_0_4_2359_1_part2 rfl rfl rfl
private theorem receipt_0_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2379 4 1 0 1 1) 0 292 = 33658873094001044532234330 :=
  phaseBlock_append receipt_0_4_2359_1_part0 receipt_0_4_2359_1_join0 rfl rfl rfl

private theorem receipt_0_4_2359_1 : fastPhase (bank 0 4).shape 179808 2379 4 1 0 1 1 = 33658873094001044532234330 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2359_1_join1

private theorem receipt_0_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 0) 0 128 = 24025674332916044609053124 := by decide +kernel
private theorem receipt_0_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 0) 128 128 = 9436581950807838022421940 := by decide +kernel
private theorem receipt_0_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 0) 256 36 = 447483383302197175596229 := by decide +kernel
private theorem receipt_0_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 0) 128 164 = 9884065334110035198018169 :=
  phaseBlock_append receipt_0_4_2360_0_part1 receipt_0_4_2360_0_part2 rfl rfl rfl
private theorem receipt_0_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 0) 0 292 = 33909739667026079807071293 :=
  phaseBlock_append receipt_0_4_2360_0_part0 receipt_0_4_2360_0_join0 rfl rfl rfl

private theorem receipt_0_4_2360_0 : fastPhase (bank 0 4).shape 179808 2380 4 1 0 1 0 = 33909739667026079807071293 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2360_0_join1

private theorem receipt_0_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 1) 0 128 = 23900551543638638178401856 := by decide +kernel
private theorem receipt_0_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 1) 128 128 = 9335536291588852773127032 := by decide +kernel
private theorem receipt_0_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 1) 256 36 = 423043549729406804446017 := by decide +kernel
private theorem receipt_0_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 1) 128 164 = 9758579841318259577573049 :=
  phaseBlock_append receipt_0_4_2360_1_part1 receipt_0_4_2360_1_part2 rfl rfl rfl
private theorem receipt_0_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2380 4 1 0 1 1) 0 292 = 33659131384956897755974905 :=
  phaseBlock_append receipt_0_4_2360_1_part0 receipt_0_4_2360_1_join0 rfl rfl rfl

private theorem receipt_0_4_2360_1 : fastPhase (bank 0 4).shape 179808 2380 4 1 0 1 1 = 33659131384956897755974905 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2360_1_join1

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2359_0 receipt_0_4_2359_1 receipt_0_4_2360_0 receipt_0_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 0) 0 128 = 21635232185305664901555944 := by decide +kernel
private theorem receipt_1_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 0) 128 128 = 8480376582520964000596648 := by decide +kernel
private theorem receipt_1_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 0) 256 36 = 401521071925254599251076 := by decide +kernel
private theorem receipt_1_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 0) 128 164 = 8881897654446218599847724 :=
  phaseBlock_append receipt_1_4_2359_0_part1 receipt_1_4_2359_0_part2 rfl rfl rfl
private theorem receipt_1_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 0) 0 292 = 30517129839751883501403668 :=
  phaseBlock_append receipt_1_4_2359_0_part0 receipt_1_4_2359_0_join0 rfl rfl rfl

private theorem receipt_1_4_2359_0 : fastPhase (bank 1 4).shape 179808 2379 4 1 0 2 0 = 30517129839751883501403668 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2359_0_join1

private theorem receipt_1_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 1) 0 128 = 21522203809140738298530021 := by decide +kernel
private theorem receipt_1_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 1) 128 128 = 8389446381768757107517057 := by decide +kernel
private theorem receipt_1_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 1) 256 36 = 379587190833975118075865 := by decide +kernel
private theorem receipt_1_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 1) 128 164 = 8769033572602732225592922 :=
  phaseBlock_append receipt_1_4_2359_1_part1 receipt_1_4_2359_1_part2 rfl rfl rfl
private theorem receipt_1_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2379 4 1 0 2 1) 0 292 = 30291237381743470524122943 :=
  phaseBlock_append receipt_1_4_2359_1_part0 receipt_1_4_2359_1_join0 rfl rfl rfl

private theorem receipt_1_4_2359_1 : fastPhase (bank 1 4).shape 179808 2379 4 1 0 2 1 = 30291237381743470524122943 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2359_1_join1

private theorem receipt_1_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 0) 0 128 = 21635413329163735113648368 := by decide +kernel
private theorem receipt_1_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 0) 128 128 = 8480427646746959248276944 := by decide +kernel
private theorem receipt_1_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 0) 256 36 = 401522699054114066111782 := by decide +kernel
private theorem receipt_1_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 0) 128 164 = 8881950345801073314388726 :=
  phaseBlock_append receipt_1_4_2360_0_part1 receipt_1_4_2360_0_part2 rfl rfl rfl
private theorem receipt_1_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 0) 0 292 = 30517363674964808428037094 :=
  phaseBlock_append receipt_1_4_2360_0_part0 receipt_1_4_2360_0_join0 rfl rfl rfl

private theorem receipt_1_4_2360_0 : fastPhase (bank 1 4).shape 179808 2380 4 1 0 2 0 = 30517363674964808428037094 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2360_0_join1

private theorem receipt_1_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 1) 0 128 = 21522384167770847425579053 := by decide +kernel
private theorem receipt_1_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 1) 128 128 = 8389496973751968035479245 := by decide +kernel
private theorem receipt_1_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 1) 256 36 = 379588734001208984733285 := by decide +kernel
private theorem receipt_1_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 1) 128 164 = 8769085707753177020212530 :=
  phaseBlock_append receipt_1_4_2360_1_part1 receipt_1_4_2360_1_part2 rfl rfl rfl
private theorem receipt_1_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2380 4 1 0 2 1) 0 292 = 30291469875524024445791583 :=
  phaseBlock_append receipt_1_4_2360_1_part0 receipt_1_4_2360_1_join0 rfl rfl rfl

private theorem receipt_1_4_2360_1 : fastPhase (bank 1 4).shape 179808 2380 4 1 0 2 1 = 30291469875524024445791583 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2360_1_join1

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2359_0 receipt_1_4_2359_1 receipt_1_4_2360_0 receipt_1_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 0) 0 128 = 11607603580392621159537227 := by decide +kernel
private theorem receipt_2_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 0) 128 128 = 4483270290755871827645052 := by decide +kernel
private theorem receipt_2_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 0) 256 36 = 209900750022461748010008 := by decide +kernel
private theorem receipt_2_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 0) 128 164 = 4693171040778333575655060 :=
  phaseBlock_append receipt_2_4_2359_0_part1 receipt_2_4_2359_0_part2 rfl rfl rfl
private theorem receipt_2_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 0) 0 292 = 16300774621170954735192287 :=
  phaseBlock_append receipt_2_4_2359_0_part0 receipt_2_4_2359_0_join0 rfl rfl rfl

private theorem receipt_2_4_2359_0 : fastPhase (bank 2 4).shape 179808 2379 4 1 0 7 0 = 16300774621170954735192287 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2359_0_join1

private theorem receipt_2_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 1) 0 128 = 11545594658718296196911204 := by decide +kernel
private theorem receipt_2_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 1) 128 128 = 4434725774721485798547096 := by decide +kernel
private theorem receipt_2_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 1) 256 36 = 198417993269519337216882 := by decide +kernel
private theorem receipt_2_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 1) 128 164 = 4633143767991005135763978 :=
  phaseBlock_append receipt_2_4_2359_1_part1 receipt_2_4_2359_1_part2 rfl rfl rfl
private theorem receipt_2_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2379 4 1 0 7 1) 0 292 = 16178738426709301332675182 :=
  phaseBlock_append receipt_2_4_2359_1_part0 receipt_2_4_2359_1_join0 rfl rfl rfl

private theorem receipt_2_4_2359_1 : fastPhase (bank 2 4).shape 179808 2379 4 1 0 7 1 = 16178738426709301332675182 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2359_1_join1

private theorem receipt_2_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 0) 0 128 = 11607700800690642280999330 := by decide +kernel
private theorem receipt_2_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 0) 128 128 = 4483297300031378910508662 := by decide +kernel
private theorem receipt_2_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 0) 256 36 = 209901600670548085070304 := by decide +kernel
private theorem receipt_2_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 0) 128 164 = 4693198900701926995578966 :=
  phaseBlock_append receipt_2_4_2360_0_part1 receipt_2_4_2360_0_part2 rfl rfl rfl
private theorem receipt_2_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 0) 0 292 = 16300899701392569276578296 :=
  phaseBlock_append receipt_2_4_2360_0_part0 receipt_2_4_2360_0_join0 rfl rfl rfl

private theorem receipt_2_4_2360_0 : fastPhase (bank 2 4).shape 179808 2380 4 1 0 7 0 = 16300899701392569276578296 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2360_0_join1

private theorem receipt_2_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 1) 0 128 = 11545691446092369213130033 := by decide +kernel
private theorem receipt_2_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 1) 128 128 = 4434752531302787598646893 := by decide +kernel
private theorem receipt_2_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 1) 256 36 = 198418799953715180181762 := by decide +kernel
private theorem receipt_2_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 1) 128 164 = 4633171331256502778828655 :=
  phaseBlock_append receipt_2_4_2360_1_part1 receipt_2_4_2360_1_part2 rfl rfl rfl
private theorem receipt_2_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2380 4 1 0 7 1) 0 292 = 16178862777348871991958688 :=
  phaseBlock_append receipt_2_4_2360_1_part0 receipt_2_4_2360_1_join0 rfl rfl rfl

private theorem receipt_2_4_2360_1 : fastPhase (bank 2 4).shape 179808 2380 4 1 0 7 1 = 16178862777348871991958688 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2360_1_join1

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2359_0 receipt_2_4_2359_1 receipt_2_4_2360_0 receipt_2_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 0) 0 128 = 1639573293717826418559168 := by decide +kernel
private theorem receipt_3_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 0) 128 128 = 662055773523073742391488 := by decide +kernel
private theorem receipt_3_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 0) 256 47 = 45909211416904597881672 := by decide +kernel
private theorem receipt_3_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 0) 128 175 = 707964984939978340273160 :=
  phaseBlock_append receipt_3_4_2359_0_part1 receipt_3_4_2359_0_part2 rfl rfl rfl
private theorem receipt_3_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 0) 0 303 = 2347538278657804758832328 :=
  phaseBlock_append receipt_3_4_2359_0_part0 receipt_3_4_2359_0_join0 rfl rfl rfl

private theorem receipt_3_4_2359_0 : fastPhase (bank 3 4).shape 179808 2379 4 1 1 1 0 = 2347538278657804758832328 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2359_0_join1

private theorem receipt_3_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 1) 0 128 = 1631141329451621339265536 := by decide +kernel
private theorem receipt_3_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 1) 128 128 = 655394635114018011732480 := by decide +kernel
private theorem receipt_3_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 1) 256 47 = 43953038444885611945020 := by decide +kernel
private theorem receipt_3_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 1) 128 175 = 699347673558903623677500 :=
  phaseBlock_append receipt_3_4_2359_1_part1 receipt_3_4_2359_1_part2 rfl rfl rfl
private theorem receipt_3_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2379 4 1 1 1 1) 0 303 = 2330489003010524962943036 :=
  phaseBlock_append receipt_3_4_2359_1_part0 receipt_3_4_2359_1_join0 rfl rfl rfl

private theorem receipt_3_4_2359_1 : fastPhase (bank 3 4).shape 179808 2379 4 1 1 1 1 = 2330489003010524962943036 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2359_1_join1

private theorem receipt_3_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 0) 0 128 = 1639585902536718885651264 := by decide +kernel
private theorem receipt_3_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 0) 128 128 = 662058574343179502158656 := by decide +kernel
private theorem receipt_3_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 0) 256 47 = 45909290262043922181944 := by decide +kernel
private theorem receipt_3_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 0) 128 175 = 707967864605223424340600 :=
  phaseBlock_append receipt_3_4_2360_0_part1 receipt_3_4_2360_0_part2 rfl rfl rfl
private theorem receipt_3_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 0) 0 303 = 2347553767141942309991864 :=
  phaseBlock_append receipt_3_4_2360_0_part0 receipt_3_4_2360_0_join0 rfl rfl rfl

private theorem receipt_3_4_2360_0 : fastPhase (bank 3 4).shape 179808 2380 4 1 1 1 0 = 2347553767141942309991864 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2360_0_join1

private theorem receipt_3_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 1) 0 128 = 1631153865396421315767104 := by decide +kernel
private theorem receipt_3_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 1) 128 128 = 655397406872695229279040 := by decide +kernel
private theorem receipt_3_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 1) 256 47 = 43953114151139522038360 := by decide +kernel
private theorem receipt_3_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 1) 128 175 = 699350521023834751317400 :=
  phaseBlock_append receipt_3_4_2360_1_part1 receipt_3_4_2360_1_part2 rfl rfl rfl
private theorem receipt_3_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2380 4 1 1 1 1) 0 303 = 2330504386420256067084504 :=
  phaseBlock_append receipt_3_4_2360_1_part0 receipt_3_4_2360_1_join0 rfl rfl rfl

private theorem receipt_3_4_2360_1 : fastPhase (bank 3 4).shape 179808 2380 4 1 1 1 1 = 2330504386420256067084504 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2360_1_join1

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2359_0 receipt_3_4_2359_1 receipt_3_4_2360_0 receipt_3_4_2360_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 4) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group1_stage i)).shape
      (cutoff h rect (group1_stage i)), ¬ G∣Q :=
  (group1_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group1_avoids

end Lower6960.RescueSource
