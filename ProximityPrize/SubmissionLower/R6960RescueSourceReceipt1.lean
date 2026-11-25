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

private theorem receipt_0_1_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 0) 0 128 = 6990081697274675837656806 := by decide +kernel
private theorem receipt_0_1_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 0) 128 128 = 2569474736826122391662374 := by decide +kernel
private theorem receipt_0_1_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 0) 256 26 = 71027887658445084781336 := by decide +kernel
private theorem receipt_0_1_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 0) 128 154 = 2640502624484567476443710 :=
  phaseBlock_append receipt_0_1_2383_0_part1 receipt_0_1_2383_0_part2 rfl rfl rfl
private theorem receipt_0_1_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 0) 0 282 = 9630584321759243314100516 :=
  phaseBlock_append receipt_0_1_2383_0_part0 receipt_0_1_2383_0_join0 rfl rfl rfl

private theorem receipt_0_1_2383_0 : fastPhase (bank 0 1).shape 179808 2383 1 1 0 1 0 = 9630584321759243314100516 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2383_0_join1

private theorem receipt_0_1_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 1) 0 128 = 6951915407452096938581698 := by decide +kernel
private theorem receipt_0_1_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 1) 128 128 = 2539089663918696197560942 := by decide +kernel
private theorem receipt_0_1_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 1) 256 26 = 65724842416186989973268 := by decide +kernel
private theorem receipt_0_1_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 1) 128 154 = 2604814506334883187534210 :=
  phaseBlock_append receipt_0_1_2383_1_part1 receipt_0_1_2383_1_part2 rfl rfl rfl
private theorem receipt_0_1_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2383 1 1 0 1 1) 0 282 = 9556729913786980126115908 :=
  phaseBlock_append receipt_0_1_2383_1_part0 receipt_0_1_2383_1_join0 rfl rfl rfl

private theorem receipt_0_1_2383_1 : fastPhase (bank 0 1).shape 179808 2383 1 1 0 1 1 = 9556729913786980126115908 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2383_1_join1

private theorem receipt_0_1_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 0) 0 128 = 6990140637020751450199311 := by decide +kernel
private theorem receipt_0_1_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 0) 128 128 = 2569490079751158249668379 := by decide +kernel
private theorem receipt_0_1_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 0) 256 26 = 71028166595956777795132 := by decide +kernel
private theorem receipt_0_1_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 0) 128 154 = 2640518246347115027463511 :=
  phaseBlock_append receipt_0_1_2384_0_part1 receipt_0_1_2384_0_part2 rfl rfl rfl
private theorem receipt_0_1_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 0) 0 282 = 9630658883367866477662822 :=
  phaseBlock_append receipt_0_1_2384_0_part0 receipt_0_1_2384_0_join0 rfl rfl rfl

private theorem receipt_0_1_2384_0 : fastPhase (bank 0 1).shape 179808 2384 1 1 0 1 0 = 9630658883367866477662822 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2384_0_join1

private theorem receipt_0_1_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 1) 0 128 = 6951974080792872425957693 := by decide +kernel
private theorem receipt_0_1_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 1) 128 128 = 2539104851155953556162263 := by decide +kernel
private theorem receipt_0_1_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 1) 256 26 = 65725101421565040668568 := by decide +kernel
private theorem receipt_0_1_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 1) 128 154 = 2604829952577518596830831 :=
  phaseBlock_append receipt_0_1_2384_1_part1 receipt_0_1_2384_1_part2 rfl rfl rfl
private theorem receipt_0_1_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179808 2384 1 1 0 1 1) 0 282 = 9556804033370391022788524 :=
  phaseBlock_append receipt_0_1_2384_1_part0 receipt_0_1_2384_1_join0 rfl rfl rfl

private theorem receipt_0_1_2384_1 : fastPhase (bank 0 1).shape 179808 2384 1 1 0 1 1 = 9556804033370391022788524 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2384_1_join1

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2383_0 receipt_0_1_2383_1 receipt_0_1_2384_0 receipt_0_1_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 0) 0 128 = 6273621395146480288770097 := by decide +kernel
private theorem receipt_1_1_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 0) 128 128 = 2298069686440461128576005 := by decide +kernel
private theorem receipt_1_1_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 0) 256 26 = 63359341075380137520266 := by decide +kernel
private theorem receipt_1_1_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 0) 128 154 = 2361429027515841266096271 :=
  phaseBlock_append receipt_1_1_2383_0_part1 receipt_1_1_2383_0_part2 rfl rfl rfl
private theorem receipt_1_1_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 0) 0 282 = 8635050422662321554866368 :=
  phaseBlock_append receipt_1_1_2383_0_part0 receipt_1_1_2383_0_join0 rfl rfl rfl

private theorem receipt_1_1_2383_0 : fastPhase (bank 1 1).shape 179808 2383 1 1 0 2 0 = 8635050422662321554866368 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2383_0_join1

private theorem receipt_1_1_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 1) 0 128 = 6239190004159078513687874 := by decide +kernel
private theorem receipt_1_1_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 1) 128 128 = 2270838334077132231539003 := by decide +kernel
private theorem receipt_1_1_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 1) 256 26 = 58627683862998894232306 := by decide +kernel
private theorem receipt_1_1_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 1) 128 154 = 2329466017940131125771309 :=
  phaseBlock_append receipt_1_1_2383_1_part1 receipt_1_1_2383_1_part2 rfl rfl rfl
private theorem receipt_1_1_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2383 1 1 0 2 1) 0 282 = 8568656022099209639459183 :=
  phaseBlock_append receipt_1_1_2383_1_part0 receipt_1_1_2383_1_join0 rfl rfl rfl

private theorem receipt_1_1_2383_1 : fastPhase (bank 1 1).shape 179808 2383 1 1 0 2 1 = 8568656022099209639459183 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2383_1_join1

private theorem receipt_1_1_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 0) 0 128 = 6273674298452106922235361 := by decide +kernel
private theorem receipt_1_1_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 0) 128 128 = 2298083410419188674433768 := by decide +kernel
private theorem receipt_1_1_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 0) 256 26 = 63359589899051721280918 := by decide +kernel
private theorem receipt_1_1_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 0) 128 154 = 2361443000318240395714686 :=
  phaseBlock_append receipt_1_1_2384_0_part1 receipt_1_1_2384_0_part2 rfl rfl rfl
private theorem receipt_1_1_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 0) 0 282 = 8635117298770347317950047 :=
  phaseBlock_append receipt_1_1_2384_0_part0 receipt_1_1_2384_0_join0 rfl rfl rfl

private theorem receipt_1_1_2384_0 : fastPhase (bank 1 1).shape 179808 2384 1 1 0 2 0 = 8635117298770347317950047 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2384_0_join1

private theorem receipt_1_1_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 1) 0 128 = 6239242666845666242098498 := by decide +kernel
private theorem receipt_1_1_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 1) 128 128 = 2270851918452418247720020 := by decide +kernel
private theorem receipt_1_1_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 1) 256 26 = 58627914901707500378486 := by decide +kernel
private theorem receipt_1_1_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 1) 128 154 = 2329479833354125748098506 :=
  phaseBlock_append receipt_1_1_2384_1_part1 receipt_1_1_2384_1_part2 rfl rfl rfl
private theorem receipt_1_1_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179808 2384 1 1 0 2 1) 0 282 = 8568722500199791990197004 :=
  phaseBlock_append receipt_1_1_2384_1_part0 receipt_1_1_2384_1_join0 rfl rfl rfl

private theorem receipt_1_1_2384_1 : fastPhase (bank 1 1).shape 179808 2384 1 1 0 2 1 = 8568722500199791990197004 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2384_1_join1

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2383_0 receipt_1_1_2383_1 receipt_1_1_2384_0 receipt_1_1_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 0) 0 128 = 3295613903234222605092337 := by decide +kernel
private theorem receipt_2_1_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 0) 128 128 = 1176689341553167002307390 := by decide +kernel
private theorem receipt_2_1_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 0) 256 26 = 31817267636125577378486 := by decide +kernel
private theorem receipt_2_1_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 0) 128 154 = 1208506609189292579685876 :=
  phaseBlock_append receipt_2_1_2383_0_part1 receipt_2_1_2383_0_part2 rfl rfl rfl
private theorem receipt_2_1_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 0) 0 282 = 4504120512423515184778213 :=
  phaseBlock_append receipt_2_1_2383_0_part0 receipt_2_1_2383_0_join0 rfl rfl rfl

private theorem receipt_2_1_2383_0 : fastPhase (bank 2 1).shape 179808 2383 1 1 0 7 0 = 4504120512423515184778213 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2383_0_join1

private theorem receipt_2_1_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 1) 0 128 = 3276850163591000715222224 := by decide +kernel
private theorem receipt_2_1_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 1) 128 128 = 1162535171163722345791298 := by decide +kernel
private theorem receipt_2_1_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 1) 256 26 = 29436826634529155757496 := by decide +kernel
private theorem receipt_2_1_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 1) 128 154 = 1191971997798251501548794 :=
  phaseBlock_append receipt_2_1_2383_1_part1 receipt_2_1_2383_1_part2 rfl rfl rfl
private theorem receipt_2_1_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2383 1 1 0 7 1) 0 282 = 4468822161389252216771018 :=
  phaseBlock_append receipt_2_1_2383_1_part0 receipt_2_1_2383_1_join0 rfl rfl rfl

private theorem receipt_2_1_2383_1 : fastPhase (bank 2 1).shape 179808 2383 1 1 0 7 1 = 4468822161389252216771018 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2383_1_join1

private theorem receipt_2_1_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 0) 0 128 = 3295641711929744515887906 := by decide +kernel
private theorem receipt_2_1_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 0) 128 128 = 1176696375020895279441968 := by decide +kernel
private theorem receipt_2_1_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 0) 256 26 = 31817392594811379785068 := by decide +kernel
private theorem receipt_2_1_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 0) 128 154 = 1208513767615706659227036 :=
  phaseBlock_append receipt_2_1_2384_0_part1 receipt_2_1_2384_0_part2 rfl rfl rfl
private theorem receipt_2_1_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 0) 0 282 = 4504155479545451175114942 :=
  phaseBlock_append receipt_2_1_2384_0_part0 receipt_2_1_2384_0_join0 rfl rfl rfl

private theorem receipt_2_1_2384_0 : fastPhase (bank 2 1).shape 179808 2384 1 1 0 7 0 = 4504155479545451175114942 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2384_0_join1

private theorem receipt_2_1_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 1) 0 128 = 3276877840077724646160523 := by decide +kernel
private theorem receipt_2_1_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 1) 128 128 = 1162542131786433184054660 := by decide +kernel
private theorem receipt_2_1_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 1) 256 26 = 29436942644085552131276 := by decide +kernel
private theorem receipt_2_1_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 1) 128 154 = 1191979074430518736185936 :=
  phaseBlock_append receipt_2_1_2384_1_part1 receipt_2_1_2384_1_part2 rfl rfl rfl
private theorem receipt_2_1_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179808 2384 1 1 0 7 1) 0 282 = 4468856914508243382346459 :=
  phaseBlock_append receipt_2_1_2384_1_part0 receipt_2_1_2384_1_join0 rfl rfl rfl

private theorem receipt_2_1_2384_1 : fastPhase (bank 2 1).shape 179808 2384 1 1 0 7 1 = 4468856914508243382346459 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2384_1_join1

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2383_0 receipt_2_1_2383_1 receipt_2_1_2384_0 receipt_2_1_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2383 1 1 1 1 0) 0 128 = 308252075714503210588896 := by decide +kernel
private theorem receipt_3_1_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2383 1 1 1 1 0) 128 80 = 45417934316212248944556 := by decide +kernel
private theorem receipt_3_1_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2383 1 1 1 1 0) 0 208 = 353670010030715459533452 :=
  phaseBlock_append receipt_3_1_2383_0_part0 receipt_3_1_2383_0_part1 rfl rfl rfl

private theorem receipt_3_1_2383_0 : fastPhase (bank 3 1).shape 179808 2383 1 1 1 1 0 = 353670010030715459533452 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2383_0_join0

private theorem receipt_3_1_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2383 1 1 1 1 1) 0 128 = 305708294803736139153504 := by decide +kernel
private theorem receipt_3_1_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2383 1 1 1 1 1) 128 80 = 44242115864363056114524 := by decide +kernel
private theorem receipt_3_1_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2383 1 1 1 1 1) 0 208 = 349950410668099195268028 :=
  phaseBlock_append receipt_3_1_2383_1_part0 receipt_3_1_2383_1_part1 rfl rfl rfl

private theorem receipt_3_1_2383_1 : fastPhase (bank 3 1).shape 179808 2383 1 1 1 1 1 = 349950410668099195268028 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2383_1_join0

private theorem receipt_3_1_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2384 1 1 1 1 0) 0 128 = 308254316097186297884448 := by decide +kernel
private theorem receipt_3_1_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2384 1 1 1 1 0) 128 80 = 45418078838343138558228 := by decide +kernel
private theorem receipt_3_1_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2384 1 1 1 1 0) 0 208 = 353672394935529436442676 :=
  phaseBlock_append receipt_3_1_2384_0_part0 receipt_3_1_2384_0_part1 rfl rfl rfl

private theorem receipt_3_1_2384_0 : fastPhase (bank 3 1).shape 179808 2384 1 1 1 1 0 = 353672394935529436442676 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2384_0_join0

private theorem receipt_3_1_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2384 1 1 1 1 1) 0 128 = 305710515150704576591904 := by decide +kernel
private theorem receipt_3_1_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2384 1 1 1 1 1) 128 80 = 44242256927249929922292 := by decide +kernel
private theorem receipt_3_1_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179808 2384 1 1 1 1 1) 0 208 = 349952772077954506514196 :=
  phaseBlock_append receipt_3_1_2384_1_part0 receipt_3_1_2384_1_part1 rfl rfl rfl

private theorem receipt_3_1_2384_1 : fastPhase (bank 3 1).shape 179808 2384 1 1 1 1 1 = 349952772077954506514196 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2384_1_join0

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2383_0 receipt_3_1_2383_1 receipt_3_1_2384_0 receipt_3_1_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 0) 0 128 = 9941216840188870224895200 := by decide +kernel
private theorem receipt_0_2_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 0) 128 128 = 3686782705343338324325669 := by decide +kernel
private theorem receipt_0_2_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 0) 256 27 = 108754210510613629076615 := by decide +kernel
private theorem receipt_0_2_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 0) 128 155 = 3795536915853951953402284 :=
  phaseBlock_append receipt_0_2_2383_0_part1 receipt_0_2_2383_0_part2 rfl rfl rfl
private theorem receipt_0_2_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 0) 0 283 = 13736753756042822178297484 :=
  phaseBlock_append receipt_0_2_2383_0_part0 receipt_0_2_2383_0_join0 rfl rfl rfl

private theorem receipt_0_2_2383_0 : fastPhase (bank 0 2).shape 179808 2383 2 1 0 1 0 = 13736753756042822178297484 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2383_0_join1

private theorem receipt_0_2_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 1) 0 128 = 9887328651745705810615200 := by decide +kernel
private theorem receipt_0_2_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 1) 128 128 = 3643679536611056068619389 := by decide +kernel
private theorem receipt_0_2_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 1) 256 27 = 100923426562613863453417 := by decide +kernel
private theorem receipt_0_2_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 1) 128 155 = 3744602963173669932072806 :=
  phaseBlock_append receipt_0_2_2383_1_part1 receipt_0_2_2383_1_part2 rfl rfl rfl
private theorem receipt_0_2_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2383 2 1 0 1 1) 0 283 = 13631931614919375742688006 :=
  phaseBlock_append receipt_0_2_2383_1_part0 receipt_0_2_2383_1_join0 rfl rfl rfl

private theorem receipt_0_2_2383_1 : fastPhase (bank 0 2).shape 179808 2383 2 1 0 1 1 = 13631931614919375742688006 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2383_1_join1

private theorem receipt_0_2_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 0) 0 128 = 9941299705749467473468960 := by decide +kernel
private theorem receipt_0_2_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 0) 128 128 = 3686804718033543501903946 := by decide +kernel
private theorem receipt_0_2_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 0) 256 27 = 108754642446344524129555 := by decide +kernel
private theorem receipt_0_2_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 0) 128 155 = 3795559360479888026033501 :=
  phaseBlock_append receipt_0_2_2384_0_part1 receipt_0_2_2384_0_part2 rfl rfl rfl
private theorem receipt_0_2_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 0) 0 283 = 13736859066229355499502461 :=
  phaseBlock_append receipt_0_2_2384_0_part0 receipt_0_2_2384_0_join0 rfl rfl rfl

private theorem receipt_0_2_2384_0 : fastPhase (bank 0 2).shape 179808 2384 2 1 0 1 0 = 13736859066229355499502461 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2384_0_join1

private theorem receipt_0_2_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 1) 0 128 = 9887411144615294314071840 := by decide +kernel
private theorem receipt_0_2_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 1) 128 128 = 3643701327804417057038900 := by decide +kernel
private theorem receipt_0_2_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 1) 256 27 = 100923828750947758915391 := by decide +kernel
private theorem receipt_0_2_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 1) 128 155 = 3744625156555364815954291 :=
  phaseBlock_append receipt_0_2_2384_1_part1 receipt_0_2_2384_1_part2 rfl rfl rfl
private theorem receipt_0_2_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179808 2384 2 1 0 1 1) 0 283 = 13632036301170659130026131 :=
  phaseBlock_append receipt_0_2_2384_1_part0 receipt_0_2_2384_1_join0 rfl rfl rfl

private theorem receipt_0_2_2384_1 : fastPhase (bank 0 2).shape 179808 2384 2 1 0 1 1 = 13632036301170659130026131 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2384_1_join1

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2383_0 receipt_0_2_2383_1 receipt_0_2_2384_0 receipt_0_2_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 0) 0 128 = 8933862833842505088256800 := by decide +kernel
private theorem receipt_1_2_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 0) 128 128 = 3303317784414368119725655 := by decide +kernel
private theorem receipt_1_2_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 0) 256 27 = 97224776388443001832303 := by decide +kernel
private theorem receipt_1_2_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 0) 128 155 = 3400542560802811121557958 :=
  phaseBlock_append receipt_1_2_2383_0_part1 receipt_1_2_2383_0_part2 rfl rfl rfl
private theorem receipt_1_2_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 0) 0 283 = 12334405394645316209814758 :=
  phaseBlock_append receipt_1_2_2383_0_part0 receipt_1_2_2383_0_join0 rfl rfl rfl

private theorem receipt_1_2_2383_0 : fastPhase (bank 1 2).shape 179808 2383 2 1 0 2 0 = 12334405394645316209814758 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2383_0_join1

private theorem receipt_1_2_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 1) 0 128 = 8885219801786312418150688 := by decide +kernel
private theorem receipt_1_2_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 1) 128 128 = 3264629111296748216538027 := by decide +kernel
private theorem receipt_1_2_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 1) 256 27 = 90222643825222796230441 := by decide +kernel
private theorem receipt_1_2_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 1) 128 155 = 3354851755121971012768468 :=
  phaseBlock_append receipt_1_2_2383_1_part1 receipt_1_2_2383_1_part2 rfl rfl rfl
private theorem receipt_1_2_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2383 2 1 0 2 1) 0 283 = 12240071556908283430919156 :=
  phaseBlock_append receipt_1_2_2383_1_part0 receipt_1_2_2383_1_join0 rfl rfl rfl

private theorem receipt_1_2_2383_1 : fastPhase (bank 1 2).shape 179808 2383 2 1 0 2 1 = 12240071556908283430919156 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2383_1_join1

private theorem receipt_1_2_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 0) 0 128 = 8933937307998044697967200 := by decide +kernel
private theorem receipt_1_2_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 0) 128 128 = 3303337509553383625822524 := by decide +kernel
private theorem receipt_1_2_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 0) 256 27 = 97225162535478892023795 := by decide +kernel
private theorem receipt_1_2_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 0) 128 155 = 3400562672088862517846319 :=
  phaseBlock_append receipt_1_2_2384_0_part1 receipt_1_2_2384_0_part2 rfl rfl rfl
private theorem receipt_1_2_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 0) 0 283 = 12334499980086907215813519 :=
  phaseBlock_append receipt_1_2_2384_0_part0 receipt_1_2_2384_0_join0 rfl rfl rfl

private theorem receipt_1_2_2384_0 : fastPhase (bank 1 2).shape 179808 2384 2 1 0 2 0 = 12334499980086907215813519 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2384_0_join1

private theorem receipt_1_2_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 1) 0 128 = 8885293939189575715910304 := by decide +kernel
private theorem receipt_1_2_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 1) 128 128 = 3264648637534377705246870 := by decide +kernel
private theorem receipt_1_2_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 1) 256 27 = 90223003372104744246745 := by decide +kernel
private theorem receipt_1_2_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 1) 128 155 = 3354871640906482449493615 :=
  phaseBlock_append receipt_1_2_2384_1_part1 receipt_1_2_2384_1_part2 rfl rfl rfl
private theorem receipt_1_2_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179808 2384 2 1 0 2 1) 0 283 = 12240165580096058165403919 :=
  phaseBlock_append receipt_1_2_2384_1_part0 receipt_1_2_2384_1_join0 rfl rfl rfl

private theorem receipt_1_2_2384_1 : fastPhase (bank 1 2).shape 179808 2384 2 1 0 2 1 = 12240165580096058165403919 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2384_1_join1

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2383_0 receipt_1_2_2383_1 receipt_1_2_2384_0 receipt_1_2_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 0) 0 128 = 4731719146441904673575904 := by decide +kernel
private theorem receipt_2_2_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 0) 128 128 = 1711902586004689725714307 := by decide +kernel
private theorem receipt_2_2_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 0) 256 27 = 49561155705446746968115 := by decide +kernel
private theorem receipt_2_2_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 0) 128 155 = 1761463741710136472682422 :=
  phaseBlock_append receipt_2_2_2383_0_part1 receipt_2_2_2383_0_part2 rfl rfl rfl
private theorem receipt_2_2_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 0) 0 283 = 6493182888152041146258326 :=
  phaseBlock_append receipt_2_2_2383_0_part0 receipt_2_2_2383_0_join0 rfl rfl rfl

private theorem receipt_2_2_2383_0 : fastPhase (bank 2 2).shape 179808 2383 2 1 0 7 0 = 6493182888152041146258326 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2383_0_join1

private theorem receipt_2_2_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 1) 0 128 = 4705129808180864792056096 := by decide +kernel
private theorem receipt_2_2_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 1) 128 128 = 1691591579759208063990393 := by decide +kernel
private theorem receipt_2_2_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 1) 256 27 = 45986027839478653529941 := by decide +kernel
private theorem receipt_2_2_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 1) 128 155 = 1737577607598686717520334 :=
  phaseBlock_append receipt_2_2_2383_1_part1 receipt_2_2_2383_1_part2 rfl rfl rfl
private theorem receipt_2_2_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2383 2 1 0 7 1) 0 283 = 6442707415779551509576430 :=
  phaseBlock_append receipt_2_2_2383_1_part0 receipt_2_2_2383_1_join0 rfl rfl rfl

private theorem receipt_2_2_2383_1 : fastPhase (bank 2 2).shape 179808 2383 2 1 0 7 1 = 6442707415779551509576430 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2383_1_join1

private theorem receipt_2_2_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 0) 0 128 = 4731758611726379741764704 := by decide +kernel
private theorem receipt_2_2_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 0) 128 128 = 1711912815917723852262570 := by decide +kernel
private theorem receipt_2_2_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 0) 256 27 = 49561352556237241079685 := by decide +kernel
private theorem receipt_2_2_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 0) 128 155 = 1761474168473961093342255 :=
  phaseBlock_append receipt_2_2_2384_0_part1 receipt_2_2_2384_0_part2 rfl rfl rfl
private theorem receipt_2_2_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 0) 0 283 = 6493232780200340835106959 :=
  phaseBlock_append receipt_2_2_2384_0_part0 receipt_2_2_2384_0_join0 rfl rfl rfl

private theorem receipt_2_2_2384_0 : fastPhase (bank 2 2).shape 179808 2384 2 1 0 7 0 = 6493232780200340835106959 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2384_0_join1

private theorem receipt_2_2_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 1) 0 128 = 4705169088101134783281888 := by decide +kernel
private theorem receipt_2_2_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 1) 128 128 = 1691601704911428333254466 := by decide +kernel
private theorem receipt_2_2_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 1) 256 27 = 45986211106509852224725 := by decide +kernel
private theorem receipt_2_2_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 1) 128 155 = 1737587916017938185479191 :=
  phaseBlock_append receipt_2_2_2384_1_part1 receipt_2_2_2384_1_part2 rfl rfl rfl
private theorem receipt_2_2_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179808 2384 2 1 0 7 1) 0 283 = 6442757004119072968761079 :=
  phaseBlock_append receipt_2_2_2384_1_part0 receipt_2_2_2384_1_join0 rfl rfl rfl

private theorem receipt_2_2_2384_1 : fastPhase (bank 2 2).shape 179808 2384 2 1 0 7 1 = 6442757004119072968761079 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2384_1_join1

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2383_0 receipt_2_2_2383_1 receipt_2_2_2384_0 receipt_2_2_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2383 2 1 1 1 0) 0 128 = 469573578971528954273568 := by decide +kernel
private theorem receipt_3_2_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2383 2 1 1 1 0) 128 95 = 88817807038905868536536 := by decide +kernel
private theorem receipt_3_2_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2383 2 1 1 1 0) 0 223 = 558391386010434822810104 :=
  phaseBlock_append receipt_3_2_2383_0_part0 receipt_3_2_2383_0_part1 rfl rfl rfl

private theorem receipt_3_2_2383_0 : fastPhase (bank 3 2).shape 179808 2383 2 1 1 1 0 = 558391386010434822810104 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2383_0_join0

private theorem receipt_3_2_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2383 2 1 1 1 1) 0 128 = 466042497512550825289120 := by decide +kernel
private theorem receipt_3_2_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2383 2 1 1 1 1) 128 95 = 86869577214797731877133 := by decide +kernel
private theorem receipt_3_2_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2383 2 1 1 1 1) 0 223 = 552912074727348557166253 :=
  phaseBlock_append receipt_3_2_2383_1_part0 receipt_3_2_2383_1_part1 rfl rfl rfl

private theorem receipt_3_2_2383_1 : fastPhase (bank 3 2).shape 179808 2383 2 1 1 1 1 = 552912074727348557166253 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2383_1_join0

private theorem receipt_3_2_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2384 2 1 1 1 0) 0 128 = 469577028903628150190112 := by decide +kernel
private theorem receipt_3_2_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2384 2 1 1 1 0) 128 95 = 88818107300192755336600 := by decide +kernel
private theorem receipt_3_2_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2384 2 1 1 1 0) 0 223 = 558395136203820905526712 :=
  phaseBlock_append receipt_3_2_2384_0_part0 receipt_3_2_2384_0_part1 rfl rfl rfl

private theorem receipt_3_2_2384_0 : fastPhase (bank 3 2).shape 179808 2384 2 1 1 1 0 = 558395136203820905526712 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2384_0_join0

private theorem receipt_3_2_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2384 2 1 1 1 1) 0 128 = 466045919071105317191200 := by decide +kernel
private theorem receipt_3_2_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2384 2 1 1 1 1) 128 95 = 86869871397841389767866 := by decide +kernel
private theorem receipt_3_2_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179808 2384 2 1 1 1 1) 0 223 = 552915790468946706959066 :=
  phaseBlock_append receipt_3_2_2384_1_part0 receipt_3_2_2384_1_part1 rfl rfl rfl

private theorem receipt_3_2_2384_1 : fastPhase (bank 3 2).shape 179808 2384 2 1 1 1 1 = 552915790468946706959066 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2384_1_join0

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2383_0 receipt_3_2_2383_1 receipt_3_2_2384_0 receipt_3_2_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 0) 0 128 = 14941820235266832142857142 := by decide +kernel
private theorem receipt_0_3_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 0) 128 128 = 5497855566890016131495714 := by decide +kernel
private theorem receipt_0_3_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 0) 256 26 = 152088920623875915165034 := by decide +kernel
private theorem receipt_0_3_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 0) 128 154 = 5649944487513892046660748 :=
  phaseBlock_append receipt_0_3_2383_0_part1 receipt_0_3_2383_0_part2 rfl rfl rfl
private theorem receipt_0_3_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 0) 0 282 = 20591764722780724189517890 :=
  phaseBlock_append receipt_0_3_2383_0_part0 receipt_0_3_2383_0_join0 rfl rfl rfl

private theorem receipt_0_3_2383_0 : fastPhase (bank 0 3).shape 179808 2383 3 1 0 1 0 = 20591764722780724189517890 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2383_0_join1

private theorem receipt_0_3_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 1) 0 128 = 14860356038412502290962398 := by decide +kernel
private theorem receipt_0_3_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 1) 128 128 = 5432878782189392600267196 := by decide +kernel
private theorem receipt_0_3_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 1) 256 26 = 140734521608117926150428 := by decide +kernel
private theorem receipt_0_3_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 1) 128 154 = 5573613303797510526417624 :=
  phaseBlock_append receipt_0_3_2383_1_part1 receipt_0_3_2383_1_part2 rfl rfl rfl
private theorem receipt_0_3_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2383 3 1 0 1 1) 0 282 = 20433969342210012817380022 :=
  phaseBlock_append receipt_0_3_2383_1_part0 receipt_0_3_2383_1_join0 rfl rfl rfl

private theorem receipt_0_3_2383_1 : fastPhase (bank 0 3).shape 179808 2383 3 1 0 1 1 = 20433969342210012817380022 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2383_1_join1

private theorem receipt_0_3_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 0) 0 128 = 14941945401348993672129756 := by decide +kernel
private theorem receipt_0_3_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 0) 128 128 = 5497888081678962075021484 := by decide +kernel
private theorem receipt_0_3_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 0) 256 26 = 152089508906895305297957 := by decide +kernel
private theorem receipt_0_3_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 0) 128 154 = 5649977590585857380319441 :=
  phaseBlock_append receipt_0_3_2384_0_part1 receipt_0_3_2384_0_part2 rfl rfl rfl
private theorem receipt_0_3_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 0) 0 282 = 20591922991934851052449197 :=
  phaseBlock_append receipt_0_3_2384_0_part0 receipt_0_3_2384_0_join0 rfl rfl rfl

private theorem receipt_0_3_2384_0 : fastPhase (bank 0 3).shape 179808 2384 3 1 0 1 0 = 20591922991934851052449197 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2384_0_join1

private theorem receipt_0_3_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 1) 0 128 = 14860480640140667755752408 := by decide +kernel
private theorem receipt_0_3_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 1) 128 128 = 5432910967686168910549446 := by decide +kernel
private theorem receipt_0_3_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 1) 256 26 = 140735067890544052306857 := by decide +kernel
private theorem receipt_0_3_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 1) 128 154 = 5573646035576712962856303 :=
  phaseBlock_append receipt_0_3_2384_1_part1 receipt_0_3_2384_1_part2 rfl rfl rfl
private theorem receipt_0_3_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179808 2384 3 1 0 1 1) 0 282 = 20434126675717380718608711 :=
  phaseBlock_append receipt_0_3_2384_1_part0 receipt_0_3_2384_1_join0 rfl rfl rfl

private theorem receipt_0_3_2384_1 : fastPhase (bank 0 3).shape 179808 2384 3 1 0 1 1 = 20434126675717380718608711 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2384_1_join1

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2383_0 receipt_0_3_2383_1 receipt_0_3_2384_0 receipt_0_3_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 0) 0 128 = 13412209977639478566132793 := by decide +kernel
private theorem receipt_1_3_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 0) 128 128 = 4923267647472066024996216 := by decide +kernel
private theorem receipt_1_3_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 0) 256 26 = 135950817285671480956086 := by decide +kernel
private theorem receipt_1_3_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 0) 128 154 = 5059218464757737505952302 :=
  phaseBlock_append receipt_1_3_2383_0_part1 receipt_1_3_2383_0_part2 rfl rfl rfl
private theorem receipt_1_3_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 0) 0 282 = 18471428442397216072085095 :=
  phaseBlock_append receipt_1_3_2383_0_part0 receipt_1_3_2383_0_join0 rfl rfl rfl

private theorem receipt_1_3_2383_0 : fastPhase (bank 1 3).shape 179808 2383 3 1 0 2 0 = 18471428442397216072085095 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2383_0_join1

private theorem receipt_1_3_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 1) 0 128 = 13338826561195234797408378 := by decide +kernel
private theorem receipt_1_3_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 1) 128 128 = 4865000118628630387711818 := by decide +kernel
private theorem receipt_1_3_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 1) 256 26 = 125799536899777308924303 := by decide +kernel
private theorem receipt_1_3_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 1) 128 154 = 4990799655528407696636121 :=
  phaseBlock_append receipt_1_3_2383_1_part1 receipt_1_3_2383_1_part2 rfl rfl rfl
private theorem receipt_1_3_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2383 3 1 0 2 1) 0 282 = 18329626216723642494044499 :=
  phaseBlock_append receipt_1_3_2383_1_part0 receipt_1_3_2383_1_join0 rfl rfl rfl

private theorem receipt_1_3_2383_1 : fastPhase (bank 1 3).shape 179808 2383 3 1 0 2 1 = 18329626216723642494044499 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2383_1_join1

private theorem receipt_1_3_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 0) 0 128 = 13412322337182452726890545 := by decide +kernel
private theorem receipt_1_3_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 0) 128 128 = 4923296766553960514373468 := by decide +kernel
private theorem receipt_1_3_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 0) 256 26 = 135951343148724061514232 := by decide +kernel
private theorem receipt_1_3_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 0) 128 154 = 5059248109702684575887700 :=
  phaseBlock_append receipt_1_3_2384_0_part1 receipt_1_3_2384_0_part2 rfl rfl rfl
private theorem receipt_1_3_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 0) 0 282 = 18471570446885137302778245 :=
  phaseBlock_append receipt_1_3_2384_0_part0 receipt_1_3_2384_0_join0 rfl rfl rfl

private theorem receipt_1_3_2384_0 : fastPhase (bank 1 3).shape 179808 2384 3 1 0 2 0 = 18471570446885137302778245 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2384_0_join1

private theorem receipt_1_3_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 1) 0 128 = 13338938411950720320835104 := by decide +kernel
private theorem receipt_1_3_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 1) 128 128 = 4865028942310483312068432 := by decide +kernel
private theorem receipt_1_3_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 1) 256 26 = 125800025211966887012721 := by decide +kernel
private theorem receipt_1_3_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 1) 128 154 = 4990828967522450199081153 :=
  phaseBlock_append receipt_1_3_2384_1_part1 receipt_1_3_2384_1_part2 rfl rfl rfl
private theorem receipt_1_3_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179808 2384 3 1 0 2 1) 0 282 = 18329767379473170519916257 :=
  phaseBlock_append receipt_1_3_2384_1_part0 receipt_1_3_2384_1_join0 rfl rfl rfl

private theorem receipt_1_3_2384_1 : fastPhase (bank 1 3).shape 179808 2384 3 1 0 2 1 = 18329767379473170519916257 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2384_1_join1

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2383_0 receipt_1_3_2383_1 receipt_1_3_2384_0 receipt_1_3_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 0) 0 128 = 7037317904204159550213203 := by decide +kernel
private theorem receipt_2_3_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 0) 128 128 = 2538481126500341179025331 := by decide +kernel
private theorem receipt_2_3_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 0) 256 26 = 69178718708789389251106 := by decide +kernel
private theorem receipt_2_3_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 0) 128 154 = 2607659845209130568276437 :=
  phaseBlock_append receipt_2_3_2383_0_part1 receipt_2_3_2383_0_part2 rfl rfl rfl
private theorem receipt_2_3_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 0) 0 282 = 9644977749413290118489640 :=
  phaseBlock_append receipt_2_3_2383_0_part0 receipt_2_3_2383_0_join0 rfl rfl rfl

private theorem receipt_2_3_2383_0 : fastPhase (bank 2 3).shape 179808 2383 3 1 0 7 0 = 9644977749413290118489640 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2383_0_join1

private theorem receipt_2_3_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 1) 0 128 = 6997825348313320265366649 := by decide +kernel
private theorem receipt_2_3_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 1) 128 128 = 2508128588093364376159140 := by decide +kernel
private theorem receipt_2_3_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 1) 256 26 = 64006846068972969519441 := by decide +kernel
private theorem receipt_2_3_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 1) 128 154 = 2572135434162337345678581 :=
  phaseBlock_append receipt_2_3_2383_1_part1 receipt_2_3_2383_1_part2 rfl rfl rfl
private theorem receipt_2_3_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2383 3 1 0 7 1) 0 282 = 9569960782475657611045230 :=
  phaseBlock_append receipt_2_3_2383_1_part0 receipt_2_3_2383_1_join0 rfl rfl rfl

private theorem receipt_2_3_2383_1 : fastPhase (bank 2 3).shape 179808 2383 3 1 0 7 1 = 9569960782475657611045230 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2383_1_join1

private theorem receipt_2_3_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 0) 0 128 = 7037376884830788721520232 := by decide +kernel
private theorem receipt_2_3_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 0) 128 128 = 2538496149863207355919154 := by decide +kernel
private theorem receipt_2_3_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 0) 256 26 = 69178986304352061223482 := by decide +kernel
private theorem receipt_2_3_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 0) 128 154 = 2607675136167559417142636 :=
  phaseBlock_append receipt_2_3_2384_0_part1 receipt_2_3_2384_0_part2 rfl rfl rfl
private theorem receipt_2_3_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 0) 0 282 = 9645052020998348138662868 :=
  phaseBlock_append receipt_2_3_2384_0_part0 receipt_2_3_2384_0_join0 rfl rfl rfl

private theorem receipt_2_3_2384_0 : fastPhase (bank 2 3).shape 179808 2384 3 1 0 7 0 = 9645052020998348138662868 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2384_0_join1

private theorem receipt_2_3_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 1) 0 128 = 6997884053548466391814386 := by decide +kernel
private theorem receipt_2_3_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 1) 128 128 = 2508143457162785284766749 := by decide +kernel
private theorem receipt_2_3_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 1) 256 26 = 64007094530577146060045 := by decide +kernel
private theorem receipt_2_3_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 1) 128 154 = 2572150551693362430826794 :=
  phaseBlock_append receipt_2_3_2384_1_part1 receipt_2_3_2384_1_part2 rfl rfl rfl
private theorem receipt_2_3_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179808 2384 3 1 0 7 1) 0 282 = 9570034605241828822641180 :=
  phaseBlock_append receipt_2_3_2384_1_part0 receipt_2_3_2384_1_join0 rfl rfl rfl

private theorem receipt_2_3_2384_1 : fastPhase (bank 2 3).shape 179808 2384 3 1 0 7 1 = 9570034605241828822641180 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2384_1_join1

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2383_0 receipt_2_3_2383_1 receipt_2_3_2384_0 receipt_2_3_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2383 3 1 1 1 0) 0 128 = 693296411742702776368800 := by decide +kernel
private theorem receipt_3_3_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2383 3 1 1 1 0) 128 110 = 161376392669812855773106 := by decide +kernel
private theorem receipt_3_3_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2383 3 1 1 1 0) 0 238 = 854672804412515632141906 :=
  phaseBlock_append receipt_3_3_2383_0_part0 receipt_3_3_2383_0_part1 rfl rfl rfl

private theorem receipt_3_3_2383_0 : fastPhase (bank 3 3).shape 179808 2383 3 1 1 1 0 = 854672804412515632141906 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2383_0_join0

private theorem receipt_3_3_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2383 3 1 1 1 1) 0 128 = 688508508072965701752480 := by decide +kernel
private theorem receipt_3_3_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2383 3 1 1 1 1) 128 110 = 158304178182143382361137 := by decide +kernel
private theorem receipt_3_3_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2383 3 1 1 1 1) 0 238 = 846812686255109084113617 :=
  phaseBlock_append receipt_3_3_2383_1_part0 receipt_3_3_2383_1_part1 rfl rfl rfl

private theorem receipt_3_3_2383_1 : fastPhase (bank 3 3).shape 179808 2383 3 1 1 1 1 = 846812686255109084113617 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2383_1_join0

private theorem receipt_3_3_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2384 3 1 1 1 0) 0 128 = 693301557579652151499744 := by decide +kernel
private theorem receipt_3_3_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2384 3 1 1 1 0) 128 110 = 161376966486167456007896 := by decide +kernel
private theorem receipt_3_3_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2384 3 1 1 1 0) 0 238 = 854678524065819607507640 :=
  phaseBlock_append receipt_3_3_2384_0_part0 receipt_3_3_2384_0_part1 rfl rfl rfl

private theorem receipt_3_3_2384_0 : fastPhase (bank 3 3).shape 179808 2384 3 1 1 1 0 = 854678524065819607507640 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2384_0_join0

private theorem receipt_3_3_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2384 3 1 1 1 1) 0 128 = 688513614757460826361440 := by decide +kernel
private theorem receipt_3_3_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2384 3 1 1 1 1) 128 110 = 158304741928625862567459 := by decide +kernel
private theorem receipt_3_3_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179808 2384 3 1 1 1 1) 0 238 = 846818356686086688928899 :=
  phaseBlock_append receipt_3_3_2384_1_part0 receipt_3_3_2384_1_part1 rfl rfl rfl

private theorem receipt_3_3_2384_1 : fastPhase (bank 3 3).shape 179808 2384 3 1 1 1 1 = 846818356686086688928899 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2384_1_join0

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2383_0 receipt_3_3_2383_1 receipt_3_3_2384_0 receipt_3_3_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 0) 0 128 = 22567093418371162390143479 := by decide +kernel
private theorem receipt_0_4_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 0) 128 128 = 8863111907981384480601051 := by decide +kernel
private theorem receipt_0_4_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 0) 256 36 = 420268312336052105923615 := by decide +kernel
private theorem receipt_0_4_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 0) 128 164 = 9283380220317436586524666 :=
  phaseBlock_append receipt_0_4_2383_0_part1 receipt_0_4_2383_0_part2 rfl rfl rfl
private theorem receipt_0_4_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 0) 0 292 = 31850473638688598976668145 :=
  phaseBlock_append receipt_0_4_2383_0_part0 receipt_0_4_2383_0_join0 rfl rfl rfl

private theorem receipt_0_4_2383_0 : fastPhase (bank 0 4).shape 179808 2383 4 1 0 1 0 = 31850473638688598976668145 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2383_0_join1

private theorem receipt_0_4_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 1) 0 128 = 22449556619132082176908398 := by decide +kernel
private theorem receipt_0_4_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 1) 128 128 = 8768203424046847745249622 := by decide +kernel
private theorem receipt_0_4_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 1) 256 36 = 397314747526724512665117 := by decide +kernel
private theorem receipt_0_4_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 1) 128 164 = 9165518171573572257914739 :=
  phaseBlock_append receipt_0_4_2383_1_part1 receipt_0_4_2383_1_part2 rfl rfl rfl
private theorem receipt_0_4_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2383 4 1 0 1 1) 0 292 = 31615074790705654434823137 :=
  phaseBlock_append receipt_0_4_2383_1_part0 receipt_0_4_2383_1_join0 rfl rfl rfl

private theorem receipt_0_4_2383_1 : fastPhase (bank 0 4).shape 179808 2383 4 1 0 1 1 = 31615074790705654434823137 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2383_1_join1

private theorem receipt_0_4_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 0) 0 128 = 22567282355037878689372232 := by decide +kernel
private theorem receipt_0_4_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 0) 128 128 = 8863165275859668343603460 := by decide +kernel
private theorem receipt_0_4_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 0) 256 36 = 420270015489282478331889 := by decide +kernel
private theorem receipt_0_4_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 0) 128 164 = 9283435291348950821935349 :=
  phaseBlock_append receipt_0_4_2384_0_part1 receipt_0_4_2384_0_part2 rfl rfl rfl
private theorem receipt_0_4_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 0) 0 292 = 31850717646386829511307581 :=
  phaseBlock_append receipt_0_4_2384_0_part0 receipt_0_4_2384_0_join0 rfl rfl rfl

private theorem receipt_0_4_2384_0 : fastPhase (bank 0 4).shape 179808 2384 4 1 0 1 0 = 31850717646386829511307581 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2384_0_join1

private theorem receipt_0_4_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 1) 0 128 = 22449744739803497326009227 := by decide +kernel
private theorem receipt_0_4_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 1) 128 128 = 8768256299145278626955707 := by decide +kernel
private theorem receipt_0_4_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 1) 256 36 = 397316362812086880103445 := by decide +kernel
private theorem receipt_0_4_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 1) 128 164 = 9165572661957365507059152 :=
  phaseBlock_append receipt_0_4_2384_1_part1 receipt_0_4_2384_1_part2 rfl rfl rfl
private theorem receipt_0_4_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179808 2384 4 1 0 1 1) 0 292 = 31615317401760862833068379 :=
  phaseBlock_append receipt_0_4_2384_1_part0 receipt_0_4_2384_1_join0 rfl rfl rfl

private theorem receipt_0_4_2384_1 : fastPhase (bank 0 4).shape 179808 2384 4 1 0 1 1 = 31615317401760862833068379 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2384_1_join1

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2383_0 receipt_0_4_2383_1 receipt_0_4_2384_0 receipt_0_4_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 0) 0 128 = 20321563221169888519918221 := by decide +kernel
private theorem receipt_1_4_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 0) 128 128 = 7964396508623703366963729 := by decide +kernel
private theorem receipt_1_4_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 0) 256 36 = 377052668183618654423233 := by decide +kernel
private theorem receipt_1_4_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 0) 128 164 = 8341449176807322021386962 :=
  phaseBlock_append receipt_1_4_2383_0_part1 receipt_1_4_2383_0_part2 rfl rfl rfl
private theorem receipt_1_4_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 0) 0 292 = 28663012397977210541305183 :=
  phaseBlock_append receipt_1_4_2383_0_part0 receipt_1_4_2383_0_join0 rfl rfl rfl

private theorem receipt_1_4_2383_0 : fastPhase (bank 1 4).shape 179808 2383 4 1 0 2 0 = 28663012397977210541305183 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2383_0_join1

private theorem receipt_1_4_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 1) 0 128 = 20215378243695841574433292 := by decide +kernel
private theorem receipt_1_4_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 1) 128 128 = 7878992121315274866458388 := by decide +kernel
private theorem receipt_1_4_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 1) 256 36 = 356455193742736470071121 := by decide +kernel
private theorem receipt_1_4_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 1) 128 164 = 8235447315058011336529509 :=
  phaseBlock_append receipt_1_4_2383_1_part1 receipt_1_4_2383_1_part2 rfl rfl rfl
private theorem receipt_1_4_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2383 4 1 0 2 1) 0 292 = 28450825558753852910962801 :=
  phaseBlock_append receipt_1_4_2383_1_part0 receipt_1_4_2383_1_join0 rfl rfl rfl

private theorem receipt_1_4_2383_1 : fastPhase (bank 1 4).shape 179808 2383 4 1 0 2 1 = 28450825558753852910962801 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2383_1_join1

private theorem receipt_1_4_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 0) 0 128 = 20321733366329896289238189 := by decide +kernel
private theorem receipt_1_4_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 0) 128 128 = 7964444468427689328760321 := by decide +kernel
private theorem receipt_1_4_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 0) 256 36 = 377054196214916589514019 := by decide +kernel
private theorem receipt_1_4_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 0) 128 164 = 8341498664642605918274340 :=
  phaseBlock_append receipt_1_4_2384_0_part1 receipt_1_4_2384_0_part2 rfl rfl rfl
private theorem receipt_1_4_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 0) 0 292 = 28663232030972502207512529 :=
  phaseBlock_append receipt_1_4_2384_0_part0 receipt_1_4_2384_0_join0 rfl rfl rfl

private theorem receipt_1_4_2384_0 : fastPhase (bank 1 4).shape 179808 2384 4 1 0 2 0 = 28663232030972502207512529 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2384_0_join1

private theorem receipt_1_4_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 1) 0 128 = 20215547651132186303137290 := by decide +kernel
private theorem receipt_1_4_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 1) 128 128 = 7879039637539546881695754 := by decide +kernel
private theorem receipt_1_4_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 1) 256 36 = 356456642923272193827513 := by decide +kernel
private theorem receipt_1_4_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 1) 128 164 = 8235496280462819075523267 :=
  phaseBlock_append receipt_1_4_2384_1_part1 receipt_1_4_2384_1_part2 rfl rfl rfl
private theorem receipt_1_4_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179808 2384 4 1 0 2 1) 0 292 = 28451043931595005378660557 :=
  phaseBlock_append receipt_1_4_2384_1_part0 receipt_1_4_2384_1_join0 rfl rfl rfl

private theorem receipt_1_4_2384_1 : fastPhase (bank 1 4).shape 179808 2384 4 1 0 2 1 = 28451043931595005378660557 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2384_1_join1

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2383_0 receipt_1_4_2383_1 receipt_1_4_2384_0 receipt_1_4_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 0) 0 128 = 10902943576865289723633306 := by decide +kernel
private theorem receipt_2_4_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 0) 128 128 = 4208558687360109023685474 := by decide +kernel
private theorem receipt_2_4_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 0) 256 36 = 196947594995870415160564 := by decide +kernel
private theorem receipt_2_4_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 0) 128 164 = 4405506282355979438846038 :=
  phaseBlock_append receipt_2_4_2383_0_part1 receipt_2_4_2383_0_part2 rfl rfl rfl
private theorem receipt_2_4_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 0) 0 292 = 15308449859221269162479344 :=
  phaseBlock_append receipt_2_4_2383_0_part0 receipt_2_4_2383_0_join0 rfl rfl rfl

private theorem receipt_2_4_2383_0 : fastPhase (bank 2 4).shape 179808 2383 4 1 0 7 0 = 15308449859221269162479344 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2383_0_join1

private theorem receipt_2_4_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 1) 0 128 = 10844647637068844690449147 := by decide +kernel
private theorem receipt_2_4_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 1) 128 128 = 4162970866729728392489823 := by decide +kernel
private theorem receipt_2_4_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 1) 256 36 = 186172826387500505422587 := by decide +kernel
private theorem receipt_2_4_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 1) 128 164 = 4349143693117228897912410 :=
  phaseBlock_append receipt_2_4_2383_1_part1 receipt_2_4_2383_1_part2 rfl rfl rfl
private theorem receipt_2_4_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2383 4 1 0 7 1) 0 292 = 15193791330186073588361557 :=
  phaseBlock_append receipt_2_4_2383_1_part0 receipt_2_4_2383_1_join0 rfl rfl rfl

private theorem receipt_2_4_2383_1 : fastPhase (bank 2 4).shape 179808 2383 4 1 0 7 1 = 15193791330186073588361557 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2383_1_join1

private theorem receipt_2_4_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 0) 0 128 = 10903034896331101587041106 := by decide +kernel
private theorem receipt_2_4_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 0) 128 128 = 4208584043389016677253638 := by decide +kernel
private theorem receipt_2_4_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 0) 256 36 = 196948393181562410397485 := by decide +kernel
private theorem receipt_2_4_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 0) 128 164 = 4405532436570579087651123 :=
  phaseBlock_append receipt_2_4_2384_0_part1 receipt_2_4_2384_0_part2 rfl rfl rfl
private theorem receipt_2_4_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 0) 0 292 = 15308567332901680674692229 :=
  phaseBlock_append receipt_2_4_2384_0_part0 receipt_2_4_2384_0_join0 rfl rfl rfl

private theorem receipt_2_4_2384_0 : fastPhase (bank 2 4).shape 179808 2384 4 1 0 7 0 = 15308567332901680674692229 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2384_0_join1

private theorem receipt_2_4_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 1) 0 128 = 10844738549450901937284639 := by decide +kernel
private theorem receipt_2_4_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 1) 128 128 = 4162995985419265004513391 := by decide +kernel
private theorem receipt_2_4_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 1) 256 36 = 186173583317187532655844 := by decide +kernel
private theorem receipt_2_4_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 1) 128 164 = 4349169568736452537169235 :=
  phaseBlock_append receipt_2_4_2384_1_part1 receipt_2_4_2384_1_part2 rfl rfl rfl
private theorem receipt_2_4_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179808 2384 4 1 0 7 1) 0 292 = 15193908118187354474453874 :=
  phaseBlock_append receipt_2_4_2384_1_part0 receipt_2_4_2384_1_join0 rfl rfl rfl

private theorem receipt_2_4_2384_1 : fastPhase (bank 2 4).shape 179808 2384 4 1 0 7 1 = 15193908118187354474453874 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2384_1_join1

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2383_0 receipt_2_4_2383_1 receipt_2_4_2384_0 receipt_2_4_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 0) 0 128 = 1606914162199332462803328 := by decide +kernel
private theorem receipt_3_4_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 0) 128 128 = 648811536510867836246400 := by decide +kernel
private theorem receipt_3_4_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 0) 256 47 = 44987800139678097888080 := by decide +kernel
private theorem receipt_3_4_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 0) 128 175 = 693799336650545934134480 :=
  phaseBlock_append receipt_3_4_2383_0_part1 receipt_3_4_2383_0_part2 rfl rfl rfl
private theorem receipt_3_4_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 0) 0 303 = 2300713498849878396937808 :=
  phaseBlock_append receipt_3_4_2383_0_part0 receipt_3_4_2383_0_join0 rfl rfl rfl

private theorem receipt_3_4_2383_0 : fastPhase (bank 3 4).shape 179808 2383 4 1 1 1 0 = 2300713498849878396937808 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2383_0_join1

private theorem receipt_3_4_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 1) 0 128 = 1598649186971611720863232 := by decide +kernel
private theorem receipt_3_4_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 1) 128 128 = 642283301903952284757504 := by decide +kernel
private theorem receipt_3_4_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 1) 256 47 = 43070871267402950419356 := by decide +kernel
private theorem receipt_3_4_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 1) 128 175 = 685354173171355235176860 :=
  phaseBlock_append receipt_3_4_2383_1_part1 receipt_3_4_2383_1_part2 rfl rfl rfl
private theorem receipt_3_4_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2383 4 1 1 1 1) 0 303 = 2284003360142966956040092 :=
  phaseBlock_append receipt_3_4_2383_1_part0 receipt_3_4_2383_1_join0 rfl rfl rfl

private theorem receipt_3_4_2383_1 : fastPhase (bank 3 4).shape 179808 2383 4 1 1 1 1 = 2284003360142966956040092 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2383_1_join1

private theorem receipt_3_4_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 0) 0 128 = 1606926519517104997875104 := by decide +kernel
private theorem receipt_3_4_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 0) 128 128 = 648814281267774140050848 := by decide +kernel
private theorem receipt_3_4_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 0) 256 47 = 44987877401930316418172 := by decide +kernel
private theorem receipt_3_4_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 0) 128 175 = 693802158669704456469020 :=
  phaseBlock_append receipt_3_4_2384_0_part1 receipt_3_4_2384_0_part2 rfl rfl rfl
private theorem receipt_3_4_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 0) 0 303 = 2300728678186809454344124 :=
  phaseBlock_append receipt_3_4_2384_0_part0 receipt_3_4_2384_0_join0 rfl rfl rfl

private theorem receipt_3_4_2384_0 : fastPhase (bank 3 4).shape 179808 2384 4 1 1 1 0 = 2300728678186809454344124 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2384_0_join1

private theorem receipt_3_4_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 1) 0 128 = 1598661472861662759553696 := by decide +kernel
private theorem receipt_3_4_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 1) 128 128 = 642286018179646931827360 := by decide +kernel
private theorem receipt_3_4_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 1) 256 47 = 43070945453751391361100 := by decide +kernel
private theorem receipt_3_4_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 1) 128 175 = 685356963633398323188460 :=
  phaseBlock_append receipt_3_4_2384_1_part1 receipt_3_4_2384_1_part2 rfl rfl rfl
private theorem receipt_3_4_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179808 2384 4 1 1 1 1) 0 303 = 2284018436495061082742156 :=
  phaseBlock_append receipt_3_4_2384_1_part0 receipt_3_4_2384_1_join0 rfl rfl rfl

private theorem receipt_3_4_2384_1 : fastPhase (bank 3 4).shape 179808 2384 4 1 1 1 1 = 2284018436495061082742156 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2384_1_join1

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2383_0 receipt_3_4_2383_1 receipt_3_4_2384_0 receipt_3_4_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 4) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group1_stage i)).shape
      (cutoff h rect (group1_stage i)), ¬ G∣Q :=
  (group1_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group1_avoids

end Lower6960.RescueSource
