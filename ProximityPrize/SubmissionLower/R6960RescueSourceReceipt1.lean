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
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 0) 0 128 = 6989556470554152313187762 := by decide +kernel
private theorem receipt_0_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 0) 128 128 = 2569453358232007299224508 := by decide +kernel
private theorem receipt_0_1_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 0) 256 26 = 71031223821289631154682 := by decide +kernel
private theorem receipt_0_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 0) 128 154 = 2640484582053296930379190 :=
  phaseBlock_append receipt_0_1_2359_0_part1 receipt_0_1_2359_0_part2 rfl rfl rfl
private theorem receipt_0_1_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 0) 0 282 = 9630041052607449243566952 :=
  phaseBlock_append receipt_0_1_2359_0_part0 receipt_0_1_2359_0_join0 rfl rfl rfl

private theorem receipt_0_1_2359_0 : fastPhase (bank 0 1).shape 179818 2359 1 1 0 1 0 = 9630041052607449243566952 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2359_0_join1

private theorem receipt_0_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 1) 0 128 = 6951392110925555682999894 := by decide +kernel
private theorem receipt_0_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 1) 128 128 = 2539068053159057657481840 := by decide +kernel
private theorem receipt_0_1_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 1) 256 26 = 65727910839753147362970 := by decide +kernel
private theorem receipt_0_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 1) 128 154 = 2604795963998810804844810 :=
  phaseBlock_append receipt_0_1_2359_1_part1 receipt_0_1_2359_1_part2 rfl rfl rfl
private theorem receipt_0_1_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2359 1 1 0 1 1) 0 282 = 9556188074924366487844704 :=
  phaseBlock_append receipt_0_1_2359_1_part0 receipt_0_1_2359_1_join0 rfl rfl rfl

private theorem receipt_0_1_2359_1 : fastPhase (bank 0 1).shape 179818 2359 1 1 0 1 1 = 9556188074924366487844704 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2359_1_join1

private theorem receipt_0_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 0) 0 128 = 6989615393361176373693772 := by decide +kernel
private theorem receipt_0_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 0) 128 128 = 2569468697750383108115600 := by decide +kernel
private theorem receipt_0_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 0) 256 26 = 71031502743535119252103 := by decide +kernel
private theorem receipt_0_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 0) 128 154 = 2640500200493918227367703 :=
  phaseBlock_append receipt_0_1_2360_0_part1 receipt_0_1_2360_0_part2 rfl rfl rfl
private theorem receipt_0_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 0) 0 282 = 9630115593855094601061475 :=
  phaseBlock_append receipt_0_1_2360_0_part0 receipt_0_1_2360_0_join0 rfl rfl rfl

private theorem receipt_0_1_2360_0 : fastPhase (bank 0 1).shape 179818 2360 1 1 0 1 0 = 9630115593855094601061475 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2360_0_join1

private theorem receipt_0_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 1) 0 128 = 6951450767402923269798494 := by decide +kernel
private theorem receipt_0_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 1) 128 128 = 2539083237026679457810724 := by decide +kernel
private theorem receipt_0_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 1) 256 26 = 65728169834226223418581 := by decide +kernel
private theorem receipt_0_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 1) 128 154 = 2604811406860905681229305 :=
  phaseBlock_append receipt_0_1_2360_1_part1 receipt_0_1_2360_1_part2 rfl rfl rfl
private theorem receipt_0_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179818 2360 1 1 0 1 1) 0 282 = 9556262174263828951027799 :=
  phaseBlock_append receipt_0_1_2360_1_part0 receipt_0_1_2360_1_join0 rfl rfl rfl

private theorem receipt_0_1_2360_1 : fastPhase (bank 0 1).shape 179818 2360 1 1 0 1 1 = 9556262174263828951027799 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2360_1_join1

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2359_0 receipt_0_1_2359_1 receipt_0_1_2360_0 receipt_0_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 0) 0 128 = 6273149874890332774876773 := by decide +kernel
private theorem receipt_1_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 0) 128 128 = 2298050520603025514484402 := by decide +kernel
private theorem receipt_1_1_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 0) 256 26 = 63362317001275858774894 := by decide +kernel
private theorem receipt_1_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 0) 128 154 = 2361412837604301373259296 :=
  phaseBlock_append receipt_1_1_2359_0_part1 receipt_1_1_2359_0_part2 rfl rfl rfl
private theorem receipt_1_1_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 0) 0 282 = 8634562712494634148136069 :=
  phaseBlock_append receipt_1_1_2359_0_part0 receipt_1_1_2359_0_join0 rfl rfl rfl

private theorem receipt_1_1_2359_0 : fastPhase (bank 1 1).shape 179818 2359 1 1 0 2 0 = 8634562712494634148136069 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2359_0_join1

private theorem receipt_1_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 1) 0 128 = 6238720230268266661564996 := by decide +kernel
private theorem receipt_1_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 1) 128 128 = 2270818961800344647620431 := by decide +kernel
private theorem receipt_1_1_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 1) 256 26 = 58630420908937051086570 := by decide +kernel
private theorem receipt_1_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 1) 128 154 = 2329449382709281698707001 :=
  phaseBlock_append receipt_1_1_2359_1_part1 receipt_1_1_2359_1_part2 rfl rfl rfl
private theorem receipt_1_1_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2359 1 1 0 2 1) 0 282 = 8568169612977548360271997 :=
  phaseBlock_append receipt_1_1_2359_1_part0 receipt_1_1_2359_1_join0 rfl rfl rfl

private theorem receipt_1_1_2359_1 : fastPhase (bank 1 1).shape 179818 2359 1 1 0 2 1 = 8568169612977548360271997 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2359_1_join1

private theorem receipt_1_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 0) 0 128 = 6273202762990029977365852 := by decide +kernel
private theorem receipt_1_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 0) 128 128 = 2298064241534916172134870 := by decide +kernel
private theorem receipt_1_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 0) 256 26 = 63362565811335129757983 := by decide +kernel
private theorem receipt_1_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 0) 128 154 = 2361426807346251301892853 :=
  phaseBlock_append receipt_1_1_2360_0_part1 receipt_1_1_2360_0_part2 rfl rfl rfl
private theorem receipt_1_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 0) 0 282 = 8634629570336281279258705 :=
  phaseBlock_append receipt_1_1_2360_0_part0 receipt_1_1_2360_0_join0 rfl rfl rfl

private theorem receipt_1_1_2360_0 : fastPhase (bank 1 1).shape 179818 2360 1 1 0 2 0 = 8634629570336281279258705 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2360_0_join1

private theorem receipt_1_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 1) 0 128 = 6238772877817258354497015 := by decide +kernel
private theorem receipt_1_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 1) 128 128 = 2270832543161982016441378 := by decide +kernel
private theorem receipt_1_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 1) 256 26 = 58630651937922371362529 := by decide +kernel
private theorem receipt_1_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 1) 128 154 = 2329463195099904387803907 :=
  phaseBlock_append receipt_1_1_2360_1_part1 receipt_1_1_2360_1_part2 rfl rfl rfl
private theorem receipt_1_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179818 2360 1 1 0 2 1) 0 282 = 8568236072917162742300922 :=
  phaseBlock_append receipt_1_1_2360_1_part0 receipt_1_1_2360_1_join0 rfl rfl rfl

private theorem receipt_1_1_2360_1 : fastPhase (bank 1 1).shape 179818 2360 1 1 0 2 1 = 8568236072917162742300922 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2360_1_join1

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2359_0 receipt_1_1_2359_1 receipt_1_1_2360_0 receipt_1_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 0) 0 128 = 3295365720445289968729833 := by decide +kernel
private theorem receipt_2_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 0) 128 128 = 1176679356610874884915077 := by decide +kernel
private theorem receipt_2_1_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 0) 256 26 = 31818761885173391133754 := by decide +kernel
private theorem receipt_2_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 0) 128 154 = 1208498118496048276048831 :=
  phaseBlock_append receipt_2_1_2359_0_part1 receipt_2_1_2359_0_part2 rfl rfl rfl
private theorem receipt_2_1_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 0) 0 282 = 4503863838941338244778664 :=
  phaseBlock_append receipt_2_1_2359_0_part0 receipt_2_1_2359_0_join0 rfl rfl rfl

private theorem receipt_2_1_2359_0 : fastPhase (bank 2 1).shape 179818 2359 1 1 0 7 0 = 4503863838941338244778664 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2359_0_join1

private theorem receipt_2_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 1) 0 128 = 3276602951785875525195781 := by decide +kernel
private theorem receipt_2_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 1) 128 128 = 1162525085081616677356446 := by decide +kernel
private theorem receipt_2_1_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 1) 256 26 = 29438200747770403034355 := by decide +kernel
private theorem receipt_2_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 1) 128 154 = 1191963285829387080390801 :=
  phaseBlock_append receipt_2_1_2359_1_part1 receipt_2_1_2359_1_part2 rfl rfl rfl
private theorem receipt_2_1_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2359 1 1 0 7 1) 0 282 = 4468566237615262605586582 :=
  phaseBlock_append receipt_2_1_2359_1_part0 receipt_2_1_2359_1_join0 rfl rfl rfl

private theorem receipt_2_1_2359_1 : fastPhase (bank 2 1).shape 179818 2359 1 1 0 7 1 = 4468566237615262605586582 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2359_1_join1

private theorem receipt_2_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 0) 0 128 = 3295393521141176667007117 := by decide +kernel
private theorem receipt_2_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 0) 128 128 = 1176686388518480657468175 := by decide +kernel
private theorem receipt_2_1_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 0) 256 26 = 31818886837044718637688 := by decide +kernel
private theorem receipt_2_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 0) 128 154 = 1208505275355525376105863 :=
  phaseBlock_append receipt_2_1_2360_0_part1 receipt_2_1_2360_0_part2 rfl rfl rfl
private theorem receipt_2_1_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 0) 0 282 = 4503898796496702043112980 :=
  phaseBlock_append receipt_2_1_2360_0_part0 receipt_2_1_2360_0_join0 rfl rfl rfl

private theorem receipt_2_1_2360_0 : fastPhase (bank 2 1).shape 179818 2360 1 1 0 7 0 = 4503898796496702043112980 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2360_0_join1

private theorem receipt_2_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 1) 0 128 = 3276630620310554930884440 := by decide +kernel
private theorem receipt_2_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 1) 128 128 = 1162532044161480271343428 := by decide +kernel
private theorem receipt_2_1_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 1) 256 26 = 29438316752460256771949 := by decide +kernel
private theorem receipt_2_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 1) 128 154 = 1191970360913940528115377 :=
  phaseBlock_append receipt_2_1_2360_1_part1 receipt_2_1_2360_1_part2 rfl rfl rfl
private theorem receipt_2_1_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179818 2360 1 1 0 7 1) 0 282 = 4468600981224495458999817 :=
  phaseBlock_append receipt_2_1_2360_1_part0 receipt_2_1_2360_1_join0 rfl rfl rfl

private theorem receipt_2_1_2360_1 : fastPhase (bank 2 1).shape 179818 2360 1 1 0 7 1 = 4468600981224495458999817 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2360_1_join1

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2359_0 receipt_2_1_2359_1 receipt_2_1_2360_0 receipt_2_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 0) 0 128 = 308235561449937969831648 := by decide +kernel
private theorem receipt_3_1_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 0) 128 80 = 45419714654692638352428 := by decide +kernel
private theorem receipt_3_1_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 0) 0 208 = 353655276104630608184076 :=
  phaseBlock_append receipt_3_1_2359_0_part0 receipt_3_1_2359_0_part1 rfl rfl rfl

private theorem receipt_3_1_2359_0 : fastPhase (bank 3 1).shape 179818 2359 1 1 1 1 0 = 353655276104630608184076 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2359_0_join0

private theorem receipt_3_1_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 1) 0 128 = 305691935680484873975904 := by decide +kernel
private theorem receipt_3_1_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 1) 128 80 = 44243841399962956864092 := by decide +kernel
private theorem receipt_3_1_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2359 1 1 1 1 1) 0 208 = 349935777080447830839996 :=
  phaseBlock_append receipt_3_1_2359_1_part0 receipt_3_1_2359_1_part1 rfl rfl rfl

private theorem receipt_3_1_2359_1 : fastPhase (bank 3 1).shape 179818 2359 1 1 1 1 1 = 349935777080447830839996 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2359_1_join0

private theorem receipt_3_1_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 0) 0 128 = 308237801832621057127200 := by decide +kernel
private theorem receipt_3_1_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 0) 128 80 = 45419859176823527966100 := by decide +kernel
private theorem receipt_3_1_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 0) 0 208 = 353657661009444585093300 :=
  phaseBlock_append receipt_3_1_2360_0_part0 receipt_3_1_2360_0_part1 rfl rfl rfl

private theorem receipt_3_1_2360_0 : fastPhase (bank 3 1).shape 179818 2360 1 1 1 1 0 = 353657661009444585093300 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2360_0_join0

private theorem receipt_3_1_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 1) 0 128 = 305694156027453311414304 := by decide +kernel
private theorem receipt_3_1_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 1) 128 80 = 44243982462849830671860 := by decide +kernel
private theorem receipt_3_1_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179818 2360 1 1 1 1 1) 0 208 = 349938138490303142086164 :=
  phaseBlock_append receipt_3_1_2360_1_part0 receipt_3_1_2360_1_part1 rfl rfl rfl

private theorem receipt_3_1_2360_1 : fastPhase (bank 3 1).shape 179818 2360 1 1 1 1 1 = 349938138490303142086164 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2360_1_join0

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2359_0 receipt_3_1_2359_1 receipt_3_1_2360_0 receipt_3_1_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 0) 0 128 = 9940485494045992698716960 := by decide +kernel
private theorem receipt_0_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 0) 128 128 = 3686750391603879716358841 := by decide +kernel
private theorem receipt_0_2_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 0) 256 27 = 108759149638198400537826 := by decide +kernel
private theorem receipt_0_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 0) 128 155 = 3795509541242078116896667 :=
  phaseBlock_append receipt_0_2_2359_0_part1 receipt_0_2_2359_0_part2 rfl rfl rfl
private theorem receipt_0_2_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 0) 0 283 = 13735995035288070815613627 :=
  phaseBlock_append receipt_0_2_2359_0_part0 receipt_0_2_2359_0_join0 rfl rfl rfl

private theorem receipt_0_2_2359_0 : fastPhase (bank 0 2).shape 179818 2359 2 1 0 1 0 = 13735995035288070815613627 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2359_0_join1

private theorem receipt_0_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 1) 0 128 = 9886599975618448504911840 := by decide +kernel
private theorem receipt_0_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 1) 128 128 = 3643646926273448063304909 := by decide +kernel
private theorem receipt_0_2_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 1) 256 27 = 100927981835475415287039 := by decide +kernel
private theorem receipt_0_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 1) 128 155 = 3744574908108923478591948 :=
  phaseBlock_append receipt_0_2_2359_1_part1 receipt_0_2_2359_1_part2 rfl rfl rfl
private theorem receipt_0_2_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2359 2 1 0 1 1) 0 283 = 13631174883727371983503788 :=
  phaseBlock_append receipt_0_2_2359_1_part0 receipt_0_2_2359_1_join0 rfl rfl rfl

private theorem receipt_0_2_2359_1 : fastPhase (bank 0 2).shape 179818 2359 2 1 0 1 1 = 13631174883727371983503788 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2359_1_join1

private theorem receipt_0_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 0) 0 128 = 9940568359606589947290720 := by decide +kernel
private theorem receipt_0_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 0) 128 128 = 3686772402412006693291662 := by decide +kernel
private theorem receipt_0_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 0) 256 27 = 108759581533958874831396 := by decide +kernel
private theorem receipt_0_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 0) 128 155 = 3795531983945965568123058 :=
  phaseBlock_append receipt_0_2_2360_0_part1 receipt_0_2_2360_0_part2 rfl rfl rfl
private theorem receipt_0_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 0) 0 283 = 13736100343552555515413778 :=
  phaseBlock_append receipt_0_2_2360_0_part0 receipt_0_2_2360_0_join0 rfl rfl rfl

private theorem receipt_0_2_2360_0 : fastPhase (bank 0 2).shape 179818 2360 2 1 0 1 0 = 13736100343552555515413778 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2360_0_join1

private theorem receipt_0_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 1) 0 128 = 9886682468488037008368480 := by decide +kernel
private theorem receipt_0_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 1) 128 128 = 3643668715614093731360721 := by decide +kernel
private theorem receipt_0_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 1) 256 27 = 100928383989988336913461 := by decide +kernel
private theorem receipt_0_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 1) 128 155 = 3744597099604082068274182 :=
  phaseBlock_append receipt_0_2_2360_1_part1 receipt_0_2_2360_1_part2 rfl rfl rfl
private theorem receipt_0_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179818 2360 2 1 0 1 1) 0 283 = 13631279568092119076642662 :=
  phaseBlock_append receipt_0_2_2360_1_part0 receipt_0_2_2360_1_join0 rfl rfl rfl

private theorem receipt_0_2_2360_1 : fastPhase (bank 0 2).shape 179818 2360 2 1 0 1 1 = 13631279568092119076642662 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2360_1_join1

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2359_0 receipt_0_2_2359_1 receipt_0_2_2360_0 receipt_0_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 0) 0 128 = 8933205445991058848594400 := by decide +kernel
private theorem receipt_1_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 0) 128 128 = 3303288777072867313637731 := by decide +kernel
private theorem receipt_1_2_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 0) 256 27 = 97229191835623353530066 := by decide +kernel
private theorem receipt_1_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 0) 128 155 = 3400517968908490667167797 :=
  phaseBlock_append receipt_1_2_2359_0_part1 receipt_1_2_2359_0_part2 rfl rfl rfl
private theorem receipt_1_2_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 0) 0 283 = 12333723414899549515762197 :=
  phaseBlock_append receipt_1_2_2359_0_part0 receipt_1_2_2359_0_join0 rfl rfl rfl

private theorem receipt_1_2_2359_0 : fastPhase (bank 1 2).shape 179818 2359 2 1 0 2 0 = 12333723414899549515762197 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2359_0_join1

private theorem receipt_1_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 1) 0 128 = 8884564830069180295307104 := by decide +kernel
private theorem receipt_1_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 1) 128 128 = 3264599839682703193085127 := by decide +kernel
private theorem receipt_1_2_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 1) 256 27 = 90226716052046242493055 := by decide +kernel
private theorem receipt_1_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 1) 128 155 = 3354826555734749435578182 :=
  phaseBlock_append receipt_1_2_2359_1_part1 receipt_1_2_2359_1_part2 rfl rfl rfl
private theorem receipt_1_2_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2359 2 1 0 2 1) 0 283 = 12239391385803929730885286 :=
  phaseBlock_append receipt_1_2_2359_1_part0 receipt_1_2_2359_1_join0 rfl rfl rfl

private theorem receipt_1_2_2359_1 : fastPhase (bank 1 2).shape 179818 2359 2 1 0 2 1 = 12239391385803929730885286 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2359_1_join1

private theorem receipt_1_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 0) 0 128 = 8933279920146598458304800 := by decide +kernel
private theorem receipt_1_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 0) 128 128 = 3303308500527085206210642 := by decide +kernel
private theorem receipt_1_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 0) 256 27 = 97229577946936866739336 := by decide +kernel
private theorem receipt_1_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 0) 128 155 = 3400538078474022072949978 :=
  phaseBlock_append receipt_1_2_2360_0_part1 receipt_1_2_2360_0_part2 rfl rfl rfl
private theorem receipt_1_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 0) 0 283 = 12333817998620620531254778 :=
  phaseBlock_append receipt_1_2_2360_0_part0 receipt_1_2_2360_0_join0 rfl rfl rfl

private theorem receipt_1_2_2360_0 : fastPhase (bank 1 2).shape 179818 2360 2 1 0 2 0 = 12333817998620620531254778 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2360_0_join1

private theorem receipt_1_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 1) 0 128 = 8884638967472443593066720 := by decide +kernel
private theorem receipt_1_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 1) 128 128 = 3264619364261856969339978 := by decide +kernel
private theorem receipt_1_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 1) 256 27 = 90227075568702453918579 := by decide +kernel
private theorem receipt_1_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 1) 128 155 = 3354846439830559423258557 :=
  phaseBlock_append receipt_1_2_2360_1_part1 receipt_1_2_2360_1_part2 rfl rfl rfl
private theorem receipt_1_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179818 2360 2 1 0 2 1) 0 283 = 12239485407303003016325277 :=
  phaseBlock_append receipt_1_2_2360_1_part0 receipt_1_2_2360_1_join0 rfl rfl rfl

private theorem receipt_1_2_2360_1 : fastPhase (bank 1 2).shape 179818 2360 2 1 0 2 1 = 12239485407303003016325277 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2360_1_join1

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2359_0 receipt_1_2_2359_1 receipt_1_2_2360_0 receipt_1_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 0) 0 128 = 4731370394192367036278304 := by decide +kernel
private theorem receipt_2_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 0) 128 128 = 1711887346130013048172219 := by decide +kernel
private theorem receipt_2_2_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 0) 256 27 = 49563406270806374810402 := by decide +kernel
private theorem receipt_2_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 0) 128 155 = 1761450752400819422982621 :=
  phaseBlock_append receipt_2_2_2359_0_part1 receipt_2_2_2359_0_part2 rfl rfl rfl
private theorem receipt_2_2_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 0) 0 283 = 6492821146593186459260925 :=
  phaseBlock_append receipt_2_2_2359_0_part0 receipt_2_2_2359_0_join0 rfl rfl rfl

private theorem receipt_2_2_2359_0 : fastPhase (bank 2 2).shape 179818 2359 2 1 0 7 0 = 6492821146593186459260925 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2359_0_join1

private theorem receipt_2_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 1) 0 128 = 4704782399618221053563488 := by decide +kernel
private theorem receipt_2_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 1) 128 128 = 1691576208554396431753101 := by decide +kernel
private theorem receipt_2_2_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 1) 256 27 = 45988103220878041241565 := by decide +kernel
private theorem receipt_2_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 1) 128 155 = 1737564311775274472994666 :=
  phaseBlock_append receipt_2_2_2359_1_part1 receipt_2_2_2359_1_part2 rfl rfl rfl
private theorem receipt_2_2_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2359 2 1 0 7 1) 0 283 = 6442346711393495526558154 :=
  phaseBlock_append receipt_2_2_2359_1_part0 receipt_2_2_2359_1_join0 rfl rfl rfl

private theorem receipt_2_2_2359_1 : fastPhase (bank 2 2).shape 179818 2359 2 1 0 7 1 = 6442346711393495526558154 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2359_1_join1

private theorem receipt_2_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 0) 0 128 = 4731409859476842104467104 := by decide +kernel
private theorem receipt_2_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 0) 128 128 = 1711897575175709321443338 := by decide +kernel
private theorem receipt_2_2_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 0) 256 27 = 49563603103427179035598 := by decide +kernel
private theorem receipt_2_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 0) 128 155 = 1761461178279136500478936 :=
  phaseBlock_append receipt_2_2_2360_0_part1 receipt_2_2_2360_0_part2 rfl rfl rfl
private theorem receipt_2_2_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 0) 0 283 = 6492871037755978604946040 :=
  phaseBlock_append receipt_2_2_2360_0_part0 receipt_2_2_2360_0_join0 rfl rfl rfl

private theorem receipt_2_2_2360_0 : fastPhase (bank 2 2).shape 179818 2360 2 1 0 7 0 = 6492871037755978604946040 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2360_0_join1

private theorem receipt_2_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 1) 0 128 = 4704821679538491044789280 := by decide +kernel
private theorem receipt_2_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 1) 128 128 = 1691586332852969076824997 := by decide +kernel
private theorem receipt_2_2_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 1) 256 27 = 45988286472538184309469 := by decide +kernel
private theorem receipt_2_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 1) 128 155 = 1737574619325507261134466 :=
  phaseBlock_append receipt_2_2_2360_1_part1 receipt_2_2_2360_1_part2 rfl rfl rfl
private theorem receipt_2_2_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179818 2360 2 1 0 7 1) 0 283 = 6442396298863998305923746 :=
  phaseBlock_append receipt_2_2_2360_1_part0 receipt_2_2_2360_1_join0 rfl rfl rfl

private theorem receipt_2_2_2360_1 : fastPhase (bank 2 2).shape 179818 2360 2 1 0 7 1 = 6442396298863998305923746 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2360_1_join1

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2359_0 receipt_2_2_2359_1 receipt_2_2_2360_0 receipt_2_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 0) 0 128 = 469547617856445800596512 := by decide +kernel
private theorem receipt_3_2_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 0) 128 95 = 88820895334741948175000 := by decide +kernel
private theorem receipt_3_2_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 0) 0 223 = 558368513191187748771512 :=
  phaseBlock_append receipt_3_2_2359_0_part0 receipt_3_2_2359_0_part1 rfl rfl rfl

private theorem receipt_3_2_2359_0 : fastPhase (bank 3 2).shape 179818 2359 2 1 1 1 0 = 558368513191187748771512 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2359_0_join0

private theorem receipt_3_2_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 1) 0 128 = 466016763621493559639200 := by decide +kernel
private theorem receipt_3_2_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 1) 128 95 = 86872582005333355777041 := by decide +kernel
private theorem receipt_3_2_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2359 2 1 1 1 1) 0 223 = 552889345626826915416241 :=
  phaseBlock_append receipt_3_2_2359_1_part0 receipt_3_2_2359_1_part1 rfl rfl rfl

private theorem receipt_3_2_2359_1 : fastPhase (bank 3 2).shape 179818 2359 2 1 1 1 1 = 552889345626826915416241 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2359_1_join0

private theorem receipt_3_2_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 0) 0 128 = 469551067788544996513056 := by decide +kernel
private theorem receipt_3_2_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 0) 128 95 = 88821195596028834975064 := by decide +kernel
private theorem receipt_3_2_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 0) 0 223 = 558372263384573831488120 :=
  phaseBlock_append receipt_3_2_2360_0_part0 receipt_3_2_2360_0_part1 rfl rfl rfl

private theorem receipt_3_2_2360_0 : fastPhase (bank 3 2).shape 179818 2360 2 1 1 1 0 = 558372263384573831488120 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2360_0_join0

private theorem receipt_3_2_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 1) 0 128 = 466020185180048051541280 := by decide +kernel
private theorem receipt_3_2_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 1) 128 95 = 86872876188377013667774 := by decide +kernel
private theorem receipt_3_2_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179818 2360 2 1 1 1 1) 0 223 = 552893061368425065209054 :=
  phaseBlock_append receipt_3_2_2360_1_part0 receipt_3_2_2360_1_part1 rfl rfl rfl

private theorem receipt_3_2_2360_1 : fastPhase (bank 3 2).shape 179818 2360 2 1 1 1 1 = 552893061368425065209054 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2360_1_join0

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2359_0 receipt_3_2_2359_1 receipt_3_2_2360_0 receipt_3_2_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 0) 0 128 = 14940717151171454928642004 := by decide +kernel
private theorem receipt_0_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 0) 128 128 = 5497817419396684296881982 := by decide +kernel
private theorem receipt_0_3_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 0) 256 26 = 152096282814575814609342 := by decide +kernel
private theorem receipt_0_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 0) 128 154 = 5649913702211260111491324 :=
  phaseBlock_append receipt_0_3_2359_0_part1 receipt_0_3_2359_0_part2 rfl rfl rfl
private theorem receipt_0_3_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 0) 0 282 = 20590630853382715040133328 :=
  phaseBlock_append receipt_0_3_2359_0_part0 receipt_0_3_2359_0_join0 rfl rfl rfl

private theorem receipt_0_3_2359_0 : fastPhase (bank 0 3).shape 179818 2359 3 1 0 1 0 = 20590630853382715040133328 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2359_0_join1

private theorem receipt_0_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 1) 0 128 = 14859256973095353653084696 := by decide +kernel
private theorem receipt_0_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 1) 128 128 = 5432840050510719708464142 := by decide +kernel
private theorem receipt_0_3_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 1) 256 26 = 140741294200437948780330 := by decide +kernel
private theorem receipt_0_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 1) 128 154 = 5573581344711157657244472 :=
  phaseBlock_append receipt_0_3_2359_1_part1 receipt_0_3_2359_1_part2 rfl rfl rfl
private theorem receipt_0_3_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2359 3 1 0 1 1) 0 282 = 20432838317806511310329168 :=
  phaseBlock_append receipt_0_3_2359_1_part0 receipt_0_3_2359_1_join0 rfl rfl rfl

private theorem receipt_0_3_2359_1 : fastPhase (bank 0 3).shape 179818 2359 3 1 0 1 1 = 20432838317806511310329168 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2359_1_join1

private theorem receipt_0_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 0) 0 128 = 14940842291962092423972752 := by decide +kernel
private theorem receipt_0_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 0) 128 128 = 5497849926737097161750638 := by decide +kernel
private theorem receipt_0_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 0) 256 26 = 152096871046215347260841 := by decide +kernel
private theorem receipt_0_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 0) 128 154 = 5649946797783312509011479 :=
  phaseBlock_append receipt_0_3_2360_0_part1 receipt_0_3_2360_0_part2 rfl rfl rfl
private theorem receipt_0_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 0) 0 282 = 20590789089745404932984231 :=
  phaseBlock_append receipt_0_3_2360_0_part0 receipt_0_3_2360_0_join0 rfl rfl rfl

private theorem receipt_0_3_2360_0 : fastPhase (bank 0 3).shape 179818 2360 3 1 0 1 0 = 20590789089745404932984231 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2360_0_join1

private theorem receipt_0_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 1) 0 128 = 14859381549652646478755660 := by decide +kernel
private theorem receipt_0_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 1) 128 128 = 5432872228638161682560637 := by decide +kernel
private theorem receipt_0_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 1) 256 26 = 140741840440825639227411 := by decide +kernel
private theorem receipt_0_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 1) 128 154 = 5573614069078987321788048 :=
  phaseBlock_append receipt_0_3_2360_1_part1 receipt_0_3_2360_1_part2 rfl rfl rfl
private theorem receipt_0_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179818 2360 3 1 0 1 1) 0 282 = 20432995618731633800543708 :=
  phaseBlock_append receipt_0_3_2360_1_part0 receipt_0_3_2360_1_join0 rfl rfl rfl

private theorem receipt_0_3_2360_1 : fastPhase (bank 0 3).shape 179818 2360 3 1 0 1 1 = 20432995618731633800543708 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2360_1_join1

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2359_0 receipt_0_3_2359_1 receipt_0_3_2360_0 receipt_0_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 0) 0 128 = 13411219630965347011863043 := by decide +kernel
private theorem receipt_1_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 0) 128 128 = 4923233420331083604867183 := by decide +kernel
private theorem receipt_1_3_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 0) 256 26 = 135957398207620261136067 := by decide +kernel
private theorem receipt_1_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 0) 128 154 = 5059190818538703866003250 :=
  phaseBlock_append receipt_1_3_2359_0_part1 receipt_1_3_2359_0_part2 rfl rfl rfl
private theorem receipt_1_3_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 0) 0 282 = 18470410449504050877866293 :=
  phaseBlock_append receipt_1_3_2359_0_part0 receipt_1_3_2359_0_join0 rfl rfl rfl

private theorem receipt_1_3_2359_0 : fastPhase (bank 1 3).shape 179818 2359 3 1 0 2 0 = 18470410449504050877866293 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2359_0_join1

private theorem receipt_1_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 1) 0 128 = 13337839842034019138679906 := by decide +kernel
private theorem receipt_1_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 1) 128 128 = 4864965370004846706232881 := by decide +kernel
private theorem receipt_1_3_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 1) 256 26 = 125805590713921131755295 := by decide +kernel
private theorem receipt_1_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 1) 128 154 = 4990770960718767837988176 :=
  phaseBlock_append receipt_1_3_2359_1_part1 receipt_1_3_2359_1_part2 rfl rfl rfl
private theorem receipt_1_3_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2359 3 1 0 2 1) 0 282 = 18328610802752786976668082 :=
  phaseBlock_append receipt_1_3_2359_1_part0 receipt_1_3_2359_1_join0 rfl rfl rfl

private theorem receipt_1_3_2359_1 : fastPhase (bank 1 3).shape 179818 2359 3 1 0 2 1 = 18328610802752786976668082 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2359_1_join1

private theorem receipt_1_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 0) 0 128 = 13411331967810385400626725 := by decide +kernel
private theorem receipt_1_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 0) 128 128 = 4923262532742658029290649 := by decide +kernel
private theorem receipt_1_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 0) 256 26 = 135957924024756106633269 := by decide +kernel
private theorem receipt_1_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 0) 128 154 = 5059220456767414135923918 :=
  phaseBlock_append receipt_1_3_2360_0_part1 receipt_1_3_2360_0_part2 rfl rfl rfl
private theorem receipt_1_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 0) 0 282 = 18470552424577799536550643 :=
  phaseBlock_append receipt_1_3_2360_0_part0 receipt_1_3_2360_0_join0 rfl rfl rfl

private theorem receipt_1_3_2360_0 : fastPhase (bank 1 3).shape 179818 2360 3 1 0 2 0 = 18470552424577799536550643 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2360_0_join1

private theorem receipt_1_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 1) 0 128 = 13337951670200290222039968 := by decide +kernel
private theorem receipt_1_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 1) 128 128 = 4864994187087415839336975 := by decide +kernel
private theorem receipt_1_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 1) 256 26 = 125806078988542888472679 := by decide +kernel
private theorem receipt_1_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 1) 128 154 = 4990800266075958727809654 :=
  phaseBlock_append receipt_1_3_2360_1_part1 receipt_1_3_2360_1_part2 rfl rfl rfl
private theorem receipt_1_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179818 2360 3 1 0 2 1) 0 282 = 18328751936276248949849622 :=
  phaseBlock_append receipt_1_3_2360_1_part0 receipt_1_3_2360_1_join0 rfl rfl rfl

private theorem receipt_1_3_2360_1 : fastPhase (bank 1 3).shape 179818 2360 3 1 0 2 1 = 18328751936276248949849622 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2360_1_join1

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2359_0 receipt_1_3_2359_1 receipt_1_3_2360_0 receipt_1_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 0) 0 128 = 7036797562219460142489219 := by decide +kernel
private theorem receipt_2_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 0) 128 128 = 2538463226756481026406318 := by decide +kernel
private theorem receipt_2_3_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 0) 256 26 = 69182067157056637858242 := by decide +kernel
private theorem receipt_2_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 0) 128 154 = 2607645293913537664264560 :=
  phaseBlock_append receipt_2_3_2359_0_part1 receipt_2_3_2359_0_part2 rfl rfl rfl
private theorem receipt_2_3_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 0) 0 282 = 9644442856132997806753779 :=
  phaseBlock_append receipt_2_3_2359_0_part0 receipt_2_3_2359_0_join0 rfl rfl rfl

private theorem receipt_2_3_2359_0 : fastPhase (bank 2 3).shape 179818 2359 3 1 0 7 0 = 9644442856132997806753779 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2359_0_join1

private theorem receipt_2_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 1) 0 128 = 6997306986666192574638061 := by decide +kernel
private theorem receipt_2_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 1) 128 128 = 2508110425734950074222822 := by decide +kernel
private theorem receipt_2_3_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 1) 256 26 = 64009926028242995665310 := by decide +kernel
private theorem receipt_2_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 1) 128 154 = 2572120351763193069888132 :=
  phaseBlock_append receipt_2_3_2359_1_part1 receipt_2_3_2359_1_part2 rfl rfl rfl
private theorem receipt_2_3_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2359 3 1 0 7 1) 0 282 = 9569427338429385644526193 :=
  phaseBlock_append receipt_2_3_2359_1_part0 receipt_2_3_2359_1_join0 rfl rfl rfl

private theorem receipt_2_3_2359_1 : fastPhase (bank 2 3).shape 179818 2359 3 1 0 7 1 = 9569427338429385644526193 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2359_1_join1

private theorem receipt_2_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 0) 0 128 = 7036856530953689350304924 := by decide +kernel
private theorem receipt_2_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 0) 128 128 = 2538478246679152071894503 := by decide +kernel
private theorem receipt_2_3_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 0) 256 26 = 69182334729296826358349 := by decide +kernel
private theorem receipt_2_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 0) 128 154 = 2607660581408448898252852 :=
  phaseBlock_append receipt_2_3_2360_0_part1 receipt_2_3_2360_0_part2 rfl rfl rfl
private theorem receipt_2_3_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 0) 0 282 = 9644517112362138248557776 :=
  phaseBlock_append receipt_2_3_2360_0_part0 receipt_2_3_2360_0_join0 rfl rfl rfl

private theorem receipt_2_3_2360_0 : fastPhase (bank 2 3).shape 179818 2360 3 1 0 7 0 = 9644517112362138248557776 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2360_0_join1

private theorem receipt_2_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 1) 0 128 = 6997365680067591637400174 := by decide +kernel
private theorem receipt_2_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 1) 128 128 = 2508125291401237805989080 := by decide +kernel
private theorem receipt_2_3_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 1) 256 26 = 64010174470768167590889 := by decide +kernel
private theorem receipt_2_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 1) 128 154 = 2572135465872005973579969 :=
  phaseBlock_append receipt_2_3_2360_1_part1 receipt_2_3_2360_1_part2 rfl rfl rfl
private theorem receipt_2_3_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179818 2360 3 1 0 7 1) 0 282 = 9569501145939597610980143 :=
  phaseBlock_append receipt_2_3_2360_1_part0 receipt_2_3_2360_1_join0 rfl rfl rfl

private theorem receipt_2_3_2360_1 : fastPhase (bank 2 3).shape 179818 2360 3 1 0 7 1 = 9569501145939597610980143 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2360_1_join1

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2359_0 receipt_2_3_2359_1 receipt_2_3_2360_0 receipt_2_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 0) 0 128 = 693256944092452864938144 := by decide +kernel
private theorem receipt_3_3_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 0) 128 110 = 161381373683709655666146 := by decide +kernel
private theorem receipt_3_3_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 0) 0 238 = 854638317776162520604290 :=
  phaseBlock_append receipt_3_3_2359_0_part0 receipt_3_3_2359_0_part1 rfl rfl rfl

private theorem receipt_3_3_2359_0 : fastPhase (bank 3 3).shape 179818 2359 3 1 1 1 0 = 854638317776162520604290 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2359_0_join0

private theorem receipt_3_3_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 1) 0 128 = 688469362908471684705440 := by decide +kernel
private theorem receipt_3_3_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 1) 128 110 = 158309037738986233937409 := by decide +kernel
private theorem receipt_3_3_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2359 3 1 1 1 1) 0 238 = 846778400647457918642849 :=
  phaseBlock_append receipt_3_3_2359_1_part0 receipt_3_3_2359_1_part1 rfl rfl rfl

private theorem receipt_3_3_2359_1 : fastPhase (bank 3 3).shape 179818 2359 3 1 1 1 1 = 846778400647457918642849 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2359_1_join0

private theorem receipt_3_3_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 0) 0 128 = 693262089929402240069088 := by decide +kernel
private theorem receipt_3_3_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 0) 128 110 = 161381947500064255900936 := by decide +kernel
private theorem receipt_3_3_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 0) 0 238 = 854644037429466495970024 :=
  phaseBlock_append receipt_3_3_2360_0_part0 receipt_3_3_2360_0_part1 rfl rfl rfl

private theorem receipt_3_3_2360_0 : fastPhase (bank 3 3).shape 179818 2360 3 1 1 1 0 = 854644037429466495970024 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2360_0_join0

private theorem receipt_3_3_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 1) 0 128 = 688474469592966809314400 := by decide +kernel
private theorem receipt_3_3_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 1) 128 110 = 158309601485468714143731 := by decide +kernel
private theorem receipt_3_3_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179818 2360 3 1 1 1 1) 0 238 = 846784071078435523458131 :=
  phaseBlock_append receipt_3_3_2360_1_part0 receipt_3_3_2360_1_part1 rfl rfl rfl

private theorem receipt_3_3_2360_1 : fastPhase (bank 3 3).shape 179818 2360 3 1 1 1 1 = 846784071078435523458131 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2360_1_join0

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2359_0 receipt_3_3_2359_1 receipt_3_3_2360_0 receipt_3_3_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 0) 0 128 = 22565421200238256272617173 := by decide +kernel
private theorem receipt_0_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 0) 128 128 = 8863021353129825510321267 := by decide +kernel
private theorem receipt_0_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 0) 256 36 = 420286394930759914191894 := by decide +kernel
private theorem receipt_0_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 0) 128 164 = 9283307748060585424513161 :=
  phaseBlock_append receipt_0_4_2359_0_part1 receipt_0_4_2359_0_part2 rfl rfl rfl
private theorem receipt_0_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 0) 0 292 = 31848728948298841697130334 :=
  phaseBlock_append receipt_0_4_2359_0_part0 receipt_0_4_2359_0_join0 rfl rfl rfl

private theorem receipt_0_4_2359_0 : fastPhase (bank 0 4).shape 179818 2359 4 1 0 1 0 = 31848728948298841697130334 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2359_0_join1

private theorem receipt_0_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 1) 0 128 = 22447890277258017435753375 := by decide +kernel
private theorem receipt_0_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 1) 128 128 = 8768112400620694197003638 := by decide +kernel
private theorem receipt_0_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 1) 256 36 = 397331735234692493035430 := by decide +kernel
private theorem receipt_0_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 1) 128 164 = 9165444135855386690039068 :=
  phaseBlock_append receipt_0_4_2359_1_part1 receipt_0_4_2359_1_part2 rfl rfl rfl
private theorem receipt_0_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2359 4 1 0 1 1) 0 292 = 31613334413113404125792443 :=
  phaseBlock_append receipt_0_4_2359_1_part0 receipt_0_4_2359_1_join0 rfl rfl rfl

private theorem receipt_0_4_2359_1 : fastPhase (bank 0 4).shape 179818 2359 4 1 0 1 1 = 31613334413113404125792443 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2359_1_join1

private theorem receipt_0_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 0) 0 128 = 22565610110918244587888050 := by decide +kernel
private theorem receipt_0_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 0) 128 128 = 8863074707442011546840869 := by decide +kernel
private theorem receipt_0_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 0) 256 36 = 420288097892983132272938 := by decide +kernel
private theorem receipt_0_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 0) 128 164 = 9283362805334994679113807 :=
  phaseBlock_append receipt_0_4_2360_0_part1 receipt_0_4_2360_0_part2 rfl rfl rfl
private theorem receipt_0_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 0) 0 292 = 31848972916253239267001857 :=
  phaseBlock_append receipt_0_4_2360_0_part0 receipt_0_4_2360_0_join0 rfl rfl rfl

private theorem receipt_0_4_2360_0 : fastPhase (bank 0 4).shape 179818 2360 4 1 0 1 0 = 31848972916253239267001857 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2360_0_join1

private theorem receipt_0_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 1) 0 128 = 22448078372069395707711201 := by decide +kernel
private theorem receipt_0_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 1) 128 128 = 8768165262285059233001445 := by decide +kernel
private theorem receipt_0_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 1) 256 36 = 397333350342222864425898 := by decide +kernel
private theorem receipt_0_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 1) 128 164 = 9165498612627282097427343 :=
  phaseBlock_append receipt_0_4_2360_1_part1 receipt_0_4_2360_1_part2 rfl rfl rfl
private theorem receipt_0_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179818 2360 4 1 0 1 1) 0 292 = 31613576984696677805138544 :=
  phaseBlock_append receipt_0_4_2360_1_part0 receipt_0_4_2360_1_join0 rfl rfl rfl

private theorem receipt_0_4_2360_1 : fastPhase (bank 0 4).shape 179818 2360 4 1 0 1 1 = 31613576984696677805138544 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2360_1_join1

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2359_0 receipt_0_4_2359_1 receipt_0_4_2360_0 receipt_0_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 0) 0 128 = 20320057162515937008827685 := by decide +kernel
private theorem receipt_1_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 0) 128 128 = 7964315043826819215542671 := by decide +kernel
private theorem receipt_1_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 0) 256 36 = 377068891068000084964584 := by decide +kernel
private theorem receipt_1_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 0) 128 164 = 8341383934894819300507255 :=
  phaseBlock_append receipt_1_4_2359_0_part1 receipt_1_4_2359_0_part2 rfl rfl rfl
private theorem receipt_1_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 0) 0 292 = 28661441097410756309334940 :=
  phaseBlock_append receipt_1_4_2359_0_part0 receipt_1_4_2359_0_join0 rfl rfl rfl

private theorem receipt_1_4_2359_0 : fastPhase (bank 1 4).shape 179818 2359 4 1 0 2 0 = 28661441097410756309334940 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2359_0_join1

private theorem receipt_1_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 1) 0 128 = 20213877503287247192287695 := by decide +kernel
private theorem receipt_1_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 1) 128 128 = 7878910237951993428407078 := by decide +kernel
private theorem receipt_1_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 1) 256 36 = 356470434178611069010498 := by decide +kernel
private theorem receipt_1_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 1) 128 164 = 8235380672130604497417576 :=
  phaseBlock_append receipt_1_4_2359_1_part1 receipt_1_4_2359_1_part2 rfl rfl rfl
private theorem receipt_1_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2359 4 1 0 2 1) 0 292 = 28449258175417851689705271 :=
  phaseBlock_append receipt_1_4_2359_1_part0 receipt_1_4_2359_1_join0 rfl rfl rfl

private theorem receipt_1_4_2359_1 : fastPhase (bank 1 4).shape 179818 2359 4 1 0 2 1 = 28449258175417851689705271 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2359_1_join1

private theorem receipt_1_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 0) 0 128 = 20320227284285611769883756 := by decide +kernel
private theorem receipt_1_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 0) 128 128 = 7964362991439742258405591 := by decide +kernel
private theorem receipt_1_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 0) 256 36 = 377070418927961620914530 := by decide +kernel
private theorem receipt_1_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 0) 128 164 = 8341433410367703879320121 :=
  phaseBlock_append receipt_1_4_2360_0_part1 receipt_1_4_2360_0_part2 rfl rfl rfl
private theorem receipt_1_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 0) 0 292 = 28661660694653315649203877 :=
  phaseBlock_append receipt_1_4_2360_0_part0 receipt_1_4_2360_0_join0 rfl rfl rfl

private theorem receipt_1_4_2360_0 : fastPhase (bank 1 4).shape 179818 2360 4 1 0 2 0 = 28661660694653315649203877 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2360_0_join1

private theorem receipt_1_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 1) 0 128 = 20214046887447694181479011 := by decide +kernel
private theorem receipt_1_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 1) 128 128 = 7878957742104033372411584 := by decide +kernel
private theorem receipt_1_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 1) 256 36 = 356471883199631512740070 := by decide +kernel
private theorem receipt_1_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 1) 128 164 = 8235429625303664885151654 :=
  phaseBlock_append receipt_1_4_2360_1_part1 receipt_1_4_2360_1_part2 rfl rfl rfl
private theorem receipt_1_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179818 2360 4 1 0 2 1) 0 292 = 28449476512751359066630665 :=
  phaseBlock_append receipt_1_4_2360_1_part0 receipt_1_4_2360_1_join0 rfl rfl rfl

private theorem receipt_1_4_2360_1 : fastPhase (bank 1 4).shape 179818 2360 4 1 0 2 1 = 28449476512751359066630665 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2360_1_join1

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2359_0 receipt_1_4_2359_1 receipt_1_4_2360_0 receipt_1_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 0) 0 128 = 10902134642734390192312161 := by decide +kernel
private theorem receipt_2_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 0) 128 128 = 4208515286625877493666197 := by decide +kernel
private theorem receipt_2_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 0) 256 36 = 196956067621048385461770 := by decide +kernel
private theorem receipt_2_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 0) 128 164 = 4405471354246925879127967 :=
  phaseBlock_append receipt_2_4_2359_0_part1 receipt_2_4_2359_0_part2 rfl rfl rfl
private theorem receipt_2_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 0) 0 292 = 15307605996981316071440128 :=
  phaseBlock_append receipt_2_4_2359_0_part0 receipt_2_4_2359_0_join0 rfl rfl rfl

private theorem receipt_2_4_2359_0 : fastPhase (bank 2 4).shape 179818 2359 4 1 0 7 0 = 15307605996981316071440128 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2359_0_join1

private theorem receipt_2_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 1) 0 128 = 10843841659343934771037815 := by decide +kernel
private theorem receipt_2_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 1) 128 128 = 4162927254397855985872565 := by decide +kernel
private theorem receipt_2_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 1) 256 36 = 186180785283273007154494 := by decide +kernel
private theorem receipt_2_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 1) 128 164 = 4349108039681128993027059 :=
  phaseBlock_append receipt_2_4_2359_1_part1 receipt_2_4_2359_1_part2 rfl rfl rfl
private theorem receipt_2_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2359 4 1 0 7 1) 0 292 = 15192949699025063764064874 :=
  phaseBlock_append receipt_2_4_2359_1_part0 receipt_2_4_2359_1_join0 rfl rfl rfl

private theorem receipt_2_4_2359_1 : fastPhase (bank 2 4).shape 179818 2359 4 1 0 7 1 = 15192949699025063764064874 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2359_1_join1

private theorem receipt_2_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 0) 0 128 = 10902225949691677847154648 := by decide +kernel
private theorem receipt_2_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 0) 128 128 = 4208540636210614839753661 := by decide +kernel
private theorem receipt_2_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 0) 256 36 = 196956865717358860140911 := by decide +kernel
private theorem receipt_2_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 0) 128 164 = 4405497501927973699894572 :=
  phaseBlock_append receipt_2_4_2360_0_part1 receipt_2_4_2360_0_part2 rfl rfl rfl
private theorem receipt_2_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 0) 0 292 = 15307723451619651547049220 :=
  phaseBlock_append receipt_2_4_2360_0_part0 receipt_2_4_2360_0_join0 rfl rfl rfl

private theorem receipt_2_4_2360_0 : fastPhase (bank 2 4).shape 179818 2360 4 1 0 7 0 = 15307723451619651547049220 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2360_0_join1

private theorem receipt_2_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 1) 0 128 = 10843932559280213801643615 := by decide +kernel
private theorem receipt_2_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 1) 128 128 = 4162952366706731367212957 := by decide +kernel
private theorem receipt_2_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 1) 256 36 = 186181542129755925731251 := by decide +kernel
private theorem receipt_2_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 1) 128 164 = 4349133908836487292944208 :=
  phaseBlock_append receipt_2_4_2360_1_part1 receipt_2_4_2360_1_part2 rfl rfl rfl
private theorem receipt_2_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179818 2360 4 1 0 7 1) 0 292 = 15193066468116701094587823 :=
  phaseBlock_append receipt_2_4_2360_1_part0 receipt_2_4_2360_1_join0 rfl rfl rfl

private theorem receipt_2_4_2360_1 : fastPhase (bank 2 4).shape 179818 2360 4 1 0 7 1 = 15193066468116701094587823 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2360_1_join1

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2359_0 receipt_2_4_2359_1 receipt_2_4_2360_0 receipt_2_4_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 0) 0 128 = 1606812472231854683252224 := by decide +kernel
private theorem receipt_3_4_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 0) 128 128 = 648821466586642278778368 := by decide +kernel
private theorem receipt_3_4_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 0) 256 47 = 44991053351731209255552 := by decide +kernel
private theorem receipt_3_4_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 0) 128 175 = 693812519938373488033920 :=
  phaseBlock_append receipt_3_4_2359_0_part1 receipt_3_4_2359_0_part2 rfl rfl rfl
private theorem receipt_3_4_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 0) 0 303 = 2300624992170228171286144 :=
  phaseBlock_append receipt_3_4_2359_0_part0 receipt_3_4_2359_0_join0 rfl rfl rfl

private theorem receipt_3_4_2359_0 : fastPhase (bank 3 4).shape 179818 2359 4 1 1 1 0 = 2300624992170228171286144 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2359_0_join1

private theorem receipt_3_4_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 1) 0 128 = 1598548139179997170745216 := by decide +kernel
private theorem receipt_3_4_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 1) 128 128 = 642293128139180915908480 := by decide +kernel
private theorem receipt_3_4_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 1) 256 47 = 43073979391294561828380 := by decide +kernel
private theorem receipt_3_4_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 1) 128 175 = 685367107530475477736860 :=
  phaseBlock_append receipt_3_4_2359_1_part1 receipt_3_4_2359_1_part2 rfl rfl rfl
private theorem receipt_3_4_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2359 4 1 1 1 1) 0 303 = 2283915246710472648482076 :=
  phaseBlock_append receipt_3_4_2359_1_part0 receipt_3_4_2359_1_join0 rfl rfl rfl

private theorem receipt_3_4_2359_1 : fastPhase (bank 3 4).shape 179818 2359 4 1 1 1 1 = 2283915246710472648482076 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2359_1_join1

private theorem receipt_3_4_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 0) 0 128 = 1606824829549627218324000 := by decide +kernel
private theorem receipt_3_4_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 0) 128 128 = 648824211343548582582816 := by decide +kernel
private theorem receipt_3_4_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 0) 256 47 = 44991130613983427785644 := by decide +kernel
private theorem receipt_3_4_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 0) 128 175 = 693815341957532010368460 :=
  phaseBlock_append receipt_3_4_2360_0_part1 receipt_3_4_2360_0_part2 rfl rfl rfl
private theorem receipt_3_4_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 0) 0 303 = 2300640171507159228692460 :=
  phaseBlock_append receipt_3_4_2360_0_part0 receipt_3_4_2360_0_join0 rfl rfl rfl

private theorem receipt_3_4_2360_0 : fastPhase (bank 3 4).shape 179818 2360 4 1 1 1 0 = 2300640171507159228692460 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2360_0_join1

private theorem receipt_3_4_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 1) 0 128 = 1598560425070048209435680 := by decide +kernel
private theorem receipt_3_4_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 1) 128 128 = 642295844414875562978336 := by decide +kernel
private theorem receipt_3_4_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 1) 256 47 = 43074053577643002770124 := by decide +kernel
private theorem receipt_3_4_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 1) 128 175 = 685369897992518565748460 :=
  phaseBlock_append receipt_3_4_2360_1_part1 receipt_3_4_2360_1_part2 rfl rfl rfl
private theorem receipt_3_4_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179818 2360 4 1 1 1 1) 0 303 = 2283930323062566775184140 :=
  phaseBlock_append receipt_3_4_2360_1_part0 receipt_3_4_2360_1_join0 rfl rfl rfl

private theorem receipt_3_4_2360_1 : fastPhase (bank 3 4).shape 179818 2360 4 1 1 1 1 = 2283930323062566775184140 :=
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
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 4) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group1_stage i)).shape
      (cutoff h rect (group1_stage i)), ¬ G∣Q :=
  (group1_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group1_avoids

end Lower6960.RescueSource
