import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_977_207_part0 :
    blockEstimate 977 207 207 128 = 315454880 := rfl
private theorem moment_977_207_part1 :
    blockEstimate 977 207 335 128 = 1893094372 := rfl
private theorem moment_977_207_part2 :
    blockEstimate 977 207 463 128 = 3762297344 := rfl
private theorem moment_977_207_part3 :
    blockEstimate 977 207 591 128 = 4827257344 := rfl
private theorem moment_977_207_part4 :
    blockEstimate 977 207 719 128 = 5019802112 := rfl
private theorem moment_977_207_part5 :
    blockEstimate 977 207 847 128 = 4339931648 := rfl
private theorem moment_977_207_part6 :
    blockEstimate 977 207 975 128 = 2905553180 := rfl
private theorem moment_977_207_part7 :
    blockEstimate 977 207 1103 128 = 1377948994 := rfl
private theorem moment_977_207_part8 :
    blockEstimate 977 207 1231 128 = 313825184 := rfl
private theorem moment_977_207_part9 :
    blockEstimate 977 207 1359 32 = 3011176 := rfl
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
    blockEstimate 1047 222 222 128 = 340498080 := rfl
private theorem moment_1047_222_part1 :
    blockEstimate 1047 222 350 128 = 2075230592 := rfl
private theorem moment_1047_222_part2 :
    blockEstimate 1047 222 478 128 = 4311457024 := rfl
private theorem moment_1047_222_part3 :
    blockEstimate 1047 222 606 128 = 5736373504 := rfl
private theorem moment_1047_222_part4 :
    blockEstimate 1047 222 734 128 = 6225960192 := rfl
private theorem moment_1047_222_part5 :
    blockEstimate 1047 222 862 128 = 5780217088 := rfl
private theorem moment_1047_222_part6 :
    blockEstimate 1047 222 990 128 = 4419886184 := rfl
private theorem moment_1047_222_part7 :
    blockEstimate 1047 222 1118 128 = 2600283532 := rfl
private theorem moment_1047_222_part8 :
    blockEstimate 1047 222 1246 128 = 1026138287 := rfl
private theorem moment_1047_222_part9 :
    blockEstimate 1047 222 1374 117 = 137654825 := rfl
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
    blockEstimate 1117 237 237 128 = 365541280 := rfl
private theorem moment_1117_237_part1 :
    blockEstimate 1117 237 365 128 = 2252469787 := rfl
private theorem moment_1117_237_part2 :
    blockEstimate 1117 237 493 128 = 4866007104 := rfl
private theorem moment_1117_237_part3 :
    blockEstimate 1117 237 621 128 = 6688972864 := rfl
private theorem moment_1117_237_part4 :
    blockEstimate 1117 237 749 128 = 7513694272 := rfl
private theorem moment_1117_237_part5 :
    blockEstimate 1117 237 877 128 = 7340171328 := rfl
private theorem moment_1117_237_part6 :
    blockEstimate 1117 237 1005 128 = 6168649768 := rfl
private theorem moment_1117_237_part7 :
    blockEstimate 1117 237 1133 128 = 4198892547 := rfl
private theorem moment_1117_237_part8 :
    blockEstimate 1117 237 1261 128 = 2189402175 := rfl
private theorem moment_1117_237_part9 :
    blockEstimate 1117 237 1389 128 = 679563600 := rfl
private theorem moment_1117_237_part10 :
    blockEstimate 1117 237 1517 74 = 38827925 := rfl
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
    blockEstimate 1326 281 281 128 = 440313120 := rfl
private theorem moment_1326_281_part1 :
    blockEstimate 1326 281 409 128 = 2769958176 := rfl
private theorem moment_1326_281_part2 :
    blockEstimate 1326 281 537 128 = 6492999306 := rfl
private theorem moment_1326_281_part3 :
    blockEstimate 1326 281 665 128 = 9717503424 := rfl
private theorem moment_1326_281_part4 :
    blockEstimate 1326 281 793 128 = 11761980864 := rfl
private theorem moment_1326_281_part5 :
    blockEstimate 1326 281 921 128 = 12623664576 := rfl
private theorem moment_1326_281_part6 :
    blockEstimate 1326 281 1049 128 = 12302554560 := rfl
private theorem moment_1326_281_part7 :
    blockEstimate 1326 281 1177 128 = 10798650816 := rfl
private theorem moment_1326_281_part8 :
    blockEstimate 1326 281 1305 128 = 8203180395 := rfl
private theorem moment_1326_281_part9 :
    blockEstimate 1326 281 1433 128 = 5254501290 := rfl
private theorem moment_1326_281_part10 :
    blockEstimate 1326 281 1561 128 = 2634292110 := rfl
private theorem moment_1326_281_part11 :
    blockEstimate 1326 281 1689 128 = 787344864 := rfl
private theorem moment_1326_281_part12 :
    blockEstimate 1326 281 1817 71 = 41059686 := rfl
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
    blockEstimate 1327 281 281 128 = 440670880 := rfl
private theorem moment_1327_281_part1 :
    blockEstimate 1327 281 409 128 = 2772429472 := rfl
private theorem moment_1327_281_part2 :
    blockEstimate 1327 281 537 128 = 6499499186 := rfl
private theorem moment_1327_281_part3 :
    blockEstimate 1327 281 665 128 = 9728620992 := rfl
private theorem moment_1327_281_part4 :
    blockEstimate 1327 281 793 128 = 11777718720 := rfl
private theorem moment_1327_281_part5 :
    blockEstimate 1327 281 921 128 = 12644022720 := rfl
private theorem moment_1327_281_part6 :
    blockEstimate 1327 281 1049 128 = 12327532992 := rfl
private theorem moment_1327_281_part7 :
    blockEstimate 1327 281 1177 128 = 10828249536 := rfl
private theorem moment_1327_281_part8 :
    blockEstimate 1327 281 1305 128 = 8234870103 := rfl
private theorem moment_1327_281_part9 :
    blockEstimate 1327 281 1433 128 = 5281874916 := rfl
private theorem moment_1327_281_part10 :
    blockEstimate 1327 281 1561 128 = 2654626290 := rfl
private theorem moment_1327_281_part11 :
    blockEstimate 1327 281 1689 128 = 798423904 := rfl
private theorem moment_1327_281_part12 :
    blockEstimate 1327 281 1817 72 = 42800046 := rfl
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
    blockEstimate 1341 282 282 128 = 445679520 := rfl
private theorem moment_1341_282_part1 :
    blockEstimate 1341 282 410 128 = 2807027616 := rfl
private theorem moment_1341_282_part2 :
    blockEstimate 1341 282 538 128 = 6595706731 := rfl
private theorem moment_1341_282_part3 :
    blockEstimate 1341 282 666 128 = 9903134464 := rfl
private theorem moment_1341_282_part4 :
    blockEstimate 1341 282 794 128 = 12026730240 := rfl
private theorem moment_1341_282_part5 :
    blockEstimate 1341 282 922 128 = 12963337984 := rfl
private theorem moment_1341_282_part6 :
    blockEstimate 1341 282 1050 128 = 12712957696 := rfl
private theorem moment_1341_282_part7 :
    blockEstimate 1341 282 1178 128 = 11275589376 := rfl
private theorem moment_1341_282_part8 :
    blockEstimate 1341 282 1306 128 = 8711118963 := rfl
private theorem moment_1341_282_part9 :
    blockEstimate 1341 282 1434 128 = 5697061300 := rfl
private theorem moment_1341_282_part10 :
    blockEstimate 1341 282 1562 128 = 2967083923 := rfl
private theorem moment_1341_282_part11 :
    blockEstimate 1341 282 1690 128 = 974195776 := rfl
private theorem moment_1341_282_part12 :
    blockEstimate 1341 282 1818 87 = 75125996 := rfl
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
    blockEstimate 1387 302 302 128 = 462136480 := rfl
private theorem moment_1387_302_part1 :
    blockEstimate 1387 302 430 128 = 2920707232 := rfl
private theorem moment_1387_302_part2 :
    blockEstimate 1387 302 558 128 = 6982836384 := rfl
private theorem moment_1387_302_part3 :
    blockEstimate 1387 302 686 128 = 10787226624 := rfl
private theorem moment_1387_302_part4 :
    blockEstimate 1387 302 814 128 = 13338903552 := rfl
private theorem moment_1387_302_part5 :
    blockEstimate 1387 302 942 128 = 14619706368 := rfl
private theorem moment_1387_302_part6 :
    blockEstimate 1387 302 1070 128 = 14629635072 := rfl
private theorem moment_1387_302_part7 :
    blockEstimate 1387 302 1198 128 = 13368689664 := rfl
private theorem moment_1387_302_part8 :
    blockEstimate 1387 302 1326 128 = 10858832125 := rfl
private theorem moment_1387_302_part9 :
    blockEstimate 1387 302 1454 128 = 7630480965 := rfl
private theorem moment_1387_302_part10 :
    blockEstimate 1387 302 1582 128 = 4503008202 := rfl
private theorem moment_1387_302_part11 :
    blockEstimate 1387 302 1710 128 = 1955193296 := rfl
private theorem moment_1387_302_part12 :
    blockEstimate 1387 302 1838 128 = 402271696 := rfl
private theorem moment_1387_302_part13 :
    blockEstimate 1387 302 1966 25 = 2128560 := rfl
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
    blockEstimate 1392 291 291 128 = 463925280 := rfl
private theorem moment_1392_291_part1 :
    blockEstimate 1392 291 419 128 = 2933063712 := rfl
private theorem moment_1392_291_part2 :
    blockEstimate 1392 291 547 128 = 6972032551 := rfl
private theorem moment_1392_291_part3 :
    blockEstimate 1392 291 675 128 = 10645366912 := rfl
private theorem moment_1392_291_part4 :
    blockEstimate 1392 291 803 128 = 13102016640 := rfl
private theorem moment_1392_291_part5 :
    blockEstimate 1392 291 931 128 = 14333929600 := rfl
private theorem moment_1392_291_part6 :
    blockEstimate 1392 291 1059 128 = 14341105792 := rfl
private theorem moment_1392_291_part7 :
    blockEstimate 1392 291 1187 128 = 13123545216 := rfl
private theorem moment_1392_291_part8 :
    blockEstimate 1392 291 1315 128 = 10691106230 := rfl
private theorem moment_1392_291_part9 :
    blockEstimate 1392 291 1443 128 = 7487810802 := rfl
private theorem moment_1392_291_part10 :
    blockEstimate 1392 291 1571 128 = 4379387141 := rfl
private theorem moment_1392_291_part11 :
    blockEstimate 1392 291 1699 128 = 1864956928 := rfl
private theorem moment_1392_291_part12 :
    blockEstimate 1392 291 1827 128 = 360231936 := rfl
private theorem moment_1392_291_part13 :
    blockEstimate 1392 291 1955 19 = 989370 := rfl
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

private theorem receipt_0_1_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 0) 0 128 = 7150698649590065104697454 := rfl
private theorem receipt_0_1_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 0) 128 128 = 2628932870395852279174392 := rfl
private theorem receipt_0_1_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 0) 256 26 = 72680822662740090530109 := rfl
private theorem receipt_0_1_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 0) 128 154 = 2701613693058592369704501 :=
  phaseBlock_append receipt_0_1_2339_0_part1 receipt_0_1_2339_0_part2 rfl rfl rfl
private theorem receipt_0_1_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 0) 0 282 = 9852312342648657474401955 :=
  phaseBlock_append receipt_0_1_2339_0_part0 receipt_0_1_2339_0_join0 rfl rfl rfl

private theorem receipt_0_1_2339_0 : fastPhase (bank 0 1).shape 179827 2339 1 1 0 1 0 = 9852312342648657474401955 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2339_0_join1

private theorem receipt_0_1_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 1) 0 128 = 7111655711963889809963283 := rfl
private theorem receipt_0_1_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 1) 128 128 = 2597844431376453545366181 := rfl
private theorem receipt_0_1_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 1) 256 26 = 67254345592752538273605 := rfl
private theorem receipt_0_1_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 1) 128 154 = 2665098776969206083639786 :=
  phaseBlock_append receipt_0_1_2339_1_part1 receipt_0_1_2339_1_part2 rfl rfl rfl
private theorem receipt_0_1_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2339 1 1 0 1 1) 0 282 = 9776754488933095893603069 :=
  phaseBlock_append receipt_0_1_2339_1_part0 receipt_0_1_2339_1_join0 rfl rfl rfl

private theorem receipt_0_1_2339_1 : fastPhase (bank 0 1).shape 179827 2339 1 1 0 1 1 = 9776754488933095893603069 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2339_1_join1

private theorem receipt_0_1_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 0) 0 128 = 7150758920382981417954803 := rfl
private theorem receipt_0_1_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 0) 128 128 = 2628948562008777540946827 := rfl
private theorem receipt_0_1_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 0) 256 26 = 72681108037479817837290 := rfl
private theorem receipt_0_1_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 0) 128 154 = 2701629670046257358784117 :=
  phaseBlock_append receipt_0_1_2340_0_part1 receipt_0_1_2340_0_part2 rfl rfl rfl
private theorem receipt_0_1_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 0) 0 282 = 9852388590429238776738920 :=
  phaseBlock_append receipt_0_1_2340_0_part0 receipt_0_1_2340_0_join0 rfl rfl rfl

private theorem receipt_0_1_2340_0 : fastPhase (bank 0 1).shape 179827 2340 1 1 0 1 0 = 9852388590429238776738920 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2340_0_join1

private theorem receipt_0_1_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 1) 0 128 = 7111715710349890286438355 := rfl
private theorem receipt_0_1_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 1) 128 128 = 2597859963770285749252011 := rfl
private theorem receipt_0_1_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 1) 256 26 = 67254610580212173384621 := rfl
private theorem receipt_0_1_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 1) 128 154 = 2665114574350497922636632 :=
  phaseBlock_append receipt_0_1_2340_1_part1 receipt_0_1_2340_1_part2 rfl rfl rfl
private theorem receipt_0_1_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 1).shape 179827 2340 1 1 0 1 1) 0 282 = 9776830284700388209074987 :=
  phaseBlock_append receipt_0_1_2340_1_part0 receipt_0_1_2340_1_join0 rfl rfl rfl

private theorem receipt_0_1_2340_1 : fastPhase (bank 0 1).shape 179827 2340 1 1 0 1 1 = 9776830284700388209074987 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_1_2340_1_join1

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2339_0 receipt_0_1_2339_1 receipt_0_1_2340_0 receipt_0_1_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 0) 0 128 = 6417951720375895488220062 := rfl
private theorem receipt_1_1_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 0) 128 128 = 2351405713133218509886401 := rfl
private theorem receipt_1_1_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 0) 256 26 = 64840128510492825968352 := rfl
private theorem receipt_1_1_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 0) 128 154 = 2416245841643711335854753 :=
  phaseBlock_append receipt_1_1_2339_0_part1 receipt_1_1_2339_0_part2 rfl rfl rfl
private theorem receipt_1_1_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 0) 0 282 = 8834197562019606824074815 :=
  phaseBlock_append receipt_1_1_2339_0_part0 receipt_1_1_2339_0_join0 rfl rfl rfl

private theorem receipt_1_1_2339_0 : fastPhase (bank 1 1).shape 179827 2339 1 1 0 2 0 = 8834197562019606824074815 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2339_0_join1

private theorem receipt_1_1_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 1) 0 128 = 6382730562792791055002253 := rfl
private theorem receipt_1_1_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 1) 128 128 = 2323542776444804226623622 := rfl
private theorem receipt_1_1_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 1) 256 26 = 59997881118642128332635 := rfl
private theorem receipt_1_1_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 1) 128 154 = 2383540657563446354956257 :=
  phaseBlock_append receipt_1_1_2339_1_part1 receipt_1_1_2339_1_part2 rfl rfl rfl
private theorem receipt_1_1_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2339 1 1 0 2 1) 0 282 = 8766271220356237409958510 :=
  phaseBlock_append receipt_1_1_2339_1_part0 receipt_1_1_2339_1_join0 rfl rfl rfl

private theorem receipt_1_1_2339_1 : fastPhase (bank 1 1).shape 179827 2339 1 1 0 2 1 = 8766271220356237409958510 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2339_1_join1

private theorem receipt_1_1_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 0) 0 128 = 6418005819833162938918187 := rfl
private theorem receipt_1_1_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 0) 128 128 = 2351419749932947532793855 := rfl
private theorem receipt_1_1_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 0) 256 26 = 64840383101208620808336 := rfl
private theorem receipt_1_1_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 0) 128 154 = 2416260133034156153602191 :=
  phaseBlock_append receipt_1_1_2340_0_part1 receipt_1_1_2340_0_part2 rfl rfl rfl
private theorem receipt_1_1_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 0) 0 282 = 8834265952867319092520378 :=
  phaseBlock_append receipt_1_1_2340_0_part0 receipt_1_1_2340_0_join0 rfl rfl rfl

private theorem receipt_1_1_2340_0 : fastPhase (bank 1 1).shape 179827 2340 1 1 0 2 0 = 8834265952867319092520378 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2340_0_join1

private theorem receipt_1_1_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 1) 0 128 = 6382784416221185931798642 := rfl
private theorem receipt_1_1_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 1) 128 128 = 2323556670469184709554922 := rfl
private theorem receipt_1_1_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 1) 256 26 = 59998117516560660594939 := rfl
private theorem receipt_1_1_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 1) 128 154 = 2383554787985745370149861 :=
  phaseBlock_append receipt_1_1_2340_1_part1 receipt_1_1_2340_1_part2 rfl rfl rfl
private theorem receipt_1_1_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 1).shape 179827 2340 1 1 0 2 1) 0 282 = 8766339204206931301948503 :=
  phaseBlock_append receipt_1_1_2340_1_part0 receipt_1_1_2340_1_join0 rfl rfl rfl

private theorem receipt_1_1_2340_1 : fastPhase (bank 1 1).shape 179827 2340 1 1 0 2 1 = 8766339204206931301948503 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_1_2340_1_join1

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2339_0 receipt_1_1_2339_1 receipt_1_1_2340_0 receipt_1_1_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 0) 0 128 = 3371705546208694889341224 := rfl
private theorem receipt_2_1_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 0) 128 128 = 1204452350491965772196517 := rfl
private theorem receipt_2_1_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 0) 256 26 = 32580578305218328215579 := rfl
private theorem receipt_2_1_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 0) 128 154 = 1237032928797184100412096 :=
  phaseBlock_append receipt_2_1_2339_0_part1 receipt_2_1_2339_0_part2 rfl rfl rfl
private theorem receipt_2_1_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 0) 0 282 = 4608738475005878989753320 :=
  phaseBlock_append receipt_2_1_2339_0_part0 receipt_2_1_2339_0_join0 rfl rfl rfl

private theorem receipt_2_1_2339_0 : fastPhase (bank 2 1).shape 179827 2339 1 1 0 7 0 = 4608738475005878989753320 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2339_0_join1

private theorem receipt_2_1_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 1) 0 128 = 3352517719341941333396010 := rfl
private theorem receipt_2_1_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 1) 128 128 = 1189966958979962651927733 := rfl
private theorem receipt_2_1_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 1) 256 26 = 30143079225780629393390 := rfl
private theorem receipt_2_1_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 1) 128 154 = 1220110038205743281321123 :=
  phaseBlock_append receipt_2_1_2339_1_part1 receipt_2_1_2339_1_part2 rfl rfl rfl
private theorem receipt_2_1_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2339 1 1 0 7 1) 0 282 = 4572627757547684614717133 :=
  phaseBlock_append receipt_2_1_2339_1_part0 receipt_2_1_2339_1_join0 rfl rfl rfl

private theorem receipt_2_1_2339_1 : fastPhase (bank 2 1).shape 179827 2339 1 1 0 7 1 = 4572627757547684614717133 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2339_1_join1

private theorem receipt_2_1_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 0) 0 128 = 3371733985746273149823632 := rfl
private theorem receipt_2_1_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 0) 128 128 = 1204459546913597057396264 := rfl
private theorem receipt_2_1_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 0) 256 26 = 32580706237418896806928 := rfl
private theorem receipt_2_1_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 0) 128 154 = 1237040253151015954203192 :=
  phaseBlock_append receipt_2_1_2340_0_part1 receipt_2_1_2340_0_part2 rfl rfl rfl
private theorem receipt_2_1_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 0) 0 282 = 4608774238897289104026824 :=
  phaseBlock_append receipt_2_1_2340_0_part0 receipt_2_1_2340_0_join0 rfl rfl rfl

private theorem receipt_2_1_2340_0 : fastPhase (bank 2 1).shape 179827 2340 1 1 0 7 0 = 4608774238897289104026824 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2340_0_join1

private theorem receipt_2_1_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 1) 0 128 = 3352546023754497546658311 := rfl
private theorem receipt_2_1_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 1) 128 128 = 1189974080889551603405613 := rfl
private theorem receipt_2_1_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 1) 256 26 = 30143197998301558743244 := rfl
private theorem receipt_2_1_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 1) 128 154 = 1220117278887853162148857 :=
  phaseBlock_append receipt_2_1_2340_1_part1 receipt_2_1_2340_1_part2 rfl rfl rfl
private theorem receipt_2_1_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 1).shape 179827 2340 1 1 0 7 1) 0 282 = 4572663302642350708807168 :=
  phaseBlock_append receipt_2_1_2340_1_part0 receipt_2_1_2340_1_join0 rfl rfl rfl

private theorem receipt_2_1_2340_1 : fastPhase (bank 2 1).shape 179827 2340 1 1 0 7 1 = 4572663302642350708807168 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_1_2340_1_join1

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2339_0 receipt_2_1_2339_1 receipt_2_1_2340_0 receipt_2_1_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2339 1 1 1 1 0) 0 128 = 313649903385269955459360 := rfl
private theorem receipt_3_1_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2339 1 1 1 1 0) 128 80 = 46224133723879606553940 := rfl
private theorem receipt_3_1_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2339 1 1 1 1 0) 0 208 = 359874037109149562013300 :=
  phaseBlock_append receipt_3_1_2339_0_part0 receipt_3_1_2339_0_part1 rfl rfl rfl

private theorem receipt_3_1_2339_0 : fastPhase (bank 3 1).shape 179827 2339 1 1 1 1 0 = 359874037109149562013300 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2339_0_join0

private theorem receipt_3_1_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2339 1 1 1 1 1) 0 128 = 311061799001923895525664 := rfl
private theorem receipt_3_1_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2339 1 1 1 1 1) 128 80 = 45027447284542547818644 := rfl
private theorem receipt_3_1_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2339 1 1 1 1 1) 0 208 = 356089246286466443344308 :=
  phaseBlock_append receipt_3_1_2339_1_part0 receipt_3_1_2339_1_part1 rfl rfl rfl

private theorem receipt_3_1_2339_1 : fastPhase (bank 3 1).shape 179827 2339 1 1 1 1 1 = 356089246286466443344308 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2339_1_join0

private theorem receipt_3_1_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2340 1 1 1 1 0) 0 128 = 313652183194502258939232 := rfl
private theorem receipt_3_1_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2340 1 1 1 1 0) 128 80 = 46224280799270102981052 := rfl
private theorem receipt_3_1_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2340 1 1 1 1 0) 0 208 = 359876463993772361920284 :=
  phaseBlock_append receipt_3_1_2340_0_part0 receipt_3_1_2340_0_part1 rfl rfl rfl

private theorem receipt_3_1_2340_0 : fastPhase (bank 3 1).shape 179827 2340 1 1 1 1 0 = 359876463993772361920284 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2340_0_join0

private theorem receipt_3_1_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2340 1 1 1 1 1) 0 128 = 311064058424217657430752 := rfl
private theorem receipt_3_1_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2340 1 1 1 1 1) 128 80 = 45027590839649048196972 := rfl
private theorem receipt_3_1_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 1).shape 179827 2340 1 1 1 1 1) 0 208 = 356091649263866705627724 :=
  phaseBlock_append receipt_3_1_2340_1_part0 receipt_3_1_2340_1_part1 rfl rfl rfl

private theorem receipt_3_1_2340_1 : fastPhase (bank 3 1).shape 179827 2340 1 1 1 1 1 = 356091649263866705627724 :=
  phase_of_block (n := 208) (by decide +kernel) receipt_3_1_2340_1_join0

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2339_0 receipt_3_1_2339_1 receipt_3_1_2340_0 receipt_3_1_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 0) 0 128 = 10223560318730402432268480 := rfl
private theorem receipt_0_2_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 0) 128 128 = 3792087093620021499346186 := rfl
private theorem receipt_0_2_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 0) 256 27 = 111874823804490500994210 := rfl
private theorem receipt_0_2_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 0) 128 155 = 3903961917424512000340396 :=
  phaseBlock_append receipt_0_2_2339_0_part1 receipt_0_2_2339_0_part2 rfl rfl rfl
private theorem receipt_0_2_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 0) 0 283 = 14127522236154914432608876 :=
  phaseBlock_append receipt_0_2_2339_0_part0 receipt_0_2_2339_0_join0 rfl rfl rfl

private theorem receipt_0_2_2339_0 : fastPhase (bank 0 2).shape 179827 2339 2 1 0 1 0 = 14127522236154914432608876 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2339_0_join1

private theorem receipt_0_2_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 1) 0 128 = 10168142334414026388720000 := rfl
private theorem receipt_0_2_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 1) 128 128 = 3747752514984864675050350 := rfl
private theorem receipt_0_2_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 1) 256 27 = 103819310908832805318384 := rfl
private theorem receipt_0_2_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 1) 128 155 = 3851571825893697480368734 :=
  phaseBlock_append receipt_0_2_2339_1_part1 receipt_0_2_2339_1_part2 rfl rfl rfl
private theorem receipt_0_2_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2339 2 1 0 1 1) 0 283 = 14019714160307723869088734 :=
  phaseBlock_append receipt_0_2_2339_1_part0 receipt_0_2_2339_1_join0 rfl rfl rfl

private theorem receipt_0_2_2339_1 : fastPhase (bank 0 2).shape 179827 2339 2 1 0 1 1 = 14019714160307723869088734 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2339_1_join1

private theorem receipt_0_2_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 0) 0 128 = 10223645548478581816555840 := rfl
private theorem receipt_0_2_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 0) 128 128 = 3792109731878027277726336 := rfl
private theorem receipt_0_2_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 0) 256 27 = 111875267997913671067206 := rfl
private theorem receipt_0_2_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 0) 128 155 = 3903984999875940948793542 :=
  phaseBlock_append receipt_0_2_2340_0_part1 receipt_0_2_2340_0_part2 rfl rfl rfl
private theorem receipt_0_2_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 0) 0 283 = 14127630548354522765349382 :=
  phaseBlock_append receipt_0_2_2340_0_part0 receipt_0_2_2340_0_join0 rfl rfl rfl

private theorem receipt_0_2_2340_0 : fastPhase (bank 0 2).shape 179827 2340 2 1 0 1 0 = 14127630548354522765349382 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2340_0_join1

private theorem receipt_0_2_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 1) 0 128 = 10168227180864129418505280 := rfl
private theorem receipt_0_2_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 1) 128 128 = 3747774925475273474046617 := rfl
private theorem receipt_0_2_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 1) 256 27 = 103819724516892405000216 := rfl
private theorem receipt_0_2_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 1) 128 155 = 3851594649992165879046833 :=
  phaseBlock_append receipt_0_2_2340_1_part1 receipt_0_2_2340_1_part2 rfl rfl rfl
private theorem receipt_0_2_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 2).shape 179827 2340 2 1 0 1 1) 0 283 = 14019821830856295297552113 :=
  phaseBlock_append receipt_0_2_2340_1_part0 receipt_0_2_2340_1_join0 rfl rfl rfl

private theorem receipt_0_2_2340_1 : fastPhase (bank 0 2).shape 179827 2340 2 1 0 1 1 = 14019821830856295297552113 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_0_2_2340_1_join1

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2339_0 receipt_0_2_2339_1 receipt_0_2_2340_0 receipt_0_2_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 0) 0 128 = 9187712536681794975339840 := rfl
private theorem receipt_1_2_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 0) 128 128 = 3397854571133825567635671 := rfl
private theorem receipt_1_2_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 0) 256 27 = 100023163598646684890100 := rfl
private theorem receipt_1_2_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 0) 128 155 = 3497877734732472252525771 :=
  phaseBlock_append receipt_1_2_2339_0_part1 receipt_1_2_2339_0_part2 rfl rfl rfl
private theorem receipt_1_2_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 0) 0 283 = 12685590271414267227865611 :=
  phaseBlock_append receipt_1_2_2339_0_part0 receipt_1_2_2339_0_join0 rfl rfl rfl

private theorem receipt_1_2_2339_0 : fastPhase (bank 1 2).shape 179827 2339 2 1 0 2 0 = 12685590271414267227865611 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2339_0_join1

private theorem receipt_1_2_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 1) 0 128 = 9137691070088681263102464 := rfl
private theorem receipt_1_2_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 1) 128 128 = 3358059429316263604199355 := rfl
private theorem receipt_1_2_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 1) 256 27 = 92819485369101221545653 := rfl
private theorem receipt_1_2_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 1) 128 155 = 3450878914685364825745008 :=
  phaseBlock_append receipt_1_2_2339_1_part1 receipt_1_2_2339_1_part2 rfl rfl rfl
private theorem receipt_1_2_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2339 2 1 0 2 1) 0 283 = 12588569984774046088847472 :=
  phaseBlock_append receipt_1_2_2339_1_part0 receipt_1_2_2339_1_join0 rfl rfl rfl

private theorem receipt_1_2_2339_1 : fastPhase (bank 1 2).shape 179827 2339 2 1 0 2 1 = 12588569984774046088847472 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2339_1_join1

private theorem receipt_1_2_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 0) 0 128 = 9187789136509111883867840 := rfl
private theorem receipt_1_2_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 0) 128 128 = 3397874857912055255390655 := rfl
private theorem receipt_1_2_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 0) 256 27 = 100023560738101239729786 := rfl
private theorem receipt_1_2_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 0) 128 155 = 3497898418650156495120441 :=
  phaseBlock_append receipt_1_2_2340_0_part1 receipt_1_2_2340_0_part2 rfl rfl rfl
private theorem receipt_1_2_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 0) 0 283 = 12685687555159268378988281 :=
  phaseBlock_append receipt_1_2_2340_0_part0 receipt_1_2_2340_0_join0 rfl rfl rfl

private theorem receipt_1_2_2340_0 : fastPhase (bank 1 2).shape 179827 2340 2 1 0 2 0 = 12685687555159268378988281 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2340_0_join1

private theorem receipt_1_2_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 1) 0 128 = 9137767323601234544233280 := rfl
private theorem receipt_1_2_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 1) 128 128 = 3358079511557197047502260 := rfl
private theorem receipt_1_2_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 1) 256 27 = 92819855156827609802943 := rfl
private theorem receipt_1_2_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 1) 128 155 = 3450899366714024657305203 :=
  phaseBlock_append receipt_1_2_2340_1_part1 receipt_1_2_2340_1_part2 rfl rfl rfl
private theorem receipt_1_2_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 2).shape 179827 2340 2 1 0 2 1) 0 283 = 12588666690315259201538483 :=
  phaseBlock_append receipt_1_2_2340_1_part0 receipt_1_2_2340_1_join0 rfl rfl rfl

private theorem receipt_1_2_2340_1 : fastPhase (bank 1 2).shape 179827 2340 2 1 0 2 1 = 12588666690315259201538483 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_1_2_2340_1_join1

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2339_0 receipt_1_2_2339_1 receipt_1_2_2340_0 receipt_1_2_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 0) 0 128 = 4866528934022790559220160 := rfl
private theorem receipt_2_2_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 0) 128 128 = 1761567597146920243366878 := rfl
private theorem receipt_2_2_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 0) 256 27 = 51019216651339941508110 := rfl
private theorem receipt_2_2_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 0) 128 155 = 1812586813798260184874988 :=
  phaseBlock_append receipt_2_2_2339_0_part1 receipt_2_2_2339_0_part2 rfl rfl rfl
private theorem receipt_2_2_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 0) 0 283 = 6679115747821050744095148 :=
  phaseBlock_append receipt_2_2_2339_0_part0 receipt_2_2_2339_0_join0 rfl rfl rfl

private theorem receipt_2_2_2339_0 : fastPhase (bank 2 2).shape 179827 2339 2 1 0 7 0 = 6679115747821050744095148 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2339_0_join1

private theorem receipt_2_2_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 1) 0 128 = 4839195932190016346264448 := rfl
private theorem receipt_2_2_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 1) 128 128 = 1740671557785423592592010 := rfl
private theorem receipt_2_2_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 1) 256 27 = 47338992819147317080860 := rfl
private theorem receipt_2_2_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 1) 128 155 = 1788010550604570909672870 :=
  phaseBlock_append receipt_2_2_2339_1_part1 receipt_2_2_2339_1_part2 rfl rfl rfl
private theorem receipt_2_2_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2339 2 1 0 7 1) 0 283 = 6627206482794587255937318 :=
  phaseBlock_append receipt_2_2_2339_1_part0 receipt_2_2_2339_1_join0 rfl rfl rfl

private theorem receipt_2_2_2339_1 : fastPhase (bank 2 2).shape 179827 2339 2 1 0 7 1 = 6627206482794587255937318 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2339_1_join1

private theorem receipt_2_2_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 0) 0 128 = 4866569528462180625110720 := rfl
private theorem receipt_2_2_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 0) 128 128 = 1761578122259148123678516 := rfl
private theorem receipt_2_2_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 0) 256 27 = 51019419231132756335478 := rfl
private theorem receipt_2_2_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 0) 128 155 = 1812597541490280880013994 :=
  phaseBlock_append receipt_2_2_2340_0_part1 receipt_2_2_2340_0_part2 rfl rfl rfl
private theorem receipt_2_2_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 0) 0 283 = 6679167069952461505124714 :=
  phaseBlock_append receipt_2_2_2340_0_part0 receipt_2_2_2340_0_join0 rfl rfl rfl

private theorem receipt_2_2_2340_0 : fastPhase (bank 2 2).shape 179827 2340 2 1 0 7 0 = 6679167069952461505124714 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2340_0_join1

private theorem receipt_2_2_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 1) 0 128 = 4839236336087418136379840 := rfl
private theorem receipt_2_2_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 1) 128 128 = 1740681975151544907127077 := rfl
private theorem receipt_2_2_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 1) 256 27 = 47339181423075872314512 := rfl
private theorem receipt_2_2_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 1) 128 155 = 1788021156574620779441589 :=
  phaseBlock_append receipt_2_2_2340_1_part1 receipt_2_2_2340_1_part2 rfl rfl rfl
private theorem receipt_2_2_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 2).shape 179827 2340 2 1 0 7 1) 0 283 = 6627257492662038915821429 :=
  phaseBlock_append receipt_2_2_2340_1_part0 receipt_2_2_2340_1_join0 rfl rfl rfl

private theorem receipt_2_2_2340_1 : fastPhase (bank 2 2).shape 179827 2340 2 1 0 7 1 = 6627257492662038915821429 :=
  phase_of_block (n := 283) (by decide +kernel) receipt_2_2_2340_1_join1

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2339_0 receipt_2_2_2339_1 receipt_2_2_2340_0 receipt_2_2_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2339 2 1 1 1 0) 0 128 = 477400365964629152547456 := rfl
private theorem receipt_3_2_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2339 2 1 1 1 0) 128 95 = 90318448742385871775968 := rfl
private theorem receipt_3_2_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2339 2 1 1 1 0) 0 223 = 567718814707015024323424 :=
  phaseBlock_append receipt_3_2_2339_0_part0 receipt_3_2_2339_0_part1 rfl rfl rfl

private theorem receipt_3_2_2339_0 : fastPhase (bank 3 2).shape 179827 2339 2 1 1 1 0 = 567718814707015024323424 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2339_0_join0

private theorem receipt_3_2_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2339 2 1 1 1 1) 0 128 = 473810737859826559799488 := rfl
private theorem receipt_3_2_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2339 2 1 1 1 1) 128 95 = 88337306707166301895714 := rfl
private theorem receipt_3_2_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2339 2 1 1 1 1) 0 223 = 562148044566992861695202 :=
  phaseBlock_append receipt_3_2_2339_1_part0 receipt_3_2_2339_1_part1 rfl rfl rfl

private theorem receipt_3_2_2339_1 : fastPhase (bank 3 2).shape 179827 2339 2 1 1 1 1 = 562148044566992861695202 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2339_1_join0

private theorem receipt_3_2_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2340 2 1 1 1 0) 0 128 = 477403873713685569235008 := rfl
private theorem receipt_3_2_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2340 2 1 1 1 0) 128 95 = 90318754054079252726832 := rfl
private theorem receipt_3_2_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2340 2 1 1 1 0) 0 223 = 567722627767764821961840 :=
  phaseBlock_append receipt_3_2_2340_0_part0 receipt_3_2_2340_0_part1 rfl rfl rfl

private theorem receipt_3_2_2340_0 : fastPhase (bank 3 2).shape 179827 2340 2 1 1 1 0 = 567722627767764821961840 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2340_0_join0

private theorem receipt_3_2_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2340 2 1 1 1 1) 0 128 = 473814216761680668112960 := rfl
private theorem receipt_3_2_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2340 2 1 1 1 1) 128 95 = 88337605838515811499392 := rfl
private theorem receipt_3_2_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 2).shape 179827 2340 2 1 1 1 1) 0 223 = 562151822600196479612352 :=
  phaseBlock_append receipt_3_2_2340_1_part0 receipt_3_2_2340_1_part1 rfl rfl rfl

private theorem receipt_3_2_2340_1 : fastPhase (bank 3 2).shape 179827 2340 2 1 1 1 1 = 562151822600196479612352 :=
  phase_of_block (n := 223) (by decide +kernel) receipt_3_2_2340_1_join0

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2339_0 receipt_3_2_2339_1 receipt_3_2_2340_0 receipt_3_2_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 0) 0 128 = 15448406863280016459962148 := rfl
private theorem receipt_0_3_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 0) 128 128 = 5685157185601372744863771 := rfl
private theorem receipt_0_3_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 0) 256 26 = 157290516428882008417245 := rfl
private theorem receipt_0_3_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 0) 128 154 = 5842447702030254753281016 :=
  phaseBlock_append receipt_0_3_2339_0_part1 receipt_0_3_2339_0_part2 rfl rfl rfl
private theorem receipt_0_3_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 0) 0 282 = 21290854565310271213243164 :=
  phaseBlock_append receipt_0_3_2339_0_part0 receipt_0_3_2339_0_join0 rfl rfl rfl

private theorem receipt_0_3_2339_0 : fastPhase (bank 0 3).shape 179827 2339 3 1 0 1 0 = 21290854565310271213243164 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2339_0_join1

private theorem receipt_0_3_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 1) 0 128 = 15364181436983191187037696 := rfl
private theorem receipt_0_3_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 1) 128 128 = 5617966226295152200832082 := rfl
private theorem receipt_0_3_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 1) 256 26 = 145547739232096543793010 := rfl
private theorem receipt_0_3_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 1) 128 154 = 5763513965527248744625092 :=
  phaseBlock_append receipt_0_3_2339_1_part1 receipt_0_3_2339_1_part2 rfl rfl rfl
private theorem receipt_0_3_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2339 3 1 0 1 1) 0 282 = 21127695402510439931662788 :=
  phaseBlock_append receipt_0_3_2339_1_part0 receipt_0_3_2339_1_join0 rfl rfl rfl

private theorem receipt_0_3_2339_1 : fastPhase (bank 0 3).shape 179827 2339 3 1 0 1 1 = 21127695402510439931662788 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2339_1_join1

private theorem receipt_0_3_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 0) 0 128 = 15448536242145995459414504 := rfl
private theorem receipt_0_3_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 0) 128 128 = 5685190793992197875527818 := rfl
private theorem receipt_0_3_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 0) 256 26 = 157291124684943384254259 := rfl
private theorem receipt_0_3_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 0) 128 154 = 5842481918677141259782077 :=
  phaseBlock_append receipt_0_3_2340_0_part1 receipt_0_3_2340_0_part2 rfl rfl rfl
private theorem receipt_0_3_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 0) 0 282 = 21291018160823136719196581 :=
  phaseBlock_append receipt_0_3_2340_0_part0 receipt_0_3_2340_0_join0 rfl rfl rfl

private theorem receipt_0_3_2340_0 : fastPhase (bank 0 3).shape 179827 2340 3 1 0 1 0 = 21291018160823136719196581 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2340_0_join1

private theorem receipt_0_3_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 1) 0 128 = 15364310232546993619821141 := rfl
private theorem receipt_0_3_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 1) 128 128 = 5617999494330443112135525 := rfl
private theorem receipt_0_3_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 1) 256 26 = 145548304069994196930981 := rfl
private theorem receipt_0_3_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 1) 128 154 = 5763547798400437309066506 :=
  phaseBlock_append receipt_0_3_2340_1_part1 receipt_0_3_2340_1_part2 rfl rfl rfl
private theorem receipt_0_3_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 3).shape 179827 2340 3 1 0 1 1) 0 282 = 21127858030947430928887647 :=
  phaseBlock_append receipt_0_3_2340_1_part0 receipt_0_3_2340_1_join0 rfl rfl rfl

private theorem receipt_0_3_2340_1 : fastPhase (bank 0 3).shape 179827 2340 3 1 0 1 1 = 21127858030947430928887647 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_0_3_2340_1_join1

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2339_0 receipt_0_3_2339_1 receipt_0_3_2340_0 receipt_0_3_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 0) 0 128 = 13867627024285025824427694 := rfl
private theorem receipt_1_3_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 0) 128 128 = 5091450140551069953038535 := rfl
private theorem receipt_1_3_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 0) 256 26 = 140617270717934959358291 := rfl
private theorem receipt_1_3_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 0) 128 154 = 5232067411269004912396826 :=
  phaseBlock_append receipt_1_3_2339_0_part1 receipt_1_3_2339_0_part2 rfl rfl rfl
private theorem receipt_1_3_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 0) 0 282 = 19099694435554030736824520 :=
  phaseBlock_append receipt_1_3_2339_0_part0 receipt_1_3_2339_0_join0 rfl rfl rfl

private theorem receipt_1_3_2339_0 : fastPhase (bank 1 3).shape 179827 2339 3 1 0 2 0 = 19099694435554030736824520 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2339_0_join1

private theorem receipt_1_3_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 1) 0 128 = 13791756950699314957758928 := rfl
private theorem receipt_1_3_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 1) 128 128 = 5031193076860437080999632 := rfl
private theorem receipt_1_3_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 1) 256 26 = 130117540018873063849836 := rfl
private theorem receipt_1_3_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 1) 128 154 = 5161310616879310144849468 :=
  phaseBlock_append receipt_1_3_2339_1_part1 receipt_1_3_2339_1_part2 rfl rfl rfl
private theorem receipt_1_3_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2339 3 1 0 2 1) 0 282 = 18953067567578625102608396 :=
  phaseBlock_append receipt_1_3_2339_1_part0 receipt_1_3_2339_1_join0 rfl rfl rfl

private theorem receipt_1_3_2339_1 : fastPhase (bank 1 3).shape 179827 2339 3 1 0 2 1 = 18953067567578625102608396 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2339_1_join1

private theorem receipt_1_3_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 0) 0 128 = 13867743171249677393545932 := rfl
private theorem receipt_1_3_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 0) 128 128 = 5091480241677810558142110 := rfl
private theorem receipt_1_3_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 0) 256 26 = 140617814499714367494259 := rfl
private theorem receipt_1_3_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 0) 128 154 = 5232098056177524925636369 :=
  phaseBlock_append receipt_1_3_2340_0_part1 receipt_1_3_2340_0_part2 rfl rfl rfl
private theorem receipt_1_3_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 0) 0 282 = 19099841227427202319182301 :=
  phaseBlock_append receipt_1_3_2340_0_part0 receipt_1_3_2340_0_join0 rfl rfl rfl

private theorem receipt_1_3_2340_0 : fastPhase (bank 1 3).shape 179827 2340 3 1 0 2 0 = 19099841227427202319182301 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2340_0_join1

private theorem receipt_1_3_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 1) 0 128 = 13791872571805503985756232 := rfl
private theorem receipt_1_3_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 1) 128 128 = 5031222872644103530632297 := rfl
private theorem receipt_1_3_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 1) 256 26 = 130118044977881170597782 := rfl
private theorem receipt_1_3_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 1) 128 154 = 5161340917621984701230079 :=
  phaseBlock_append receipt_1_3_2340_1_part1 receipt_1_3_2340_1_part2 rfl rfl rfl
private theorem receipt_1_3_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 3).shape 179827 2340 3 1 0 2 1) 0 282 = 18953213489427488686986311 :=
  phaseBlock_append receipt_1_3_2340_1_part0 receipt_1_3_2340_1_join0 rfl rfl rfl

private theorem receipt_1_3_2340_1 : fastPhase (bank 1 3).shape 179827 2340 3 1 0 2 1 = 18953213489427488686986311 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_1_3_2340_1_join1

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2339_0 receipt_1_3_2339_1 receipt_1_3_2340_0 receipt_1_3_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 0) 0 128 = 7277004834630743651385084 := rfl
private theorem receipt_2_3_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 0) 128 128 = 2626231868566739167984920 := rfl
private theorem receipt_2_3_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 0) 256 26 = 71597504422597947317916 := rfl
private theorem receipt_2_3_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 0) 128 154 = 2697829372989337115302836 :=
  phaseBlock_append receipt_2_3_2339_0_part1 receipt_2_3_2339_0_part2 rfl rfl rfl
private theorem receipt_2_3_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 0) 0 282 = 9974834207620080766687920 :=
  phaseBlock_append receipt_2_3_2339_0_part0 receipt_2_3_2339_0_join0 rfl rfl rfl

private theorem receipt_2_3_2339_0 : fastPhase (bank 2 3).shape 179827 2339 3 1 0 7 0 = 9974834207620080766687920 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2339_0_join1

private theorem receipt_2_3_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 1) 0 128 = 7236186918861016728447648 := rfl
private theorem receipt_2_3_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 1) 128 128 = 2594835986833917152997312 := rfl
private theorem receipt_2_3_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 1) 256 26 = 66244907560322305323936 := rfl
private theorem receipt_2_3_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 1) 128 154 = 2661080894394239458321248 :=
  phaseBlock_append receipt_2_3_2339_1_part1 receipt_2_3_2339_1_part2 rfl rfl rfl
private theorem receipt_2_3_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2339 3 1 0 7 1) 0 282 = 9897267813255256186768896 :=
  phaseBlock_append receipt_2_3_2339_1_part0 receipt_2_3_2339_1_join0 rfl rfl rfl

private theorem receipt_2_3_2339_1 : fastPhase (bank 2 3).shape 179827 2339 3 1 0 7 1 = 9897267813255256186768896 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2339_1_join1

private theorem receipt_2_3_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 0) 0 128 = 7277065809105321763164572 := rfl
private theorem receipt_2_3_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 0) 128 128 = 2626247404552963152027300 := rfl
private theorem receipt_2_3_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 0) 256 26 = 71597781307500174504624 := rfl
private theorem receipt_2_3_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 0) 128 154 = 2697845185860463326531924 :=
  phaseBlock_append receipt_2_3_2340_0_part1 receipt_2_3_2340_0_part2 rfl rfl rfl
private theorem receipt_2_3_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 0) 0 282 = 9974910994965785089696496 :=
  phaseBlock_append receipt_2_3_2340_0_part0 receipt_2_3_2340_0_join0 rfl rfl rfl

private theorem receipt_2_3_2340_0 : fastPhase (bank 2 3).shape 179827 2340 3 1 0 7 0 = 9974910994965785089696496 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2340_0_join1

private theorem receipt_2_3_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 1) 0 128 = 7236247608819436789040127 := rfl
private theorem receipt_2_3_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 1) 128 128 = 2594851363304910098883942 := rfl
private theorem receipt_2_3_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 1) 256 26 = 66245164651379063380977 := rfl
private theorem receipt_2_3_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 1) 128 154 = 2661096527956289162264919 :=
  phaseBlock_append receipt_2_3_2340_1_part1 receipt_2_3_2340_1_part2 rfl rfl rfl
private theorem receipt_2_3_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 3).shape 179827 2340 3 1 0 7 1) 0 282 = 9897344136775725951305046 :=
  phaseBlock_append receipt_2_3_2340_1_part0 receipt_2_3_2340_1_join0 rfl rfl rfl

private theorem receipt_2_3_2340_1 : fastPhase (bank 2 3).shape 179827 2340 3 1 0 7 1 = 9897344136775725951305046 :=
  phase_of_block (n := 282) (by decide +kernel) receipt_2_3_2340_1_join1

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2339_0 receipt_2_3_2339_1 receipt_2_3_2340_0 receipt_2_3_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2339 3 1 1 1 0) 0 128 = 704306906949054358389504 := rfl
private theorem receipt_3_3_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2339 3 1 1 1 0) 128 110 = 163974459826906698118666 := rfl
private theorem receipt_3_3_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2339 3 1 1 1 0) 0 238 = 868281366775961056508170 :=
  phaseBlock_append receipt_3_3_2339_0_part0 receipt_3_3_2339_0_part1 rfl rfl rfl

private theorem receipt_3_3_2339_0 : fastPhase (bank 3 3).shape 179827 2339 3 1 1 1 0 = 868281366775961056508170 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2339_0_join0

private theorem receipt_3_3_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2339 3 1 1 1 1) 0 128 = 699443383552342396891520 := rfl
private theorem receipt_3_3_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2339 3 1 1 1 1) 128 110 = 160852789105736542953864 := rfl
private theorem receipt_3_3_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2339 3 1 1 1 1) 0 238 = 860296172658078939845384 :=
  phaseBlock_append receipt_3_3_2339_1_part0 receipt_3_3_2339_1_part1 rfl rfl rfl

private theorem receipt_3_3_2339_1 : fastPhase (bank 3 3).shape 179827 2339 3 1 1 1 1 = 860296172658078939845384 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2339_1_join0

private theorem receipt_3_3_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2340 3 1 1 1 0) 0 128 = 704312134995993241157568 := rfl
private theorem receipt_3_3_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2340 3 1 1 1 0) 128 110 = 163975042842054246926156 := rfl
private theorem receipt_3_3_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2340 3 1 1 1 0) 0 238 = 868287177838047488083724 :=
  phaseBlock_append receipt_3_3_2340_0_part0 receipt_3_3_2340_0_part1 rfl rfl rfl

private theorem receipt_3_3_2340_0 : fastPhase (bank 3 3).shape 179827 2340 3 1 1 1 0 = 868287177838047488083724 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2340_0_join0

private theorem receipt_3_3_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2340 3 1 1 1 1) 0 128 = 699448571823767184037760 := rfl
private theorem receipt_3_3_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2340 3 1 1 1 1) 128 110 = 160853361889812137604036 := rfl
private theorem receipt_3_3_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 3).shape 179827 2340 3 1 1 1 1) 0 238 = 860301933713579321641796 :=
  phaseBlock_append receipt_3_3_2340_1_part0 receipt_3_3_2340_1_part1 rfl rfl rfl

private theorem receipt_3_3_2340_1 : fastPhase (bank 3 3).shape 179827 2340 3 1 1 1 1 = 860301933713579321641796 :=
  phase_of_block (n := 238) (by decide +kernel) receipt_3_3_2340_1_join0

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2339_0 receipt_3_3_2339_1 receipt_3_3_2340_0 receipt_3_3_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 0) 0 128 = 23490782181973808922617898 := rfl
private theorem receipt_0_4_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 0) 128 128 = 9227320649148170592885828 := rfl
private theorem receipt_0_4_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 0) 256 36 = 437593638384000931850616 := rfl
private theorem receipt_0_4_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 0) 128 164 = 9664914287532171524736444 :=
  phaseBlock_append receipt_0_4_2339_0_part1 receipt_0_4_2339_0_part2 rfl rfl rfl
private theorem receipt_0_4_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 0) 0 292 = 33155696469505980447354342 :=
  phaseBlock_append receipt_0_4_2339_0_part0 receipt_0_4_2339_0_join0 rfl rfl rfl

private theorem receipt_0_4_2339_0 : fastPhase (bank 0 4).shape 179827 2339 4 1 0 1 0 = 33155696469505980447354342 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2339_0_join1

private theorem receipt_0_4_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 1) 0 128 = 23368436329719494266736158 := rfl
private theorem receipt_0_4_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 1) 128 128 = 9128511899452748836304724 := rfl
private theorem receipt_0_4_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 1) 256 36 = 413693709452915810010130 := rfl
private theorem receipt_0_4_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 1) 128 164 = 9542205608905664646314854 :=
  phaseBlock_append receipt_0_4_2339_1_part1 receipt_0_4_2339_1_part2 rfl rfl rfl
private theorem receipt_0_4_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2339 4 1 0 1 1) 0 292 = 32910641938625158913051012 :=
  phaseBlock_append receipt_0_4_2339_1_part0 receipt_0_4_2339_1_join0 rfl rfl rfl

private theorem receipt_0_4_2339_1 : fastPhase (bank 0 4).shape 179827 2339 4 1 0 1 1 = 32910641938625158913051012 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2339_1_join1

private theorem receipt_0_4_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 0) 0 128 = 23490978828512933637191577 := rfl
private theorem receipt_0_4_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 0) 128 128 = 9227376185980917142022813 := rfl
private theorem receipt_0_4_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 0) 256 36 = 437595411165808260175650 := rfl
private theorem receipt_0_4_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 0) 128 164 = 9664971597146725402198463 :=
  phaseBlock_append receipt_0_4_2340_0_part1 receipt_0_4_2340_0_part2 rfl rfl rfl
private theorem receipt_0_4_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 0) 0 292 = 33155950425659659039390040 :=
  phaseBlock_append receipt_0_4_2340_0_part0 receipt_0_4_2340_0_join0 rfl rfl rfl

private theorem receipt_0_4_2340_0 : fastPhase (bank 0 4).shape 179827 2340 4 1 0 1 0 = 33155950425659659039390040 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2340_0_join1

private theorem receipt_0_4_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 1) 0 128 = 23368632127050174278749475 := rfl
private theorem receipt_0_4_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 1) 128 128 = 9128566923500699522925380 := rfl
private theorem receipt_0_4_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 1) 256 36 = 413695390780505258276602 := rfl
private theorem receipt_0_4_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 1) 128 164 = 9542262314281204781201982 :=
  phaseBlock_append receipt_0_4_2340_1_part1 receipt_0_4_2340_1_part2 rfl rfl rfl
private theorem receipt_0_4_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 4).shape 179827 2340 4 1 0 1 1) 0 292 = 32910894441331379059951457 :=
  phaseBlock_append receipt_0_4_2340_1_part0 receipt_0_4_2340_1_join0 rfl rfl rfl

private theorem receipt_0_4_2340_1 : fastPhase (bank 0 4).shape 179827 2340 4 1 0 1 1 = 32910894441331379059951457 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_0_4_2340_1_join1

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2339_0 receipt_0_4_2339_1 receipt_0_4_2340_0 receipt_0_4_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 0) 0 128 = 21153571715587508354688699 := rfl
private theorem receipt_1_4_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 0) 128 128 = 8292113850172286745637884 := rfl
private theorem receipt_1_4_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 0) 256 36 = 392629763139184603821684 := rfl
private theorem receipt_1_4_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 0) 128 164 = 8684743613311471349459568 :=
  phaseBlock_append receipt_1_4_2339_0_part1 receipt_1_4_2339_0_part2 rfl rfl rfl
private theorem receipt_1_4_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 0) 0 292 = 29838315328898979704148267 :=
  phaseBlock_append receipt_1_4_2339_0_part0 receipt_1_4_2339_0_join0 rfl rfl rfl

private theorem receipt_1_4_2339_0 : fastPhase (bank 1 4).shape 179827 2339 4 1 0 2 0 = 29838315328898979704148267 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2339_0_join1

private theorem receipt_1_4_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 1) 0 128 = 21043048064882203453153087 := rfl
private theorem receipt_1_4_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 1) 128 128 = 8203197547925626844436114 := rfl
private theorem receipt_1_4_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 1) 256 36 = 371181332941775547912460 := rfl
private theorem receipt_1_4_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 1) 128 164 = 8574378880867402392348574 :=
  phaseBlock_append receipt_1_4_2339_1_part1 receipt_1_4_2339_1_part2 rfl rfl rfl
private theorem receipt_1_4_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2339 4 1 0 2 1) 0 292 = 29617426945749605845501661 :=
  phaseBlock_append receipt_1_4_2339_1_part0 receipt_1_4_2339_1_join0 rfl rfl rfl

private theorem receipt_1_4_2339_1 : fastPhase (bank 1 4).shape 179827 2339 4 1 0 2 1 = 29617426945749605845501661 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2339_1_join1

private theorem receipt_1_4_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 0) 0 128 = 21153748805582436297161076 := rfl
private theorem receipt_1_4_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 0) 128 128 = 8292163761711931737893120 := rfl
private theorem receipt_1_4_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 0) 256 36 = 392631353774474099133258 := rfl
private theorem receipt_1_4_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 0) 128 164 = 8684795115486405837026378 :=
  phaseBlock_append receipt_1_4_2340_0_part1 receipt_1_4_2340_0_part2 rfl rfl rfl
private theorem receipt_1_4_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 0) 0 292 = 29838543921068842134187454 :=
  phaseBlock_append receipt_1_4_2340_0_part0 receipt_1_4_2340_0_join0 rfl rfl rfl

private theorem receipt_1_4_2340_0 : fastPhase (bank 1 4).shape 179827 2340 4 1 0 2 0 = 29838543921068842134187454 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2340_0_join1

private theorem receipt_1_4_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 1) 0 128 = 21043224387178039024034309 := rfl
private theorem receipt_1_4_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 1) 128 128 = 8203246997869416545932781 := rfl
private theorem receipt_1_4_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 1) 256 36 = 371182841501402148848824 := rfl
private theorem receipt_1_4_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 1) 128 164 = 8574429839370818694781605 :=
  phaseBlock_append receipt_1_4_2340_1_part1 receipt_1_4_2340_1_part2 rfl rfl rfl
private theorem receipt_1_4_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 4).shape 179827 2340 4 1 0 2 1) 0 292 = 29617654226548857718815914 :=
  phaseBlock_append receipt_1_4_2340_1_part0 receipt_1_4_2340_1_join0 rfl rfl rfl

private theorem receipt_1_4_2340_1 : fastPhase (bank 1 4).shape 179827 2340 4 1 0 2 1 = 29617654226548857718815914 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_1_4_2340_1_join1

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2339_0 receipt_1_4_2339_1 receipt_1_4_2340_0 receipt_1_4_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 0) 0 128 = 11350313573537375042627295 := rfl
private theorem receipt_2_4_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 0) 128 128 = 4383449582235245101678821 := rfl
private theorem receipt_2_4_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 0) 256 36 = 205212761194688376197565 := rfl
private theorem receipt_2_4_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 0) 128 164 = 4588662343429933477876386 :=
  phaseBlock_append receipt_2_4_2339_0_part1 receipt_2_4_2339_0_part2 rfl rfl rfl
private theorem receipt_2_4_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 0) 0 292 = 15938975916967308520503681 :=
  phaseBlock_append receipt_2_4_2339_0_part0 receipt_2_4_2339_0_join0 rfl rfl rfl

private theorem receipt_2_4_2339_0 : fastPhase (bank 2 4).shape 179827 2339 4 1 0 7 0 = 15938975916967308520503681 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2339_0_join1

private theorem receipt_2_4_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 1) 0 128 = 11289657904754130402751918 := rfl
private theorem receipt_2_4_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 1) 128 128 = 4335978172279102834936116 := rfl
private theorem receipt_2_4_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 1) 256 36 = 193986146371876810743538 := rfl
private theorem receipt_2_4_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 1) 128 164 = 4529964318650979645679654 :=
  phaseBlock_append receipt_2_4_2339_1_part1 receipt_2_4_2339_1_part2 rfl rfl rfl
private theorem receipt_2_4_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2339 4 1 0 7 1) 0 292 = 15819622223405110048431572 :=
  phaseBlock_append receipt_2_4_2339_1_part0 receipt_2_4_2339_1_join0 rfl rfl rfl

private theorem receipt_2_4_2339_1 : fastPhase (bank 2 4).shape 179827 2339 4 1 0 7 1 = 15819622223405110048431572 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2339_1_join1

private theorem receipt_2_4_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 0) 0 128 = 11350408628015858194118736 := rfl
private theorem receipt_2_4_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 0) 128 128 = 4383475980209912024759816 := rfl
private theorem receipt_2_4_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 0) 256 36 = 205213592603151574921620 := rfl
private theorem receipt_2_4_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 0) 128 164 = 4588689572813063599681436 :=
  phaseBlock_append receipt_2_4_2340_0_part1 receipt_2_4_2340_0_part2 rfl rfl rfl
private theorem receipt_2_4_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 0) 0 292 = 15939098200828921793800172 :=
  phaseBlock_append receipt_2_4_2340_0_part0 receipt_2_4_2340_0_join0 rfl rfl rfl

private theorem receipt_2_4_2340_0 : fastPhase (bank 2 4).shape 179827 2340 4 1 0 7 0 = 15939098200828921793800172 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2340_0_join1

private theorem receipt_2_4_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 1) 0 128 = 11289752535803624507428232 := rfl
private theorem receipt_2_4_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 1) 128 128 = 4336004323239573781360067 := rfl
private theorem receipt_2_4_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 1) 256 36 = 193986934811525860915585 := rfl
private theorem receipt_2_4_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 1) 128 164 = 4529991258051099642275652 :=
  phaseBlock_append receipt_2_4_2340_1_part1 receipt_2_4_2340_1_part2 rfl rfl rfl
private theorem receipt_2_4_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 4).shape 179827 2340 4 1 0 7 1) 0 292 = 15819743793854724149703884 :=
  phaseBlock_append receipt_2_4_2340_1_part0 receipt_2_4_2340_1_join0 rfl rfl rfl

private theorem receipt_2_4_2340_1 : fastPhase (bank 2 4).shape 179827 2340 4 1 0 7 1 = 15819743793854724149703884 :=
  phase_of_block (n := 292) (by decide +kernel) receipt_2_4_2340_1_join1

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2339_0 receipt_2_4_2339_1 receipt_2_4_2340_0 receipt_2_4_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 0) 0 128 = 1617864498483779007780192 := rfl
private theorem receipt_3_4_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 0) 128 128 = 653343260881003710178656 := rfl
private theorem receipt_3_4_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 0) 256 47 = 45307634028280152732324 := rfl
private theorem receipt_3_4_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 0) 128 175 = 698650894909283862910980 :=
  phaseBlock_append receipt_3_4_2339_0_part1 receipt_3_4_2339_0_part2 rfl rfl rfl
private theorem receipt_3_4_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 0) 0 303 = 2316515393393062870691172 :=
  phaseBlock_append receipt_3_4_2339_0_part0 receipt_3_4_2339_0_join0 rfl rfl rfl

private theorem receipt_3_4_2339_0 : fastPhase (bank 3 4).shape 179827 2339 4 1 1 1 0 = 2316515393393062870691172 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2339_0_join1

private theorem receipt_3_4_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 1) 0 128 = 1609543741228721472110944 := rfl
private theorem receipt_3_4_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 1) 128 128 = 646769539914693059588448 := rfl
private theorem receipt_3_4_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 1) 256 47 = 43377071148365053836397 := rfl
private theorem receipt_3_4_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 1) 128 175 = 690146611063058113424845 :=
  phaseBlock_append receipt_3_4_2339_1_part1 receipt_3_4_2339_1_part2 rfl rfl rfl
private theorem receipt_3_4_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2339 4 1 1 1 1) 0 303 = 2299690352291779585535789 :=
  phaseBlock_append receipt_3_4_2339_1_part0 receipt_3_4_2339_1_join0 rfl rfl rfl

private theorem receipt_3_4_2339_1 : fastPhase (bank 3 4).shape 179827 2339 4 1 1 1 1 = 2299690352291779585535789 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2339_1_join1

private theorem receipt_3_4_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 0) 0 128 = 1617876941340601399190688 := rfl
private theorem receipt_3_4_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 0) 128 128 = 653346024705562703975584 := rfl
private theorem receipt_3_4_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 0) 256 47 = 45307711828882674577436 := rfl
private theorem receipt_3_4_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 0) 128 175 = 698653736534445378553020 :=
  phaseBlock_append receipt_3_4_2340_0_part1 receipt_3_4_2340_0_part2 rfl rfl rfl
private theorem receipt_3_4_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 0) 0 303 = 2316530677875046777743708 :=
  phaseBlock_append receipt_3_4_2340_0_part0 receipt_3_4_2340_0_join0 rfl rfl rfl

private theorem receipt_3_4_2340_0 : fastPhase (bank 3 4).shape 179827 2340 4 1 1 1 0 = 2316530677875046777743708 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2340_0_join1

private theorem receipt_3_4_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 1) 0 128 = 1609556112165883110066208 := rfl
private theorem receipt_3_4_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 1) 128 128 = 646772275060701134682144 := rfl
private theorem receipt_3_4_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 1) 256 47 = 43377145851643290227426 := rfl
private theorem receipt_3_4_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 1) 128 175 = 690149420912344424909570 :=
  phaseBlock_append receipt_3_4_2340_1_part1 receipt_3_4_2340_1_part2 rfl rfl rfl
private theorem receipt_3_4_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 4).shape 179827 2340 4 1 1 1 1) 0 303 = 2299705533078227534975778 :=
  phaseBlock_append receipt_3_4_2340_1_part0 receipt_3_4_2340_1_join0 rfl rfl rfl

private theorem receipt_3_4_2340_1 : fastPhase (bank 3 4).shape 179827 2340 4 1 1 1 1 = 2299705533078227534975778 :=
  phase_of_block (n := 303) (by decide +kernel) receipt_3_4_2340_1_join1

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2339_0 receipt_3_4_2339_1 receipt_3_4_2340_0 receipt_3_4_2340_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 4) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group1_stage i)).shape
      (cutoff h rect (group1_stage i)), ¬ G∣Q :=
  (group1_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group1_avoids

end Lower6960.RescueSource
