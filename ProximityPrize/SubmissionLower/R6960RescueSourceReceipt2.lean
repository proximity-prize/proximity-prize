import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_1696_356_part0 :
    blockEstimate 1696 356 356 128 = 572684320 := by decide +kernel
private theorem moment_1696_356_part1 :
    blockEstimate 1696 356 484 128 = 3684337696 := by decide +kernel
private theorem moment_1696_356_part2 :
    blockEstimate 1696 356 612 128 = 9136834131 := by decide +kernel
private theorem moment_1696_356_part3 :
    blockEstimate 1696 356 740 128 = 15370032384 := by decide +kernel
private theorem moment_1696_356_part4 :
    blockEstimate 1696 356 868 128 = 20341757184 := by decide +kernel
private theorem moment_1696_356_part5 :
    blockEstimate 1696 356 996 128 = 23816115456 := by decide +kernel
private theorem moment_1696_356_part6 :
    blockEstimate 1696 356 1124 128 = 25793107200 := by decide +kernel
private theorem moment_1696_356_part7 :
    blockEstimate 1696 356 1252 128 = 26272732416 := by decide +kernel
private theorem moment_1696_356_part8 :
    blockEstimate 1696 356 1380 128 = 25254991104 := by decide +kernel
private theorem moment_1696_356_part9 :
    blockEstimate 1696 356 1508 128 = 22739883264 := by decide +kernel
private theorem moment_1696_356_part10 :
    blockEstimate 1696 356 1636 128 = 18755777396 := by decide +kernel
private theorem moment_1696_356_part11 :
    blockEstimate 1696 356 1764 128 = 13945647249 := by decide +kernel
private theorem moment_1696_356_part12 :
    blockEstimate 1696 356 1892 128 = 9230875643 := by decide +kernel
private theorem moment_1696_356_part13 :
    blockEstimate 1696 356 2020 128 = 5110148823 := by decide +kernel
private theorem moment_1696_356_part14 :
    blockEstimate 1696 356 2148 128 = 2022537952 := by decide +kernel
private theorem moment_1696_356_part15 :
    blockEstimate 1696 356 2276 128 = 324080352 := by decide +kernel
private theorem moment_1696_356_part16 :
    blockEstimate 1696 356 2404 4 = 22031 := by decide +kernel
private theorem moment_1696_356_join0 :
    blockEstimate 1696 356 356 256 = 4257022016 :=
  block_append moment_1696_356_part0 moment_1696_356_part1 rfl rfl rfl
private theorem moment_1696_356_join1 :
    blockEstimate 1696 356 612 256 = 24506866515 :=
  block_append moment_1696_356_part2 moment_1696_356_part3 rfl rfl rfl
private theorem moment_1696_356_join2 :
    blockEstimate 1696 356 356 512 = 28763888531 :=
  block_append moment_1696_356_join0 moment_1696_356_join1 rfl rfl rfl
private theorem moment_1696_356_join3 :
    blockEstimate 1696 356 868 256 = 44157872640 :=
  block_append moment_1696_356_part4 moment_1696_356_part5 rfl rfl rfl
private theorem moment_1696_356_join4 :
    blockEstimate 1696 356 1124 256 = 52065839616 :=
  block_append moment_1696_356_part6 moment_1696_356_part7 rfl rfl rfl
private theorem moment_1696_356_join5 :
    blockEstimate 1696 356 868 512 = 96223712256 :=
  block_append moment_1696_356_join3 moment_1696_356_join4 rfl rfl rfl
private theorem moment_1696_356_join6 :
    blockEstimate 1696 356 356 1024 = 124987600787 :=
  block_append moment_1696_356_join2 moment_1696_356_join5 rfl rfl rfl
private theorem moment_1696_356_join7 :
    blockEstimate 1696 356 1380 256 = 47994874368 :=
  block_append moment_1696_356_part8 moment_1696_356_part9 rfl rfl rfl
private theorem moment_1696_356_join8 :
    blockEstimate 1696 356 1636 256 = 32701424645 :=
  block_append moment_1696_356_part10 moment_1696_356_part11 rfl rfl rfl
private theorem moment_1696_356_join9 :
    blockEstimate 1696 356 1380 512 = 80696299013 :=
  block_append moment_1696_356_join7 moment_1696_356_join8 rfl rfl rfl
private theorem moment_1696_356_join10 :
    blockEstimate 1696 356 1892 256 = 14341024466 :=
  block_append moment_1696_356_part12 moment_1696_356_part13 rfl rfl rfl
private theorem moment_1696_356_join11 :
    blockEstimate 1696 356 2276 132 = 324102383 :=
  block_append moment_1696_356_part15 moment_1696_356_part16 rfl rfl rfl
private theorem moment_1696_356_join12 :
    blockEstimate 1696 356 2148 260 = 2346640335 :=
  block_append moment_1696_356_part14 moment_1696_356_join11 rfl rfl rfl
private theorem moment_1696_356_join13 :
    blockEstimate 1696 356 1892 516 = 16687664801 :=
  block_append moment_1696_356_join10 moment_1696_356_join12 rfl rfl rfl
private theorem moment_1696_356_join14 :
    blockEstimate 1696 356 1380 1028 = 97383963814 :=
  block_append moment_1696_356_join9 moment_1696_356_join13 rfl rfl rfl
private theorem moment_1696_356_join15 :
    blockEstimate 1696 356 356 2052 = 222371564601 :=
  block_append moment_1696_356_join6 moment_1696_356_join14 rfl rfl rfl

theorem moment_1696_356 : momentEstimate 1696 356 = 222371564601 := moment_1696_356_join15

private theorem moment_1696_370_part0 :
    blockEstimate 1696 370 370 128 = 572684320 := by decide +kernel
private theorem moment_1696_370_part1 :
    blockEstimate 1696 370 498 128 = 3684337696 := by decide +kernel
private theorem moment_1696_370_part2 :
    blockEstimate 1696 370 626 128 = 9141056804 := by decide +kernel
private theorem moment_1696_370_part3 :
    blockEstimate 1696 370 754 128 = 15557757376 := by decide +kernel
private theorem moment_1696_370_part4 :
    blockEstimate 1696 370 882 128 = 20767001024 := by decide +kernel
private theorem moment_1696_370_part5 :
    blockEstimate 1696 370 1010 128 = 24420157888 := by decide +kernel
private theorem moment_1696_370_part6 :
    blockEstimate 1696 370 1138 128 = 26517227968 := by decide +kernel
private theorem moment_1696_370_part7 :
    blockEstimate 1696 370 1266 128 = 27058211264 := by decide +kernel
private theorem moment_1696_370_part8 :
    blockEstimate 1696 370 1394 128 = 26043107776 := by decide +kernel
private theorem moment_1696_370_part9 :
    blockEstimate 1696 370 1522 128 = 23471917504 := by decide +kernel
private theorem moment_1696_370_part10 :
    blockEstimate 1696 370 1650 128 = 19393615038 := by decide +kernel
private theorem moment_1696_370_part11 :
    blockEstimate 1696 370 1778 128 = 14532053576 := by decide +kernel
private theorem moment_1696_370_part12 :
    blockEstimate 1696 370 1906 128 = 9746328986 := by decide +kernel
private theorem moment_1696_370_part13 :
    blockEstimate 1696 370 2034 128 = 5521630460 := by decide +kernel
private theorem moment_1696_370_part14 :
    blockEstimate 1696 370 2162 128 = 2297261808 := by decide +kernel
private theorem moment_1696_370_part15 :
    blockEstimate 1696 370 2290 128 = 434348784 := by decide +kernel
private theorem moment_1696_370_part16 :
    blockEstimate 1696 370 2418 18 = 1038245 := by decide +kernel
private theorem moment_1696_370_join0 :
    blockEstimate 1696 370 370 256 = 4257022016 :=
  block_append moment_1696_370_part0 moment_1696_370_part1 rfl rfl rfl
private theorem moment_1696_370_join1 :
    blockEstimate 1696 370 626 256 = 24698814180 :=
  block_append moment_1696_370_part2 moment_1696_370_part3 rfl rfl rfl
private theorem moment_1696_370_join2 :
    blockEstimate 1696 370 370 512 = 28955836196 :=
  block_append moment_1696_370_join0 moment_1696_370_join1 rfl rfl rfl
private theorem moment_1696_370_join3 :
    blockEstimate 1696 370 882 256 = 45187158912 :=
  block_append moment_1696_370_part4 moment_1696_370_part5 rfl rfl rfl
private theorem moment_1696_370_join4 :
    blockEstimate 1696 370 1138 256 = 53575439232 :=
  block_append moment_1696_370_part6 moment_1696_370_part7 rfl rfl rfl
private theorem moment_1696_370_join5 :
    blockEstimate 1696 370 882 512 = 98762598144 :=
  block_append moment_1696_370_join3 moment_1696_370_join4 rfl rfl rfl
private theorem moment_1696_370_join6 :
    blockEstimate 1696 370 370 1024 = 127718434340 :=
  block_append moment_1696_370_join2 moment_1696_370_join5 rfl rfl rfl
private theorem moment_1696_370_join7 :
    blockEstimate 1696 370 1394 256 = 49515025280 :=
  block_append moment_1696_370_part8 moment_1696_370_part9 rfl rfl rfl
private theorem moment_1696_370_join8 :
    blockEstimate 1696 370 1650 256 = 33925668614 :=
  block_append moment_1696_370_part10 moment_1696_370_part11 rfl rfl rfl
private theorem moment_1696_370_join9 :
    blockEstimate 1696 370 1394 512 = 83440693894 :=
  block_append moment_1696_370_join7 moment_1696_370_join8 rfl rfl rfl
private theorem moment_1696_370_join10 :
    blockEstimate 1696 370 1906 256 = 15267959446 :=
  block_append moment_1696_370_part12 moment_1696_370_part13 rfl rfl rfl
private theorem moment_1696_370_join11 :
    blockEstimate 1696 370 2290 146 = 435387029 :=
  block_append moment_1696_370_part15 moment_1696_370_part16 rfl rfl rfl
private theorem moment_1696_370_join12 :
    blockEstimate 1696 370 2162 274 = 2732648837 :=
  block_append moment_1696_370_part14 moment_1696_370_join11 rfl rfl rfl
private theorem moment_1696_370_join13 :
    blockEstimate 1696 370 1906 530 = 18000608283 :=
  block_append moment_1696_370_join10 moment_1696_370_join12 rfl rfl rfl
private theorem moment_1696_370_join14 :
    blockEstimate 1696 370 1394 1042 = 101441302177 :=
  block_append moment_1696_370_join9 moment_1696_370_join13 rfl rfl rfl
private theorem moment_1696_370_join15 :
    blockEstimate 1696 370 370 2066 = 229159736517 :=
  block_append moment_1696_370_join6 moment_1696_370_join14 rfl rfl rfl

theorem moment_1696_370 : momentEstimate 1696 370 = 229159736517 := moment_1696_370_join15

private theorem moment_1809_380_part0 :
    blockEstimate 1809 380 380 128 = 613111200 := by decide +kernel
private theorem moment_1809_380_part1 :
    blockEstimate 1809 380 508 128 = 3963594144 := by decide +kernel
private theorem moment_1809_380_part2 :
    blockEstimate 1809 380 636 128 = 9896705511 := by decide +kernel
private theorem moment_1809_380_part3 :
    blockEstimate 1809 380 764 128 = 17097207360 := by decide +kernel
private theorem moment_1809_380_part4 :
    blockEstimate 1809 380 892 128 = 23183453760 := by decide +kernel
private theorem moment_1809_380_part5 :
    blockEstimate 1809 380 1020 128 = 27671670336 := by decide +kernel
private theorem moment_1809_380_part6 :
    blockEstimate 1809 380 1148 128 = 30561857088 := by decide +kernel
private theorem moment_1809_380_part7 :
    blockEstimate 1809 380 1276 128 = 31854014016 := by decide +kernel
private theorem moment_1809_380_part8 :
    blockEstimate 1809 380 1404 128 = 31548141120 := by decide +kernel
private theorem moment_1809_380_part9 :
    blockEstimate 1809 380 1532 128 = 29644238400 := by decide +kernel
private theorem moment_1809_380_part10 :
    blockEstimate 1809 380 1660 128 = 26142305856 := by decide +kernel
private theorem moment_1809_380_part11 :
    blockEstimate 1809 380 1788 128 = 21163152440 := by decide +kernel
private theorem moment_1809_380_part12 :
    blockEstimate 1809 380 1916 128 = 15641164329 := by decide +kernel
private theorem moment_1809_380_part13 :
    blockEstimate 1809 380 2044 128 = 10359919872 := by decide +kernel
private theorem moment_1809_380_part14 :
    blockEstimate 1809 380 2172 128 = 5784462598 := by decide +kernel
private theorem moment_1809_380_part15 :
    blockEstimate 1809 380 2300 128 = 2356385168 := by decide +kernel
private theorem moment_1809_380_part16 :
    blockEstimate 1809 380 2428 128 = 419948944 := by decide +kernel
private theorem moment_1809_380_part17 :
    blockEstimate 1809 380 2556 13 = 454490 := by decide +kernel
private theorem moment_1809_380_join0 :
    blockEstimate 1809 380 380 256 = 4576705344 :=
  block_append moment_1809_380_part0 moment_1809_380_part1 rfl rfl rfl
private theorem moment_1809_380_join1 :
    blockEstimate 1809 380 636 256 = 26993912871 :=
  block_append moment_1809_380_part2 moment_1809_380_part3 rfl rfl rfl
private theorem moment_1809_380_join2 :
    blockEstimate 1809 380 380 512 = 31570618215 :=
  block_append moment_1809_380_join0 moment_1809_380_join1 rfl rfl rfl
private theorem moment_1809_380_join3 :
    blockEstimate 1809 380 892 256 = 50855124096 :=
  block_append moment_1809_380_part4 moment_1809_380_part5 rfl rfl rfl
private theorem moment_1809_380_join4 :
    blockEstimate 1809 380 1276 256 = 63402155136 :=
  block_append moment_1809_380_part7 moment_1809_380_part8 rfl rfl rfl
private theorem moment_1809_380_join5 :
    blockEstimate 1809 380 1148 384 = 93964012224 :=
  block_append moment_1809_380_part6 moment_1809_380_join4 rfl rfl rfl
private theorem moment_1809_380_join6 :
    blockEstimate 1809 380 892 640 = 144819136320 :=
  block_append moment_1809_380_join3 moment_1809_380_join5 rfl rfl rfl
private theorem moment_1809_380_join7 :
    blockEstimate 1809 380 380 1152 = 176389754535 :=
  block_append moment_1809_380_join2 moment_1809_380_join6 rfl rfl rfl
private theorem moment_1809_380_join8 :
    blockEstimate 1809 380 1532 256 = 55786544256 :=
  block_append moment_1809_380_part9 moment_1809_380_part10 rfl rfl rfl
private theorem moment_1809_380_join9 :
    blockEstimate 1809 380 1788 256 = 36804316769 :=
  block_append moment_1809_380_part11 moment_1809_380_part12 rfl rfl rfl
private theorem moment_1809_380_join10 :
    blockEstimate 1809 380 1532 512 = 92590861025 :=
  block_append moment_1809_380_join8 moment_1809_380_join9 rfl rfl rfl
private theorem moment_1809_380_join11 :
    blockEstimate 1809 380 2044 256 = 16144382470 :=
  block_append moment_1809_380_part13 moment_1809_380_part14 rfl rfl rfl
private theorem moment_1809_380_join12 :
    blockEstimate 1809 380 2428 141 = 420403434 :=
  block_append moment_1809_380_part16 moment_1809_380_part17 rfl rfl rfl
private theorem moment_1809_380_join13 :
    blockEstimate 1809 380 2300 269 = 2776788602 :=
  block_append moment_1809_380_part15 moment_1809_380_join12 rfl rfl rfl
private theorem moment_1809_380_join14 :
    blockEstimate 1809 380 2044 525 = 18921171072 :=
  block_append moment_1809_380_join11 moment_1809_380_join13 rfl rfl rfl
private theorem moment_1809_380_join15 :
    blockEstimate 1809 380 1532 1037 = 111512032097 :=
  block_append moment_1809_380_join10 moment_1809_380_join14 rfl rfl rfl
private theorem moment_1809_380_join16 :
    blockEstimate 1809 380 380 2189 = 287901786632 :=
  block_append moment_1809_380_join7 moment_1809_380_join15 rfl rfl rfl

theorem moment_1809_380 : momentEstimate 1809 380 = 287901786632 := moment_1809_380_join16

private theorem moment_1809_395_part0 :
    blockEstimate 1809 395 395 128 = 613111200 := by decide +kernel
private theorem moment_1809_395_part1 :
    blockEstimate 1809 395 523 128 = 3963594144 := by decide +kernel
private theorem moment_1809_395_part2 :
    blockEstimate 1809 395 651 128 = 9896719776 := by decide +kernel
private theorem moment_1809_395_part3 :
    blockEstimate 1809 395 779 128 = 17253050925 := by decide +kernel
private theorem moment_1809_395_part4 :
    blockEstimate 1809 395 907 128 = 23627260800 := by decide +kernel
private theorem moment_1809_395_part5 :
    blockEstimate 1809 395 1035 128 = 28340839296 := by decide +kernel
private theorem moment_1809_395_part6 :
    blockEstimate 1809 395 1163 128 = 31393473408 := by decide +kernel
private theorem moment_1809_395_part7 :
    blockEstimate 1809 395 1291 128 = 32785163136 := by decide +kernel
private theorem moment_1809_395_part8 :
    blockEstimate 1809 395 1419 128 = 32515908480 := by decide +kernel
private theorem moment_1809_395_part9 :
    blockEstimate 1809 395 1547 128 = 30585709440 := by decide +kernel
private theorem moment_1809_395_part10 :
    blockEstimate 1809 395 1675 128 = 26994566016 := by decide +kernel
private theorem moment_1809_395_part11 :
    blockEstimate 1809 395 1803 128 = 21919153025 := by decide +kernel
private theorem moment_1809_395_part12 :
    blockEstimate 1809 395 1931 128 = 16340444489 := by decide +kernel
private theorem moment_1809_395_part13 :
    blockEstimate 1809 395 2059 128 = 10971561561 := by decide +kernel
private theorem moment_1809_395_part14 :
    blockEstimate 1809 395 2187 128 = 6272279892 := by decide +kernel
private theorem moment_1809_395_part15 :
    blockEstimate 1809 395 2315 128 = 2685846592 := by decide +kernel
private theorem moment_1809_395_part16 :
    blockEstimate 1809 395 2443 128 = 561511488 := by decide +kernel
private theorem moment_1809_395_part17 :
    blockEstimate 1809 395 2571 28 = 3835580 := by decide +kernel
private theorem moment_1809_395_join0 :
    blockEstimate 1809 395 395 256 = 4576705344 :=
  block_append moment_1809_395_part0 moment_1809_395_part1 rfl rfl rfl
private theorem moment_1809_395_join1 :
    blockEstimate 1809 395 651 256 = 27149770701 :=
  block_append moment_1809_395_part2 moment_1809_395_part3 rfl rfl rfl
private theorem moment_1809_395_join2 :
    blockEstimate 1809 395 395 512 = 31726476045 :=
  block_append moment_1809_395_join0 moment_1809_395_join1 rfl rfl rfl
private theorem moment_1809_395_join3 :
    blockEstimate 1809 395 907 256 = 51968100096 :=
  block_append moment_1809_395_part4 moment_1809_395_part5 rfl rfl rfl
private theorem moment_1809_395_join4 :
    blockEstimate 1809 395 1291 256 = 65301071616 :=
  block_append moment_1809_395_part7 moment_1809_395_part8 rfl rfl rfl
private theorem moment_1809_395_join5 :
    blockEstimate 1809 395 1163 384 = 96694545024 :=
  block_append moment_1809_395_part6 moment_1809_395_join4 rfl rfl rfl
private theorem moment_1809_395_join6 :
    blockEstimate 1809 395 907 640 = 148662645120 :=
  block_append moment_1809_395_join3 moment_1809_395_join5 rfl rfl rfl
private theorem moment_1809_395_join7 :
    blockEstimate 1809 395 395 1152 = 180389121165 :=
  block_append moment_1809_395_join2 moment_1809_395_join6 rfl rfl rfl
private theorem moment_1809_395_join8 :
    blockEstimate 1809 395 1547 256 = 57580275456 :=
  block_append moment_1809_395_part9 moment_1809_395_part10 rfl rfl rfl
private theorem moment_1809_395_join9 :
    blockEstimate 1809 395 1803 256 = 38259597514 :=
  block_append moment_1809_395_part11 moment_1809_395_part12 rfl rfl rfl
private theorem moment_1809_395_join10 :
    blockEstimate 1809 395 1547 512 = 95839872970 :=
  block_append moment_1809_395_join8 moment_1809_395_join9 rfl rfl rfl
private theorem moment_1809_395_join11 :
    blockEstimate 1809 395 2059 256 = 17243841453 :=
  block_append moment_1809_395_part13 moment_1809_395_part14 rfl rfl rfl
private theorem moment_1809_395_join12 :
    blockEstimate 1809 395 2443 156 = 565347068 :=
  block_append moment_1809_395_part16 moment_1809_395_part17 rfl rfl rfl
private theorem moment_1809_395_join13 :
    blockEstimate 1809 395 2315 284 = 3251193660 :=
  block_append moment_1809_395_part15 moment_1809_395_join12 rfl rfl rfl
private theorem moment_1809_395_join14 :
    blockEstimate 1809 395 2059 540 = 20495035113 :=
  block_append moment_1809_395_join11 moment_1809_395_join13 rfl rfl rfl
private theorem moment_1809_395_join15 :
    blockEstimate 1809 395 1547 1052 = 116334908083 :=
  block_append moment_1809_395_join10 moment_1809_395_join14 rfl rfl rfl
private theorem moment_1809_395_join16 :
    blockEstimate 1809 395 395 2204 = 296724029248 :=
  block_append moment_1809_395_join7 moment_1809_395_join15 rfl rfl rfl

theorem moment_1809_395 : momentEstimate 1809 395 = 296724029248 := moment_1809_395_join16

private theorem moment_1817_380_part0 :
    blockEstimate 1817 380 380 128 = 615973280 := by decide +kernel
private theorem moment_1817_380_part1 :
    blockEstimate 1817 380 508 128 = 3983364512 := by decide +kernel
private theorem moment_1817_380_part2 :
    blockEstimate 1817 380 636 128 = 9950161303 := by decide +kernel
private theorem moment_1817_380_part3 :
    blockEstimate 1817 380 764 128 = 17198059584 := by decide +kernel
private theorem moment_1817_380_part4 :
    blockEstimate 1817 380 892 128 = 23334244416 := by decide +kernel
private theorem moment_1817_380_part5 :
    blockEstimate 1817 380 1020 128 = 27872399424 := by decide +kernel
private theorem moment_1817_380_part6 :
    blockEstimate 1817 380 1148 128 = 30812524608 := by decide +kernel
private theorem moment_1817_380_part7 :
    blockEstimate 1817 380 1276 128 = 32154619968 := by decide +kernel
private theorem moment_1817_380_part8 :
    blockEstimate 1817 380 1404 128 = 31898685504 := by decide +kernel
private theorem moment_1817_380_part9 :
    blockEstimate 1817 380 1532 128 = 30044721216 := by decide +kernel
private theorem moment_1817_380_part10 :
    blockEstimate 1817 380 1660 128 = 26592727104 := by decide +kernel
private theorem moment_1817_380_part11 :
    blockEstimate 1817 380 1788 128 = 21638440059 := by decide +kernel
private theorem moment_1817_380_part12 :
    blockEstimate 1817 380 1916 128 = 16076646528 := by decide +kernel
private theorem moment_1817_380_part13 :
    blockEstimate 1817 380 2044 128 = 10730530099 := by decide +kernel
private theorem moment_1817_380_part14 :
    blockEstimate 1817 380 2172 128 = 6072063646 := by decide +kernel
private theorem moment_1817_380_part15 :
    blockEstimate 1817 380 2300 128 = 2541701328 := by decide +kernel
private theorem moment_1817_380_part16 :
    blockEstimate 1817 380 2428 128 = 494759120 := by decide +kernel
private theorem moment_1817_380_part17 :
    blockEstimate 1817 380 2556 21 = 1710177 := by decide +kernel
private theorem moment_1817_380_join0 :
    blockEstimate 1817 380 380 256 = 4599337792 :=
  block_append moment_1817_380_part0 moment_1817_380_part1 rfl rfl rfl
private theorem moment_1817_380_join1 :
    blockEstimate 1817 380 636 256 = 27148220887 :=
  block_append moment_1817_380_part2 moment_1817_380_part3 rfl rfl rfl
private theorem moment_1817_380_join2 :
    blockEstimate 1817 380 380 512 = 31747558679 :=
  block_append moment_1817_380_join0 moment_1817_380_join1 rfl rfl rfl
private theorem moment_1817_380_join3 :
    blockEstimate 1817 380 892 256 = 51206643840 :=
  block_append moment_1817_380_part4 moment_1817_380_part5 rfl rfl rfl
private theorem moment_1817_380_join4 :
    blockEstimate 1817 380 1276 256 = 64053305472 :=
  block_append moment_1817_380_part7 moment_1817_380_part8 rfl rfl rfl
private theorem moment_1817_380_join5 :
    blockEstimate 1817 380 1148 384 = 94865830080 :=
  block_append moment_1817_380_part6 moment_1817_380_join4 rfl rfl rfl
private theorem moment_1817_380_join6 :
    blockEstimate 1817 380 892 640 = 146072473920 :=
  block_append moment_1817_380_join3 moment_1817_380_join5 rfl rfl rfl
private theorem moment_1817_380_join7 :
    blockEstimate 1817 380 380 1152 = 177820032599 :=
  block_append moment_1817_380_join2 moment_1817_380_join6 rfl rfl rfl
private theorem moment_1817_380_join8 :
    blockEstimate 1817 380 1532 256 = 56637448320 :=
  block_append moment_1817_380_part9 moment_1817_380_part10 rfl rfl rfl
private theorem moment_1817_380_join9 :
    blockEstimate 1817 380 1788 256 = 37715086587 :=
  block_append moment_1817_380_part11 moment_1817_380_part12 rfl rfl rfl
private theorem moment_1817_380_join10 :
    blockEstimate 1817 380 1532 512 = 94352534907 :=
  block_append moment_1817_380_join8 moment_1817_380_join9 rfl rfl rfl
private theorem moment_1817_380_join11 :
    blockEstimate 1817 380 2044 256 = 16802593745 :=
  block_append moment_1817_380_part13 moment_1817_380_part14 rfl rfl rfl
private theorem moment_1817_380_join12 :
    blockEstimate 1817 380 2428 149 = 496469297 :=
  block_append moment_1817_380_part16 moment_1817_380_part17 rfl rfl rfl
private theorem moment_1817_380_join13 :
    blockEstimate 1817 380 2300 277 = 3038170625 :=
  block_append moment_1817_380_part15 moment_1817_380_join12 rfl rfl rfl
private theorem moment_1817_380_join14 :
    blockEstimate 1817 380 2044 533 = 19840764370 :=
  block_append moment_1817_380_join11 moment_1817_380_join13 rfl rfl rfl
private theorem moment_1817_380_join15 :
    blockEstimate 1817 380 1532 1045 = 114193299277 :=
  block_append moment_1817_380_join10 moment_1817_380_join14 rfl rfl rfl
private theorem moment_1817_380_join16 :
    blockEstimate 1817 380 380 2197 = 292013331876 :=
  block_append moment_1817_380_join7 moment_1817_380_join15 rfl rfl rfl

theorem moment_1817_380 : momentEstimate 1817 380 = 292013331876 := moment_1817_380_join16

private theorem moment_2285_480_part0 :
    blockEstimate 2285 480 480 128 = 783404960 := by decide +kernel
private theorem moment_2285_480_part1 :
    blockEstimate 2285 480 608 128 = 5139931040 := by decide +kernel
private theorem moment_2285_480_part2 :
    blockEstimate 2285 480 736 128 = 13077344160 := by decide +kernel
private theorem moment_2285_480_part3 :
    blockEstimate 2285 480 864 128 = 23780618088 := by decide +kernel
private theorem moment_2285_480_part4 :
    blockEstimate 2285 480 992 128 = 35332736192 := by decide +kernel
private theorem moment_2285_480_part5 :
    blockEstimate 2285 480 1120 128 = 45144212672 := by decide +kernel
private theorem moment_2285_480_part6 :
    blockEstimate 2285 480 1248 128 = 52938228928 := by decide +kernel
private theorem moment_2285_480_part7 :
    blockEstimate 2285 480 1376 128 = 58714784960 := by decide +kernel
private theorem moment_2285_480_part8 :
    blockEstimate 2285 480 1504 128 = 62473880768 := by decide +kernel
private theorem moment_2285_480_part9 :
    blockEstimate 2285 480 1632 128 = 64215516352 := by decide +kernel
private theorem moment_2285_480_part10 :
    blockEstimate 2285 480 1760 128 = 63939691712 := by decide +kernel
private theorem moment_2285_480_part11 :
    blockEstimate 2285 480 1888 128 = 61646406848 := by decide +kernel
private theorem moment_2285_480_part12 :
    blockEstimate 2285 480 2016 128 = 57335661760 := by decide +kernel
private theorem moment_2285_480_part13 :
    blockEstimate 2285 480 2144 128 = 51007456448 := by decide +kernel
private theorem moment_2285_480_part14 :
    blockEstimate 2285 480 2272 128 = 42848244955 := by decide +kernel
private theorem moment_2285_480_part15 :
    blockEstimate 2285 480 2400 128 = 34024165326 := by decide +kernel
private theorem moment_2285_480_part16 :
    blockEstimate 2285 480 2528 128 = 25358865055 := by decide +kernel
private theorem moment_2285_480_part17 :
    blockEstimate 2285 480 2656 128 = 17353338622 := by decide +kernel
private theorem moment_2285_480_part18 :
    blockEstimate 2285 480 2784 128 = 10420160528 := by decide +kernel
private theorem moment_2285_480_part19 :
    blockEstimate 2285 480 2912 128 = 5035269136 := by decide +kernel
private theorem moment_2285_480_part20 :
    blockEstimate 2285 480 3040 128 = 1515991056 := by decide +kernel
private theorem moment_2285_480_part21 :
    blockEstimate 2285 480 3168 77 = 90657650 := by decide +kernel
private theorem moment_2285_480_join0 :
    blockEstimate 2285 480 480 256 = 5923336000 :=
  block_append moment_2285_480_part0 moment_2285_480_part1 rfl rfl rfl
private theorem moment_2285_480_join1 :
    blockEstimate 2285 480 864 256 = 59113354280 :=
  block_append moment_2285_480_part3 moment_2285_480_part4 rfl rfl rfl
private theorem moment_2285_480_join2 :
    blockEstimate 2285 480 736 384 = 72190698440 :=
  block_append moment_2285_480_part2 moment_2285_480_join1 rfl rfl rfl
private theorem moment_2285_480_join3 :
    blockEstimate 2285 480 480 640 = 78114034440 :=
  block_append moment_2285_480_join0 moment_2285_480_join2 rfl rfl rfl
private theorem moment_2285_480_join4 :
    blockEstimate 2285 480 1248 256 = 111653013888 :=
  block_append moment_2285_480_part6 moment_2285_480_part7 rfl rfl rfl
private theorem moment_2285_480_join5 :
    blockEstimate 2285 480 1120 384 = 156797226560 :=
  block_append moment_2285_480_part5 moment_2285_480_join4 rfl rfl rfl
private theorem moment_2285_480_join6 :
    blockEstimate 2285 480 1632 256 = 128155208064 :=
  block_append moment_2285_480_part9 moment_2285_480_part10 rfl rfl rfl
private theorem moment_2285_480_join7 :
    blockEstimate 2285 480 1504 384 = 190629088832 :=
  block_append moment_2285_480_part8 moment_2285_480_join6 rfl rfl rfl
private theorem moment_2285_480_join8 :
    blockEstimate 2285 480 1120 768 = 347426315392 :=
  block_append moment_2285_480_join5 moment_2285_480_join7 rfl rfl rfl
private theorem moment_2285_480_join9 :
    blockEstimate 2285 480 480 1408 = 425540349832 :=
  block_append moment_2285_480_join3 moment_2285_480_join8 rfl rfl rfl
private theorem moment_2285_480_join10 :
    blockEstimate 2285 480 1888 256 = 118982068608 :=
  block_append moment_2285_480_part11 moment_2285_480_part12 rfl rfl rfl
private theorem moment_2285_480_join11 :
    blockEstimate 2285 480 2272 256 = 76872410281 :=
  block_append moment_2285_480_part14 moment_2285_480_part15 rfl rfl rfl
private theorem moment_2285_480_join12 :
    blockEstimate 2285 480 2144 384 = 127879866729 :=
  block_append moment_2285_480_part13 moment_2285_480_join11 rfl rfl rfl
private theorem moment_2285_480_join13 :
    blockEstimate 2285 480 1888 640 = 246861935337 :=
  block_append moment_2285_480_join10 moment_2285_480_join12 rfl rfl rfl
private theorem moment_2285_480_join14 :
    blockEstimate 2285 480 2656 256 = 27773499150 :=
  block_append moment_2285_480_part17 moment_2285_480_part18 rfl rfl rfl
private theorem moment_2285_480_join15 :
    blockEstimate 2285 480 2528 384 = 53132364205 :=
  block_append moment_2285_480_part16 moment_2285_480_join14 rfl rfl rfl
private theorem moment_2285_480_join16 :
    blockEstimate 2285 480 3040 205 = 1606648706 :=
  block_append moment_2285_480_part20 moment_2285_480_part21 rfl rfl rfl
private theorem moment_2285_480_join17 :
    blockEstimate 2285 480 2912 333 = 6641917842 :=
  block_append moment_2285_480_part19 moment_2285_480_join16 rfl rfl rfl
private theorem moment_2285_480_join18 :
    blockEstimate 2285 480 2528 717 = 59774282047 :=
  block_append moment_2285_480_join15 moment_2285_480_join17 rfl rfl rfl
private theorem moment_2285_480_join19 :
    blockEstimate 2285 480 1888 1357 = 306636217384 :=
  block_append moment_2285_480_join13 moment_2285_480_join18 rfl rfl rfl
private theorem moment_2285_480_join20 :
    blockEstimate 2285 480 480 2765 = 732176567216 :=
  block_append moment_2285_480_join9 moment_2285_480_join19 rfl rfl rfl

theorem moment_2285_480 : momentEstimate 2285 480 = 732176567216 := moment_2285_480_join20

private theorem moment_2285_498_part0 :
    blockEstimate 2285 498 498 128 = 783404960 := by decide +kernel
private theorem moment_2285_498_part1 :
    blockEstimate 2285 498 626 128 = 5139931040 := by decide +kernel
private theorem moment_2285_498_part2 :
    blockEstimate 2285 498 754 128 = 13077344160 := by decide +kernel
private theorem moment_2285_498_part3 :
    blockEstimate 2285 498 882 128 = 23789529417 := by decide +kernel
private theorem moment_2285_498_part4 :
    blockEstimate 2285 498 1010 128 = 35672256512 := by decide +kernel
private theorem moment_2285_498_part5 :
    blockEstimate 2285 498 1138 128 = 45924478976 := by decide +kernel
private theorem moment_2285_498_part6 :
    blockEstimate 2285 498 1266 128 = 54083743744 := by decide +kernel
private theorem moment_2285_498_part7 :
    blockEstimate 2285 498 1394 128 = 60150050816 := by decide +kernel
private theorem moment_2285_498_part8 :
    blockEstimate 2285 498 1522 128 = 64123400192 := by decide +kernel
private theorem moment_2285_498_part9 :
    blockEstimate 2285 498 1650 128 = 66003791872 := by decide +kernel
private theorem moment_2285_498_part10 :
    blockEstimate 2285 498 1778 128 = 65791225856 := by decide +kernel
private theorem moment_2285_498_part11 :
    blockEstimate 2285 498 1906 128 = 63485702144 := by decide +kernel
private theorem moment_2285_498_part12 :
    blockEstimate 2285 498 2034 128 = 59087220736 := by decide +kernel
private theorem moment_2285_498_part13 :
    blockEstimate 2285 498 2162 128 = 52595798457 := by decide +kernel
private theorem moment_2285_498_part14 :
    blockEstimate 2285 498 2290 128 = 44296056302 := by decide +kernel
private theorem moment_2285_498_part15 :
    blockEstimate 2285 498 2418 128 = 35392420168 := by decide +kernel
private theorem moment_2285_498_part16 :
    blockEstimate 2285 498 2546 128 = 26610909096 := by decide +kernel
private theorem moment_2285_498_part17 :
    blockEstimate 2285 498 2674 128 = 18448620482 := by decide +kernel
private theorem moment_2285_498_part18 :
    blockEstimate 2285 498 2802 128 = 11312632000 := by decide +kernel
private theorem moment_2285_498_part19 :
    blockEstimate 2285 498 2930 128 = 5685571776 := by decide +kernel
private theorem moment_2285_498_part20 :
    blockEstimate 2285 498 3058 128 = 1888735424 := by decide +kernel
private theorem moment_2285_498_part21 :
    blockEstimate 2285 498 3186 95 = 167798160 := by decide +kernel
private theorem moment_2285_498_join0 :
    blockEstimate 2285 498 498 256 = 5923336000 :=
  block_append moment_2285_498_part0 moment_2285_498_part1 rfl rfl rfl
private theorem moment_2285_498_join1 :
    blockEstimate 2285 498 882 256 = 59461785929 :=
  block_append moment_2285_498_part3 moment_2285_498_part4 rfl rfl rfl
private theorem moment_2285_498_join2 :
    blockEstimate 2285 498 754 384 = 72539130089 :=
  block_append moment_2285_498_part2 moment_2285_498_join1 rfl rfl rfl
private theorem moment_2285_498_join3 :
    blockEstimate 2285 498 498 640 = 78462466089 :=
  block_append moment_2285_498_join0 moment_2285_498_join2 rfl rfl rfl
private theorem moment_2285_498_join4 :
    blockEstimate 2285 498 1266 256 = 114233794560 :=
  block_append moment_2285_498_part6 moment_2285_498_part7 rfl rfl rfl
private theorem moment_2285_498_join5 :
    blockEstimate 2285 498 1138 384 = 160158273536 :=
  block_append moment_2285_498_part5 moment_2285_498_join4 rfl rfl rfl
private theorem moment_2285_498_join6 :
    blockEstimate 2285 498 1650 256 = 131795017728 :=
  block_append moment_2285_498_part9 moment_2285_498_part10 rfl rfl rfl
private theorem moment_2285_498_join7 :
    blockEstimate 2285 498 1522 384 = 195918417920 :=
  block_append moment_2285_498_part8 moment_2285_498_join6 rfl rfl rfl
private theorem moment_2285_498_join8 :
    blockEstimate 2285 498 1138 768 = 356076691456 :=
  block_append moment_2285_498_join5 moment_2285_498_join7 rfl rfl rfl
private theorem moment_2285_498_join9 :
    blockEstimate 2285 498 498 1408 = 434539157545 :=
  block_append moment_2285_498_join3 moment_2285_498_join8 rfl rfl rfl
private theorem moment_2285_498_join10 :
    blockEstimate 2285 498 1906 256 = 122572922880 :=
  block_append moment_2285_498_part11 moment_2285_498_part12 rfl rfl rfl
private theorem moment_2285_498_join11 :
    blockEstimate 2285 498 2290 256 = 79688476470 :=
  block_append moment_2285_498_part14 moment_2285_498_part15 rfl rfl rfl
private theorem moment_2285_498_join12 :
    blockEstimate 2285 498 2162 384 = 132284274927 :=
  block_append moment_2285_498_part13 moment_2285_498_join11 rfl rfl rfl
private theorem moment_2285_498_join13 :
    blockEstimate 2285 498 1906 640 = 254857197807 :=
  block_append moment_2285_498_join10 moment_2285_498_join12 rfl rfl rfl
private theorem moment_2285_498_join14 :
    blockEstimate 2285 498 2674 256 = 29761252482 :=
  block_append moment_2285_498_part17 moment_2285_498_part18 rfl rfl rfl
private theorem moment_2285_498_join15 :
    blockEstimate 2285 498 2546 384 = 56372161578 :=
  block_append moment_2285_498_part16 moment_2285_498_join14 rfl rfl rfl
private theorem moment_2285_498_join16 :
    blockEstimate 2285 498 3058 223 = 2056533584 :=
  block_append moment_2285_498_part20 moment_2285_498_part21 rfl rfl rfl
private theorem moment_2285_498_join17 :
    blockEstimate 2285 498 2930 351 = 7742105360 :=
  block_append moment_2285_498_part19 moment_2285_498_join16 rfl rfl rfl
private theorem moment_2285_498_join18 :
    blockEstimate 2285 498 2546 735 = 64114266938 :=
  block_append moment_2285_498_join15 moment_2285_498_join17 rfl rfl rfl
private theorem moment_2285_498_join19 :
    blockEstimate 2285 498 1906 1375 = 318971464745 :=
  block_append moment_2285_498_join13 moment_2285_498_join18 rfl rfl rfl
private theorem moment_2285_498_join20 :
    blockEstimate 2285 498 498 2783 = 753510622290 :=
  block_append moment_2285_498_join9 moment_2285_498_join19 rfl rfl rfl

theorem moment_2285_498 : momentEstimate 2285 498 = 753510622290 := moment_2285_498_join20

private theorem receipt_0_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 0) 0 128 = 32090974217140337048559616 := by decide +kernel
private theorem receipt_0_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 0) 128 128 = 16444188410928575317060663 := by decide +kernel
private theorem receipt_0_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 0) 256 101 = 3674653120490114819289943 := by decide +kernel
private theorem receipt_0_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 0) 128 229 = 20118841531418690136350606 :=
  phaseBlock_append receipt_0_5_2359_0_part1 receipt_0_5_2359_0_part2 rfl rfl rfl
private theorem receipt_0_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 0) 0 357 = 52209815748559027184910222 :=
  phaseBlock_append receipt_0_5_2359_0_part0 receipt_0_5_2359_0_join0 rfl rfl rfl

private theorem receipt_0_5_2359_0 : fastPhase (bank 0 5).shape 179818 2359 5 1 0 1 0 = 52209815748559027184910222 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2359_0_join1

private theorem receipt_0_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 1) 0 128 = 31959412462546846365865344 := by decide +kernel
private theorem receipt_0_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 1) 128 128 = 16333510924268776573255875 := by decide +kernel
private theorem receipt_0_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 1) 256 101 = 3600847688945402891411370 := by decide +kernel
private theorem receipt_0_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 1) 128 229 = 19934358613214179464667245 :=
  phaseBlock_append receipt_0_5_2359_1_part1 receipt_0_5_2359_1_part2 rfl rfl rfl
private theorem receipt_0_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2359 5 1 0 1 1) 0 357 = 51893771075761025830532589 :=
  phaseBlock_append receipt_0_5_2359_1_part0 receipt_0_5_2359_1_join0 rfl rfl rfl

private theorem receipt_0_5_2359_1 : fastPhase (bank 0 5).shape 179818 2359 5 1 0 1 1 = 51893771075761025830532589 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2359_1_join1

private theorem receipt_0_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 0) 0 128 = 32091246487400997903568960 := by decide +kernel
private theorem receipt_0_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 0) 128 128 = 16444296591815446334974448 := by decide +kernel
private theorem receipt_0_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 0) 256 101 = 3674670579410656996386942 := by decide +kernel
private theorem receipt_0_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 0) 128 229 = 20118967171226103331361390 :=
  phaseBlock_append receipt_0_5_2360_0_part1 receipt_0_5_2360_0_part2 rfl rfl rfl
private theorem receipt_0_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 0) 0 357 = 52210213658627101234930350 :=
  phaseBlock_append receipt_0_5_2360_0_part0 receipt_0_5_2360_0_join0 rfl rfl rfl

private theorem receipt_0_5_2360_0 : fastPhase (bank 0 5).shape 179818 2360 5 1 0 1 0 = 52210213658627101234930350 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2360_0_join1

private theorem receipt_0_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 1) 0 128 = 31959683807434762056946880 := by decide +kernel
private theorem receipt_0_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 1) 128 128 = 16333618475413542895298770 := by decide +kernel
private theorem receipt_0_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 1) 256 101 = 3600864835348802450398563 := by decide +kernel
private theorem receipt_0_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 1) 128 229 = 19934483310762345345697333 :=
  phaseBlock_append receipt_0_5_2360_1_part1 receipt_0_5_2360_1_part2 rfl rfl rfl
private theorem receipt_0_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179818 2360 5 1 0 1 1) 0 357 = 51894167118197107402644213 :=
  phaseBlock_append receipt_0_5_2360_1_part0 receipt_0_5_2360_1_join0 rfl rfl rfl

private theorem receipt_0_5_2360_1 : fastPhase (bank 0 5).shape 179818 2360 5 1 0 1 1 = 51894167118197107402644213 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2360_1_join1

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2359_0 receipt_0_5_2359_1 receipt_0_5_2360_0 receipt_0_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 0) 0 128 = 28861436947913444218583488 := by decide +kernel
private theorem receipt_1_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 0) 128 128 = 14751765671627144305622983 := by decide +kernel
private theorem receipt_1_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 0) 256 101 = 3289265401574729438352865 := by decide +kernel
private theorem receipt_1_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 0) 128 229 = 18041031073201873743975848 :=
  phaseBlock_append receipt_1_5_2359_0_part1 receipt_1_5_2359_0_part2 rfl rfl rfl
private theorem receipt_1_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 0) 0 357 = 46902468021115317962559336 :=
  phaseBlock_append receipt_1_5_2359_0_part0 receipt_1_5_2359_0_join0 rfl rfl rfl

private theorem receipt_1_5_2359_0 : fastPhase (bank 1 5).shape 179818 2359 5 1 0 2 0 = 46902468021115317962559336 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2359_0_join1

private theorem receipt_1_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 1) 0 128 = 28742538543763505459069184 := by decide +kernel
private theorem receipt_1_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 1) 128 128 = 14652194130046026255274881 := by decide +kernel
private theorem receipt_1_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 1) 256 101 = 3223155795847169784128676 := by decide +kernel
private theorem receipt_1_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 1) 128 229 = 17875349925893196039403557 :=
  phaseBlock_append receipt_1_5_2359_1_part1 receipt_1_5_2359_1_part2 rfl rfl rfl
private theorem receipt_1_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2359 5 1 0 2 1) 0 357 = 46617888469656701498472741 :=
  phaseBlock_append receipt_1_5_2359_1_part0 receipt_1_5_2359_1_join0 rfl rfl rfl

private theorem receipt_1_5_2359_1 : fastPhase (bank 1 5).shape 179818 2359 5 1 0 2 1 = 46617888469656701498472741 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2359_1_join1

private theorem receipt_1_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 0) 0 128 = 28861681829159471843282944 := by decide +kernel
private theorem receipt_1_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 0) 128 128 = 14751862724961680602094954 := by decide +kernel
private theorem receipt_1_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 0) 256 101 = 3289281030145839404347179 := by decide +kernel
private theorem receipt_1_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 0) 128 229 = 18041143755107520006442133 :=
  phaseBlock_append receipt_1_5_2360_0_part1 receipt_1_5_2360_0_part2 rfl rfl rfl
private theorem receipt_1_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 0) 0 357 = 46902825584266991849725077 :=
  phaseBlock_append receipt_1_5_2360_0_part0 receipt_1_5_2360_0_join0 rfl rfl rfl

private theorem receipt_1_5_2360_0 : fastPhase (bank 1 5).shape 179818 2360 5 1 0 2 0 = 46902825584266991849725077 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2360_0_join1

private theorem receipt_1_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 1) 0 128 = 28742782587822503531127680 := by decide +kernel
private theorem receipt_1_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 1) 128 128 = 14652290616529863122750911 := by decide +kernel
private theorem receipt_1_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 1) 256 101 = 3223171144437039789594033 := by decide +kernel
private theorem receipt_1_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 1) 128 229 = 17875461760966902912344944 :=
  phaseBlock_append receipt_1_5_2360_1_part1 receipt_1_5_2360_1_part2 rfl rfl rfl
private theorem receipt_1_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179818 2360 5 1 0 2 1) 0 357 = 46618244348789406443472624 :=
  phaseBlock_append receipt_1_5_2360_1_part0 receipt_1_5_2360_1_join0 rfl rfl rfl

private theorem receipt_1_5_2360_1 : fastPhase (bank 1 5).shape 179818 2360 5 1 0 2 1 = 46618244348789406443472624 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2360_1_join1

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2359_0 receipt_1_5_2359_1 receipt_1_5_2360_0 receipt_1_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 0) 0 128 = 15374571540781802447333568 := by decide +kernel
private theorem receipt_2_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 0) 128 128 = 7714755793333521272996496 := by decide +kernel
private theorem receipt_2_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 0) 256 101 = 1692861883912775081057627 := by decide +kernel
private theorem receipt_2_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 0) 128 229 = 9407617677246296354054123 :=
  phaseBlock_append receipt_2_5_2359_0_part1 receipt_2_5_2359_0_part2 rfl rfl rfl
private theorem receipt_2_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 0) 0 357 = 24782189218028098801387691 :=
  phaseBlock_append receipt_2_5_2359_0_part0 receipt_2_5_2359_0_join0 rfl rfl rfl

private theorem receipt_2_5_2359_0 : fastPhase (bank 2 5).shape 179818 2359 5 1 0 7 0 = 24782189218028098801387691 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2359_0_join1

private theorem receipt_2_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 1) 0 128 = 15309016971635925313804672 := by decide +kernel
private theorem receipt_2_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 1) 128 128 = 7661595948710983655366890 := by decide +kernel
private theorem receipt_2_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 1) 256 101 = 1658668332912156584089585 := by decide +kernel
private theorem receipt_2_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 1) 128 229 = 9320264281623140239456475 :=
  phaseBlock_append receipt_2_5_2359_1_part1 receipt_2_5_2359_1_part2 rfl rfl rfl
private theorem receipt_2_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2359 5 1 0 7 1) 0 357 = 24629281253259065553261147 :=
  phaseBlock_append receipt_2_5_2359_1_part0 receipt_2_5_2359_1_join0 rfl rfl rfl

private theorem receipt_2_5_2359_1 : fastPhase (bank 2 5).shape 179818 2359 5 1 0 7 1 = 24629281253259065553261147 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2359_1_join1

private theorem receipt_2_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 0) 0 128 = 15374702033669311636576800 := by decide +kernel
private theorem receipt_2_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 0) 128 128 = 7714806573645479281186607 := by decide +kernel
private theorem receipt_2_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 0) 256 101 = 1692869929985522462262311 := by decide +kernel
private theorem receipt_2_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 0) 128 229 = 9407676503631001743448918 :=
  phaseBlock_append receipt_2_5_2360_0_part1 receipt_2_5_2360_0_part2 rfl rfl rfl
private theorem receipt_2_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 0) 0 357 = 24782378537300313380025718 :=
  phaseBlock_append receipt_2_5_2360_0_part0 receipt_2_5_2360_0_join0 rfl rfl rfl

private theorem receipt_2_5_2360_0 : fastPhase (bank 2 5).shape 179818 2360 5 1 0 7 0 = 24782378537300313380025718 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2360_0_join1

private theorem receipt_2_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 1) 0 128 = 15309146999550437747179680 := by decide +kernel
private theorem receipt_2_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 1) 128 128 = 7661646425245799792641497 := by decide +kernel
private theorem receipt_2_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 1) 256 101 = 1658676233979025918661433 := by decide +kernel
private theorem receipt_2_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 1) 128 229 = 9320322659224825711302930 :=
  phaseBlock_append receipt_2_5_2360_1_part1 receipt_2_5_2360_1_part2 rfl rfl rfl
private theorem receipt_2_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179818 2360 5 1 0 7 1) 0 357 = 24629469658775263458482610 :=
  phaseBlock_append receipt_2_5_2360_1_part0 receipt_2_5_2360_1_join0 rfl rfl rfl

private theorem receipt_2_5_2360_1 : fastPhase (bank 2 5).shape 179818 2360 5 1 0 7 1 = 24629469658775263458482610 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2360_1_join1

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2359_0 receipt_2_5_2359_1 receipt_2_5_2360_0 receipt_2_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 0) 0 128 = 3772041337147178468052448 := by decide +kernel
private theorem receipt_3_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 0) 128 128 = 1960040005477657700589024 := by decide +kernel
private theorem receipt_3_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 0) 256 115 = 503806392474238575377877 := by decide +kernel
private theorem receipt_3_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 0) 128 243 = 2463846397951896275966901 :=
  phaseBlock_append receipt_3_5_2359_0_part1 receipt_3_5_2359_0_part2 rfl rfl rfl
private theorem receipt_3_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 0) 0 371 = 6235887735099074744019349 :=
  phaseBlock_append receipt_3_5_2359_0_part0 receipt_3_5_2359_0_join0 rfl rfl rfl

private theorem receipt_3_5_2359_0 : fastPhase (bank 3 5).shape 179818 2359 5 1 1 1 0 = 6235887735099074744019349 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2359_0_join1

private theorem receipt_3_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 1) 0 128 = 3756785034142476698368800 := by decide +kernel
private theorem receipt_3_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 1) 128 128 = 1947311365606146921638688 := by decide +kernel
private theorem receipt_3_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 1) 256 115 = 494745975022114824923649 := by decide +kernel
private theorem receipt_3_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 1) 128 243 = 2442057340628261746562337 :=
  phaseBlock_append receipt_3_5_2359_1_part1 receipt_3_5_2359_1_part2 rfl rfl rfl
private theorem receipt_3_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2359 5 1 1 1 1) 0 371 = 6198842374770738444931137 :=
  phaseBlock_append receipt_3_5_2359_1_part0 receipt_3_5_2359_1_join0 rfl rfl rfl

private theorem receipt_3_5_2359_1 : fastPhase (bank 3 5).shape 179818 2359 5 1 1 1 1 = 6198842374770738444931137 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2359_1_join1

private theorem receipt_3_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 0) 0 128 = 3772071364902596559931104 := by decide +kernel
private theorem receipt_3_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 0) 128 128 = 1960049842191485491451616 := by decide +kernel
private theorem receipt_3_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 0) 256 115 = 503807676709892279957973 := by decide +kernel
private theorem receipt_3_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 0) 128 243 = 2463857518901377771409589 :=
  phaseBlock_append receipt_3_5_2360_0_part1 receipt_3_5_2360_0_part2 rfl rfl rfl
private theorem receipt_3_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 0) 0 371 = 6235928883803974331340693 :=
  phaseBlock_append receipt_3_5_2360_0_part0 receipt_3_5_2360_0_join0 rfl rfl rfl

private theorem receipt_3_5_2360_0 : fastPhase (bank 3 5).shape 179818 2360 5 1 1 1 0 = 6235928883803974331340693 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2360_0_join1

private theorem receipt_3_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 1) 0 128 = 3756814924086543244447584 := by decide +kernel
private theorem receipt_3_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 1) 128 128 = 1947321132987303367769952 := by decide +kernel
private theorem receipt_3_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 1) 256 115 = 494747238050280786734478 := by decide +kernel
private theorem receipt_3_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 1) 128 243 = 2442068371037584154504430 :=
  phaseBlock_append receipt_3_5_2360_1_part1 receipt_3_5_2360_1_part2 rfl rfl rfl
private theorem receipt_3_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179818 2360 5 1 1 1 1) 0 371 = 6198883295124127398952014 :=
  phaseBlock_append receipt_3_5_2360_1_part0 receipt_3_5_2360_1_join0 rfl rfl rfl

private theorem receipt_3_5_2360_1 : fastPhase (bank 3 5).shape 179818 2360 5 1 1 1 1 = 6198883295124127398952014 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2360_1_join1

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2359_0 receipt_3_5_2359_1 receipt_3_5_2360_0 receipt_3_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 0) 0 128 = 58778265899368218944800036 := by decide +kernel
private theorem receipt_0_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 0) 128 128 = 32070585476402042965846152 := by decide +kernel
private theorem receipt_0_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 0) 256 125 = 9575397186287682243513156 := by decide +kernel
private theorem receipt_0_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 0) 128 253 = 41645982662689725209359308 :=
  phaseBlock_append receipt_0_6_2359_0_part1 receipt_0_6_2359_0_part2 rfl rfl rfl
private theorem receipt_0_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 0) 0 381 = 100424248562057944154159344 :=
  phaseBlock_append receipt_0_6_2359_0_part0 receipt_0_6_2359_0_join0 rfl rfl rfl

private theorem receipt_0_6_2359_0 : fastPhase (bank 0 6).shape 179818 2359 7 1 0 1 0 = 100424248562057944154159344 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2359_0_join1

private theorem receipt_0_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 1) 0 128 = 58555046318472817367735556 := by decide +kernel
private theorem receipt_0_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 1) 128 128 = 31880497311077722960511358 := by decide +kernel
private theorem receipt_0_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 1) 256 125 = 9419131699814318904877296 := by decide +kernel
private theorem receipt_0_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 1) 128 253 = 41299629010892041865388654 :=
  phaseBlock_append receipt_0_6_2359_1_part1 receipt_0_6_2359_1_part2 rfl rfl rfl
private theorem receipt_0_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2359 7 1 0 1 1) 0 381 = 99854675329364859233124210 :=
  phaseBlock_append receipt_0_6_2359_1_part0 receipt_0_6_2359_1_join0 rfl rfl rfl

private theorem receipt_0_6_2359_1 : fastPhase (bank 0 6).shape 179818 2359 7 1 0 1 1 = 99854675329364859233124210 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2359_1_join1

private theorem receipt_0_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 0) 0 128 = 58778769138807546556912188 := by decide +kernel
private theorem receipt_0_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 0) 128 128 = 32070801342606573208886589 := by decide +kernel
private theorem receipt_0_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 0) 256 125 = 9575444213735315445900441 := by decide +kernel
private theorem receipt_0_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 0) 128 253 = 41646245556341888654787030 :=
  phaseBlock_append receipt_0_6_2360_0_part1 receipt_0_6_2360_0_part2 rfl rfl rfl
private theorem receipt_0_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 0) 0 381 = 100425014695149435211699218 :=
  phaseBlock_append receipt_0_6_2360_0_part0 receipt_0_6_2360_0_join0 rfl rfl rfl

private theorem receipt_0_6_2360_0 : fastPhase (bank 0 6).shape 179818 2360 7 1 0 1 0 = 100425014695149435211699218 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2360_0_join1

private theorem receipt_0_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 1) 0 128 = 58555547975204332776120651 := by decide +kernel
private theorem receipt_0_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 1) 128 128 = 31880712073603128526025685 := by decide +kernel
private theorem receipt_0_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 1) 256 125 = 9419178053239920806667441 := by decide +kernel
private theorem receipt_0_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 1) 128 253 = 41299890126843049332693126 :=
  phaseBlock_append receipt_0_6_2360_1_part1 receipt_0_6_2360_1_part2 rfl rfl rfl
private theorem receipt_0_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179818 2360 7 1 0 1 1) 0 381 = 99855438102047382108813777 :=
  phaseBlock_append receipt_0_6_2360_1_part0 receipt_0_6_2360_1_join0 rfl rfl rfl

private theorem receipt_0_6_2360_1 : fastPhase (bank 0 6).shape 179818 2360 7 1 0 1 1 = 99855438102047382108813777 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2360_1_join1

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2359_0 receipt_0_6_2359_1 receipt_0_6_2360_0 receipt_0_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 0) 0 128 = 52937648879691676095706978 := by decide +kernel
private theorem receipt_1_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 0) 128 128 = 28823398774324243421282217 := by decide +kernel
private theorem receipt_1_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 0) 256 125 = 8589515294107664757559326 := by decide +kernel
private theorem receipt_1_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 0) 128 253 = 37412914068431908178841543 :=
  phaseBlock_append receipt_1_6_2359_0_part1 receipt_1_6_2359_0_part2 rfl rfl rfl
private theorem receipt_1_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 0) 0 381 = 90350562948123584274548521 :=
  phaseBlock_append receipt_1_6_2359_0_part0 receipt_1_6_2359_0_join0 rfl rfl rfl

private theorem receipt_1_6_2359_0 : fastPhase (bank 1 6).shape 179818 2359 7 1 0 2 0 = 90350562948123584274548521 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2359_0_join1

private theorem receipt_1_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 1) 0 128 = 52735740363500658437312661 := by decide +kernel
private theorem receipt_1_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 1) 128 128 = 28652095102469098302510654 := by decide +kernel
private theorem receipt_1_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 1) 256 125 = 8449242729010390886576238 := by decide +kernel
private theorem receipt_1_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 1) 128 253 = 37101337831479489189086892 :=
  phaseBlock_append receipt_1_6_2359_1_part1 receipt_1_6_2359_1_part2 rfl rfl rfl
private theorem receipt_1_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2359 7 1 0 2 1) 0 381 = 89837078194980147626399553 :=
  phaseBlock_append receipt_1_6_2359_1_part0 receipt_1_6_2359_1_join0 rfl rfl rfl

private theorem receipt_1_6_2359_1 : fastPhase (bank 1 6).shape 179818 2359 7 1 0 2 1 = 89837078194980147626399553 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2359_1_join1

private theorem receipt_1_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 0) 0 128 = 52938102130268715999366561 := by decide +kernel
private theorem receipt_1_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 0) 128 128 = 28823592793533402334666191 := by decide +kernel
private theorem receipt_1_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 0) 256 125 = 8589557481727145415880449 := by decide +kernel
private theorem receipt_1_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 0) 128 253 = 37413150275260547750546640 :=
  phaseBlock_append receipt_1_6_2360_0_part1 receipt_1_6_2360_0_part2 rfl rfl rfl
private theorem receipt_1_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 0) 0 381 = 90351252405529263749913201 :=
  phaseBlock_append receipt_1_6_2360_0_part0 receipt_1_6_2360_0_join0 rfl rfl rfl

private theorem receipt_1_6_2360_0 : fastPhase (bank 1 6).shape 179818 2360 7 1 0 2 0 = 90351252405529263749913201 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2360_0_join1

private theorem receipt_1_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 1) 0 128 = 52736192181128648261990610 := by decide +kernel
private theorem receipt_1_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 1) 128 128 = 28652288126575244996795349 := by decide +kernel
private theorem receipt_1_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 1) 256 125 = 8449284311464604574130077 := by decide +kernel
private theorem receipt_1_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 1) 128 253 = 37101572438039849570925426 :=
  phaseBlock_append receipt_1_6_2360_1_part1 receipt_1_6_2360_1_part2 rfl rfl rfl
private theorem receipt_1_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179818 2360 7 1 0 2 1) 0 381 = 89837764619168497832916036 :=
  phaseBlock_append receipt_1_6_2360_1_part0 receipt_1_6_2360_1_join0 rfl rfl rfl

private theorem receipt_1_6_2360_1 : fastPhase (bank 1 6).shape 179818 2360 7 1 0 2 1 = 89837764619168497832916036 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2360_1_join1

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2359_0 receipt_1_6_2359_1 receipt_1_6_2360_0 receipt_1_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 0) 0 128 = 28629467793418586293707200 := by decide +kernel
private theorem receipt_2_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 0) 128 128 = 15355578352539634826314176 := by decide +kernel
private theorem receipt_2_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 0) 256 125 = 4513399602743975719807616 := by decide +kernel
private theorem receipt_2_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 0) 128 253 = 19868977955283610546121792 :=
  phaseBlock_append receipt_2_6_2359_0_part1 receipt_2_6_2359_0_part2 rfl rfl rfl
private theorem receipt_2_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 0) 0 381 = 48498445748702196839828992 :=
  phaseBlock_append receipt_2_6_2359_0_part0 receipt_2_6_2359_0_join0 rfl rfl rfl

private theorem receipt_2_6_2359_0 : fastPhase (bank 2 6).shape 179818 2359 7 1 0 7 0 = 48498445748702196839828992 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2359_0_join1

private theorem receipt_2_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 1) 0 128 = 28516908022037931471004608 := by decide +kernel
private theorem receipt_2_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 1) 128 128 = 15262540231022923888272320 := by decide +kernel
private theorem receipt_2_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 1) 256 125 = 4439325067312220869452188 := by decide +kernel
private theorem receipt_2_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 1) 128 253 = 19701865298335144757724508 :=
  phaseBlock_append receipt_2_6_2359_1_part1 receipt_2_6_2359_1_part2 rfl rfl rfl
private theorem receipt_2_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2359 7 1 0 7 1) 0 381 = 48218773320373076228729116 :=
  phaseBlock_append receipt_2_6_2359_1_part0 receipt_2_6_2359_1_join0 rfl rfl rfl

private theorem receipt_2_6_2359_1 : fastPhase (bank 2 6).shape 179818 2359 7 1 0 7 1 = 48218773320373076228729116 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2359_1_join1

private theorem receipt_2_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 0) 0 128 = 28629710962350403279627712 := by decide +kernel
private theorem receipt_2_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 0) 128 128 = 15355681388240244373382592 := by decide +kernel
private theorem receipt_2_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 0) 256 125 = 4513421778488134825768694 := by decide +kernel
private theorem receipt_2_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 0) 128 253 = 19869103166728379199151286 :=
  phaseBlock_append receipt_2_6_2360_0_part1 receipt_2_6_2360_0_part2 rfl rfl rfl
private theorem receipt_2_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 0) 0 381 = 48498814129078782478778998 :=
  phaseBlock_append receipt_2_6_2360_0_part0 receipt_2_6_2360_0_join0 rfl rfl rfl

private theorem receipt_2_6_2360_0 : fastPhase (bank 2 6).shape 179818 2360 7 1 0 7 0 = 48498814129078782478778998 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2360_0_join1

private theorem receipt_2_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 1) 0 128 = 28517150393462786507271424 := by decide +kernel
private theorem receipt_2_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 1) 128 128 = 15262642726149990682512640 := by decide +kernel
private theorem receipt_2_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 1) 256 125 = 4439346923002908334349267 := by decide +kernel
private theorem receipt_2_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 1) 128 253 = 19701989649152899016861907 :=
  phaseBlock_append receipt_2_6_2360_1_part1 receipt_2_6_2360_1_part2 rfl rfl rfl
private theorem receipt_2_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179818 2360 7 1 0 7 1) 0 381 = 48219140042615685524133331 :=
  phaseBlock_append receipt_2_6_2360_1_part0 receipt_2_6_2360_1_join0 rfl rfl rfl

private theorem receipt_2_6_2360_1 : fastPhase (bank 2 6).shape 179818 2360 7 1 0 7 1 = 48219140042615685524133331 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2360_1_join1

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2359_0 receipt_2_6_2359_1 receipt_2_6_2360_0 receipt_2_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 0 128 = 5788116794601520380142176 := by decide +kernel
private theorem receipt_3_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 128 128 = 3194534712977282224460384 := by decide +kernel
private theorem receipt_3_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 256 128 = 1061025838957477080384096 := by decide +kernel
private theorem receipt_3_6_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 384 12 = 7634993378600916346759 := by decide +kernel
private theorem receipt_3_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 0 256 = 8982651507578802604602560 :=
  phaseBlock_append receipt_3_6_2359_0_part0 receipt_3_6_2359_0_part1 rfl rfl rfl
private theorem receipt_3_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 256 140 = 1068660832336077996730855 :=
  phaseBlock_append receipt_3_6_2359_0_part2 receipt_3_6_2359_0_part3 rfl rfl rfl
private theorem receipt_3_6_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 0) 0 396 = 10051312339914880601333415 :=
  phaseBlock_append receipt_3_6_2359_0_join0 receipt_3_6_2359_0_join1 rfl rfl rfl

private theorem receipt_3_6_2359_0 : fastPhase (bank 3 6).shape 179818 2359 7 1 1 1 0 = 10051312339914880601333415 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2359_0_join2

private theorem receipt_3_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 0 128 = 5766428242309502563298016 := by decide +kernel
private theorem receipt_3_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 128 128 = 3176167982000869250824928 := by decide +kernel
private theorem receipt_3_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 256 128 = 1046316131669203746245344 := by decide +kernel
private theorem receipt_3_6_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 384 12 = 6455184937893467236263 := by decide +kernel
private theorem receipt_3_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 0 256 = 8942596224310371814122944 :=
  phaseBlock_append receipt_3_6_2359_1_part0 receipt_3_6_2359_1_part1 rfl rfl rfl
private theorem receipt_3_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 256 140 = 1052771316607097213481607 :=
  phaseBlock_append receipt_3_6_2359_1_part2 receipt_3_6_2359_1_part3 rfl rfl rfl
private theorem receipt_3_6_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2359 7 1 1 1 1) 0 396 = 9995367540917469027604551 :=
  phaseBlock_append receipt_3_6_2359_1_join0 receipt_3_6_2359_1_join1 rfl rfl rfl

private theorem receipt_3_6_2359_1 : fastPhase (bank 3 6).shape 179818 2359 7 1 1 1 1 = 9995367540917469027604551 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2359_1_join2

private theorem receipt_3_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 0 128 = 5788163097407730963246624 := by decide +kernel
private theorem receipt_3_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 128 128 = 3194551397721287268285984 := by decide +kernel
private theorem receipt_3_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 256 128 = 1061028774489696743755296 := by decide +kernel
private theorem receipt_3_6_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 384 12 = 7635001107401285320053 := by decide +kernel
private theorem receipt_3_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 0 256 = 8982714495129018231532608 :=
  phaseBlock_append receipt_3_6_2360_0_part0 receipt_3_6_2360_0_part1 rfl rfl rfl
private theorem receipt_3_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 256 140 = 1068663775597098029075349 :=
  phaseBlock_append receipt_3_6_2360_0_part2 receipt_3_6_2360_0_part3 rfl rfl rfl
private theorem receipt_3_6_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 0) 0 396 = 10051378270726116260607957 :=
  phaseBlock_append receipt_3_6_2360_0_join0 receipt_3_6_2360_0_join1 rfl rfl rfl

private theorem receipt_3_6_2360_0 : fastPhase (bank 3 6).shape 179818 2360 7 1 1 1 0 = 10051378270726116260607957 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2360_0_join2

private theorem receipt_3_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 0 128 = 5766474347727853174011936 := by decide +kernel
private theorem receipt_3_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 128 128 = 3176184561646410816563232 := by decide +kernel
private theorem receipt_3_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 256 128 = 1046319028298899745806368 := by decide +kernel
private theorem receipt_3_6_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 384 12 = 6455191498778725593561 := by decide +kernel
private theorem receipt_3_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 0 256 = 8942658909374263990575168 :=
  phaseBlock_append receipt_3_6_2360_1_part0 receipt_3_6_2360_1_part1 rfl rfl rfl
private theorem receipt_3_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 256 140 = 1052774219797678471399929 :=
  phaseBlock_append receipt_3_6_2360_1_part2 receipt_3_6_2360_1_part3 rfl rfl rfl
private theorem receipt_3_6_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179818 2360 7 1 1 1 1) 0 396 = 9995433129171942461975097 :=
  phaseBlock_append receipt_3_6_2360_1_join0 receipt_3_6_2360_1_join1 rfl rfl rfl

private theorem receipt_3_6_2360_1 : fastPhase (bank 3 6).shape 179818 2360 7 1 1 1 1 = 9995433129171942461975097 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2360_1_join2

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2359_0 receipt_3_6_2359_1 receipt_3_6_2360_0 receipt_3_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 0 128 = 142809870241073667244552192 := by decide +kernel
private theorem receipt_0_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 128 128 = 92173418804280466962296832 := by decide +kernel
private theorem receipt_0_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 256 128 = 47833151552411051739602178 := by decide +kernel
private theorem receipt_0_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 384 97 = 10330230589638939005135754 := by decide +kernel
private theorem receipt_0_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 0 256 = 234983289045354134206849024 :=
  phaseBlock_append receipt_0_7_2359_0_part0 receipt_0_7_2359_0_part1 rfl rfl rfl
private theorem receipt_0_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 256 225 = 58163382142049990744737932 :=
  phaseBlock_append receipt_0_7_2359_0_part2 receipt_0_7_2359_0_part3 rfl rfl rfl
private theorem receipt_0_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 0) 0 481 = 293146671187404124951586956 :=
  phaseBlock_append receipt_0_7_2359_0_join0 receipt_0_7_2359_0_join1 rfl rfl rfl

private theorem receipt_0_7_2359_0 : fastPhase (bank 0 7).shape 179818 2359 10 1 0 1 0 = 293146671187404124951586956 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2359_0_join2

private theorem receipt_0_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 0 128 = 142393905028524072796386240 := by decide +kernel
private theorem receipt_0_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 128 128 = 91806581160278912173364160 := by decide +kernel
private theorem receipt_0_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 256 128 = 47512267842666746502357074 := by decide +kernel
private theorem receipt_0_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 384 97 = 10115736448320802597960678 := by decide +kernel
private theorem receipt_0_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 0 256 = 234200486188802984969750400 :=
  phaseBlock_append receipt_0_7_2359_1_part0 receipt_0_7_2359_1_part1 rfl rfl rfl
private theorem receipt_0_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 256 225 = 57628004290987549100317752 :=
  phaseBlock_append receipt_0_7_2359_1_part2 receipt_0_7_2359_1_part3 rfl rfl rfl
private theorem receipt_0_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2359 10 1 0 1 1) 0 481 = 291828490479790534070068152 :=
  phaseBlock_append receipt_0_7_2359_1_join0 receipt_0_7_2359_1_join1 rfl rfl rfl

private theorem receipt_0_7_2359_1 : fastPhase (bank 0 7).shape 179818 2359 10 1 0 1 1 = 291828490479790534070068152 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2359_1_join2

private theorem receipt_0_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 0 128 = 142811103302212485174998112 := by decide +kernel
private theorem receipt_0_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 128 128 = 92174085391381525430731872 := by decide +kernel
private theorem receipt_0_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 256 128 = 47833425687563811580675164 := by decide +kernel
private theorem receipt_0_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 384 97 = 10330275448383151050394234 := by decide +kernel
private theorem receipt_0_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 0 256 = 234985188693594010605729984 :=
  phaseBlock_append receipt_0_7_2360_0_part0 receipt_0_7_2360_0_part1 rfl rfl rfl
private theorem receipt_0_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 256 225 = 58163701135946962631069398 :=
  phaseBlock_append receipt_0_7_2360_0_part2 receipt_0_7_2360_0_part3 rfl rfl rfl
private theorem receipt_0_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 0) 0 481 = 293148889829540973236799382 :=
  phaseBlock_append receipt_0_7_2360_0_join0 receipt_0_7_2360_0_join1 rfl rfl rfl

private theorem receipt_0_7_2360_0 : fastPhase (bank 0 7).shape 179818 2360 10 1 0 1 0 = 293148889829540973236799382 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2360_0_join2

private theorem receipt_0_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 0 128 = 142395135120196347349622880 := by decide +kernel
private theorem receipt_0_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 128 128 = 91807245479331760716435552 := by decide +kernel
private theorem receipt_0_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 256 128 = 47512540345106659147471371 := by decide +kernel
private theorem receipt_0_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 384 97 = 10115780455138850250714647 := by decide +kernel
private theorem receipt_0_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 0 256 = 234202380599528108066058432 :=
  phaseBlock_append receipt_0_7_2360_1_part0 receipt_0_7_2360_1_part1 rfl rfl rfl
private theorem receipt_0_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 256 225 = 57628320800245509398186018 :=
  phaseBlock_append receipt_0_7_2360_1_part2 receipt_0_7_2360_1_part3 rfl rfl rfl
private theorem receipt_0_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179818 2360 10 1 0 1 1) 0 481 = 291830701399773617464244450 :=
  phaseBlock_append receipt_0_7_2360_1_join0 receipt_0_7_2360_1_join1 rfl rfl rfl

private theorem receipt_0_7_2360_1 : fastPhase (bank 0 7).shape 179818 2360 10 1 0 1 1 = 291830701399773617464244450 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2360_1_join2

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2359_0 receipt_0_7_2359_1 receipt_0_7_2360_0 receipt_0_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 0 128 = 128461283632278458491329952 := by decide +kernel
private theorem receipt_1_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 128 128 = 82748632099019896430366112 := by decide +kernel
private theorem receipt_1_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 256 128 = 42858631393028760777528324 := by decide +kernel
private theorem receipt_1_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 384 97 = 9240599790811691004599265 := by decide +kernel
private theorem receipt_1_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 0 256 = 211209915731298354921696064 :=
  phaseBlock_append receipt_1_7_2359_0_part0 receipt_1_7_2359_0_part1 rfl rfl rfl
private theorem receipt_1_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 256 225 = 52099231183840451782127589 :=
  phaseBlock_append receipt_1_7_2359_0_part2 receipt_1_7_2359_0_part3 rfl rfl rfl
private theorem receipt_1_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 0) 0 481 = 263309146915138806703823653 :=
  phaseBlock_append receipt_1_7_2359_0_join0 receipt_1_7_2359_0_join1 rfl rfl rfl

private theorem receipt_1_7_2359_0 : fastPhase (bank 1 7).shape 179818 2359 10 1 0 2 0 = 263309146915138806703823653 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2359_0_join2

private theorem receipt_1_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 0 128 = 128085128652927786976634080 := by decide +kernel
private theorem receipt_1_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 128 128 = 82418035054340932081792224 := by decide +kernel
private theorem receipt_1_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 256 128 = 42570485570570767434587358 := by decide +kernel
private theorem receipt_1_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 384 97 = 9048634651031665206853092 := by decide +kernel
private theorem receipt_1_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 0 256 = 210503163707268719058426304 :=
  phaseBlock_append receipt_1_7_2359_1_part0 receipt_1_7_2359_1_part1 rfl rfl rfl
private theorem receipt_1_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 256 225 = 51619120221602432641440450 :=
  phaseBlock_append receipt_1_7_2359_1_part2 receipt_1_7_2359_1_part3 rfl rfl rfl
private theorem receipt_1_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2359 10 1 0 2 1) 0 481 = 262122283928871151699866754 :=
  phaseBlock_append receipt_1_7_2359_1_join0 receipt_1_7_2359_1_join1 rfl rfl rfl

private theorem receipt_1_7_2359_1 : fastPhase (bank 1 7).shape 179818 2359 10 1 0 2 1 = 262122283928871151699866754 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2359_1_join2

private theorem receipt_1_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 0 128 = 128462392832479601054096832 := by decide +kernel
private theorem receipt_1_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 128 128 = 82749230547247565324893632 := by decide +kernel
private theorem receipt_1_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 256 128 = 42858877029893786241274803 := by decide +kernel
private theorem receipt_1_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 384 97 = 9240639918909951733729011 := by decide +kernel
private theorem receipt_1_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 0 256 = 211211623379727166378990464 :=
  phaseBlock_append receipt_1_7_2360_0_part0 receipt_1_7_2360_0_part1 rfl rfl rfl
private theorem receipt_1_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 256 225 = 52099516948803737975003814 :=
  phaseBlock_append receipt_1_7_2360_0_part2 receipt_1_7_2360_0_part3 rfl rfl rfl
private theorem receipt_1_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 0) 0 481 = 263311140328530904353994278 :=
  phaseBlock_append receipt_1_7_2360_0_join0 receipt_1_7_2360_0_join1 rfl rfl rfl

private theorem receipt_1_7_2360_0 : fastPhase (bank 1 7).shape 179818 2360 10 1 0 2 0 = 263311140328530904353994278 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2360_0_join2

private theorem receipt_1_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 0 128 = 128086235164802937714239040 := by decide +kernel
private theorem receipt_1_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 128 128 = 82418631457170668296652352 := by decide +kernel
private theorem receipt_1_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 256 128 = 42570729740809664015894544 := by decide +kernel
private theorem receipt_1_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 384 97 = 9048674016605467972245918 := by decide +kernel
private theorem receipt_1_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 0 256 = 210504866621973606010891392 :=
  phaseBlock_append receipt_1_7_2360_1_part0 receipt_1_7_2360_1_part1 rfl rfl rfl
private theorem receipt_1_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 256 225 = 51619403757415131988140462 :=
  phaseBlock_append receipt_1_7_2360_1_part2 receipt_1_7_2360_1_part3 rfl rfl rfl
private theorem receipt_1_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179818 2360 10 1 0 2 1) 0 481 = 262124270379388737999031854 :=
  phaseBlock_append receipt_1_7_2360_1_join0 receipt_1_7_2360_1_join1 rfl rfl rfl

private theorem receipt_1_7_2360_1 : fastPhase (bank 1 7).shape 179818 2360 10 1 0 2 1 = 262124270379388737999031854 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2360_1_join2

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2359_0 receipt_1_7_2359_1 receipt_1_7_2360_0 receipt_1_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 0 128 = 68539217503527077618691360 := by decide +kernel
private theorem receipt_2_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 128 128 = 43521965885755780545305888 := by decide +kernel
private theorem receipt_2_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 256 128 = 22223452260932670215682314 := by decide +kernel
private theorem receipt_2_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 384 97 = 4733505386807110452577078 := by decide +kernel
private theorem receipt_2_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 0 256 = 112061183389282858163997248 :=
  phaseBlock_append receipt_2_7_2359_0_part0 receipt_2_7_2359_0_part1 rfl rfl rfl
private theorem receipt_2_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 256 225 = 26956957647739780668259392 :=
  phaseBlock_append receipt_2_7_2359_0_part2 receipt_2_7_2359_0_part3 rfl rfl rfl
private theorem receipt_2_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 0) 0 481 = 139018141037022638832256640 :=
  phaseBlock_append receipt_2_7_2359_0_join0 receipt_2_7_2359_0_join1 rfl rfl rfl

private theorem receipt_2_7_2359_0 : fastPhase (bank 2 7).shape 179818 2359 10 1 0 7 0 = 139018141037022638832256640 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2359_0_join2

private theorem receipt_2_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 0 128 = 68330893607180597065150816 := by decide +kernel
private theorem receipt_2_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 128 128 = 43343235575041423126864224 := by decide +kernel
private theorem receipt_2_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 256 128 = 22071633893156426184518085 := by decide +kernel
private theorem receipt_2_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 384 97 = 4634808713296574291527188 := by decide +kernel
private theorem receipt_2_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 0 256 = 111674129182222020192015040 :=
  phaseBlock_append receipt_2_7_2359_1_part0 receipt_2_7_2359_1_part1 rfl rfl rfl
private theorem receipt_2_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 256 225 = 26706442606453000476045273 :=
  phaseBlock_append receipt_2_7_2359_1_part2 receipt_2_7_2359_1_part3 rfl rfl rfl
private theorem receipt_2_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2359 10 1 0 7 1) 0 481 = 138380571788675020668060313 :=
  phaseBlock_append receipt_2_7_2359_1_join0 receipt_2_7_2359_1_join1 rfl rfl rfl

private theorem receipt_2_7_2359_1 : fastPhase (bank 2 7).shape 179818 2359 10 1 0 7 1 = 138380571788675020668060313 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2359_1_join2

private theorem receipt_2_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 0 128 = 68539809417051430252196160 := by decide +kernel
private theorem receipt_2_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 128 128 = 43522280718598668194459968 := by decide +kernel
private theorem receipt_2_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 256 128 = 22223579672752552229698135 := by decide +kernel
private theorem receipt_2_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 384 97 = 4733525946413663112312854 := by decide +kernel
private theorem receipt_2_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 0 256 = 112062090135650098446656128 :=
  phaseBlock_append receipt_2_7_2360_0_part0 receipt_2_7_2360_0_part1 rfl rfl rfl
private theorem receipt_2_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 256 225 = 26957105619166215342010989 :=
  phaseBlock_append receipt_2_7_2360_0_part2 receipt_2_7_2360_0_part3 rfl rfl rfl
private theorem receipt_2_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 0) 0 481 = 139019195754816313788667117 :=
  phaseBlock_append receipt_2_7_2360_0_join0 receipt_2_7_2360_0_join1 rfl rfl rfl

private theorem receipt_2_7_2360_0 : fastPhase (bank 2 7).shape 179818 2360 10 1 0 7 0 = 139019195754816313788667117 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2360_0_join2

private theorem receipt_2_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 0 128 = 68331484020147577127819648 := by decide +kernel
private theorem receipt_2_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 128 128 = 43343549296689935146039680 := by decide +kernel
private theorem receipt_2_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 256 128 = 22071760530381336754255775 := by decide +kernel
private theorem receipt_2_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 384 97 = 4634828880561994387095891 := by decide +kernel
private theorem receipt_2_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 0 256 = 111675033316837512273859328 :=
  phaseBlock_append receipt_2_7_2360_1_part0 receipt_2_7_2360_1_part1 rfl rfl rfl
private theorem receipt_2_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 256 225 = 26706589410943331141351666 :=
  phaseBlock_append receipt_2_7_2360_1_part2 receipt_2_7_2360_1_part3 rfl rfl rfl
private theorem receipt_2_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179818 2360 10 1 0 7 1) 0 481 = 138381622727780843415210994 :=
  phaseBlock_append receipt_2_7_2360_1_join0 receipt_2_7_2360_1_join1 rfl rfl rfl

private theorem receipt_2_7_2360_1 : fastPhase (bank 2 7).shape 179818 2360 10 1 0 7 1 = 138381622727780843415210994 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2360_1_join2

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2359_0 receipt_2_7_2359_1 receipt_2_7_2360_0 receipt_2_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 0 128 = 17322618370408446801647392 := by decide +kernel
private theorem receipt_3_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 128 128 = 11244206499958642587551520 := by decide +kernel
private theorem receipt_3_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 256 128 = 5971267114922924700071712 := by decide +kernel
private theorem receipt_3_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 384 115 = 1576088710010788064672451 := by decide +kernel
private theorem receipt_3_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 0 256 = 28566824870367089389198912 :=
  phaseBlock_append receipt_3_7_2359_0_part0 receipt_3_7_2359_0_part1 rfl rfl rfl
private theorem receipt_3_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 256 243 = 7547355824933712764744163 :=
  phaseBlock_append receipt_3_7_2359_0_part2 receipt_3_7_2359_0_part3 rfl rfl rfl
private theorem receipt_3_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 0) 0 499 = 36114180695300802153943075 :=
  phaseBlock_append receipt_3_7_2359_0_join0 receipt_3_7_2359_0_join1 rfl rfl rfl

private theorem receipt_3_7_2359_0 : fastPhase (bank 3 7).shape 179818 2359 10 1 1 1 0 = 36114180695300802153943075 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2359_0_join2

private theorem receipt_3_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 0 128 = 17272759068906282993359136 := by decide +kernel
private theorem receipt_3_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 128 128 = 11200200051333472347777312 := by decide +kernel
private theorem receipt_3_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 256 128 = 5933588191357737920117024 := by decide +kernel
private theorem receipt_3_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 384 115 = 1548014822390577977818378 := by decide +kernel
private theorem receipt_3_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 0 256 = 28472959120239755341136448 :=
  phaseBlock_append receipt_3_7_2359_1_part0 receipt_3_7_2359_1_part1 rfl rfl rfl
private theorem receipt_3_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 256 243 = 7481603013748315897935402 :=
  phaseBlock_append receipt_3_7_2359_1_part2 receipt_3_7_2359_1_part3 rfl rfl rfl
private theorem receipt_3_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2359 10 1 1 1 1) 0 499 = 35954562133988071239071850 :=
  phaseBlock_append receipt_3_7_2359_1_join0 receipt_3_7_2359_1_join1 rfl rfl rfl

private theorem receipt_3_7_2359_1 : fastPhase (bank 3 7).shape 179818 2359 10 1 1 1 1 = 35954562133988071239071850 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2359_1_join2

private theorem receipt_3_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 0 128 = 17322761099788718566802688 := by decide +kernel
private theorem receipt_3_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 128 128 = 11244273890066665997149440 := by decide +kernel
private theorem receipt_3_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 256 128 = 5971290264312235024336128 := by decide +kernel
private theorem receipt_3_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 384 115 = 1576091982259343206117044 := by decide +kernel
private theorem receipt_3_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 0 256 = 28567034989855384563952128 :=
  phaseBlock_append receipt_3_7_2360_0_part0 receipt_3_7_2360_0_part1 rfl rfl rfl
private theorem receipt_3_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 256 243 = 7547382246571578230453172 :=
  phaseBlock_append receipt_3_7_2360_0_part2 receipt_3_7_2360_0_part3 rfl rfl rfl
private theorem receipt_3_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 0) 0 499 = 36114417236426962794405300 :=
  phaseBlock_append receipt_3_7_2360_0_join0 receipt_3_7_2360_0_join1 rfl rfl rfl

private theorem receipt_3_7_2360_0 : fastPhase (bank 3 7).shape 179818 2360 10 1 1 1 0 = 36114417236426962794405300 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2360_0_join2

private theorem receipt_3_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 0 128 = 17272901328028966613256768 := by decide +kernel
private theorem receipt_3_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 128 128 = 11200267146557133811771968 := by decide +kernel
private theorem receipt_3_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 256 128 = 5933611183736160443910720 := by decide +kernel
private theorem receipt_3_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 384 115 = 1548018040917338598725349 := by decide +kernel
private theorem receipt_3_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 0 256 = 28473168474586100425028736 :=
  phaseBlock_append receipt_3_7_2360_1_part0 receipt_3_7_2360_1_part1 rfl rfl rfl
private theorem receipt_3_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 256 243 = 7481629224653499042636069 :=
  phaseBlock_append receipt_3_7_2360_1_part2 receipt_3_7_2360_1_part3 rfl rfl rfl
private theorem receipt_3_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179818 2360 10 1 1 1 1) 0 499 = 35954797699239599467664805 :=
  phaseBlock_append receipt_3_7_2360_1_join0 receipt_3_7_2360_1_join1 rfl rfl rfl

private theorem receipt_3_7_2360_1 : fastPhase (bank 3 7).shape 179818 2360 10 1 1 1 1 = 35954797699239599467664805 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2360_1_join2

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_498)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_7_2359_0 receipt_3_7_2359_1 receipt_3_7_2360_0 receipt_3_7_2360_1 (by decide +kernel) (by decide +kernel)

def group2_stage (i : Fin 3) : Fin 17 :=
  ⟨5+i.val, by have := i.isLt; omega⟩

theorem group2_checked (rect : Fin 4) (i : Fin 3) :
    Checked (bank rect (group2_stage i)) (reserve (group2_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_5
    · exact receipt_1_5
    · exact receipt_2_5
    · exact receipt_3_5
  · fin_cases rect
    · exact receipt_0_6
    · exact receipt_1_6
    · exact receipt_2_6
    · exact receipt_3_6
  · fin_cases rect
    · exact receipt_0_7
    · exact receipt_1_7
    · exact receipt_2_7
    · exact receipt_3_7

theorem group2_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group2_stage i)).shape
      (cutoff h rect (group2_stage i)), ¬ G∣Q :=
  (group2_checked rect i).avoids Crt word lo hi irr seeded slope hs hj


end Lower6960.RescueSource
