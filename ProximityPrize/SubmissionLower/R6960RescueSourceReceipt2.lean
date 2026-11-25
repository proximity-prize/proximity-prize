import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0

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

private theorem receipt_0_5_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 0) 0 128 = 32093469297609091146524672 := by decide +kernel
private theorem receipt_0_5_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 0) 128 128 = 16444607431572128552980545 := by decide +kernel
private theorem receipt_0_5_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 0) 256 101 = 3674564382796403737550941 := by decide +kernel
private theorem receipt_0_5_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 0) 128 229 = 20119171814368532290531486 :=
  phaseBlock_append receipt_0_5_2383_0_part1 receipt_0_5_2383_0_part2 rfl rfl rfl
private theorem receipt_0_5_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 0) 0 357 = 52212641111977623437056158 :=
  phaseBlock_append receipt_0_5_2383_0_part0 receipt_0_5_2383_0_join0 rfl rfl rfl

private theorem receipt_0_5_2383_0 : fastPhase (bank 0 5).shape 179808 2383 5 1 0 1 0 = 52212641111977623437056158 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2383_0_join1

private theorem receipt_0_5_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 1) 0 128 = 31961900499538710157787008 := by decide +kernel
private theorem receipt_0_5_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 1) 128 128 = 16333928744265128222502315 := by decide +kernel
private theorem receipt_0_5_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 1) 256 101 = 3600761529533860912516362 := by decide +kernel
private theorem receipt_0_5_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 1) 128 229 = 19934690273798989135018677 :=
  phaseBlock_append receipt_0_5_2383_1_part1 receipt_0_5_2383_1_part2 rfl rfl rfl
private theorem receipt_0_5_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2383 5 1 0 1 1) 0 357 = 51896590773337699292805685 :=
  phaseBlock_append receipt_0_5_2383_1_part0 receipt_0_5_2383_1_join0 rfl rfl rfl

private theorem receipt_0_5_2383_1 : fastPhase (bank 0 5).shape 179808 2383 5 1 0 1 1 = 51896590773337699292805685 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2383_1_join1

private theorem receipt_0_5_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 0) 0 128 = 32093741567869752001534016 := by decide +kernel
private theorem receipt_0_5_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 0) 128 128 = 16444715619081741790078695 := by decide +kernel
private theorem receipt_0_5_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 0) 256 101 = 3674581844541354108237540 := by decide +kernel
private theorem receipt_0_5_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 0) 128 229 = 20119297463623095898316235 :=
  phaseBlock_append receipt_0_5_2384_0_part1 receipt_0_5_2384_0_part2 rfl rfl rfl
private theorem receipt_0_5_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 0) 0 357 = 52213039031492847899850251 :=
  phaseBlock_append receipt_0_5_2384_0_part0 receipt_0_5_2384_0_join0 rfl rfl rfl

private theorem receipt_0_5_2384_0 : fastPhase (bank 0 5).shape 179808 2384 5 1 0 1 0 = 52213039031492847899850251 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2384_0_join1

private theorem receipt_0_5_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 1) 0 128 = 31962171844426625848868544 := by decide +kernel
private theorem receipt_0_5_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 1) 128 128 = 16334036301975804749325135 := by decide +kernel
private theorem receipt_0_5_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 1) 256 101 = 3600778678705059410518482 := by decide +kernel
private theorem receipt_0_5_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 1) 128 229 = 19934814980680864159843617 :=
  phaseBlock_append receipt_0_5_2384_1_part1 receipt_0_5_2384_1_part2 rfl rfl rfl
private theorem receipt_0_5_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2384 5 1 0 1 1) 0 357 = 51896986825107490008712161 :=
  phaseBlock_append receipt_0_5_2384_1_part0 receipt_0_5_2384_1_join0 rfl rfl rfl

private theorem receipt_0_5_2384_1 : fastPhase (bank 0 5).shape 179808 2384 5 1 0 1 1 = 51896986825107490008712161 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2384_1_join1

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2383_0 receipt_0_5_2383_1 receipt_0_5_2384_0 receipt_0_5_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 0) 0 128 = 28863681245323079224125632 := by decide +kernel
private theorem receipt_1_5_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 0) 128 128 = 14752141740141644824046895 := by decide +kernel
private theorem receipt_1_5_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 0) 256 101 = 3289185989239379345181919 := by decide +kernel
private theorem receipt_1_5_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 0) 128 229 = 18041327729381024169228814 :=
  phaseBlock_append receipt_1_5_2383_0_part1 receipt_1_5_2383_0_part2 rfl rfl rfl
private theorem receipt_1_5_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 0) 0 357 = 46905008974704103393354446 :=
  phaseBlock_append receipt_1_5_2383_0_part0 receipt_1_5_2383_0_join0 rfl rfl rfl

private theorem receipt_1_5_2383_0 : fastPhase (bank 1 5).shape 179808 2383 5 1 0 2 0 = 46905008974704103393354446 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2383_0_join1

private theorem receipt_1_5_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 1) 0 128 = 28744776460407434266021888 := by decide +kernel
private theorem receipt_1_5_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 1) 128 128 = 14652569112966096659773551 := by decide +kernel
private theorem receipt_1_5_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 1) 256 101 = 3223078691723929274520762 := by decide +kernel
private theorem receipt_1_5_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 1) 128 229 = 17875647804690025934294313 :=
  phaseBlock_append receipt_1_5_2383_1_part1 receipt_1_5_2383_1_part2 rfl rfl rfl
private theorem receipt_1_5_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2383 5 1 0 2 1) 0 357 = 46620424265097460200316201 :=
  phaseBlock_append receipt_1_5_2383_1_part0 receipt_1_5_2383_1_join0 rfl rfl rfl

private theorem receipt_1_5_2383_1 : fastPhase (bank 1 5).shape 179808 2383 5 1 0 2 1 = 46620424265097460200316201 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2383_1_join1

private theorem receipt_1_5_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 0) 0 128 = 28863926126569106848825088 := by decide +kernel
private theorem receipt_1_5_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 0) 128 128 = 14752238799410533958602125 := by decide +kernel
private theorem receipt_1_5_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 0) 256 101 = 3289201620338242200569556 := by decide +kernel
private theorem receipt_1_5_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 0) 128 229 = 18041440419748776159171681 :=
  phaseBlock_append receipt_1_5_2384_0_part1 receipt_1_5_2384_0_part2 rfl rfl rfl
private theorem receipt_1_5_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 0) 0 357 = 46905366546317883007996769 :=
  phaseBlock_append receipt_1_5_2384_0_part0 receipt_1_5_2384_0_join0 rfl rfl rfl

private theorem receipt_1_5_2384_0 : fastPhase (bank 1 5).shape 179808 2384 5 1 0 2 0 = 46905366546317883007996769 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2384_0_join1

private theorem receipt_1_5_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 1) 0 128 = 28745020504466432338080384 := by decide +kernel
private theorem receipt_1_5_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 1) 128 128 = 14652665605333242781063203 := by decide +kernel
private theorem receipt_1_5_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 1) 256 101 = 3223094042790847997287131 := by decide +kernel
private theorem receipt_1_5_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 1) 128 229 = 17875759648124090778350334 :=
  phaseBlock_append receipt_1_5_2384_1_part1 receipt_1_5_2384_1_part2 rfl rfl rfl
private theorem receipt_1_5_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2384 5 1 0 2 1) 0 357 = 46620780152590523116430718 :=
  phaseBlock_append receipt_1_5_2384_1_part0 receipt_1_5_2384_1_join0 rfl rfl rfl

private theorem receipt_1_5_2384_1 : fastPhase (bank 1 5).shape 179808 2384 5 1 0 2 1 = 46620780152590523116430718 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2384_1_join1

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2383_0 receipt_1_5_2383_1 receipt_1_5_2384_0 receipt_1_5_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 0) 0 128 = 15375768292255684068793536 := by decide +kernel
private theorem receipt_2_5_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 0) 128 128 = 7714953126664663559387824 := by decide +kernel
private theorem receipt_2_5_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 0) 256 101 = 1692821084485565598928275 := by decide +kernel
private theorem receipt_2_5_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 0) 128 229 = 9407774211150229158316099 :=
  phaseBlock_append receipt_2_5_2383_0_part1 receipt_2_5_2383_0_part2 rfl rfl rfl
private theorem receipt_2_5_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 0) 0 357 = 24783542503405913227109635 :=
  phaseBlock_append receipt_2_5_2383_0_part0 receipt_2_5_2383_0_join0 rfl rfl rfl

private theorem receipt_2_5_2383_0 : fastPhase (bank 2 5).shape 179808 2383 5 1 0 7 0 = 24783542503405913227109635 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2383_0_join1

private theorem receipt_2_5_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 1) 0 128 = 15310210146621769688443264 := by decide +kernel
private theorem receipt_2_5_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 1) 128 128 = 7661792681766572870119074 := by decide +kernel
private theorem receipt_2_5_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 1) 256 101 = 1658628722698650744823169 := by decide +kernel
private theorem receipt_2_5_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 1) 128 229 = 9320421404465223614942243 :=
  phaseBlock_append receipt_2_5_2383_1_part1 receipt_2_5_2383_1_part2 rfl rfl rfl
private theorem receipt_2_5_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2383 5 1 0 7 1) 0 357 = 24630631551086993303385507 :=
  phaseBlock_append receipt_2_5_2383_1_part0 receipt_2_5_2383_1_join0 rfl rfl rfl

private theorem receipt_2_5_2383_1 : fastPhase (bank 2 5).shape 179808 2383 5 1 0 7 1 = 24630631551086993303385507 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2383_1_join1

private theorem receipt_2_5_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 0) 0 128 = 15375898785143193258036768 := by decide +kernel
private theorem receipt_2_5_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 0) 128 128 = 7715003910054288891005574 := by decide +kernel
private theorem receipt_2_5_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 0) 256 101 = 1692829131857588868527475 := by decide +kernel
private theorem receipt_2_5_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 0) 128 229 = 9407833041911877759533049 :=
  phaseBlock_append receipt_2_5_2384_0_part1 receipt_2_5_2384_0_part2 rfl rfl rfl
private theorem receipt_2_5_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 0) 0 357 = 24783731827055071017569817 :=
  phaseBlock_append receipt_2_5_2384_0_part0 receipt_2_5_2384_0_join0 rfl rfl rfl

private theorem receipt_2_5_2384_0 : fastPhase (bank 2 5).shape 179808 2384 5 1 0 7 0 = 24783731827055071017569817 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2384_0_join1

private theorem receipt_2_5_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 1) 0 128 = 15310340174536282121818272 := by decide +kernel
private theorem receipt_2_5_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 1) 128 128 = 7661843161352132357354490 := by decide +kernel
private theorem receipt_2_5_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 1) 256 101 = 1658636625038579516949262 := by decide +kernel
private theorem receipt_2_5_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 1) 128 229 = 9320479786390711874303752 :=
  phaseBlock_append receipt_2_5_2384_1_part1 receipt_2_5_2384_1_part2 rfl rfl rfl
private theorem receipt_2_5_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2384 5 1 0 7 1) 0 357 = 24630819960926993996122024 :=
  phaseBlock_append receipt_2_5_2384_1_part0 receipt_2_5_2384_1_join0 rfl rfl rfl

private theorem receipt_2_5_2384_1 : fastPhase (bank 2 5).shape 179808 2384 5 1 0 7 1 = 24630819960926993996122024 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2384_1_join1

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2383_0 receipt_2_5_2383_1 receipt_2_5_2384_0 receipt_2_5_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 0) 0 128 = 3772302978443266927405792 := by decide +kernel
private theorem receipt_3_5_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 0) 128 128 = 1960044965201359670737632 := by decide +kernel
private theorem receipt_3_5_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 0) 256 115 = 503779434982676760366381 := by decide +kernel
private theorem receipt_3_5_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 0) 128 243 = 2463824400184036431104013 :=
  phaseBlock_append receipt_3_5_2383_0_part1 receipt_3_5_2383_0_part2 rfl rfl rfl
private theorem receipt_3_5_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 0) 0 371 = 6236127378627303358509805 :=
  phaseBlock_append receipt_3_5_2383_0_part0 receipt_3_5_2383_0_join0 rfl rfl rfl

private theorem receipt_3_5_2383_0 : fastPhase (bank 3 5).shape 179808 2383 5 1 1 1 0 = 6236127378627303358509805 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2383_0_join1

private theorem receipt_3_5_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 1) 0 128 = 3757045360443845208515616 := by decide +kernel
private theorem receipt_3_5_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 1) 128 128 = 1947316227957234983867424 := by decide +kernel
private theorem receipt_3_5_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 1) 256 115 = 494719559892219206849745 := by decide +kernel
private theorem receipt_3_5_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 1) 128 243 = 2442035787849454190717169 :=
  phaseBlock_append receipt_3_5_2383_1_part1 receipt_3_5_2383_1_part2 rfl rfl rfl
private theorem receipt_3_5_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2383 5 1 1 1 1) 0 371 = 6199081148293299399232785 :=
  phaseBlock_append receipt_3_5_2383_1_part0 receipt_3_5_2383_1_join0 rfl rfl rfl

private theorem receipt_3_5_2383_1 : fastPhase (bank 3 5).shape 179808 2383 5 1 1 1 1 = 6199081148293299399232785 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2383_1_join1

private theorem receipt_3_5_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 0) 0 128 = 3772333006198685019284448 := by decide +kernel
private theorem receipt_3_5_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 0) 128 128 = 1960054801915187461600224 := by decide +kernel
private theorem receipt_3_5_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 0) 256 115 = 503780719218330464946477 := by decide +kernel
private theorem receipt_3_5_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 0) 128 243 = 2463835521133517926546701 :=
  phaseBlock_append receipt_3_5_2384_0_part1 receipt_3_5_2384_0_part2 rfl rfl rfl
private theorem receipt_3_5_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 0) 0 371 = 6236168527332202945831149 :=
  phaseBlock_append receipt_3_5_2384_0_part0 receipt_3_5_2384_0_join0 rfl rfl rfl

private theorem receipt_3_5_2384_0 : fastPhase (bank 3 5).shape 179808 2384 5 1 1 1 0 = 6236168527332202945831149 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2384_0_join1

private theorem receipt_3_5_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 1) 0 128 = 3757075250387911754594400 := by decide +kernel
private theorem receipt_3_5_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 1) 128 128 = 1947325995338391429998688 := by decide +kernel
private theorem receipt_3_5_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 1) 256 115 = 494720822920385168660574 := by decide +kernel
private theorem receipt_3_5_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 1) 128 243 = 2442046818258776598659262 :=
  phaseBlock_append receipt_3_5_2384_1_part1 receipt_3_5_2384_1_part2 rfl rfl rfl
private theorem receipt_3_5_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2384 5 1 1 1 1) 0 371 = 6199122068646688353253662 :=
  phaseBlock_append receipt_3_5_2384_1_part0 receipt_3_5_2384_1_join0 rfl rfl rfl

private theorem receipt_3_5_2384_1 : fastPhase (bank 3 5).shape 179808 2384 5 1 1 1 1 = 6199122068646688353253662 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2384_1_join1

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2383_0 receipt_3_5_2383_1 receipt_3_5_2384_0 receipt_3_5_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 0) 0 128 = 58782927430194873986991310 := by decide +kernel
private theorem receipt_0_6_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 0) 128 128 = 32071533635612189011997862 := by decide +kernel
private theorem receipt_0_6_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 0) 256 125 = 9575208292938792494607162 := by decide +kernel
private theorem receipt_0_6_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 0) 128 253 = 41646741928550981506605024 :=
  phaseBlock_append receipt_0_6_2383_0_part1 receipt_0_6_2383_0_part2 rfl rfl rfl
private theorem receipt_0_6_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 0) 0 381 = 100429669358745855493596334 :=
  phaseBlock_append receipt_0_6_2383_0_part0 receipt_0_6_2383_0_join0 rfl rfl rfl

private theorem receipt_0_6_2383_0 : fastPhase (bank 0 6).shape 179808 2383 7 1 0 1 0 = 100429669358745855493596334 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2383_0_join1

private theorem receipt_0_6_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 1) 0 128 = 58559695613491125293769684 := by decide +kernel
private theorem receipt_0_6_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 1) 128 128 = 31881442698443855371698612 := by decide +kernel
private theorem receipt_0_6_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 1) 256 125 = 9418947839881221870430782 := by decide +kernel
private theorem receipt_0_6_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 1) 128 253 = 41300390538325077242129394 :=
  phaseBlock_append receipt_0_6_2383_1_part1 receipt_0_6_2383_1_part2 rfl rfl rfl
private theorem receipt_0_6_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2383 7 1 0 1 1) 0 381 = 99860086151816202535899078 :=
  phaseBlock_append receipt_0_6_2383_1_part0 receipt_0_6_2383_1_join0 rfl rfl rfl

private theorem receipt_0_6_2383_1 : fastPhase (bank 0 6).shape 179808 2383 7 1 0 1 1 = 99860086151816202535899078 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2383_1_join1

private theorem receipt_0_6_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 0) 0 128 = 58783430739304304058311640 := by decide +kernel
private theorem receipt_0_6_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 0) 128 128 = 32071749555726117031719759 := by decide +kernel
private theorem receipt_0_6_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 0) 256 125 = 9575255329635777495494364 := by decide +kernel
private theorem receipt_0_6_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 0) 128 253 = 41647004885361894527214123 :=
  phaseBlock_append receipt_0_6_2384_0_part1 receipt_0_6_2384_0_part2 rfl rfl rfl
private theorem receipt_0_6_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 0) 0 381 = 100430435624666198585525763 :=
  phaseBlock_append receipt_0_6_2384_0_part0 receipt_0_6_2384_0_join0 rfl rfl rfl

private theorem receipt_0_6_2384_0 : fastPhase (bank 0 6).shape 179808 2384 7 1 0 1 0 = 100430435624666198585525763 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2384_0_join1

private theorem receipt_0_6_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 1) 0 128 = 58560197339662246286100781 := by decide +kernel
private theorem receipt_0_6_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 1) 128 128 = 31881657514608234589041243 := by decide +kernel
private theorem receipt_0_6_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 1) 256 125 = 9418994202418024336152363 := by decide +kernel
private theorem receipt_0_6_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 1) 128 253 = 41300651717026258925193606 :=
  phaseBlock_append receipt_0_6_2384_1_part1 receipt_0_6_2384_1_part2 rfl rfl rfl
private theorem receipt_0_6_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2384 7 1 0 1 1) 0 381 = 99860849056688505211294387 :=
  phaseBlock_append receipt_0_6_2384_1_part0 receipt_0_6_2384_1_join0 rfl rfl rfl

private theorem receipt_0_6_2384_1 : fastPhase (bank 0 6).shape 179808 2384 7 1 0 1 1 = 99860849056688505211294387 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2384_1_join1

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2383_0 receipt_0_6_2383_1 receipt_0_6_2384_0 receipt_0_6_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 0) 0 128 = 52941847658326312913953600 := by decide +kernel
private theorem receipt_1_6_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 0) 128 128 = 28824251195119411572672642 := by decide +kernel
private theorem receipt_1_6_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 0) 256 125 = 8589345906304201118404737 := by decide +kernel
private theorem receipt_1_6_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 0) 128 253 = 37413597101423612691077379 :=
  phaseBlock_append receipt_1_6_2383_0_part1 receipt_1_6_2383_0_part2 rfl rfl rfl
private theorem receipt_1_6_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 0) 0 381 = 90355444759749925605030979 :=
  phaseBlock_append receipt_1_6_2383_0_part0 receipt_1_6_2383_0_join0 rfl rfl rfl

private theorem receipt_1_6_2383_0 : fastPhase (bank 1 6).shape 179808 2383 7 1 0 2 0 = 90355444759749925605030979 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2383_0_join1

private theorem receipt_1_6_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 1) 0 128 = 52739928051492033147197688 := by decide +kernel
private theorem receipt_1_6_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 1) 128 128 = 28652945016764038420917372 := by decide +kernel
private theorem receipt_1_6_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 1) 256 125 = 8449077856443313958701572 := by decide +kernel
private theorem receipt_1_6_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 1) 128 253 = 37102022873207352379618944 :=
  phaseBlock_append receipt_1_6_2383_1_part1 receipt_1_6_2383_1_part2 rfl rfl rfl
private theorem receipt_1_6_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2383 7 1 0 2 1) 0 381 = 89841950924699385526816632 :=
  phaseBlock_append receipt_1_6_2383_1_part0 receipt_1_6_2383_1_join0 rfl rfl rfl

private theorem receipt_1_6_2383_1 : fastPhase (bank 1 6).shape 179808 2383 7 1 0 2 1 = 89841950924699385526816632 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2383_1_join1

private theorem receipt_1_6_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 0) 0 128 = 52942300971634709529605745 := by decide +kernel
private theorem receipt_1_6_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 0) 128 128 = 28824445262788319874898875 := by decide +kernel
private theorem receipt_1_6_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 0) 256 125 = 8589388102221108031709109 := by decide +kernel
private theorem receipt_1_6_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 0) 128 253 = 37413833365009427906607984 :=
  phaseBlock_append receipt_1_6_2384_0_part1 receipt_1_6_2384_0_part2 rfl rfl rfl
private theorem receipt_1_6_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 0) 0 381 = 90356134336644137436213729 :=
  phaseBlock_append receipt_1_6_2384_0_part0 receipt_1_6_2384_0_join0 rfl rfl rfl

private theorem receipt_1_6_2384_0 : fastPhase (bank 1 6).shape 179808 2384 7 1 0 2 0 = 90356134336644137436213729 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2384_0_join1

private theorem receipt_1_6_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 1) 0 128 = 52740379931642798369242978 := by decide +kernel
private theorem receipt_1_6_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 1) 128 128 = 28653138089086069363948995 := by decide +kernel
private theorem receipt_1_6_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 1) 256 125 = 8449119447070925191915935 := by decide +kernel
private theorem receipt_1_6_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 1) 128 253 = 37102257536156994555864930 :=
  phaseBlock_append receipt_1_6_2384_1_part1 receipt_1_6_2384_1_part2 rfl rfl rfl
private theorem receipt_1_6_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2384 7 1 0 2 1) 0 381 = 89842637467799792925107908 :=
  phaseBlock_append receipt_1_6_2384_1_part0 receipt_1_6_2384_1_join0 rfl rfl rfl

private theorem receipt_1_6_2384_1 : fastPhase (bank 1 6).shape 179808 2384 7 1 0 2 1 = 89842637467799792925107908 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2384_1_join1

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2383_0 receipt_1_6_2383_1 receipt_1_6_2384_0 receipt_1_6_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 0) 0 128 = 28631707056790211179871168 := by decide +kernel
private theorem receipt_2_6_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 0) 128 128 = 15356027769485435266161600 := by decide +kernel
private theorem receipt_2_6_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 0) 256 125 = 4513310815236887793955147 := by decide +kernel
private theorem receipt_2_6_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 0) 128 253 = 19869338584722323060116747 :=
  phaseBlock_append receipt_2_6_2383_0_part1 receipt_2_6_2383_0_part2 rfl rfl rfl
private theorem receipt_2_6_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 0) 0 381 = 48501045641512534239987915 :=
  phaseBlock_append receipt_2_6_2383_0_part0 receipt_2_6_2383_0_join0 rfl rfl rfl

private theorem receipt_2_6_2383_0 : fastPhase (bank 2 6).shape 179808 2383 7 1 0 7 0 = 48501045641512534239987915 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2383_0_join1

private theorem receipt_2_6_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 1) 0 128 = 28519141120931193350334912 := by decide +kernel
private theorem receipt_2_6_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 1) 128 128 = 15262988281348925688113600 := by decide +kernel
private theorem receipt_2_6_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 1) 256 125 = 4439238652588148791900257 := by decide +kernel
private theorem receipt_2_6_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 1) 128 253 = 19702226933937074480013857 :=
  phaseBlock_append receipt_2_6_2383_1_part1 receipt_2_6_2383_1_part2 rfl rfl rfl
private theorem receipt_2_6_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2383 7 1 0 7 1) 0 381 = 48221368054868267830348769 :=
  phaseBlock_append receipt_2_6_2383_1_part0 receipt_2_6_2383_1_join0 rfl rfl rfl

private theorem receipt_2_6_2383_1 : fastPhase (bank 2 6).shape 179808 2383 7 1 0 7 1 = 48221368054868267830348769 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2383_1_join1

private theorem receipt_2_6_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 0) 0 128 = 28631950225722028165791680 := by decide +kernel
private theorem receipt_2_6_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 0) 128 128 = 15356130805186044813230016 := by decide +kernel
private theorem receipt_2_6_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 0) 256 125 = 4513332995342443255670404 := by decide +kernel
private theorem receipt_2_6_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 0) 128 253 = 19869463800528488068900420 :=
  phaseBlock_append receipt_2_6_2384_0_part1 receipt_2_6_2384_0_part2 rfl rfl rfl
private theorem receipt_2_6_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 0) 0 381 = 48501414026250516234692100 :=
  phaseBlock_append receipt_2_6_2384_0_part0 receipt_2_6_2384_0_join0 rfl rfl rfl

private theorem receipt_2_6_2384_0 : fastPhase (bank 2 6).shape 179808 2384 7 1 0 7 0 = 48501414026250516234692100 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2384_0_join1

private theorem receipt_2_6_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 1) 0 128 = 28519383492356048386601728 := by decide +kernel
private theorem receipt_2_6_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 1) 128 128 = 15263090776475992482353920 := by decide +kernel
private theorem receipt_2_6_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 1) 256 125 = 4439260512574672963271660 := by decide +kernel
private theorem receipt_2_6_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 1) 128 253 = 19702351289050665445625580 :=
  phaseBlock_append receipt_2_6_2384_1_part1 receipt_2_6_2384_1_part2 rfl rfl rfl
private theorem receipt_2_6_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2384 7 1 0 7 1) 0 381 = 48221734781406713832227308 :=
  phaseBlock_append receipt_2_6_2384_1_part0 receipt_2_6_2384_1_join0 rfl rfl rfl

private theorem receipt_2_6_2384_1 : fastPhase (bank 2 6).shape 179808 2384 7 1 0 7 1 = 48221734781406713832227308 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2384_1_join1

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2383_0 receipt_2_6_2383_1 receipt_2_6_2384_0 receipt_2_6_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 0 128 = 5788523463556739077347168 := by decide +kernel
private theorem receipt_3_6_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 128 128 = 3194557638409954187986784 := by decide +kernel
private theorem receipt_3_6_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 256 128 = 1060974309889739133024096 := by decide +kernel
private theorem receipt_3_6_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 384 12 = 7634318982977670110335 := by decide +kernel
private theorem receipt_3_6_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 0 256 = 8983081101966693265333952 :=
  phaseBlock_append receipt_3_6_2383_0_part0 receipt_3_6_2383_0_part1 rfl rfl rfl
private theorem receipt_3_6_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 256 140 = 1068608628872716803134431 :=
  phaseBlock_append receipt_3_6_2383_0_part2 receipt_3_6_2383_0_part3 rfl rfl rfl
private theorem receipt_3_6_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 0) 0 396 = 10051689730839410068468383 :=
  phaseBlock_append receipt_3_6_2383_0_join0 receipt_3_6_2383_0_join1 rfl rfl rfl

private theorem receipt_3_6_2383_0 : fastPhase (bank 3 6).shape 179808 2383 7 1 1 1 0 = 10051689730839410068468383 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2383_0_join2

private theorem receipt_3_6_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 0 128 = 5766833010053105856201696 := by decide +kernel
private theorem receipt_3_6_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 128 128 = 3176190657042280474448864 := by decide +kernel
private theorem receipt_3_6_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 256 128 = 1046265386928728248968160 := by decide +kernel
private theorem receipt_3_6_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 384 12 = 6454615532292410894895 := by decide +kernel
private theorem receipt_3_6_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 0 256 = 8943023667095386330650560 :=
  phaseBlock_append receipt_3_6_2383_1_part0 receipt_3_6_2383_1_part1 rfl rfl rfl
private theorem receipt_3_6_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 256 140 = 1052720002461020659863055 :=
  phaseBlock_append receipt_3_6_2383_1_part2 receipt_3_6_2383_1_part3 rfl rfl rfl
private theorem receipt_3_6_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2383 7 1 1 1 1) 0 396 = 9995743669556406990513615 :=
  phaseBlock_append receipt_3_6_2383_1_join0 receipt_3_6_2383_1_join1 rfl rfl rfl

private theorem receipt_3_6_2383_1 : fastPhase (bank 3 6).shape 179808 2383 7 1 1 1 1 = 9995743669556406990513615 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2383_1_join2

private theorem receipt_3_6_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 0 128 = 5788569766362949660451616 := by decide +kernel
private theorem receipt_3_6_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 128 128 = 3194574323153959231812384 := by decide +kernel
private theorem receipt_3_6_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 256 128 = 1060977245421958796395296 := by decide +kernel
private theorem receipt_3_6_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 384 12 = 7634326711778039083629 := by decide +kernel
private theorem receipt_3_6_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 0 256 = 8983144089516908892264000 :=
  phaseBlock_append receipt_3_6_2384_0_part0 receipt_3_6_2384_0_part1 rfl rfl rfl
private theorem receipt_3_6_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 256 140 = 1068611572133736835478925 :=
  phaseBlock_append receipt_3_6_2384_0_part2 receipt_3_6_2384_0_part3 rfl rfl rfl
private theorem receipt_3_6_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 0) 0 396 = 10051755661650645727742925 :=
  phaseBlock_append receipt_3_6_2384_0_join0 receipt_3_6_2384_0_join1 rfl rfl rfl

private theorem receipt_3_6_2384_0 : fastPhase (bank 3 6).shape 179808 2384 7 1 1 1 0 = 10051755661650645727742925 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2384_0_join2

private theorem receipt_3_6_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 0 128 = 5766879115471456466915616 := by decide +kernel
private theorem receipt_3_6_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 128 128 = 3176207236687822040187168 := by decide +kernel
private theorem receipt_3_6_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 256 128 = 1046268283558424248529184 := by decide +kernel
private theorem receipt_3_6_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 384 12 = 6454622093177669252193 := by decide +kernel
private theorem receipt_3_6_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 0 256 = 8943086352159278507102784 :=
  phaseBlock_append receipt_3_6_2384_1_part0 receipt_3_6_2384_1_part1 rfl rfl rfl
private theorem receipt_3_6_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 256 140 = 1052722905651601917781377 :=
  phaseBlock_append receipt_3_6_2384_1_part2 receipt_3_6_2384_1_part3 rfl rfl rfl
private theorem receipt_3_6_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2384 7 1 1 1 1) 0 396 = 9995809257810880424884161 :=
  phaseBlock_append receipt_3_6_2384_1_join0 receipt_3_6_2384_1_join1 rfl rfl rfl

private theorem receipt_3_6_2384_1 : fastPhase (bank 3 6).shape 179808 2384 7 1 1 1 1 = 9995809257810880424884161 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2384_1_join2

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2383_0 receipt_3_6_2383_1 receipt_3_6_2384_0 receipt_3_6_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 0 128 = 142821588075357581265471232 := by decide +kernel
private theorem receipt_0_7_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 128 128 = 92177432148721769237137152 := by decide +kernel
private theorem receipt_0_7_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 256 128 = 47833272063200223652611222 := by decide +kernel
private theorem receipt_0_7_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 384 97 = 10329868322793921628522790 := by decide +kernel
private theorem receipt_0_7_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 0 256 = 234999020224079350502608384 :=
  phaseBlock_append receipt_0_7_2383_0_part0 receipt_0_7_2383_0_part1 rfl rfl rfl
private theorem receipt_0_7_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 256 225 = 58163140385994145281134012 :=
  phaseBlock_append receipt_0_7_2383_0_part2 receipt_0_7_2383_0_part3 rfl rfl rfl
private theorem receipt_0_7_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 0) 0 481 = 293162160610073495783742396 :=
  phaseBlock_append receipt_0_7_2383_0_join0 receipt_0_7_2383_0_join1 rfl rfl rfl

private theorem receipt_0_7_2383_0 : fastPhase (bank 0 7).shape 179808 2383 10 1 0 1 0 = 293162160610073495783742396 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2383_0_join2

private theorem receipt_0_7_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 0 128 = 142405599048822545227550400 := by decide +kernel
private theorem receipt_0_7_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 128 128 = 91810584643436609857384128 := by decide +kernel
private theorem receipt_0_7_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 256 128 = 47512390850058483183928142 := by decide +kernel
private theorem receipt_0_7_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 384 97 = 10115383360045756575117454 := by decide +kernel
private theorem receipt_0_7_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 0 256 = 234216183692259155084934528 :=
  phaseBlock_append receipt_0_7_2383_1_part0 receipt_0_7_2383_1_part1 rfl rfl rfl
private theorem receipt_0_7_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 256 225 = 57627774210104239759045596 :=
  phaseBlock_append receipt_0_7_2383_1_part2 receipt_0_7_2383_1_part3 rfl rfl rfl
private theorem receipt_0_7_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2383 10 1 0 1 1) 0 481 = 291843957902363394843980124 :=
  phaseBlock_append receipt_0_7_2383_1_join0 receipt_0_7_2383_1_join1 rfl rfl rfl

private theorem receipt_0_7_2383_1 : fastPhase (bank 0 7).shape 179808 2383 10 1 0 1 1 = 291843957902363394843980124 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2383_1_join2

private theorem receipt_0_7_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 0 128 = 142822821136496399195917152 := by decide +kernel
private theorem receipt_0_7_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 128 128 = 92178098735822827705572192 := by decide +kernel
private theorem receipt_0_7_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 256 128 = 47833546227980639048395053 := by decide +kernel
private theorem receipt_0_7_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 384 97 = 10329913190979905300685866 := by decide +kernel
private theorem receipt_0_7_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 0 256 = 235000919872319226901489344 :=
  phaseBlock_append receipt_0_7_2384_0_part0 receipt_0_7_2384_0_part1 rfl rfl rfl
private theorem receipt_0_7_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 256 225 = 58163459418960544349080919 :=
  phaseBlock_append receipt_0_7_2384_0_part2 receipt_0_7_2384_0_part3 rfl rfl rfl
private theorem receipt_0_7_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 0) 0 481 = 293164379291279771250570263 :=
  phaseBlock_append receipt_0_7_2384_0_join0 receipt_0_7_2384_0_join1 rfl rfl rfl

private theorem receipt_0_7_2384_0 : fastPhase (bank 0 7).shape 179808 2384 10 1 0 1 0 = 293164379291279771250570263 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2384_0_join2

private theorem receipt_0_7_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 0 128 = 142406829140494819780787040 := by decide +kernel
private theorem receipt_0_7_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 128 128 = 91811248962489458400455520 := by decide +kernel
private theorem receipt_0_7_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 256 128 = 47512663381917127673544279 := by decide +kernel
private theorem receipt_0_7_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 384 97 = 10115427376112158935823051 := by decide +kernel
private theorem receipt_0_7_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 0 256 = 234218078102984278181242560 :=
  phaseBlock_append receipt_0_7_2384_1_part0 receipt_0_7_2384_1_part1 rfl rfl rfl
private theorem receipt_0_7_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 256 225 = 57628090758029286609367330 :=
  phaseBlock_append receipt_0_7_2384_1_part2 receipt_0_7_2384_1_part3 rfl rfl rfl
private theorem receipt_0_7_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2384 10 1 0 1 1) 0 481 = 291846168861013564790609890 :=
  phaseBlock_append receipt_0_7_2384_1_join0 receipt_0_7_2384_1_join1 rfl rfl rfl

private theorem receipt_0_7_2384_1 : fastPhase (bank 0 7).shape 179808 2384 10 1 0 1 1 = 291846168861013564790609890 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2384_1_join2

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2383_0 receipt_0_7_2383_1 receipt_0_7_2384_0 receipt_0_7_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 0 128 = 128471824929712769110140832 := by decide +kernel
private theorem receipt_1_7_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 128 128 = 82752235626520129294768032 := by decide +kernel
private theorem receipt_1_7_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 256 128 = 42858739670591731358628744 := by decide +kernel
private theorem receipt_1_7_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 384 97 = 9240275764054361379999744 := by decide +kernel
private theorem receipt_1_7_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 0 256 = 211224060556232898404908864 :=
  phaseBlock_append receipt_1_7_2383_0_part0 receipt_1_7_2383_0_part1 rfl rfl rfl
private theorem receipt_1_7_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 256 225 = 52099015434646092738628488 :=
  phaseBlock_append receipt_1_7_2383_0_part2 receipt_1_7_2383_0_part3 rfl rfl rfl
private theorem receipt_1_7_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 0) 0 481 = 263323075990878991143537352 :=
  phaseBlock_append receipt_1_7_2383_0_join0 receipt_1_7_2383_0_join1 rfl rfl rfl

private theorem receipt_1_7_2383_0 : fastPhase (bank 1 7).shape 179808 2383 10 1 0 2 0 = 263323075990878991143537352 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2383_0_join2

private theorem receipt_1_7_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 0 128 = 128095648364011859614186720 := by decide +kernel
private theorem receipt_1_7_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 128 128 = 82421629671423467652877536 := by decide +kernel
private theorem receipt_1_7_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 256 128 = 42570596081302899697307097 := by decide +kernel
private theorem receipt_1_7_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 384 97 = 9048318836886222103431813 := by decide +kernel
private theorem receipt_1_7_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 0 256 = 210517278035435327267064256 :=
  phaseBlock_append receipt_1_7_2383_1_part0 receipt_1_7_2383_1_part1 rfl rfl rfl
private theorem receipt_1_7_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 256 225 = 51618914918189121800738910 :=
  phaseBlock_append receipt_1_7_2383_1_part2 receipt_1_7_2383_1_part3 rfl rfl rfl
private theorem receipt_1_7_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2383 10 1 0 2 1) 0 481 = 262136192953624449067803166 :=
  phaseBlock_append receipt_1_7_2383_1_join0 receipt_1_7_2383_1_join1 rfl rfl rfl

private theorem receipt_1_7_2383_1 : fastPhase (bank 1 7).shape 179808 2383 10 1 0 2 1 = 262136192953624449067803166 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2383_1_join2

private theorem receipt_1_7_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 0 128 = 128472934129913911672907712 := by decide +kernel
private theorem receipt_1_7_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 128 128 = 82752834074747798189295552 := by decide +kernel
private theorem receipt_1_7_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 256 128 = 42858985333992394623206199 := by decide +kernel
private theorem receipt_1_7_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 384 97 = 9240315900598845443887023 := by decide +kernel
private theorem receipt_1_7_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 0 256 = 211225768204661709862203264 :=
  phaseBlock_append receipt_1_7_2384_0_part0 receipt_1_7_2384_0_part1 rfl rfl rfl
private theorem receipt_1_7_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 256 225 = 52099301234591240067093222 :=
  phaseBlock_append receipt_1_7_2384_0_part2 receipt_1_7_2384_0_part3 rfl rfl rfl
private theorem receipt_1_7_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 0) 0 481 = 263325069439252949929296486 :=
  phaseBlock_append receipt_1_7_2384_0_join0 receipt_1_7_2384_0_join1 rfl rfl rfl

private theorem receipt_1_7_2384_0 : fastPhase (bank 1 7).shape 179808 2384 10 1 0 2 0 = 263325069439252949929296486 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2384_0_join2

private theorem receipt_1_7_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 0 128 = 128096754875887010351791680 := by decide +kernel
private theorem receipt_1_7_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 128 128 = 82422226074253203867737664 := by decide +kernel
private theorem receipt_1_7_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 256 128 = 42570840277889910292118088 := by decide +kernel
private theorem receipt_1_7_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 384 97 = 9048358210733147765966910 := by decide +kernel
private theorem receipt_1_7_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 0 256 = 210518980950140214219529344 :=
  phaseBlock_append receipt_1_7_2384_1_part0 receipt_1_7_2384_1_part1 rfl rfl rfl
private theorem receipt_1_7_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 256 225 = 51619198488623058058084998 :=
  phaseBlock_append receipt_1_7_2384_1_part2 receipt_1_7_2384_1_part3 rfl rfl rfl
private theorem receipt_1_7_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2384 10 1 0 2 1) 0 481 = 262138179438763272277614342 :=
  phaseBlock_append receipt_1_7_2384_1_join0 receipt_1_7_2384_1_join1 rfl rfl rfl

private theorem receipt_1_7_2384_1 : fastPhase (bank 1 7).shape 179808 2384 10 1 0 2 1 = 262138179438763272277614342 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2384_1_join2

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2383_0 receipt_1_7_2383_1 receipt_1_7_2384_0 receipt_1_7_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 0 128 = 68544844757683432519376160 := by decide +kernel
private theorem receipt_2_7_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 128 128 = 43523863277424164437314848 := by decide +kernel
private theorem receipt_2_7_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 256 128 = 22223509544135804355993157 := by decide +kernel
private theorem receipt_2_7_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 384 97 = 4733339510562567381201417 := by decide +kernel
private theorem receipt_2_7_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 0 256 = 112068708035107596956691008 :=
  phaseBlock_append receipt_2_7_2383_0_part0 receipt_2_7_2383_0_part1 rfl rfl rfl
private theorem receipt_2_7_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 256 225 = 26956849054698371737194574 :=
  phaseBlock_append receipt_2_7_2383_0_part2 receipt_2_7_2383_0_part3 rfl rfl rfl
private theorem receipt_2_7_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 0) 0 481 = 139025557089805968693885582 :=
  phaseBlock_append receipt_2_7_2383_0_join0 receipt_2_7_2383_0_join1 rfl rfl rfl

private theorem receipt_2_7_2383_0 : fastPhase (bank 2 7).shape 179808 2383 10 1 0 7 0 = 139025557089805968693885582 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2383_0_join2

private theorem receipt_2_7_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 0 128 = 68336508708997826273083744 := by decide +kernel
private theorem receipt_2_7_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 128 128 = 43345128060407139042308448 := by decide +kernel
private theorem receipt_2_7_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 256 128 = 22071692319837049280380434 := by decide +kernel
private theorem receipt_2_7_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 384 97 = 4634647052275130075314986 := by decide +kernel
private theorem receipt_2_7_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 0 256 = 111681636769404965315392192 :=
  phaseBlock_append receipt_2_7_2383_1_part0 receipt_2_7_2383_1_part1 rfl rfl rfl
private theorem receipt_2_7_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 256 225 = 26706339372112179355695420 :=
  phaseBlock_append receipt_2_7_2383_1_part2 receipt_2_7_2383_1_part3 rfl rfl rfl
private theorem receipt_2_7_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2383 10 1 0 7 1) 0 481 = 138387976141517144671087612 :=
  phaseBlock_append receipt_2_7_2383_1_join0 receipt_2_7_2383_1_join1 rfl rfl rfl

private theorem receipt_2_7_2383_1 : fastPhase (bank 2 7).shape 179808 2383 10 1 0 7 1 = 138387976141517144671087612 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2383_1_join2

private theorem receipt_2_7_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 0 128 = 68545436671207785152880960 := by decide +kernel
private theorem receipt_2_7_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 128 128 = 43524178110267052086468928 := by decide +kernel
private theorem receipt_2_7_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 256 128 = 22223636969674058674146484 := by decide +kernel
private theorem receipt_2_7_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 384 97 = 4733360074497096245271290 := by decide +kernel
private theorem receipt_2_7_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 0 256 = 112069614781474837239349888 :=
  phaseBlock_append receipt_2_7_2384_0_part0 receipt_2_7_2384_0_part1 rfl rfl rfl
private theorem receipt_2_7_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 256 225 = 26956997044171154919417774 :=
  phaseBlock_append receipt_2_7_2384_0_part2 receipt_2_7_2384_0_part3 rfl rfl rfl
private theorem receipt_2_7_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 0) 0 481 = 139026611825645992158767662 :=
  phaseBlock_append receipt_2_7_2384_0_join0 receipt_2_7_2384_0_join1 rfl rfl rfl

private theorem receipt_2_7_2384_0 : fastPhase (bank 2 7).shape 179808 2384 10 1 0 7 0 = 139026611825645992158767662 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2384_0_join2

private theorem receipt_2_7_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 0 128 = 68337099121964806335752576 := by decide +kernel
private theorem receipt_2_7_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 128 128 = 43345441782055651061483904 := by decide +kernel
private theorem receipt_2_7_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 256 128 = 22071818970681853294822070 := by decide +kernel
private theorem receipt_2_7_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 384 97 = 4634667223779533477349223 := by decide +kernel
private theorem receipt_2_7_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 0 256 = 111682540904020457397236480 :=
  phaseBlock_append receipt_2_7_2384_1_part0 receipt_2_7_2384_1_part1 rfl rfl rfl
private theorem receipt_2_7_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 256 225 = 26706486194461386772171293 :=
  phaseBlock_append receipt_2_7_2384_1_part2 receipt_2_7_2384_1_part3 rfl rfl rfl
private theorem receipt_2_7_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2384 10 1 0 7 1) 0 481 = 138389027098481844169407773 :=
  phaseBlock_append receipt_2_7_2384_1_join0 receipt_2_7_2384_1_join1 rfl rfl rfl

private theorem receipt_2_7_2384_1 : fastPhase (bank 2 7).shape 179808 2384 10 1 0 7 1 = 138389027098481844169407773 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2384_1_join2

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2383_0 receipt_2_7_2383_1 receipt_2_7_2384_0 receipt_2_7_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 0 128 = 17323928994649254967353376 := by decide +kernel
private theorem receipt_3_7_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 128 128 = 11244483371352870507040800 := by decide +kernel
private theorem receipt_3_7_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 256 128 = 5971127210455776451231776 := by decide +kernel
private theorem receipt_3_7_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 384 115 = 1575987415840865794718523 := by decide +kernel
private theorem receipt_3_7_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 0 256 = 28568412366002125474394176 :=
  phaseBlock_append receipt_3_7_2383_0_part0 receipt_3_7_2383_0_part1 rfl rfl rfl
private theorem receipt_3_7_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 256 243 = 7547114626296642245950299 :=
  phaseBlock_append receipt_3_7_2383_0_part2 receipt_3_7_2383_0_part3 rfl rfl rfl
private theorem receipt_3_7_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 0) 0 499 = 36115526992298767720344475 :=
  phaseBlock_append receipt_3_7_2383_0_join0 receipt_3_7_2383_0_join1 rfl rfl rfl

private theorem receipt_3_7_2383_0 : fastPhase (bank 3 7).shape 179808 2383 10 1 1 1 0 = 36115526992298767720344475 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2383_0_join2

private theorem receipt_3_7_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 0 128 = 17274064963404901818775584 := by decide +kernel
private theorem receipt_3_7_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 128 128 = 11200475383501377302923296 := by decide +kernel
private theorem receipt_3_7_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 256 128 = 5933449053483297748801568 := by decide +kernel
private theorem receipt_3_7_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 384 115 = 1547915470225462533952522 := by decide +kernel
private theorem receipt_3_7_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 0 256 = 28474540346906279121698880 :=
  phaseBlock_append receipt_3_7_2383_1_part0 receipt_3_7_2383_1_part1 rfl rfl rfl
private theorem receipt_3_7_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 256 243 = 7481364523708760282754090 :=
  phaseBlock_append receipt_3_7_2383_1_part2 receipt_3_7_2383_1_part3 rfl rfl rfl
private theorem receipt_3_7_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2383 10 1 1 1 1) 0 499 = 35955904870615039404452970 :=
  phaseBlock_append receipt_3_7_2383_1_join0 receipt_3_7_2383_1_join1 rfl rfl rfl

private theorem receipt_3_7_2383_1 : fastPhase (bank 3 7).shape 179808 2383 10 1 1 1 1 = 35955904870615039404452970 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2383_1_join2

private theorem receipt_3_7_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 0 128 = 17324071724029526732508672 := by decide +kernel
private theorem receipt_3_7_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 128 128 = 11244550761460893916638720 := by decide +kernel
private theorem receipt_3_7_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 256 128 = 5971150359845086775496192 := by decide +kernel
private theorem receipt_3_7_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 384 115 = 1575990688089420936163116 := by decide +kernel
private theorem receipt_3_7_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 0 256 = 28568622485490420649147392 :=
  phaseBlock_append receipt_3_7_2384_0_part0 receipt_3_7_2384_0_part1 rfl rfl rfl
private theorem receipt_3_7_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 256 243 = 7547141047934507711659308 :=
  phaseBlock_append receipt_3_7_2384_0_part2 receipt_3_7_2384_0_part3 rfl rfl rfl
private theorem receipt_3_7_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 0) 0 499 = 36115763533424928360806700 :=
  phaseBlock_append receipt_3_7_2384_0_join0 receipt_3_7_2384_0_join1 rfl rfl rfl

private theorem receipt_3_7_2384_0 : fastPhase (bank 3 7).shape 179808 2384 10 1 1 1 0 = 36115763533424928360806700 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2384_0_join2

private theorem receipt_3_7_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 0 128 = 17274207222527585438673216 := by decide +kernel
private theorem receipt_3_7_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 128 128 = 11200542478725038766917952 := by decide +kernel
private theorem receipt_3_7_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 256 128 = 5933472045861720272595264 := by decide +kernel
private theorem receipt_3_7_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 384 115 = 1547918688752223154859493 := by decide +kernel
private theorem receipt_3_7_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 0 256 = 28474749701252624205591168 :=
  phaseBlock_append receipt_3_7_2384_1_part0 receipt_3_7_2384_1_part1 rfl rfl rfl
private theorem receipt_3_7_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 256 243 = 7481390734613943427454757 :=
  phaseBlock_append receipt_3_7_2384_1_part2 receipt_3_7_2384_1_part3 rfl rfl rfl
private theorem receipt_3_7_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2384 10 1 1 1 1) 0 499 = 35956140435866567633045925 :=
  phaseBlock_append receipt_3_7_2384_1_join0 receipt_3_7_2384_1_join1 rfl rfl rfl

private theorem receipt_3_7_2384_1 : fastPhase (bank 3 7).shape 179808 2384 10 1 1 1 1 = 35956140435866567633045925 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2384_1_join2

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_498)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_7_2383_0 receipt_3_7_2383_1 receipt_3_7_2384_0 receipt_3_7_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group2_stage i)).shape
      (cutoff h rect (group2_stage i)), ¬ G∣Q :=
  (group2_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group2_avoids

end Lower6960.RescueSource
