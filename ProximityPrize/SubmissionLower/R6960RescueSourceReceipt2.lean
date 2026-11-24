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

private theorem receipt_0_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 0) 0 128 = 33781472171333376244307840 := by decide +kernel
private theorem receipt_0_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 0) 128 128 = 17310671093300540458673112 := by decide +kernel
private theorem receipt_0_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 0) 256 101 = 3868308101395205093195264 := by decide +kernel
private theorem receipt_0_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 0) 128 229 = 21178979194695745551868376 :=
  phaseBlock_append receipt_0_5_2359_0_part1 receipt_0_5_2359_0_part2 rfl rfl rfl
private theorem receipt_0_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 0) 0 357 = 54960451366029121796176216 :=
  phaseBlock_append receipt_0_5_2359_0_part0 receipt_0_5_2359_0_join0 rfl rfl rfl

private theorem receipt_0_5_2359_0 : fastPhase (bank 0 5).shape 179808 2379 5 1 0 1 0 = 54960451366029121796176216 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2359_0_join1

private theorem receipt_0_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 1) 0 128 = 33642997927669145547472640 := by decide +kernel
private theorem receipt_0_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 1) 128 128 = 17194170665821573029723953 := by decide +kernel
private theorem receipt_0_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 1) 256 101 = 3790614982707225284866770 := by decide +kernel
private theorem receipt_0_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 1) 128 229 = 20984785648528798314590723 :=
  phaseBlock_append receipt_0_5_2359_1_part1 receipt_0_5_2359_1_part2 rfl rfl rfl
private theorem receipt_0_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2379 5 1 0 1 1) 0 357 = 54627783576197943862063363 :=
  phaseBlock_append receipt_0_5_2359_1_part0 receipt_0_5_2359_1_join0 rfl rfl rfl

private theorem receipt_0_5_2359_1 : fastPhase (bank 0 5).shape 179808 2379 5 1 0 1 1 = 54627783576197943862063363 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2359_1_join1

private theorem receipt_0_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 0) 0 128 = 33781758771466187700515360 := by decide +kernel
private theorem receipt_0_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 0) 128 128 = 17310784979659263407246952 := by decide +kernel
private theorem receipt_0_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 0) 256 101 = 3868326483182986064132677 := by decide +kernel
private theorem receipt_0_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 0) 128 229 = 21179111462842249471379629 :=
  phaseBlock_append receipt_0_5_2360_0_part1 receipt_0_5_2360_0_part2 rfl rfl rfl
private theorem receipt_0_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 0) 0 357 = 54960870234308437171894989 :=
  phaseBlock_append receipt_0_5_2360_0_part0 receipt_0_5_2360_0_join0 rfl rfl rfl

private theorem receipt_0_5_2360_0 : fastPhase (bank 0 5).shape 179808 2380 5 1 0 1 0 = 54960870234308437171894989 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2360_0_join1

private theorem receipt_0_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 1) 0 128 = 33643283553856869942411040 := by decide +kernel
private theorem receipt_0_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 1) 128 128 = 17194283889261598747973914 := by decide +kernel
private theorem receipt_0_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 1) 256 101 = 3790633035460610115468528 := by decide +kernel
private theorem receipt_0_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 1) 128 229 = 20984916924722208863442442 :=
  phaseBlock_append receipt_0_5_2360_1_part1 receipt_0_5_2360_1_part2 rfl rfl rfl
private theorem receipt_0_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179808 2380 5 1 0 1 1) 0 357 = 54628200478579078805853482 :=
  phaseBlock_append receipt_0_5_2360_1_part0 receipt_0_5_2360_1_join0 rfl rfl rfl

private theorem receipt_0_5_2360_1 : fastPhase (bank 0 5).shape 179808 2380 5 1 0 1 1 = 54628200478579078805853482 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2360_1_join1

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2359_0 receipt_0_5_2359_1 receipt_0_5_2360_0 receipt_0_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 0) 0 128 = 30382365133434373825078848 := by decide +kernel
private theorem receipt_1_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 0) 128 128 = 15530356792599636543468410 := by decide +kernel
private theorem receipt_1_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 0) 256 101 = 3463089835660722248522202 := by decide +kernel
private theorem receipt_1_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 0) 128 229 = 18993446628260358791990612 :=
  phaseBlock_append receipt_1_5_2359_0_part1 receipt_1_5_2359_0_part2 rfl rfl rfl
private theorem receipt_1_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 0) 0 357 = 49375811761694732617069460 :=
  phaseBlock_append receipt_1_5_2359_0_part0 receipt_1_5_2359_0_join0 rfl rfl rfl

private theorem receipt_1_5_2359_0 : fastPhase (bank 1 5).shape 179808 2379 5 1 0 2 0 = 49375811761694732617069460 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2359_0_join1

private theorem receipt_1_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 1) 0 128 = 30257232603213361847157632 := by decide +kernel
private theorem receipt_1_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 1) 128 128 = 15425545536219545250570975 := by decide +kernel
private theorem receipt_1_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 1) 256 101 = 3393489481264987845487230 := by decide +kernel
private theorem receipt_1_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 1) 128 229 = 18819035017484533096058205 :=
  phaseBlock_append receipt_1_5_2359_1_part1 receipt_1_5_2359_1_part2 rfl rfl rfl
private theorem receipt_1_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2379 5 1 0 2 1) 0 357 = 49076267620697894943215837 :=
  phaseBlock_append receipt_1_5_2359_1_part0 receipt_1_5_2359_1_join0 rfl rfl rfl

private theorem receipt_1_5_2359_1 : fastPhase (bank 1 5).shape 179808 2379 5 1 0 2 1 = 49076267620697894943215837 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2359_1_join1

private theorem receipt_1_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 0) 0 128 = 30382622907456328898831520 := by decide +kernel
private theorem receipt_1_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 0) 128 128 = 15530458972823638641662740 := by decide +kernel
private theorem receipt_1_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 0) 256 101 = 3463106292607349810113947 := by decide +kernel
private theorem receipt_1_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 0) 128 229 = 18993565265430988451776687 :=
  phaseBlock_append receipt_1_5_2360_0_part1 receipt_1_5_2360_0_part2 rfl rfl rfl
private theorem receipt_1_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 0) 0 357 = 49376188172887317350608207 :=
  phaseBlock_append receipt_1_5_2360_0_part0 receipt_1_5_2360_0_join0 rfl rfl rfl

private theorem receipt_1_5_2360_0 : fastPhase (bank 1 5).shape 179808 2380 5 1 0 2 0 = 49376188172887317350608207 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2360_0_join1

private theorem receipt_1_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 1) 0 128 = 30257489496219715767291040 := by decide +kernel
private theorem receipt_1_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 1) 128 128 = 15425647119731499006842511 := by decide +kernel
private theorem receipt_1_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 1) 256 101 = 3393505643398353034880033 := by decide +kernel
private theorem receipt_1_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 1) 128 229 = 18819152763129852041722544 :=
  phaseBlock_append receipt_1_5_2360_1_part1 receipt_1_5_2360_1_part2 rfl rfl rfl
private theorem receipt_1_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179808 2380 5 1 0 2 1) 0 357 = 49076642259349567809013584 :=
  phaseBlock_append receipt_1_5_2360_1_part0 receipt_1_5_2360_1_join0 rfl rfl rfl

private theorem receipt_1_5_2360_1 : fastPhase (bank 1 5).shape 179808 2380 5 1 0 2 1 = 49076642259349567809013584 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2360_1_join1

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2359_0 receipt_1_5_2359_1 receipt_1_5_2360_0 receipt_1_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 0) 0 128 = 16184868244353999086720512 := by decide +kernel
private theorem receipt_2_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 0) 128 128 = 8125804480385722975105193 := by decide +kernel
private theorem receipt_2_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 0) 256 101 = 1783909683263703395016540 := by decide +kernel
private theorem receipt_2_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 0) 128 229 = 9909714163649426370121733 :=
  phaseBlock_append receipt_2_5_2359_0_part1 receipt_2_5_2359_0_part2 rfl rfl rfl
private theorem receipt_2_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 0) 0 357 = 26094582408003425456842245 :=
  phaseBlock_append receipt_2_5_2359_0_part0 receipt_2_5_2359_0_join0 rfl rfl rfl

private theorem receipt_2_5_2359_0 : fastPhase (bank 2 5).shape 179808 2379 5 1 0 7 0 = 26094582408003425456842245 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2359_0_join1

private theorem receipt_2_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 1) 0 128 = 16115934627082015517166720 := by decide +kernel
private theorem receipt_2_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 1) 128 128 = 8069849804951536691382071 := by decide +kernel
private theorem receipt_2_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 1) 256 101 = 1747883212498686922267155 := by decide +kernel
private theorem receipt_2_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 1) 128 229 = 9817733017450223613649226 :=
  phaseBlock_append receipt_2_5_2359_1_part1 receipt_2_5_2359_1_part2 rfl rfl rfl
private theorem receipt_2_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2379 5 1 0 7 1) 0 357 = 25933667644532239130815946 :=
  phaseBlock_append receipt_2_5_2359_1_part0 receipt_2_5_2359_1_join0 rfl rfl rfl

private theorem receipt_2_5_2359_1 : fastPhase (bank 2 5).shape 179808 2379 5 1 0 7 1 = 25933667644532239130815946 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2359_1_join1

private theorem receipt_2_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 0) 0 128 = 16185005607190231556859584 := by decide +kernel
private theorem receipt_2_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 0) 128 128 = 8125857967972752869570923 := by decide +kernel
private theorem receipt_2_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 0) 256 101 = 1783918163279540918679111 := by decide +kernel
private theorem receipt_2_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 0) 128 229 = 9909776131252293788250034 :=
  phaseBlock_append receipt_2_5_2360_0_part1 receipt_2_5_2360_0_part2 rfl rfl rfl
private theorem receipt_2_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 0) 0 357 = 26094781738442525345109618 :=
  phaseBlock_append receipt_2_5_2360_0_part0 receipt_2_5_2360_0_join0 rfl rfl rfl

private theorem receipt_2_5_2360_0 : fastPhase (bank 2 5).shape 179808 2380 5 1 0 7 0 = 26094781738442525345109618 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2360_0_join1

private theorem receipt_2_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 1) 0 128 = 16116071501101208469637440 := by decide +kernel
private theorem receipt_2_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 1) 128 128 = 8069902972803806468330599 := by decide +kernel
private theorem receipt_2_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 1) 256 101 = 1747891539715946381267352 := by decide +kernel
private theorem receipt_2_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 1) 128 229 = 9817794512519752849597951 :=
  phaseBlock_append receipt_2_5_2360_1_part1 receipt_2_5_2360_1_part2 rfl rfl rfl
private theorem receipt_2_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179808 2380 5 1 0 7 1) 0 357 = 25933866013620961319235391 :=
  phaseBlock_append receipt_2_5_2360_1_part0 receipt_2_5_2360_1_join0 rfl rfl rfl

private theorem receipt_2_5_2360_1 : fastPhase (bank 2 5).shape 179808 2380 5 1 0 7 1 = 25933866013620961319235391 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2360_1_join1

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2359_0 receipt_2_5_2359_1 receipt_2_5_2360_0 receipt_2_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 0) 0 128 = 3848526554853736386731360 := by decide +kernel
private theorem receipt_3_5_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 0) 128 128 = 1999809443164628100132192 := by decide +kernel
private theorem receipt_3_5_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 0) 256 115 = 514036164606701980127721 := by decide +kernel
private theorem receipt_3_5_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 0) 128 243 = 2513845607771330080259913 :=
  phaseBlock_append receipt_3_5_2359_0_part1 receipt_3_5_2359_0_part2 rfl rfl rfl
private theorem receipt_3_5_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 0) 0 371 = 6362372162625066466991273 :=
  phaseBlock_append receipt_3_5_2359_0_part0 receipt_3_5_2359_0_join0 rfl rfl rfl

private theorem receipt_3_5_2359_0 : fastPhase (bank 3 5).shape 179808 2379 5 1 1 1 0 = 6362372162625066466991273 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2359_0_join1

private theorem receipt_3_5_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 1) 0 128 = 3832962758442644029333728 := by decide +kernel
private theorem receipt_3_5_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 1) 128 128 = 1986823533955183121035488 := by decide +kernel
private theorem receipt_3_5_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 1) 256 115 = 504792016077948826297893 := by decide +kernel
private theorem receipt_3_5_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 1) 128 243 = 2491615550033131947333381 :=
  phaseBlock_append receipt_3_5_2359_1_part1 receipt_3_5_2359_1_part2 rfl rfl rfl
private theorem receipt_3_5_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2379 5 1 1 1 1) 0 371 = 6324578308475775976667109 :=
  phaseBlock_append receipt_3_5_2359_1_part0 receipt_3_5_2359_1_join0 rfl rfl rfl

private theorem receipt_3_5_2359_1 : fastPhase (bank 3 5).shape 179808 2379 5 1 1 1 1 = 6324578308475775976667109 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2359_1_join1

private theorem receipt_3_5_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 0) 0 128 = 3848557190260793171538496 := by decide +kernel
private theorem receipt_3_5_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 0) 128 128 = 1999819479610224241816128 := by decide +kernel
private theorem receipt_3_5_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 0) 256 115 = 514037474997738747031002 := by decide +kernel
private theorem receipt_3_5_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 0) 128 243 = 2513856954607962988847130 :=
  phaseBlock_append receipt_3_5_2360_0_part1 receipt_3_5_2360_0_part2 rfl rfl rfl
private theorem receipt_3_5_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 0) 0 371 = 6362414144868756160385626 :=
  phaseBlock_append receipt_3_5_2360_0_part0 receipt_3_5_2360_0_join0 rfl rfl rfl

private theorem receipt_3_5_2360_0 : fastPhase (bank 3 5).shape 179808 2380 5 1 1 1 0 = 6362414144868756160385626 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2360_0_join1

private theorem receipt_3_5_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 1) 0 128 = 3832993253265867626078208 := by decide +kernel
private theorem receipt_3_5_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 1) 128 128 = 1986833499665554034589696 := by decide +kernel
private theorem receipt_3_5_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 1) 256 115 = 504793304830140723996492 := by decide +kernel
private theorem receipt_3_5_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 1) 128 243 = 2491626804495694758586188 :=
  phaseBlock_append receipt_3_5_2360_1_part1 receipt_3_5_2360_1_part2 rfl rfl rfl
private theorem receipt_3_5_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179808 2380 5 1 1 1 1) 0 371 = 6324620057761562384664396 :=
  phaseBlock_append receipt_3_5_2360_1_part0 receipt_3_5_2360_1_join0 rfl rfl rfl

private theorem receipt_3_5_2360_1 : fastPhase (bank 3 5).shape 179808 2380 5 1 1 1 1 = 6324620057761562384664396 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2360_1_join1

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2359_0 receipt_3_5_2359_1 receipt_3_5_2360_0 receipt_3_5_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 0) 0 128 = 62298162509860579686047465 := by decide +kernel
private theorem receipt_0_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 0) 128 128 = 33991508877546040477338765 := by decide +kernel
private theorem receipt_0_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 0) 256 125 = 10149004517144396893194639 := by decide +kernel
private theorem receipt_0_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 0) 128 253 = 44140513394690437370533404 :=
  phaseBlock_append receipt_0_6_2359_0_part1 receipt_0_6_2359_0_part2 rfl rfl rfl
private theorem receipt_0_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 0) 0 381 = 106438675904551017056580869 :=
  phaseBlock_append receipt_0_6_2359_0_part0 receipt_0_6_2359_0_join0 rfl rfl rfl

private theorem receipt_0_6_2359_0 : fastPhase (bank 0 6).shape 179808 2379 7 1 0 1 0 = 106438675904551017056580869 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2359_0_join1

private theorem receipt_0_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 1) 0 128 = 62061606441960480143353377 := by decide +kernel
private theorem receipt_0_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 1) 128 128 = 33790051404603136451408313 := by decide +kernel
private theorem receipt_0_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 1) 256 125 = 9983382661699535111059323 := by decide +kernel
private theorem receipt_0_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 1) 128 253 = 43773434066302671562467636 :=
  phaseBlock_append receipt_0_6_2359_1_part1 receipt_0_6_2359_1_part2 rfl rfl rfl
private theorem receipt_0_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2379 7 1 0 1 1) 0 381 = 105835040508263151705821013 :=
  phaseBlock_append receipt_0_6_2359_1_part0 receipt_0_6_2359_1_join0 rfl rfl rfl

private theorem receipt_0_6_2359_1 : fastPhase (bank 0 6).shape 179808 2379 7 1 0 1 1 = 105835040508263151705821013 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2359_1_join1

private theorem receipt_0_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 0) 0 128 = 62298695920875708903133564 := by decide +kernel
private theorem receipt_0_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 0) 128 128 = 33991737716708389582861872 := by decide +kernel
private theorem receipt_0_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 0) 256 125 = 10149054370163387936308635 := by decide +kernel
private theorem receipt_0_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 0) 128 253 = 44140792086871777519170507 :=
  phaseBlock_append receipt_0_6_2360_0_part1 receipt_0_6_2360_0_part2 rfl rfl rfl
private theorem receipt_0_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 0) 0 381 = 106439488007747486422304071 :=
  phaseBlock_append receipt_0_6_2360_0_part0 receipt_0_6_2360_0_join0 rfl rfl rfl

private theorem receipt_0_6_2360_0 : fastPhase (bank 0 6).shape 179808 2380 7 1 0 1 0 = 106439488007747486422304071 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2360_0_join1

private theorem receipt_0_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 1) 0 128 = 62062138175594334931511481 := by decide +kernel
private theorem receipt_0_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 1) 128 128 = 33790279073859011609623113 := by decide +kernel
private theorem receipt_0_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 1) 256 125 = 9983431800214352925498162 := by decide +kernel
private theorem receipt_0_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 1) 128 253 = 43773710874073364535121275 :=
  phaseBlock_append receipt_0_6_2360_1_part1 receipt_0_6_2360_1_part2 rfl rfl rfl
private theorem receipt_0_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179808 2380 7 1 0 1 1) 0 381 = 105835849049667699466632756 :=
  phaseBlock_append receipt_0_6_2360_1_part0 receipt_0_6_2360_1_join0 rfl rfl rfl

private theorem receipt_0_6_2360_1 : fastPhase (bank 0 6).shape 179808 2380 7 1 0 1 1 = 105835849049667699466632756 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2360_1_join1

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2359_0 receipt_0_6_2359_1 receipt_0_6_2360_0 receipt_0_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 0) 0 128 = 56107905498598053246389189 := by decide +kernel
private theorem receipt_1_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 0) 128 128 = 30551727637953072336569559 := by decide +kernel
private theorem receipt_1_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 0) 256 125 = 9105128995270334618215904 := by decide +kernel
private theorem receipt_1_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 0) 128 253 = 39656856633223406954785463 :=
  phaseBlock_append receipt_1_6_2359_0_part1 receipt_1_6_2359_0_part2 rfl rfl rfl
private theorem receipt_1_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 0) 0 381 = 95764762131821460201174652 :=
  phaseBlock_append receipt_1_6_2359_0_part0 receipt_1_6_2359_0_join0 rfl rfl rfl

private theorem receipt_1_6_2359_0 : fastPhase (bank 1 6).shape 179808 2379 7 1 0 2 0 = 95764762131821460201174652 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2359_0_join1

private theorem receipt_1_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 1) 0 128 = 55893959561269835928681650 := by decide +kernel
private theorem receipt_1_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 1) 128 128 = 30370180904133360108391752 := by decide +kernel
private theorem receipt_1_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 1) 256 125 = 8956443176510336586629305 := by decide +kernel
private theorem receipt_1_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 1) 128 253 = 39326624080643696695021057 :=
  phaseBlock_append receipt_1_6_2359_1_part1 receipt_1_6_2359_1_part2 rfl rfl rfl
private theorem receipt_1_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2379 7 1 0 2 1) 0 381 = 95220583641913532623702707 :=
  phaseBlock_append receipt_1_6_2359_1_part0 receipt_1_6_2359_1_join0 rfl rfl rfl

private theorem receipt_1_6_2359_1 : fastPhase (bank 1 6).shape 179808 2379 7 1 0 2 1 = 95220583641913532623702707 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2359_1_join1

private theorem receipt_1_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 0) 0 128 = 56108385924203643449995198 := by decide +kernel
private theorem receipt_1_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 0) 128 128 = 30551933329685705085844460 := by decide +kernel
private theorem receipt_1_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 0) 256 125 = 9105173722834194027613902 := by decide +kernel
private theorem receipt_1_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 0) 128 253 = 39657107052519899113458362 :=
  phaseBlock_append receipt_1_6_2360_0_part1 receipt_1_6_2360_0_part2 rfl rfl rfl
private theorem receipt_1_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 0) 0 381 = 95765492976723542563453560 :=
  phaseBlock_append receipt_1_6_2360_0_part0 receipt_1_6_2360_0_join0 rfl rfl rfl

private theorem receipt_1_6_2360_0 : fastPhase (bank 1 6).shape 179808 2380 7 1 0 2 0 = 95765492976723542563453560 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2360_0_join1

private theorem receipt_1_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 1) 0 128 = 55894438468434823819446589 := by decide +kernel
private theorem receipt_1_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 1) 128 128 = 30370385541081504884525935 := by decide +kernel
private theorem receipt_1_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 1) 256 125 = 8956487262503817912975624 := by decide +kernel
private theorem receipt_1_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 1) 128 253 = 39326872803585322797501559 :=
  phaseBlock_append receipt_1_6_2360_1_part1 receipt_1_6_2360_1_part2 rfl rfl rfl
private theorem receipt_1_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179808 2380 7 1 0 2 1) 0 381 = 95221311272020146616948148 :=
  phaseBlock_append receipt_1_6_2360_1_part0 receipt_1_6_2360_1_join0 rfl rfl rfl

private theorem receipt_1_6_2360_1 : fastPhase (bank 1 6).shape 179808 2380 7 1 0 2 1 = 95221311272020146616948148 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2360_1_join1

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2359_0 receipt_1_6_2359_1 receipt_1_6_2360_0 receipt_1_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 0) 0 128 = 30446592124363841388049440 := by decide +kernel
private theorem receipt_2_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 0) 128 128 = 16338976432007447843202080 := by decide +kernel
private theorem receipt_2_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 0) 256 125 = 4804810802174462891902349 := by decide +kernel
private theorem receipt_2_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 0) 128 253 = 21143787234181910735104429 :=
  phaseBlock_append receipt_2_6_2359_0_part1 receipt_2_6_2359_0_part2 rfl rfl rfl
private theorem receipt_2_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 0) 0 381 = 51590379358545752123153869 :=
  phaseBlock_append receipt_2_6_2359_0_part0 receipt_2_6_2359_0_join0 rfl rfl rfl

private theorem receipt_2_6_2359_0 : fastPhase (bank 2 6).shape 179808 2379 7 1 0 7 0 = 51590379358545752123153869 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2359_0_join1

private theorem receipt_2_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 1) 0 128 = 30327027411310285275109280 := by decide +kernel
private theorem receipt_2_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 1) 128 128 = 16240054060076520204945312 := by decide +kernel
private theorem receipt_2_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 1) 256 125 = 4725969596475216018260030 := by decide +kernel
private theorem receipt_2_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 1) 128 253 = 20966023656551736223205342 :=
  phaseBlock_append receipt_2_6_2359_1_part1 receipt_2_6_2359_1_part2 rfl rfl rfl
private theorem receipt_2_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2379 7 1 0 7 1) 0 381 = 51293051067862021498314622 :=
  phaseBlock_append receipt_2_6_2359_1_part0 receipt_2_6_2359_1_join0 rfl rfl rfl

private theorem receipt_2_6_2359_1 : fastPhase (bank 2 6).shape 179808 2379 7 1 0 7 1 = 51293051067862021498314622 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2359_1_join1

private theorem receipt_2_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 0) 0 128 = 30446850713349788624723040 := by decide +kernel
private theorem receipt_2_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 0) 128 128 = 16339086064528769298476128 := by decide +kernel
private theorem receipt_2_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 0) 256 125 = 4804834413399600534658537 := by decide +kernel
private theorem receipt_2_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 0) 128 253 = 21143920477928369833134665 :=
  phaseBlock_append receipt_2_6_2360_0_part1 receipt_2_6_2360_0_part2 rfl rfl rfl
private theorem receipt_2_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 0) 0 381 = 51590771191278158457857705 :=
  phaseBlock_append receipt_2_6_2360_0_part0 receipt_2_6_2360_0_join0 rfl rfl rfl

private theorem receipt_2_6_2360_0 : fastPhase (bank 2 6).shape 179808 2380 7 1 0 7 0 = 51590771191278158457857705 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2360_0_join1

private theorem receipt_2_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 1) 0 128 = 30327285153383482307568992 := by decide +kernel
private theorem receipt_2_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 1) 128 128 = 16240163117905713846539616 := by decide +kernel
private theorem receipt_2_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 1) 256 125 = 4725992867009865737407824 := by decide +kernel
private theorem receipt_2_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 1) 128 253 = 20966155984915579583947440 :=
  phaseBlock_append receipt_2_6_2360_1_part1 receipt_2_6_2360_1_part2 rfl rfl rfl
private theorem receipt_2_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179808 2380 7 1 0 7 1) 0 381 = 51293441138299061891516432 :=
  phaseBlock_append receipt_2_6_2360_1_part0 receipt_2_6_2360_1_join0 rfl rfl rfl

private theorem receipt_2_6_2360_1 : fastPhase (bank 2 6).shape 179808 2380 7 1 0 7 1 = 51293441138299061891516432 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2360_1_join1

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2359_0 receipt_2_6_2359_1 receipt_2_6_2360_0 receipt_2_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 0 128 = 5915113518768465222259296 := by decide +kernel
private theorem receipt_3_6_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 128 128 = 3264672466991972002103904 := by decide +kernel
private theorem receipt_3_6_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 256 128 = 1084338905187199980843616 := by decide +kernel
private theorem receipt_3_6_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 384 12 = 7802859054163407575159 := by decide +kernel
private theorem receipt_3_6_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 0 256 = 9179785985760437224363200 :=
  phaseBlock_append receipt_3_6_2359_0_part0 receipt_3_6_2359_0_part1 rfl rfl rfl
private theorem receipt_3_6_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 256 140 = 1092141764241363388418775 :=
  phaseBlock_append receipt_3_6_2359_0_part2 receipt_3_6_2359_0_part3 rfl rfl rfl
private theorem receipt_3_6_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 0) 0 396 = 10271927750001800612781975 :=
  phaseBlock_append receipt_3_6_2359_0_join0 receipt_3_6_2359_0_join1 rfl rfl rfl

private theorem receipt_3_6_2359_0 : fastPhase (bank 3 6).shape 179808 2379 7 1 1 1 0 = 10271927750001800612781975 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2359_0_join2

private theorem receipt_3_6_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 0 128 = 5892951876874369602515616 := by decide +kernel
private theorem receipt_3_6_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 128 128 = 3245904064494188946006688 := by decide +kernel
private theorem receipt_3_6_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 256 128 = 1069306497783072731615904 := by decide +kernel
private theorem receipt_3_6_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 384 12 = 6597113976590178202733 := by decide +kernel
private theorem receipt_3_6_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 0 256 = 9138855941368558548522304 :=
  phaseBlock_append receipt_3_6_2359_1_part0 receipt_3_6_2359_1_part1 rfl rfl rfl
private theorem receipt_3_6_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 256 140 = 1075903611759662909818637 :=
  phaseBlock_append receipt_3_6_2359_1_part2 receipt_3_6_2359_1_part3 rfl rfl rfl
private theorem receipt_3_6_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2379 7 1 1 1 1) 0 396 = 10214759553128221458340941 :=
  phaseBlock_append receipt_3_6_2359_1_join0 receipt_3_6_2359_1_join1 rfl rfl rfl

private theorem receipt_3_6_2359_1 : fastPhase (bank 3 6).shape 179808 2379 7 1 1 1 1 = 10214759553128221458340941 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2359_1_join2

private theorem receipt_3_6_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 0 128 = 5915160835596104113713504 := by decide +kernel
private theorem receipt_3_6_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 128 128 = 3264689518243732173627744 := by decide +kernel
private theorem receipt_3_6_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 256 128 = 1084341905386316008935776 := by decide +kernel
private theorem receipt_3_6_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 384 12 = 7802866953620964586543 := by decide +kernel
private theorem receipt_3_6_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 0 256 = 9179850353839836287341248 :=
  phaseBlock_append receipt_3_6_2360_0_part0 receipt_3_6_2360_0_part1 rfl rfl rfl
private theorem receipt_3_6_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 256 140 = 1092144772339936973522319 :=
  phaseBlock_append receipt_3_6_2360_0_part2 receipt_3_6_2360_0_part3 rfl rfl rfl
private theorem receipt_3_6_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 0) 0 396 = 10271995126179773260863567 :=
  phaseBlock_append receipt_3_6_2360_0_join0 receipt_3_6_2360_0_join1 rfl rfl rfl

private theorem receipt_3_6_2360_0 : fastPhase (bank 3 6).shape 179808 2380 7 1 1 1 0 = 10271995126179773260863567 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2360_0_join2

private theorem receipt_3_6_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 0 128 = 5892998992015891617947616 := by decide +kernel
private theorem receipt_3_6_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 128 128 = 3245921008347513778745312 := by decide +kernel
private theorem receipt_3_6_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 256 128 = 1069309458224006716866528 := by decide +kernel
private theorem receipt_3_6_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 384 12 = 6597120682346758709431 := by decide +kernel
private theorem receipt_3_6_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 0 256 = 9138920000363405396692928 :=
  phaseBlock_append receipt_3_6_2360_1_part0 receipt_3_6_2360_1_part1 rfl rfl rfl
private theorem receipt_3_6_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 256 140 = 1075906578906353475575959 :=
  phaseBlock_append receipt_3_6_2360_1_part2 receipt_3_6_2360_1_part3 rfl rfl rfl
private theorem receipt_3_6_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179808 2380 7 1 1 1 1) 0 396 = 10214826579269758872268887 :=
  phaseBlock_append receipt_3_6_2360_1_join0 receipt_3_6_2360_1_join1 rfl rfl rfl

private theorem receipt_3_6_2360_1 : fastPhase (bank 3 6).shape 179808 2380 7 1 1 1 1 = 10214826579269758872268887 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2360_1_join2

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2359_0 receipt_3_6_2359_1 receipt_3_6_2360_0 receipt_3_6_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 0 128 = 151074754664878900466217152 := by decide +kernel
private theorem receipt_0_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 128 128 = 97509412592204560804761792 := by decide +kernel
private theorem receipt_0_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 256 128 = 50602939055591618043116799 := by decide +kernel
private theorem receipt_0_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 384 97 = 10928505655069683721970011 := by decide +kernel
private theorem receipt_0_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 0 256 = 248584167257083461270978944 :=
  phaseBlock_append receipt_0_7_2359_0_part0 receipt_0_7_2359_0_part1 rfl rfl rfl
private theorem receipt_0_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 256 225 = 61531444710661301765086810 :=
  phaseBlock_append receipt_0_7_2359_0_part2 receipt_0_7_2359_0_part3 rfl rfl rfl
private theorem receipt_0_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 0) 0 481 = 310115611967744763036065754 :=
  phaseBlock_append receipt_0_7_2359_0_join0 receipt_0_7_2359_0_join1 rfl rfl rfl

private theorem receipt_0_7_2359_0 : fastPhase (bank 0 7).shape 179808 2379 10 1 0 1 0 = 310115611967744763036065754 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2359_0_join2

private theorem receipt_0_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 0 128 = 150634782737216914490802240 := by decide +kernel
private theorem receipt_0_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 128 128 = 97121380591713828244176960 := by decide +kernel
private theorem receipt_0_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 256 128 = 50263495788268062722149675 := by decide +kernel
private theorem receipt_0_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 384 97 = 10701593330542592650255759 := by decide +kernel
private theorem receipt_0_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 0 256 = 247756163328930742734979200 :=
  phaseBlock_append receipt_0_7_2359_1_part0 receipt_0_7_2359_1_part1 rfl rfl rfl
private theorem receipt_0_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 256 225 = 60965089118810655372405434 :=
  phaseBlock_append receipt_0_7_2359_1_part2 receipt_0_7_2359_1_part3 rfl rfl rfl
private theorem receipt_0_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2379 10 1 0 1 1) 0 481 = 308721252447741398107384634 :=
  phaseBlock_append receipt_0_7_2359_1_join0 receipt_0_7_2359_1_join1 rfl rfl rfl

private theorem receipt_0_7_2359_1 : fastPhase (bank 0 7).shape 179808 2379 10 1 0 1 1 = 308721252447741398107384634 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2359_1_join2

private theorem receipt_0_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 0 128 = 151076059024561962467731072 := by decide +kernel
private theorem receipt_0_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 128 128 = 97510117757677123909256832 := by decide +kernel
private theorem receipt_0_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 256 128 = 50603229092040453500476794 := by decide +kernel
private theorem receipt_0_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 384 97 = 10928553120710360502060460 := by decide +kernel
private theorem receipt_0_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 0 256 = 248586176782239086376987904 :=
  phaseBlock_append receipt_0_7_2360_0_part0 receipt_0_7_2360_0_part1 rfl rfl rfl
private theorem receipt_0_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 256 225 = 61531782212750814002537254 :=
  phaseBlock_append receipt_0_7_2360_0_part2 receipt_0_7_2360_0_part3 rfl rfl rfl
private theorem receipt_0_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 0) 0 481 = 310117958994989900379525158 :=
  phaseBlock_append receipt_0_7_2360_0_join0 receipt_0_7_2360_0_join1 rfl rfl rfl

private theorem receipt_0_7_2360_0 : fastPhase (bank 0 7).shape 179808 2380 10 1 0 1 0 = 310117958994989900379525158 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2360_0_join2

private theorem receipt_0_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 0 128 = 150636083956235683283311680 := by decide +kernel
private theorem receipt_0_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 128 128 = 97122083358146547695295552 := by decide +kernel
private theorem receipt_0_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 256 128 = 50263784097380506652333282 := by decide +kernel
private theorem receipt_0_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 384 97 = 10701639894755717241169678 := by decide +kernel
private theorem receipt_0_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 0 256 = 247758167314382230978607232 :=
  phaseBlock_append receipt_0_7_2360_1_part0 receipt_0_7_2360_1_part1 rfl rfl rfl
private theorem receipt_0_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 256 225 = 60965423992136223893502960 :=
  phaseBlock_append receipt_0_7_2360_1_part2 receipt_0_7_2360_1_part3 rfl rfl rfl
private theorem receipt_0_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179808 2380 10 1 0 1 1) 0 481 = 308723591306518454872110192 :=
  phaseBlock_append receipt_0_7_2360_1_join0 receipt_0_7_2360_1_join1 rfl rfl rfl

private theorem receipt_0_7_2360_1 : fastPhase (bank 0 7).shape 179808 2380 10 1 0 1 1 = 308723591306518454872110192 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2360_1_join2

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2359_0 receipt_0_7_2359_1 receipt_0_7_2360_0 receipt_0_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 0 128 = 135899381849906715487996640 := by decide +kernel
private theorem receipt_1_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 128 128 = 87546154911288542513765088 := by decide +kernel
private theorem receipt_1_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 256 128 = 45346524922322782988992980 := by decide +kernel
private theorem receipt_1_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 384 97 = 9777548348017357106398788 := by decide +kernel
private theorem receipt_1_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 0 256 = 223445536761195258001761728 :=
  phaseBlock_append receipt_1_7_2359_0_part0 receipt_1_7_2359_0_part1 rfl rfl rfl
private theorem receipt_1_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 256 225 = 55124073270340140095391768 :=
  phaseBlock_append receipt_1_7_2359_0_part2 receipt_1_7_2359_0_part3 rfl rfl rfl
private theorem receipt_1_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 0) 0 481 = 278569610031535398097153496 :=
  phaseBlock_append receipt_1_7_2359_0_join0 receipt_1_7_2359_0_join1 rfl rfl rfl

private theorem receipt_1_7_2359_0 : fastPhase (bank 1 7).shape 179808 2379 10 1 0 2 0 = 278569610031535398097153496 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2359_0_join2

private theorem receipt_1_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 0 128 = 135501565032905818037329376 := by decide +kernel
private theorem receipt_1_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 128 128 = 87196466018726094480068064 := by decide +kernel
private theorem receipt_1_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 256 128 = 45041690317125017078266155 := by decide +kernel
private theorem receipt_1_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 384 97 = 9574435212188440802903439 := by decide +kernel
private theorem receipt_1_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 0 256 = 222698031051631912517397440 :=
  phaseBlock_append receipt_1_7_2359_1_part0 receipt_1_7_2359_1_part1 rfl rfl rfl
private theorem receipt_1_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 256 225 = 54616125529313457881169594 :=
  phaseBlock_append receipt_1_7_2359_1_part2 receipt_1_7_2359_1_part3 rfl rfl rfl
private theorem receipt_1_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2379 10 1 0 2 1) 0 481 = 277314156580945370398567034 :=
  phaseBlock_append receipt_1_7_2359_1_join0 receipt_1_7_2359_1_join1 rfl rfl rfl

private theorem receipt_1_7_2359_1 : fastPhase (bank 1 7).shape 179808 2379 10 1 0 2 1 = 277314156580945370398567034 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2359_1_join2

private theorem receipt_1_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 0 128 = 135900555217071386540326240 := by decide +kernel
private theorem receipt_1_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 128 128 = 87546788045412237755657568 := by decide +kernel
private theorem receipt_1_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 256 128 = 45346784842384642597400835 := by decide +kernel
private theorem receipt_1_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 384 97 = 9777590815795881871657254 := by decide +kernel
private theorem receipt_1_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 0 256 = 223447343262483624295983808 :=
  phaseBlock_append receipt_1_7_2360_0_part0 receipt_1_7_2360_0_part1 rfl rfl rfl
private theorem receipt_1_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 256 225 = 55124375658180524469058089 :=
  phaseBlock_append receipt_1_7_2360_0_part2 receipt_1_7_2360_0_part3 rfl rfl rfl
private theorem receipt_1_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 0) 0 481 = 278571718920664148765041897 :=
  phaseBlock_append receipt_1_7_2360_0_join0 receipt_1_7_2360_0_join1 rfl rfl rfl

private theorem receipt_1_7_2360_0 : fastPhase (bank 1 7).shape 179808 2380 10 1 0 2 0 = 278571718920664148765041897 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2360_0_join2

private theorem receipt_1_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 0 128 = 135502735557181798969978528 := by decide +kernel
private theorem receipt_1_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 128 128 = 87197096989414406693772960 := by decide +kernel
private theorem receipt_1_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 256 128 = 45041948685461426565173922 := by decide +kernel
private theorem receipt_1_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 384 97 = 9574476873002555735813754 := by decide +kernel
private theorem receipt_1_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 0 256 = 222699832546596205663751488 :=
  phaseBlock_append receipt_1_7_2360_1_part0 receipt_1_7_2360_1_part1 rfl rfl rfl
private theorem receipt_1_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 256 225 = 54616425558463982300987676 :=
  phaseBlock_append receipt_1_7_2360_1_part2 receipt_1_7_2360_1_part3 rfl rfl rfl
private theorem receipt_1_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179808 2380 10 1 0 2 1) 0 481 = 277316258105060187964739164 :=
  phaseBlock_append receipt_1_7_2360_1_join0 receipt_1_7_2360_1_join1 rfl rfl rfl

private theorem receipt_1_7_2360_1 : fastPhase (bank 1 7).shape 179808 2380 10 1 0 2 1 = 277316258105060187964739164 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2360_1_join2

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2359_0 receipt_1_7_2359_1 receipt_1_7_2360_0 receipt_1_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 0 128 = 72503326449037693835274272 := by decide +kernel
private theorem receipt_2_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 128 128 = 46060797833688888155183136 := by decide +kernel
private theorem receipt_2_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 256 128 = 23530851589034540848546248 := by decide +kernel
private theorem receipt_2_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 384 97 = 5013989446695801095243592 := by decide +kernel
private theorem receipt_2_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 0 256 = 118564124282726581990457408 :=
  phaseBlock_append receipt_2_7_2359_0_part0 receipt_2_7_2359_0_part1 rfl rfl rfl
private theorem receipt_2_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 256 225 = 28544841035730341943789840 :=
  phaseBlock_append receipt_2_7_2359_0_part2 receipt_2_7_2359_0_part3 rfl rfl rfl
private theorem receipt_2_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 0) 0 481 = 147108965318456923934247248 :=
  phaseBlock_append receipt_2_7_2359_0_join0 receipt_2_7_2359_0_join1 rfl rfl rfl

private theorem receipt_2_7_2359_0 : fastPhase (bank 2 7).shape 179808 2379 10 1 0 7 0 = 147108965318456923934247248 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2359_0_join2

private theorem receipt_2_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 0 128 = 72283240203625655143248608 := by decide +kernel
private theorem receipt_2_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 128 128 = 45871824633014346742391520 := by decide +kernel
private theorem receipt_2_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 256 128 = 23370193431524778013161825 := by decide +kernel
private theorem receipt_2_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 384 97 = 4909458853083391966297653 := by decide +kernel
private theorem receipt_2_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 0 256 = 118155064836640001885640128 :=
  phaseBlock_append receipt_2_7_2359_1_part0 receipt_2_7_2359_1_part1 rfl rfl rfl
private theorem receipt_2_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 256 225 = 28279652284608169979459478 :=
  phaseBlock_append receipt_2_7_2359_1_part2 receipt_2_7_2359_1_part3 rfl rfl rfl
private theorem receipt_2_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2379 10 1 0 7 1) 0 481 = 146434717121248171865099606 :=
  phaseBlock_append receipt_2_7_2359_1_join0 receipt_2_7_2359_1_join1 rfl rfl rfl

private theorem receipt_2_7_2359_1 : fastPhase (bank 2 7).shape 179808 2379 10 1 0 7 1 = 146434717121248171865099606 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2359_1_join2

private theorem receipt_2_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 0 128 = 72503952563233293779811712 := by decide +kernel
private theorem receipt_2_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 128 128 = 46061131024403548353518976 := by decide +kernel
private theorem receipt_2_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 256 128 = 23530986507757445440329651 := by decide +kernel
private theorem receipt_2_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 384 97 = 5014011228513599715105147 := by decide +kernel
private theorem receipt_2_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 0 256 = 118565083587636842133330688 :=
  phaseBlock_append receipt_2_7_2360_0_part0 receipt_2_7_2360_0_part1 rfl rfl rfl
private theorem receipt_2_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 256 225 = 28544997736271045155434798 :=
  phaseBlock_append receipt_2_7_2360_0_part2 receipt_2_7_2360_0_part3 rfl rfl rfl
private theorem receipt_2_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 0) 0 481 = 147110081323907887288765486 :=
  phaseBlock_append receipt_2_7_2360_0_join0 receipt_2_7_2360_0_join1 rfl rfl rfl

private theorem receipt_2_7_2360_0 : fastPhase (bank 2 7).shape 179808 2380 10 1 0 7 0 = 147110081323907887288765486 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2360_0_join2

private theorem receipt_2_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 0 128 = 72283864733003837506636864 := by decide +kernel
private theorem receipt_2_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 128 128 = 45872156649051859426331712 := by decide +kernel
private theorem receipt_2_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 256 128 = 23370327530523852660217998 := by decide +kernel
private theorem receipt_2_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 384 97 = 4909480219296646310557434 := by decide +kernel
private theorem receipt_2_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 0 256 = 118156021382055696932968576 :=
  phaseBlock_append receipt_2_7_2360_1_part0 receipt_2_7_2360_1_part1 rfl rfl rfl
private theorem receipt_2_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 256 225 = 28279807749820498970775432 :=
  phaseBlock_append receipt_2_7_2360_1_part2 receipt_2_7_2360_1_part3 rfl rfl rfl
private theorem receipt_2_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179808 2380 10 1 0 7 1) 0 481 = 146435829131876195903744008 :=
  phaseBlock_append receipt_2_7_2360_1_join0 receipt_2_7_2360_1_join1 rfl rfl rfl

private theorem receipt_2_7_2360_1 : fastPhase (bank 2 7).shape 179808 2380 10 1 0 7 1 = 146435829131876195903744008 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2360_1_join2

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2359_0 receipt_2_7_2359_1 receipt_2_7_2360_0 receipt_2_7_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 0 128 = 17706104493420944138518112 := by decide +kernel
private theorem receipt_3_7_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 128 128 = 11493297207173203577900640 := by decide +kernel
private theorem receipt_3_7_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 256 128 = 6103648227532667766038112 := by decide +kernel
private theorem receipt_3_7_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 384 115 = 1611056348015388012881961 := by decide +kernel
private theorem receipt_3_7_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 0 256 = 29199401700594147716418752 :=
  phaseBlock_append receipt_3_7_2359_0_part0 receipt_3_7_2359_0_part1 rfl rfl rfl
private theorem receipt_3_7_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 256 243 = 7714704575548055778920073 :=
  phaseBlock_append receipt_3_7_2359_0_part2 receipt_3_7_2359_0_part3 rfl rfl rfl
private theorem receipt_3_7_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 0) 0 499 = 36914106276142203495338825 :=
  phaseBlock_append receipt_3_7_2359_0_join0 receipt_3_7_2359_0_join1 rfl rfl rfl

private theorem receipt_3_7_2359_0 : fastPhase (bank 3 7).shape 179808 2379 10 1 1 1 0 = 36914106276142203495338825 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2359_0_join2

private theorem receipt_3_7_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 0 128 = 17655148494153903177414176 := by decide +kernel
private theorem receipt_3_7_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 128 128 = 11448320611351232373736992 := by decide +kernel
private theorem receipt_3_7_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 256 128 = 6065136516895764368676384 := by decide +kernel
private theorem receipt_3_7_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 384 115 = 1582360211529365555442948 := by decide +kernel
private theorem receipt_3_7_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 0 256 = 29103469105505135551151168 :=
  phaseBlock_append receipt_3_7_2359_1_part0 receipt_3_7_2359_1_part1 rfl rfl rfl
private theorem receipt_3_7_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 256 243 = 7647496728425129924119332 :=
  phaseBlock_append receipt_3_7_2359_1_part2 receipt_3_7_2359_1_part3 rfl rfl rfl
private theorem receipt_3_7_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2379 10 1 1 1 1) 0 499 = 36750965833930265475270500 :=
  phaseBlock_append receipt_3_7_2359_1_join0 receipt_3_7_2359_1_join1 rfl rfl rfl

private theorem receipt_3_7_2359_1 : fastPhase (bank 3 7).shape 179808 2379 10 1 1 1 1 = 36750965833930265475270500 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2359_1_join2

private theorem receipt_3_7_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 0 128 = 17706250376104620124688608 := by decide +kernel
private theorem receipt_3_7_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 128 128 = 11493366089996660158406880 := by decide +kernel
private theorem receipt_3_7_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 256 128 = 6103671890998887707767008 := by decide +kernel
private theorem receipt_3_7_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 384 115 = 1611059693097436809630429 := by decide +kernel
private theorem receipt_3_7_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 0 256 = 29199616466101280283095488 :=
  phaseBlock_append receipt_3_7_2360_0_part0 receipt_3_7_2360_0_part1 rfl rfl rfl
private theorem receipt_3_7_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 256 243 = 7714731584096324517397437 :=
  phaseBlock_append receipt_3_7_2360_0_part2 receipt_3_7_2360_0_part3 rfl rfl rfl
private theorem receipt_3_7_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 0) 0 499 = 36914348050197604800492925 :=
  phaseBlock_append receipt_3_7_2360_0_join0 receipt_3_7_2360_0_join1 rfl rfl rfl

private theorem receipt_3_7_2360_0 : fastPhase (bank 3 7).shape 179808 2380 10 1 1 1 0 = 36914348050197604800492925 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2360_0_join2

private theorem receipt_3_7_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 0 128 = 17655293896254992300452768 := by decide +kernel
private theorem receipt_3_7_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 128 128 = 11448389192788808928082848 := by decide +kernel
private theorem receipt_3_7_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 256 128 = 6065160019874521592318880 := by decide +kernel
private theorem receipt_3_7_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 384 115 = 1582363501695048797672844 := by decide +kernel
private theorem receipt_3_7_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 0 256 = 29103683089043801228535616 :=
  phaseBlock_append receipt_3_7_2360_1_part0 receipt_3_7_2360_1_part1 rfl rfl rfl
private theorem receipt_3_7_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 256 243 = 7647523521569570389991724 :=
  phaseBlock_append receipt_3_7_2360_1_part2 receipt_3_7_2360_1_part3 rfl rfl rfl
private theorem receipt_3_7_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179808 2380 10 1 1 1 1) 0 499 = 36751206610613371618527340 :=
  phaseBlock_append receipt_3_7_2360_1_join0 receipt_3_7_2360_1_join1 rfl rfl rfl

private theorem receipt_3_7_2360_1 : fastPhase (bank 3 7).shape 179808 2380 10 1 1 1 1 = 36751206610613371618527340 :=
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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group2_stage i)).shape
      (cutoff h rect (group2_stage i)), ¬ G∣Q :=
  (group2_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group2_avoids

end Lower6960.RescueSource
