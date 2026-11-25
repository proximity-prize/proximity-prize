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

private theorem receipt_0_5_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 0) 0 128 = 32145369434481166886848800 := by decide +kernel
private theorem receipt_0_5_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 0) 128 128 = 16470526822546579836574269 := by decide +kernel
private theorem receipt_0_5_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 0) 256 101 = 3680212792810398987206391 := by decide +kernel
private theorem receipt_0_5_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 0) 128 229 = 20150739615356978823780660 :=
  phaseBlock_append receipt_0_5_2402_0_part1 receipt_0_5_2402_0_part2 rfl rfl rfl
private theorem receipt_0_5_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 0) 0 357 = 52296109049838145710629460 :=
  phaseBlock_append receipt_0_5_2402_0_part0 receipt_0_5_2402_0_join0 rfl rfl rfl

private theorem receipt_0_5_2402_0 : fastPhase (bank 0 5).shape 179798 2402 5 1 0 1 0 = 52296109049838145710629460 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2402_0_join1

private theorem receipt_0_5_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 1) 0 128 = 32013590561371392917774880 := by decide +kernel
private theorem receipt_0_5_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 1) 128 128 = 16359675043314283863145488 := by decide +kernel
private theorem receipt_0_5_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 1) 256 101 = 3606297134269452494264196 := by decide +kernel
private theorem receipt_0_5_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 1) 128 229 = 19965972177583736357409684 :=
  phaseBlock_append receipt_0_5_2402_1_part1 receipt_0_5_2402_1_part2 rfl rfl rfl
private theorem receipt_0_5_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2402 5 1 0 1 1) 0 357 = 51979562738955129275184564 :=
  phaseBlock_append receipt_0_5_2402_1_part0 receipt_0_5_2402_1_join0 rfl rfl rfl

private theorem receipt_0_5_2402_1 : fastPhase (bank 0 5).shape 179798 2402 5 1 0 1 1 = 51979562738955129275184564 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2402_1_join1

private theorem receipt_0_5_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 0) 0 128 = 32145642135402775490892160 := by decide +kernel
private theorem receipt_0_5_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 0) 128 128 = 16470635183223701994007793 := by decide +kernel
private theorem receipt_0_5_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 0) 256 101 = 3680230285081879008700038 := by decide +kernel
private theorem receipt_0_5_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 0) 128 229 = 20150865468305581002707831 :=
  phaseBlock_append receipt_0_5_2403_0_part1 receipt_0_5_2403_0_part2 rfl rfl rfl
private theorem receipt_0_5_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 0) 0 357 = 52296507603708356493599991 :=
  phaseBlock_append receipt_0_5_2403_0_part0 receipt_0_5_2403_0_join0 rfl rfl rfl

private theorem receipt_0_5_2403_0 : fastPhase (bank 0 5).shape 179798 2403 5 1 0 1 0 = 52296507603708356493599991 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2403_0_join1

private theorem receipt_0_5_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 1) 0 128 = 32013862335460445492524800 := by decide +kernel
private theorem receipt_0_5_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 1) 128 128 = 16359782773182124215847664 := by decide +kernel
private theorem receipt_0_5_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 1) 256 101 = 3606314313431128282639416 := by decide +kernel
private theorem receipt_0_5_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 1) 128 229 = 19966097086613252498487080 :=
  phaseBlock_append receipt_0_5_2403_1_part1 receipt_0_5_2403_1_part2 rfl rfl rfl
private theorem receipt_0_5_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179798 2403 5 1 0 1 1) 0 357 = 51979959422073697991011880 :=
  phaseBlock_append receipt_0_5_2403_1_part0 receipt_0_5_2403_1_join0 rfl rfl rfl

private theorem receipt_0_5_2403_1 : fastPhase (bank 0 5).shape 179798 2403 5 1 0 1 1 = 51979959422073697991011880 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2403_1_join1

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2402_0 receipt_0_5_2402_1 receipt_0_5_2403_0 receipt_0_5_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 0) 0 128 = 28910046122375818331467104 := by decide +kernel
private theorem receipt_1_5_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 0) 128 128 = 14775263309266984916285869 := by decide +kernel
private theorem receipt_1_5_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 0) 256 101 = 3294218601847094712442346 := by decide +kernel
private theorem receipt_1_5_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 0) 128 229 = 18069481911114079628728215 :=
  phaseBlock_append receipt_1_5_2402_0_part1 receipt_1_5_2402_0_part2 rfl rfl rfl
private theorem receipt_1_5_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 0) 0 357 = 46979528033489897960195319 :=
  phaseBlock_append receipt_1_5_2402_0_part0 receipt_1_5_2402_0_join0 rfl rfl rfl

private theorem receipt_1_5_2402_0 : fastPhase (bank 1 5).shape 179798 2402 5 1 0 2 0 = 46979528033489897960195319 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2402_0_join1

private theorem receipt_1_5_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 1) 0 128 = 28790953207560714388328416 := by decide +kernel
private theorem receipt_1_5_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 1) 128 128 = 14675536057737121072214074 := by decide +kernel
private theorem receipt_1_5_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 1) 256 101 = 3228010766357029353986019 := by decide +kernel
private theorem receipt_1_5_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 1) 128 229 = 17903546824094150426200093 :=
  phaseBlock_append receipt_1_5_2402_1_part1 receipt_1_5_2402_1_part2 rfl rfl rfl
private theorem receipt_1_5_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2402 5 1 0 2 1) 0 357 = 46694500031654864814528509 :=
  phaseBlock_append receipt_1_5_2402_1_part0 receipt_1_5_2402_1_join0 rfl rfl rfl

private theorem receipt_1_5_2402_1 : fastPhase (bank 1 5).shape 179798 2402 5 1 0 2 1 = 46694500031654864814528509 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2402_1_join1

private theorem receipt_1_5_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 0) 0 128 = 28910291388300827977229376 := by decide +kernel
private theorem receipt_1_5_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 0) 128 128 = 14775360523026877845019653 := by decide +kernel
private theorem receipt_1_5_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 0) 256 101 = 3294234260160840498190678 := by decide +kernel
private theorem receipt_1_5_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 0) 128 229 = 18069594783187718343210331 :=
  phaseBlock_append receipt_1_5_2403_0_part1 receipt_1_5_2403_0_part2 rfl rfl rfl
private theorem receipt_1_5_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 0) 0 357 = 46979886171488546320439707 :=
  phaseBlock_append receipt_1_5_2403_0_part0 receipt_1_5_2403_0_join0 rfl rfl rfl

private theorem receipt_1_5_2403_0 : fastPhase (bank 1 5).shape 179798 2403 5 1 0 2 0 = 46979886171488546320439707 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2403_0_join1

private theorem receipt_1_5_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 1) 0 128 = 28791197634990899765821824 := by decide +kernel
private theorem receipt_1_5_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 1) 128 128 = 14675632703692361850883378 := by decide +kernel
private theorem receipt_1_5_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 1) 256 101 = 3228026144160748307998716 := by decide +kernel
private theorem receipt_1_5_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 1) 128 229 = 17903658847853110158882094 :=
  phaseBlock_append receipt_1_5_2403_1_part1 receipt_1_5_2403_1_part2 rfl rfl rfl
private theorem receipt_1_5_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179798 2403 5 1 0 2 1) 0 357 = 46694856482844009924703918 :=
  phaseBlock_append receipt_1_5_2403_1_part0 receipt_1_5_2403_1_join0 rfl rfl rfl

private theorem receipt_1_5_2403_1 : fastPhase (bank 1 5).shape 179798 2403 5 1 0 2 1 = 46694856482844009924703918 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2403_1_join1

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2402_0 receipt_1_5_2402_1 receipt_1_5_2403_0 receipt_1_5_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 0) 0 128 = 15400010442402046252631424 := by decide +kernel
private theorem receipt_2_5_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 0) 128 128 = 7726925893031937357967074 := by decide +kernel
private theorem receipt_2_5_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 0) 256 101 = 1695406203060667328407257 := by decide +kernel
private theorem receipt_2_5_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 0) 128 229 = 9422332096092604686374331 :=
  phaseBlock_append receipt_2_5_2402_0_part1 receipt_2_5_2402_0_part2 rfl rfl rfl
private theorem receipt_2_5_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 0) 0 357 = 24822342538494650939005755 :=
  phaseBlock_append receipt_2_5_2402_0_part0 receipt_2_5_2402_0_join0 rfl rfl rfl

private theorem receipt_2_5_2402_0 : fastPhase (bank 2 5).shape 179798 2402 5 1 0 7 0 = 24822342538494650939005755 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2402_0_join1

private theorem receipt_2_5_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 1) 0 128 = 15334352165039567399212800 := by decide +kernel
private theorem receipt_2_5_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 1) 128 128 = 7673684546865695868186690 := by decide +kernel
private theorem receipt_2_5_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 1) 256 101 = 1661162071883275762778379 := by decide +kernel
private theorem receipt_2_5_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 1) 128 229 = 9334846618748971630965069 :=
  phaseBlock_append receipt_2_5_2402_1_part1 receipt_2_5_2402_1_part2 rfl rfl rfl
private theorem receipt_2_5_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2402 5 1 0 7 1) 0 357 = 24669198783788539030177869 :=
  phaseBlock_append receipt_2_5_2402_1_part0 receipt_2_5_2402_1_join0 rfl rfl rfl

private theorem receipt_2_5_2402_1 : fastPhase (bank 2 5).shape 179798 2402 5 1 0 7 1 = 24669198783788539030177869 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2402_1_join1

private theorem receipt_2_5_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 0) 0 128 = 15400141136361499078959040 := by decide +kernel
private theorem receipt_2_5_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 0) 128 128 = 7726976756441186406123710 := by decide +kernel
private theorem receipt_2_5_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 0) 256 101 = 1695414264419853800070156 := by decide +kernel
private theorem receipt_2_5_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 0) 128 229 = 9422391020861040206193866 :=
  phaseBlock_append receipt_2_5_2403_0_part1 receipt_2_5_2403_0_part2 rfl rfl rfl
private theorem receipt_2_5_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 0) 0 357 = 24822532157222539285152906 :=
  phaseBlock_append receipt_2_5_2403_0_part0 receipt_2_5_2403_0_join0 rfl rfl rfl

private theorem receipt_2_5_2403_0 : fastPhase (bank 2 5).shape 179798 2403 5 1 0 7 0 = 24822532157222539285152906 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2403_0_join1

private theorem receipt_2_5_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 1) 0 128 = 15334482393327919778524800 := by decide +kernel
private theorem receipt_2_5_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 1) 128 128 = 7673735105997477676519994 := by decide +kernel
private theorem receipt_2_5_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 1) 256 101 = 1661169987963829024983228 := by decide +kernel
private theorem receipt_2_5_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 1) 128 229 = 9334905093961306701503222 :=
  phaseBlock_append receipt_2_5_2403_1_part1 receipt_2_5_2403_1_part2 rfl rfl rfl
private theorem receipt_2_5_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179798 2403 5 1 0 7 1) 0 357 = 24669387487289226480028022 :=
  phaseBlock_append receipt_2_5_2403_1_part0 receipt_2_5_2403_1_join0 rfl rfl rfl

private theorem receipt_2_5_2403_1 : fastPhase (bank 2 5).shape 179798 2403 5 1 0 7 1 = 24669387487289226480028022 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2403_1_join1

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2402_0 receipt_2_5_2402_1 receipt_2_5_2403_0 receipt_2_5_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 0) 0 128 = 3796952755176549475200288 := by decide +kernel
private theorem receipt_3_5_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 0) 128 128 = 1972793462170202779180320 := by decide +kernel
private theorem receipt_3_5_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 0) 256 115 = 507043950635690262146259 := by decide +kernel
private theorem receipt_3_5_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 0) 128 243 = 2479837412805893041326579 :=
  phaseBlock_append receipt_3_5_2402_0_part1 receipt_3_5_2402_0_part2 rfl rfl rfl
private theorem receipt_3_5_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 0) 0 371 = 6276790167982442516526867 :=
  phaseBlock_append receipt_3_5_2402_0_part0 receipt_3_5_2402_0_join0 rfl rfl rfl

private theorem receipt_3_5_2402_0 : fastPhase (bank 3 5).shape 179798 2402 5 1 1 1 0 = 6276790167982442516526867 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2402_0_join1

private theorem receipt_3_5_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 1) 0 128 = 3781595918862920437361568 := by decide +kernel
private theorem receipt_3_5_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 1) 128 128 = 1959982229970165534931872 := by decide +kernel
private theorem receipt_3_5_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 1) 256 115 = 497925476198867815165620 := by decide +kernel
private theorem receipt_3_5_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 1) 128 243 = 2457907706169033350097492 :=
  phaseBlock_append receipt_3_5_2402_1_part1 receipt_3_5_2402_1_part2 rfl rfl rfl
private theorem receipt_3_5_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2402 5 1 1 1 1) 0 371 = 6239503625031953787459060 :=
  phaseBlock_append receipt_3_5_2402_1_part0 receipt_3_5_2402_1_join0 rfl rfl rfl

private theorem receipt_3_5_2402_1 : fastPhase (bank 3 5).shape 179798 2402 5 1 1 1 1 = 6239503625031953787459060 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2402_1_join1

private theorem receipt_3_5_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 0) 0 128 = 3796982978230537535711424 := by decide +kernel
private theorem receipt_3_5_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 0) 128 128 = 1972803363076870474328256 := by decide +kernel
private theorem receipt_3_5_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 0) 256 115 = 507045243277473139700790 := by decide +kernel
private theorem receipt_3_5_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 0) 128 243 = 2479848606354343614029046 :=
  phaseBlock_append receipt_3_5_2403_0_part1 receipt_3_5_2403_0_part2 rfl rfl rfl
private theorem receipt_3_5_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 0) 0 371 = 6276831584584881149740470 :=
  phaseBlock_append receipt_3_5_2403_0_part0 receipt_3_5_2403_0_join0 rfl rfl rfl

private theorem receipt_3_5_2403_0 : fastPhase (bank 3 5).shape 179798 2403 5 1 1 1 0 = 6276831584584881149740470 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2403_0_join1

private theorem receipt_3_5_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 1) 0 128 = 3781626003214466718234048 := by decide +kernel
private theorem receipt_3_5_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 1) 128 128 = 1959992061093382059718080 := by decide +kernel
private theorem receipt_3_5_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 1) 256 115 = 497926747494527632439844 := by decide +kernel
private theorem receipt_3_5_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 1) 128 243 = 2457918808587909692157924 :=
  phaseBlock_append receipt_3_5_2403_1_part1 receipt_3_5_2403_1_part2 rfl rfl rfl
private theorem receipt_3_5_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179798 2403 5 1 1 1 1) 0 371 = 6239544811802376410391972 :=
  phaseBlock_append receipt_3_5_2403_1_part0 receipt_3_5_2403_1_join0 rfl rfl rfl

private theorem receipt_3_5_2403_1 : fastPhase (bank 3 5).shape 179798 2403 5 1 1 1 1 = 6239544811802376410391972 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2403_1_join1

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2402_0 receipt_3_5_2402_1 receipt_3_5_2403_0 receipt_3_5_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 0) 0 128 = 58904052279960870298951629 := by decide +kernel
private theorem receipt_0_6_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 0) 128 128 = 32136375601672070819098414 := by decide +kernel
private theorem receipt_0_6_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 0) 256 125 = 9594198304211260320223221 := by decide +kernel
private theorem receipt_0_6_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 0) 128 253 = 41730573905883331139321635 :=
  phaseBlock_append receipt_0_6_2402_0_part1 receipt_0_6_2402_0_part2 rfl rfl rfl
private theorem receipt_0_6_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 0) 0 381 = 100634626185844201438273264 :=
  phaseBlock_append receipt_0_6_2402_0_part0 receipt_0_6_2402_0_join0 rfl rfl rfl

private theorem receipt_0_6_2402_0 : fastPhase (bank 0 6).shape 179798 2402 7 1 0 1 0 = 100634626185844201438273264 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2402_0_join1

private theorem receipt_0_6_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 1) 0 128 = 58680365199727951913896316 := by decide +kernel
private theorem receipt_0_6_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 1) 128 128 = 31945902783241233669532104 := by decide +kernel
private theorem receipt_0_6_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 1) 256 125 = 9437629532516867038306852 := by decide +kernel
private theorem receipt_0_6_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 1) 128 253 = 41383532315758100707838956 :=
  phaseBlock_append receipt_0_6_2402_1_part1 receipt_0_6_2402_1_part2 rfl rfl rfl
private theorem receipt_0_6_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2402 7 1 0 1 1) 0 381 = 100063897515486052621735272 :=
  phaseBlock_append receipt_0_6_2402_1_part0 receipt_0_6_2402_1_join0 rfl rfl rfl

private theorem receipt_0_6_2402_1 : fastPhase (bank 0 6).shape 179798 2402 7 1 0 1 1 = 100063897515486052621735272 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2402_1_join1

private theorem receipt_0_6_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 0) 0 128 = 58904556659619513951301083 := by decide +kernel
private theorem receipt_0_6_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 0) 128 128 = 32136591999250362430174335 := by decide +kernel
private theorem receipt_0_6_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 0) 256 125 = 9594245443123619525350609 := by decide +kernel
private theorem receipt_0_6_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 0) 128 253 = 41730837442373981955524944 :=
  phaseBlock_append receipt_0_6_2403_0_part1 receipt_0_6_2403_0_part2 rfl rfl rfl
private theorem receipt_0_6_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 0) 0 381 = 100635394101993495906826027 :=
  phaseBlock_append receipt_0_6_2403_0_part0 receipt_0_6_2403_0_join0 rfl rfl rfl

private theorem receipt_0_6_2403_0 : fastPhase (bank 0 6).shape 179798 2403 7 1 0 1 0 = 100635394101993495906826027 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2403_0_join1

private theorem receipt_0_6_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 1) 0 128 = 58680867993078430362777204 := by decide +kernel
private theorem receipt_0_6_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 1) 128 128 = 31946118074435435317399998 := by decide +kernel
private theorem receipt_0_6_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 1) 256 125 = 9437675995795282712022789 := by decide +kernel
private theorem receipt_0_6_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 1) 128 253 = 41383794070230718029422787 :=
  phaseBlock_append receipt_0_6_2403_1_part1 receipt_0_6_2403_1_part2 rfl rfl rfl
private theorem receipt_0_6_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179798 2403 7 1 0 1 1) 0 381 = 100064662063309148392199991 :=
  phaseBlock_append receipt_0_6_2403_1_part0 receipt_0_6_2403_1_join0 rfl rfl rfl

private theorem receipt_0_6_2403_1 : fastPhase (bank 0 6).shape 179798 2403 7 1 0 1 1 = 100064662063309148392199991 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2403_1_join1

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2402_0 receipt_0_6_2402_1 receipt_0_6_2403_0 receipt_0_6_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 0) 0 128 = 53049109093614265854542910 := by decide +kernel
private theorem receipt_1_6_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 0) 128 128 = 28881592070917930936116540 := by decide +kernel
private theorem receipt_1_6_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 0) 256 125 = 8606117935924309976238139 := by decide +kernel
private theorem receipt_1_6_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 0) 128 253 = 37487710006842240912354679 :=
  phaseBlock_append receipt_1_6_2402_0_part1 receipt_1_6_2402_0_part2 rfl rfl rfl
private theorem receipt_1_6_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 0) 0 381 = 90536819100456506766897589 :=
  phaseBlock_append receipt_1_6_2402_0_part0 receipt_1_6_2402_0_join0 rfl rfl rfl

private theorem receipt_1_6_2402_0 : fastPhase (bank 1 6).shape 179798 2402 7 1 0 2 0 = 90536819100456506766897589 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2402_0_join1

private theorem receipt_1_6_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 1) 0 128 = 52846785491758701765426435 := by decide +kernel
private theorem receipt_1_6_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 1) 128 128 = 28709947758160093707397420 := by decide +kernel
private theorem receipt_1_6_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 1) 256 125 = 8465577506348512064090693 := by decide +kernel
private theorem receipt_1_6_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 1) 128 253 = 37175525264508605771488113 :=
  phaseBlock_append receipt_1_6_2402_1_part1 receipt_1_6_2402_1_part2 rfl rfl rfl
private theorem receipt_1_6_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2402 7 1 0 2 1) 0 381 = 90022310756267307536914548 :=
  phaseBlock_append receipt_1_6_2402_1_part0 receipt_1_6_2402_1_join0 rfl rfl rfl

private theorem receipt_1_6_2402_1 : fastPhase (bank 1 6).shape 179798 2402 7 1 0 2 1 = 90022310756267307536914548 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2402_1_join1

private theorem receipt_1_6_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 0) 0 128 = 53049563355442451964257150 := by decide +kernel
private theorem receipt_1_6_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 0) 128 128 = 28881786561419075532472977 := by decide +kernel
private theorem receipt_1_6_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 0) 256 125 = 8606160222243653637386251 := by decide +kernel
private theorem receipt_1_6_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 0) 128 253 = 37487946783662729169859228 :=
  phaseBlock_append receipt_1_6_2403_0_part1 receipt_1_6_2403_0_part2 rfl rfl rfl
private theorem receipt_1_6_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 0) 0 381 = 90537510139105181134116378 :=
  phaseBlock_append receipt_1_6_2403_0_part0 receipt_1_6_2403_0_join0 rfl rfl rfl

private theorem receipt_1_6_2403_0 : fastPhase (bank 1 6).shape 179798 2403 7 1 0 2 0 = 90537510139105181134116378 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2403_0_join1

private theorem receipt_1_6_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 1) 0 128 = 52847238317435177527461839 := by decide +kernel
private theorem receipt_1_6_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 1) 128 128 = 28710141251154737327925498 := by decide +kernel
private theorem receipt_1_6_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 1) 256 125 = 8465619186074430929905014 := by decide +kernel
private theorem receipt_1_6_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 1) 128 253 = 37175760437229168257830512 :=
  phaseBlock_append receipt_1_6_2403_1_part1 receipt_1_6_2403_1_part2 rfl rfl rfl
private theorem receipt_1_6_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179798 2403 7 1 0 2 1) 0 381 = 90022998754664345785292351 :=
  phaseBlock_append receipt_1_6_2403_1_part0 receipt_1_6_2403_1_join0 rfl rfl rfl

private theorem receipt_1_6_2403_1 : fastPhase (bank 1 6).shape 179798 2403 7 1 0 2 1 = 90022998754664345785292351 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2403_1_join1

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2402_0 receipt_1_6_2402_1 receipt_1_6_2403_0 receipt_1_6_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 0) 0 128 = 28817594734061108362800096 := by decide +kernel
private theorem receipt_2_6_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 0) 128 128 = 15456055628681038144781280 := by decide +kernel
private theorem receipt_2_6_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 0) 256 125 = 4542786189944798310904839 := by decide +kernel
private theorem receipt_2_6_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 0) 128 253 = 19998841818625836455686119 :=
  phaseBlock_append receipt_2_6_2402_0_part1 receipt_2_6_2402_0_part2 rfl rfl rfl
private theorem receipt_2_6_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 0) 0 381 = 48816436552686944818486215 :=
  phaseBlock_append receipt_2_6_2402_0_part0 receipt_2_6_2402_0_join0 rfl rfl rfl

private theorem receipt_2_6_2402_0 : fastPhase (bank 2 6).shape 179798 2402 7 1 0 7 0 = 48816436552686944818486215 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2402_0_join1

private theorem receipt_2_6_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 1) 0 128 = 28704313609415608435213280 := by decide +kernel
private theorem receipt_2_6_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 1) 128 128 = 15362418360622839415337952 := by decide +kernel
private theorem receipt_2_6_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 1) 256 125 = 4468232508025426810268908 := by decide +kernel
private theorem receipt_2_6_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 1) 128 253 = 19830650868648266225606860 :=
  phaseBlock_append receipt_2_6_2402_1_part1 receipt_2_6_2402_1_part2 rfl rfl rfl
private theorem receipt_2_6_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2402 7 1 0 7 1) 0 381 = 48534964478063874660820140 :=
  phaseBlock_append receipt_2_6_2402_1_part0 receipt_2_6_2402_1_join0 rfl rfl rfl

private theorem receipt_2_6_2402_1 : fastPhase (bank 2 6).shape 179798 2402 7 1 0 7 1 = 48534964478063874660820140 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2402_1_join1

private theorem receipt_2_6_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 0) 0 128 = 28817839472732971424452608 := by decide +kernel
private theorem receipt_2_6_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 0) 128 128 = 15456159335841048734191616 := by decide +kernel
private theorem receipt_2_6_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 0) 256 125 = 4542808519099965430062940 := by decide +kernel
private theorem receipt_2_6_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 0) 128 253 = 19998967854941014164254556 :=
  phaseBlock_append receipt_2_6_2403_0_part1 receipt_2_6_2403_0_part2 rfl rfl rfl
private theorem receipt_2_6_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 0) 0 381 = 48816807327673985588707164 :=
  phaseBlock_append receipt_2_6_2403_0_part0 receipt_2_6_2403_0_join0 rfl rfl rfl

private theorem receipt_2_6_2403_0 : fastPhase (bank 2 6).shape 179798 2403 7 1 0 7 0 = 48816807327673985588707164 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2403_0_join1

private theorem receipt_2_6_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 1) 0 128 = 28704557545549459631063744 := by decide +kernel
private theorem receipt_2_6_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 1) 128 128 = 15362521523735852535440064 := by decide +kernel
private theorem receipt_2_6_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 1) 256 125 = 4468254514914142021798098 := by decide +kernel
private theorem receipt_2_6_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 1) 128 253 = 19830776038649994557238162 :=
  phaseBlock_append receipt_2_6_2403_1_part1 receipt_2_6_2403_1_part2 rfl rfl rfl
private theorem receipt_2_6_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179798 2403 7 1 0 7 1) 0 381 = 48535333584199454188301906 :=
  phaseBlock_append receipt_2_6_2403_1_part0 receipt_2_6_2403_1_join0 rfl rfl rfl

private theorem receipt_2_6_2403_1 : fastPhase (bank 2 6).shape 179798 2403 7 1 0 7 1 = 48535333584199454188301906 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2403_1_join1

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2402_0 receipt_2_6_2402_1 receipt_2_6_2403_0 receipt_2_6_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 0 128 = 5837255062516288463022720 := by decide +kernel
private theorem receipt_3_6_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 128 128 = 3221375624345434320767616 := by decide +kernel
private theorem receipt_3_6_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 256 128 = 1069860325553655404522112 := by decide +kernel
private theorem receipt_3_6_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 384 12 = 7698159116018045384736 := by decide +kernel
private theorem receipt_3_6_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 0 256 = 9058630686861722783790336 :=
  phaseBlock_append receipt_3_6_2402_0_part0 receipt_3_6_2402_0_part1 rfl rfl rfl
private theorem receipt_3_6_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 256 140 = 1077558484669673449906848 :=
  phaseBlock_append receipt_3_6_2402_0_part2 receipt_3_6_2402_0_part3 rfl rfl rfl
private theorem receipt_3_6_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 0) 0 396 = 10136189171531396233697184 :=
  phaseBlock_append receipt_3_6_2402_0_join0 receipt_3_6_2402_0_join1 rfl rfl rfl

private theorem receipt_3_6_2402_0 : fastPhase (bank 3 6).shape 179798 2402 7 1 1 1 0 = 10136189171531396233697184 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2402_0_join2

private theorem receipt_3_6_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 0 128 = 5815382914689330139236288 := by decide +kernel
private theorem receipt_3_6_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 128 128 = 3202855015786393203902400 := by decide +kernel
private theorem receipt_3_6_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 256 128 = 1055028439972588408932288 := by decide +kernel
private theorem receipt_3_6_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 384 12 = 6508592236128621035826 := by decide +kernel
private theorem receipt_3_6_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 0 256 = 9018237930475723343138688 :=
  phaseBlock_append receipt_3_6_2402_1_part0 receipt_3_6_2402_1_part1 rfl rfl rfl
private theorem receipt_3_6_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 256 140 = 1061537032208717029968114 :=
  phaseBlock_append receipt_3_6_2402_1_part2 receipt_3_6_2402_1_part3 rfl rfl rfl
private theorem receipt_3_6_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2402 7 1 1 1 1) 0 396 = 10079774962684440373106802 :=
  phaseBlock_append receipt_3_6_2402_1_join0 receipt_3_6_2402_1_join1 rfl rfl rfl

private theorem receipt_3_6_2402_1 : fastPhase (bank 3 6).shape 179798 2402 7 1 1 1 1 = 10079774962684440373106802 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2402_1_join2

private theorem receipt_3_6_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 0 128 = 5837301753680788868526720 := by decide +kernel
private theorem receipt_3_6_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 128 128 = 3221392449456183981134464 := by decide +kernel
private theorem receipt_3_6_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 256 128 = 1069863285852052696150656 := by decide +kernel
private theorem receipt_3_6_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 384 12 = 7698166910176325138816 := by decide +kernel
private theorem receipt_3_6_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 0 256 = 9058694203136972849661184 :=
  phaseBlock_append receipt_3_6_2403_0_part0 receipt_3_6_2403_0_part1 rfl rfl rfl
private theorem receipt_3_6_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 256 140 = 1077561452762229021289472 :=
  phaseBlock_append receipt_3_6_2403_0_part2 receipt_3_6_2403_0_part3 rfl rfl rfl
private theorem receipt_3_6_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 0) 0 396 = 10136255655899201870950656 :=
  phaseBlock_append receipt_3_6_2403_0_join0 receipt_3_6_2403_0_join1 rfl rfl rfl

private theorem receipt_3_6_2403_0 : fastPhase (bank 3 6).shape 179798 2403 7 1 1 1 0 = 10136255655899201870950656 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2403_0_join2

private theorem receipt_3_6_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 0 128 = 5815429406819757643134720 := by decide +kernel
private theorem receipt_3_6_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 128 128 = 3202871734917815047558912 := by decide +kernel
private theorem receipt_3_6_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 256 128 = 1055031361040759643322112 := by decide +kernel
private theorem receipt_3_6_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 384 12 = 6508598852496373345284 := by decide +kernel
private theorem receipt_3_6_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 0 256 = 9018301141737572690693632 :=
  phaseBlock_append receipt_3_6_2403_1_part0 receipt_3_6_2403_1_part1 rfl rfl rfl
private theorem receipt_3_6_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 256 140 = 1061539959893256016667396 :=
  phaseBlock_append receipt_3_6_2403_1_part2 receipt_3_6_2403_1_part3 rfl rfl rfl
private theorem receipt_3_6_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179798 2403 7 1 1 1 1) 0 396 = 10079841101630828707361028 :=
  phaseBlock_append receipt_3_6_2403_1_join0 receipt_3_6_2403_1_join1 rfl rfl rfl

private theorem receipt_3_6_2403_1 : fastPhase (bank 3 6).shape 179798 2403 7 1 1 1 1 = 10079841101630828707361028 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2403_1_join2

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2402_0 receipt_3_6_2402_1 receipt_3_6_2403_0 receipt_3_6_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 0 128 = 144988535157837370353867360 := by decide +kernel
private theorem receipt_0_7_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 128 128 = 93574286557481433244887648 := by decide +kernel
private theorem receipt_0_7_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 256 128 = 48557146029272641031664156 := by decide +kernel
private theorem receipt_0_7_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 384 97 = 10485988551001360971127077 := by decide +kernel
private theorem receipt_0_7_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 0 256 = 238562821715318803598755008 :=
  phaseBlock_append receipt_0_7_2402_0_part0 receipt_0_7_2402_0_part1 rfl rfl rfl
private theorem receipt_0_7_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 256 225 = 59043134580274002002791233 :=
  phaseBlock_append receipt_0_7_2402_0_part2 receipt_0_7_2402_0_part3 rfl rfl rfl
private theorem receipt_0_7_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 0) 0 481 = 297605956295592805601546241 :=
  phaseBlock_append receipt_0_7_2402_0_join0 receipt_0_7_2402_0_join1 rfl rfl rfl

private theorem receipt_0_7_2402_0 : fastPhase (bank 0 7).shape 179798 2402 10 1 0 1 0 = 297605956295592805601546241 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2402_0_join2

private theorem receipt_0_7_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 0 128 = 144566256996074168154414432 := by decide +kernel
private theorem receipt_0_7_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 128 128 = 93201893776884147269209440 := by decide +kernel
private theorem receipt_0_7_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 256 128 = 48231415972227467634392391 := by decide +kernel
private theorem receipt_0_7_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 384 97 = 10268263984430458922603115 := by decide +kernel
private theorem receipt_0_7_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 0 256 = 237768150772958315423623872 :=
  phaseBlock_append receipt_0_7_2402_1_part0 receipt_0_7_2402_1_part1 rfl rfl rfl
private theorem receipt_0_7_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 256 225 = 58499679956657926556995506 :=
  phaseBlock_append receipt_0_7_2402_1_part2 receipt_0_7_2402_1_part3 rfl rfl rfl
private theorem receipt_0_7_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2402 10 1 0 1 1) 0 481 = 296267830729616241980619378 :=
  phaseBlock_append receipt_0_7_2402_1_join0 receipt_0_7_2402_1_join1 rfl rfl rfl

private theorem receipt_0_7_2402_1 : fastPhase (bank 0 7).shape 179798 2402 10 1 0 1 1 = 296267830729616241980619378 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2402_1_join2

private theorem receipt_0_7_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 0 128 = 144989786878596851026988000 := by decide +kernel
private theorem receipt_0_7_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 128 128 = 93574963240878325369134048 := by decide +kernel
private theorem receipt_0_7_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 256 128 = 48557424369078887765656293 := by decide +kernel
private theorem receipt_0_7_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 384 97 = 10486034106045833946055193 := by decide +kernel
private theorem receipt_0_7_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 0 256 = 238564750119475176396122048 :=
  phaseBlock_append receipt_0_7_2403_0_part0 receipt_0_7_2403_0_part1 rfl rfl rfl
private theorem receipt_0_7_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 256 225 = 59043458475124721711711486 :=
  phaseBlock_append receipt_0_7_2403_0_part2 receipt_0_7_2403_0_part3 rfl rfl rfl
private theorem receipt_0_7_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 0) 0 481 = 297608208594599898107833534 :=
  phaseBlock_append receipt_0_7_2403_0_join0 receipt_0_7_2403_0_join1 rfl rfl rfl

private theorem receipt_0_7_2403_0 : fastPhase (bank 0 7).shape 179798 2403 10 1 0 1 0 = 297608208594599898107833534 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2403_0_join2

private theorem receipt_0_7_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 0 128 = 144567505702561414307453664 := by decide +kernel
private theorem receipt_0_7_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 128 128 = 93202568157950458668837600 := by decide +kernel
private theorem receipt_0_7_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 256 128 = 48231692654248352381601751 := by decide +kernel
private theorem receipt_0_7_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 384 97 = 10268308674306030227896490 := by decide +kernel
private theorem receipt_0_7_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 0 256 = 237770073860511872976291264 :=
  phaseBlock_append receipt_0_7_2403_1_part0 receipt_0_7_2403_1_part1 rfl rfl rfl
private theorem receipt_0_7_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 256 225 = 58500001328554382609498241 :=
  phaseBlock_append receipt_0_7_2403_1_part2 receipt_0_7_2403_1_part3 rfl rfl rfl
private theorem receipt_0_7_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179798 2403 10 1 0 1 1) 0 481 = 296270075189066255585789505 :=
  phaseBlock_append receipt_0_7_2403_1_join0 receipt_0_7_2403_1_join1 rfl rfl rfl

private theorem receipt_0_7_2403_1 : fastPhase (bank 0 7).shape 179798 2403 10 1 0 1 1 = 296270075189066255585789505 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2403_1_join2

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2402_0 receipt_0_7_2402_1 receipt_0_7_2403_0 receipt_0_7_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 0 128 = 130421488925181300497575296 := by decide +kernel
private theorem receipt_1_7_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 128 128 = 84007787831894219370081664 := by decide +kernel
private theorem receipt_1_7_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 256 128 = 43508760366045437841134776 := by decide +kernel
private theorem receipt_1_7_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 384 97 = 9380353271459271036304553 := by decide +kernel
private theorem receipt_1_7_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 0 256 = 214429276757075519867656960 :=
  phaseBlock_append receipt_1_7_2402_0_part0 receipt_1_7_2402_0_part1 rfl rfl rfl
private theorem receipt_1_7_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 256 225 = 52889113637504708877439329 :=
  phaseBlock_append receipt_1_7_2402_0_part2 receipt_1_7_2402_0_part3 rfl rfl rfl
private theorem receipt_1_7_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 0) 0 481 = 267318390394580228745096289 :=
  phaseBlock_append receipt_1_7_2402_0_join0 receipt_1_7_2402_0_join1 rfl rfl rfl

private theorem receipt_1_7_2402_0 : fastPhase (bank 1 7).shape 179798 2402 10 1 0 2 0 = 267318390394580228745096289 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2402_0_join2

private theorem receipt_1_7_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 0 128 = 130039638812209640440514432 := by decide +kernel
private theorem receipt_1_7_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 128 128 = 83672187948622121172371328 := by decide +kernel
private theorem receipt_1_7_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 256 128 = 43216257856668998403378713 := by decide +kernel
private theorem receipt_1_7_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 384 97 = 9185488913706776783670043 := by decide +kernel
private theorem receipt_1_7_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 0 256 = 213711826760831761612885760 :=
  phaseBlock_append receipt_1_7_2402_1_part0 receipt_1_7_2402_1_part1 rfl rfl rfl
private theorem receipt_1_7_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 256 225 = 52401746770375775187048756 :=
  phaseBlock_append receipt_1_7_2402_1_part2 receipt_1_7_2402_1_part3 rfl rfl rfl
private theorem receipt_1_7_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2402 10 1 0 2 1) 0 481 = 266113573531207536799934516 :=
  phaseBlock_append receipt_1_7_2402_1_join0 receipt_1_7_2402_1_join1 rfl rfl rfl

private theorem receipt_1_7_2402_1 : fastPhase (bank 1 7).shape 179798 2402 10 1 0 2 1 = 266113573531207536799934516 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2402_1_join2

private theorem receipt_1_7_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 0 128 = 130422614914196013358852896 := by decide +kernel
private theorem receipt_1_7_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 128 128 = 84008395355255934175812384 := by decide +kernel
private theorem receipt_1_7_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 256 128 = 43509009778538627853424729 := by decide +kernel
private theorem receipt_1_7_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 384 97 = 9380394024266013043533197 := by decide +kernel
private theorem receipt_1_7_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 0 256 = 214431010269451947534665280 :=
  phaseBlock_append receipt_1_7_2403_0_part0 receipt_1_7_2403_0_part1 rfl rfl rfl
private theorem receipt_1_7_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 256 225 = 52889403802804640896957926 :=
  phaseBlock_append receipt_1_7_2403_0_part2 receipt_1_7_2403_0_part3 rfl rfl rfl
private theorem receipt_1_7_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 0) 0 481 = 267320414072256588431623206 :=
  phaseBlock_append receipt_1_7_2403_0_join0 receipt_1_7_2403_0_join1 rfl rfl rfl

private theorem receipt_1_7_2403_0 : fastPhase (bank 1 7).shape 179798 2403 10 1 0 2 0 = 267320414072256588431623206 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2403_0_join2

private theorem receipt_1_7_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 0 128 = 130040762072455627219473504 := by decide +kernel
private theorem receipt_1_7_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 128 128 = 83672793395701503055438944 := by decide +kernel
private theorem receipt_1_7_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 256 128 = 43216505779993727266759709 := by decide +kernel
private theorem receipt_1_7_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 384 97 = 9185528892104502871642688 := by decide +kernel
private theorem receipt_1_7_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 0 256 = 213713555468157130274912448 :=
  phaseBlock_append receipt_1_7_2403_1_part0 receipt_1_7_2403_1_part1 rfl rfl rfl
private theorem receipt_1_7_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 256 225 = 52402034672098230138402397 :=
  phaseBlock_append receipt_1_7_2403_1_part2 receipt_1_7_2403_1_part3 rfl rfl rfl
private theorem receipt_1_7_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179798 2403 10 1 0 2 1) 0 481 = 266115590140255360413314845 :=
  phaseBlock_append receipt_1_7_2403_1_join0 receipt_1_7_2403_1_join1 rfl rfl rfl

private theorem receipt_1_7_2403_1 : fastPhase (bank 1 7).shape 179798 2403 10 1 0 2 1 = 266115590140255360413314845 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2403_1_join2

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2402_0 receipt_1_7_2402_1 receipt_1_7_2403_0 receipt_1_7_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 0 128 = 69582085135688478728387520 := by decide +kernel
private theorem receipt_2_7_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 128 128 = 44187075415636206975204288 := by decide +kernel
private theorem receipt_2_7_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 256 128 = 22564450282066394384296692 := by decide +kernel
private theorem receipt_2_7_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 384 97 = 4806370126487894142571875 := by decide +kernel
private theorem receipt_2_7_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 0 256 = 113769160551324685703591808 :=
  phaseBlock_append receipt_2_7_2402_0_part0 receipt_2_7_2402_0_part1 rfl rfl rfl
private theorem receipt_2_7_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 256 225 = 27370820408554288526868567 :=
  phaseBlock_append receipt_2_7_2402_0_part2 receipt_2_7_2402_0_part3 rfl rfl rfl
private theorem receipt_2_7_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 0) 0 481 = 141139980959878974230460375 :=
  phaseBlock_append receipt_2_7_2402_0_join0 receipt_2_7_2402_0_join1 rfl rfl rfl

private theorem receipt_2_7_2402_0 : fastPhase (bank 2 7).shape 179798 2402 10 1 0 7 0 = 141139980959878974230460375 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2402_0_join2

private theorem receipt_2_7_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 0 128 = 69370673042399870385624192 := by decide +kernel
private theorem receipt_2_7_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 128 128 = 44005665435312319898481792 := by decide +kernel
private theorem receipt_2_7_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 256 128 = 22410328402183834812941775 := by decide +kernel
private theorem receipt_2_7_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 384 97 = 4706159069726035319432565 := by decide +kernel
private theorem receipt_2_7_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 0 256 = 113376338477712190284105984 :=
  phaseBlock_append receipt_2_7_2402_1_part0 receipt_2_7_2402_1_part1 rfl rfl rfl
private theorem receipt_2_7_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 256 225 = 27116487471909870132374340 :=
  phaseBlock_append receipt_2_7_2402_1_part2 receipt_2_7_2402_1_part3 rfl rfl rfl
private theorem receipt_2_7_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2402 10 1 0 7 1) 0 481 = 140492825949622060416480324 :=
  phaseBlock_append receipt_2_7_2402_1_join0 receipt_2_7_2402_1_join1 rfl rfl rfl

private theorem receipt_2_7_2402_1 : fastPhase (bank 2 7).shape 179798 2402 10 1 0 7 1 = 140492825949622060416480324 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2402_1_join2

private theorem receipt_2_7_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 0 128 = 69582685981773097382489120 := by decide +kernel
private theorem receipt_2_7_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 128 128 = 44187395042757020364430368 := by decide +kernel
private theorem receipt_2_7_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 256 128 = 22564579674181262494087845 := by decide +kernel
private theorem receipt_2_7_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 384 97 = 4806391011676420991501328 := by decide +kernel
private theorem receipt_2_7_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 0 256 = 113770081024530117746919488 :=
  phaseBlock_append receipt_2_7_2403_0_part0 receipt_2_7_2403_0_part1 rfl rfl rfl
private theorem receipt_2_7_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 256 225 = 27370970685857683485589173 :=
  phaseBlock_append receipt_2_7_2403_0_part2 receipt_2_7_2403_0_part3 rfl rfl rfl
private theorem receipt_2_7_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 0) 0 481 = 141141051710387801232508661 :=
  phaseBlock_append receipt_2_7_2403_0_join0 receipt_2_7_2403_0_join1 rfl rfl rfl

private theorem receipt_2_7_2403_0 : fastPhase (bank 2 7).shape 179798 2403 10 1 0 7 0 = 141141051710387801232508661 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2403_0_join2

private theorem receipt_2_7_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 0 128 = 69371272365913529348782304 := by decide +kernel
private theorem receipt_2_7_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 128 128 = 44005983934656310633375968 := by decide +kernel
private theorem receipt_2_7_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 256 128 = 22410457007772252587257536 := by decide +kernel
private theorem receipt_2_7_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 384 97 = 4706179556366365100074017 := by decide +kernel
private theorem receipt_2_7_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 0 256 = 113377256300569839982158272 :=
  phaseBlock_append receipt_2_7_2403_1_part0 receipt_2_7_2403_1_part1 rfl rfl rfl
private theorem receipt_2_7_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 256 225 = 27116636564138617687331553 :=
  phaseBlock_append receipt_2_7_2403_1_part2 receipt_2_7_2403_1_part3 rfl rfl rfl
private theorem receipt_2_7_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179798 2403 10 1 0 7 1) 0 481 = 140493892864708457669489825 :=
  phaseBlock_append receipt_2_7_2403_1_join0 receipt_2_7_2403_1_join1 rfl rfl rfl

private theorem receipt_2_7_2403_1 : fastPhase (bank 2 7).shape 179798 2403 10 1 0 7 1 = 140493892864708457669489825 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2403_1_join2

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2402_0 receipt_2_7_2402_1 receipt_2_7_2403_0 receipt_2_7_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 0 128 = 17515031543824843942796064 := by decide +kernel
private theorem receipt_3_7_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 128 128 = 11368393420818078223059744 := by decide +kernel
private theorem receipt_3_7_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 256 128 = 6036870562186039139400480 := by decide +kernel
private theorem receipt_3_7_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 384 115 = 1593328552460299362369987 := by decide +kernel
private theorem receipt_3_7_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 0 256 = 28883424964642922165855808 :=
  phaseBlock_append receipt_3_7_2402_0_part0 receipt_3_7_2402_0_part1 rfl rfl rfl
private theorem receipt_3_7_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 256 243 = 7630199114646338501770467 :=
  phaseBlock_append receipt_3_7_2402_0_part2 receipt_3_7_2402_0_part3 rfl rfl rfl
private theorem receipt_3_7_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 0) 0 499 = 36513624079289260667626275 :=
  phaseBlock_append receipt_3_7_2402_0_join0 receipt_3_7_2402_0_join1 rfl rfl rfl

private theorem receipt_3_7_2402_0 : fastPhase (bank 3 7).shape 179798 2402 10 1 1 1 0 = 36513624079289260667626275 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2402_0_join2

private theorem receipt_3_7_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 0 128 = 17464620668777854651991520 := by decide +kernel
private theorem receipt_3_7_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 128 128 = 11323902688241051632629216 := by decide +kernel
private theorem receipt_3_7_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 256 128 = 5998778797476065972905440 := by decide +kernel
private theorem receipt_3_7_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 384 115 = 1564948078758875026517868 := by decide +kernel
private theorem receipt_3_7_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 0 256 = 28788523357018906284620736 :=
  phaseBlock_append receipt_3_7_2402_1_part0 receipt_3_7_2402_1_part1 rfl rfl rfl
private theorem receipt_3_7_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 256 243 = 7563726876234940999423308 :=
  phaseBlock_append receipt_3_7_2402_1_part2 receipt_3_7_2402_1_part3 rfl rfl rfl
private theorem receipt_3_7_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2402 10 1 1 1 1) 0 499 = 36352250233253847284044044 :=
  phaseBlock_append receipt_3_7_2402_1_join0 receipt_3_7_2402_1_join1 rfl rfl rfl

private theorem receipt_3_7_2402_1 : fastPhase (bank 3 7).shape 179798 2402 10 1 1 1 1 = 36352250233253847284044044 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2402_1_join2

private theorem receipt_3_7_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 0 128 = 17515175842603163638877600 := by decide +kernel
private theorem receipt_3_7_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 128 128 = 11368461553844826171588000 := by decide +kernel
private theorem receipt_3_7_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 256 128 = 6036893967427670334352800 := by decide +kernel
private theorem receipt_3_7_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 384 115 = 1593331860957324918222975 := by decide +kernel
private theorem receipt_3_7_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 0 256 = 28883637396447989810465600 :=
  phaseBlock_append receipt_3_7_2403_0_part0 receipt_3_7_2403_0_part1 rfl rfl rfl
private theorem receipt_3_7_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 256 243 = 7630225828384995252575775 :=
  phaseBlock_append receipt_3_7_2403_0_part2 receipt_3_7_2403_0_part3 rfl rfl rfl
private theorem receipt_3_7_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 0) 0 499 = 36513863224832985063041375 :=
  phaseBlock_append receipt_3_7_2403_0_join0 receipt_3_7_2403_0_join1 rfl rfl rfl

private theorem receipt_3_7_2403_0 : fastPhase (bank 3 7).shape 179798 2403 10 1 1 1 0 = 36513863224832985063041375 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2403_0_join2

private theorem receipt_3_7_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 0 128 = 17464764492159750871012320 := by decide +kernel
private theorem receipt_3_7_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 128 128 = 11323970523147616108282848 := by decide +kernel
private theorem receipt_3_7_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 256 128 = 5998802043976529650824160 := by decide +kernel
private theorem receipt_3_7_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 384 115 = 1564951332939578927912744 := by decide +kernel
private theorem receipt_3_7_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 0 256 = 28788735015307366979295168 :=
  phaseBlock_append receipt_3_7_2403_1_part0 receipt_3_7_2403_1_part1 rfl rfl rfl
private theorem receipt_3_7_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 256 243 = 7563753376916108578736904 :=
  phaseBlock_append receipt_3_7_2403_1_part2 receipt_3_7_2403_1_part3 rfl rfl rfl
private theorem receipt_3_7_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179798 2403 10 1 1 1 1) 0 499 = 36352488392223475558032072 :=
  phaseBlock_append receipt_3_7_2403_1_join0 receipt_3_7_2403_1_join1 rfl rfl rfl

private theorem receipt_3_7_2403_1 : fastPhase (bank 3 7).shape 179798 2403 10 1 1 1 1 = 36352488392223475558032072 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2403_1_join2

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_498)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_7_2402_0 receipt_3_7_2402_1 receipt_3_7_2403_0 receipt_3_7_2403_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group2_stage i)).shape
      (cutoff h rect (group2_stage i)), ¬ G∣Q :=
  (group2_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group2_avoids

end Lower6960.RescueSource
