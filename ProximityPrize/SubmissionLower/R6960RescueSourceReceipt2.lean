import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_1696_356_part0 :
    blockEstimate 1696 356 356 128 = 572684320 := rfl
private theorem moment_1696_356_part1 :
    blockEstimate 1696 356 484 128 = 3684337696 := rfl
private theorem moment_1696_356_part2 :
    blockEstimate 1696 356 612 128 = 9136834131 := rfl
private theorem moment_1696_356_part3 :
    blockEstimate 1696 356 740 128 = 15370032384 := rfl
private theorem moment_1696_356_part4 :
    blockEstimate 1696 356 868 128 = 20341757184 := rfl
private theorem moment_1696_356_part5 :
    blockEstimate 1696 356 996 128 = 23816115456 := rfl
private theorem moment_1696_356_part6 :
    blockEstimate 1696 356 1124 128 = 25793107200 := rfl
private theorem moment_1696_356_part7 :
    blockEstimate 1696 356 1252 128 = 26272732416 := rfl
private theorem moment_1696_356_part8 :
    blockEstimate 1696 356 1380 128 = 25254991104 := rfl
private theorem moment_1696_356_part9 :
    blockEstimate 1696 356 1508 128 = 22739883264 := rfl
private theorem moment_1696_356_part10 :
    blockEstimate 1696 356 1636 128 = 18755777396 := rfl
private theorem moment_1696_356_part11 :
    blockEstimate 1696 356 1764 128 = 13945647249 := rfl
private theorem moment_1696_356_part12 :
    blockEstimate 1696 356 1892 128 = 9230875643 := rfl
private theorem moment_1696_356_part13 :
    blockEstimate 1696 356 2020 128 = 5110148823 := rfl
private theorem moment_1696_356_part14 :
    blockEstimate 1696 356 2148 128 = 2022537952 := rfl
private theorem moment_1696_356_part15 :
    blockEstimate 1696 356 2276 128 = 324080352 := rfl
private theorem moment_1696_356_part16 :
    blockEstimate 1696 356 2404 4 = 22031 := rfl
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
    blockEstimate 1696 370 370 128 = 572684320 := rfl
private theorem moment_1696_370_part1 :
    blockEstimate 1696 370 498 128 = 3684337696 := rfl
private theorem moment_1696_370_part2 :
    blockEstimate 1696 370 626 128 = 9141056804 := rfl
private theorem moment_1696_370_part3 :
    blockEstimate 1696 370 754 128 = 15557757376 := rfl
private theorem moment_1696_370_part4 :
    blockEstimate 1696 370 882 128 = 20767001024 := rfl
private theorem moment_1696_370_part5 :
    blockEstimate 1696 370 1010 128 = 24420157888 := rfl
private theorem moment_1696_370_part6 :
    blockEstimate 1696 370 1138 128 = 26517227968 := rfl
private theorem moment_1696_370_part7 :
    blockEstimate 1696 370 1266 128 = 27058211264 := rfl
private theorem moment_1696_370_part8 :
    blockEstimate 1696 370 1394 128 = 26043107776 := rfl
private theorem moment_1696_370_part9 :
    blockEstimate 1696 370 1522 128 = 23471917504 := rfl
private theorem moment_1696_370_part10 :
    blockEstimate 1696 370 1650 128 = 19393615038 := rfl
private theorem moment_1696_370_part11 :
    blockEstimate 1696 370 1778 128 = 14532053576 := rfl
private theorem moment_1696_370_part12 :
    blockEstimate 1696 370 1906 128 = 9746328986 := rfl
private theorem moment_1696_370_part13 :
    blockEstimate 1696 370 2034 128 = 5521630460 := rfl
private theorem moment_1696_370_part14 :
    blockEstimate 1696 370 2162 128 = 2297261808 := rfl
private theorem moment_1696_370_part15 :
    blockEstimate 1696 370 2290 128 = 434348784 := rfl
private theorem moment_1696_370_part16 :
    blockEstimate 1696 370 2418 18 = 1038245 := rfl
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
    blockEstimate 1809 380 380 128 = 613111200 := rfl
private theorem moment_1809_380_part1 :
    blockEstimate 1809 380 508 128 = 3963594144 := rfl
private theorem moment_1809_380_part2 :
    blockEstimate 1809 380 636 128 = 9896705511 := rfl
private theorem moment_1809_380_part3 :
    blockEstimate 1809 380 764 128 = 17097207360 := rfl
private theorem moment_1809_380_part4 :
    blockEstimate 1809 380 892 128 = 23183453760 := rfl
private theorem moment_1809_380_part5 :
    blockEstimate 1809 380 1020 128 = 27671670336 := rfl
private theorem moment_1809_380_part6 :
    blockEstimate 1809 380 1148 128 = 30561857088 := rfl
private theorem moment_1809_380_part7 :
    blockEstimate 1809 380 1276 128 = 31854014016 := rfl
private theorem moment_1809_380_part8 :
    blockEstimate 1809 380 1404 128 = 31548141120 := rfl
private theorem moment_1809_380_part9 :
    blockEstimate 1809 380 1532 128 = 29644238400 := rfl
private theorem moment_1809_380_part10 :
    blockEstimate 1809 380 1660 128 = 26142305856 := rfl
private theorem moment_1809_380_part11 :
    blockEstimate 1809 380 1788 128 = 21163152440 := rfl
private theorem moment_1809_380_part12 :
    blockEstimate 1809 380 1916 128 = 15641164329 := rfl
private theorem moment_1809_380_part13 :
    blockEstimate 1809 380 2044 128 = 10359919872 := rfl
private theorem moment_1809_380_part14 :
    blockEstimate 1809 380 2172 128 = 5784462598 := rfl
private theorem moment_1809_380_part15 :
    blockEstimate 1809 380 2300 128 = 2356385168 := rfl
private theorem moment_1809_380_part16 :
    blockEstimate 1809 380 2428 128 = 419948944 := rfl
private theorem moment_1809_380_part17 :
    blockEstimate 1809 380 2556 13 = 454490 := rfl
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
    blockEstimate 1809 395 395 128 = 613111200 := rfl
private theorem moment_1809_395_part1 :
    blockEstimate 1809 395 523 128 = 3963594144 := rfl
private theorem moment_1809_395_part2 :
    blockEstimate 1809 395 651 128 = 9896719776 := rfl
private theorem moment_1809_395_part3 :
    blockEstimate 1809 395 779 128 = 17253050925 := rfl
private theorem moment_1809_395_part4 :
    blockEstimate 1809 395 907 128 = 23627260800 := rfl
private theorem moment_1809_395_part5 :
    blockEstimate 1809 395 1035 128 = 28340839296 := rfl
private theorem moment_1809_395_part6 :
    blockEstimate 1809 395 1163 128 = 31393473408 := rfl
private theorem moment_1809_395_part7 :
    blockEstimate 1809 395 1291 128 = 32785163136 := rfl
private theorem moment_1809_395_part8 :
    blockEstimate 1809 395 1419 128 = 32515908480 := rfl
private theorem moment_1809_395_part9 :
    blockEstimate 1809 395 1547 128 = 30585709440 := rfl
private theorem moment_1809_395_part10 :
    blockEstimate 1809 395 1675 128 = 26994566016 := rfl
private theorem moment_1809_395_part11 :
    blockEstimate 1809 395 1803 128 = 21919153025 := rfl
private theorem moment_1809_395_part12 :
    blockEstimate 1809 395 1931 128 = 16340444489 := rfl
private theorem moment_1809_395_part13 :
    blockEstimate 1809 395 2059 128 = 10971561561 := rfl
private theorem moment_1809_395_part14 :
    blockEstimate 1809 395 2187 128 = 6272279892 := rfl
private theorem moment_1809_395_part15 :
    blockEstimate 1809 395 2315 128 = 2685846592 := rfl
private theorem moment_1809_395_part16 :
    blockEstimate 1809 395 2443 128 = 561511488 := rfl
private theorem moment_1809_395_part17 :
    blockEstimate 1809 395 2571 28 = 3835580 := rfl
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
    blockEstimate 1817 380 380 128 = 615973280 := rfl
private theorem moment_1817_380_part1 :
    blockEstimate 1817 380 508 128 = 3983364512 := rfl
private theorem moment_1817_380_part2 :
    blockEstimate 1817 380 636 128 = 9950161303 := rfl
private theorem moment_1817_380_part3 :
    blockEstimate 1817 380 764 128 = 17198059584 := rfl
private theorem moment_1817_380_part4 :
    blockEstimate 1817 380 892 128 = 23334244416 := rfl
private theorem moment_1817_380_part5 :
    blockEstimate 1817 380 1020 128 = 27872399424 := rfl
private theorem moment_1817_380_part6 :
    blockEstimate 1817 380 1148 128 = 30812524608 := rfl
private theorem moment_1817_380_part7 :
    blockEstimate 1817 380 1276 128 = 32154619968 := rfl
private theorem moment_1817_380_part8 :
    blockEstimate 1817 380 1404 128 = 31898685504 := rfl
private theorem moment_1817_380_part9 :
    blockEstimate 1817 380 1532 128 = 30044721216 := rfl
private theorem moment_1817_380_part10 :
    blockEstimate 1817 380 1660 128 = 26592727104 := rfl
private theorem moment_1817_380_part11 :
    blockEstimate 1817 380 1788 128 = 21638440059 := rfl
private theorem moment_1817_380_part12 :
    blockEstimate 1817 380 1916 128 = 16076646528 := rfl
private theorem moment_1817_380_part13 :
    blockEstimate 1817 380 2044 128 = 10730530099 := rfl
private theorem moment_1817_380_part14 :
    blockEstimate 1817 380 2172 128 = 6072063646 := rfl
private theorem moment_1817_380_part15 :
    blockEstimate 1817 380 2300 128 = 2541701328 := rfl
private theorem moment_1817_380_part16 :
    blockEstimate 1817 380 2428 128 = 494759120 := rfl
private theorem moment_1817_380_part17 :
    blockEstimate 1817 380 2556 21 = 1710177 := rfl
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
    blockEstimate 2285 480 480 128 = 783404960 := rfl
private theorem moment_2285_480_part1 :
    blockEstimate 2285 480 608 128 = 5139931040 := rfl
private theorem moment_2285_480_part2 :
    blockEstimate 2285 480 736 128 = 13077344160 := rfl
private theorem moment_2285_480_part3 :
    blockEstimate 2285 480 864 128 = 23780618088 := rfl
private theorem moment_2285_480_part4 :
    blockEstimate 2285 480 992 128 = 35332736192 := rfl
private theorem moment_2285_480_part5 :
    blockEstimate 2285 480 1120 128 = 45144212672 := rfl
private theorem moment_2285_480_part6 :
    blockEstimate 2285 480 1248 128 = 52938228928 := rfl
private theorem moment_2285_480_part7 :
    blockEstimate 2285 480 1376 128 = 58714784960 := rfl
private theorem moment_2285_480_part8 :
    blockEstimate 2285 480 1504 128 = 62473880768 := rfl
private theorem moment_2285_480_part9 :
    blockEstimate 2285 480 1632 128 = 64215516352 := rfl
private theorem moment_2285_480_part10 :
    blockEstimate 2285 480 1760 128 = 63939691712 := rfl
private theorem moment_2285_480_part11 :
    blockEstimate 2285 480 1888 128 = 61646406848 := rfl
private theorem moment_2285_480_part12 :
    blockEstimate 2285 480 2016 128 = 57335661760 := rfl
private theorem moment_2285_480_part13 :
    blockEstimate 2285 480 2144 128 = 51007456448 := rfl
private theorem moment_2285_480_part14 :
    blockEstimate 2285 480 2272 128 = 42848244955 := rfl
private theorem moment_2285_480_part15 :
    blockEstimate 2285 480 2400 128 = 34024165326 := rfl
private theorem moment_2285_480_part16 :
    blockEstimate 2285 480 2528 128 = 25358865055 := rfl
private theorem moment_2285_480_part17 :
    blockEstimate 2285 480 2656 128 = 17353338622 := rfl
private theorem moment_2285_480_part18 :
    blockEstimate 2285 480 2784 128 = 10420160528 := rfl
private theorem moment_2285_480_part19 :
    blockEstimate 2285 480 2912 128 = 5035269136 := rfl
private theorem moment_2285_480_part20 :
    blockEstimate 2285 480 3040 128 = 1515991056 := rfl
private theorem moment_2285_480_part21 :
    blockEstimate 2285 480 3168 77 = 90657650 := rfl
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
    blockEstimate 2285 498 498 128 = 783404960 := rfl
private theorem moment_2285_498_part1 :
    blockEstimate 2285 498 626 128 = 5139931040 := rfl
private theorem moment_2285_498_part2 :
    blockEstimate 2285 498 754 128 = 13077344160 := rfl
private theorem moment_2285_498_part3 :
    blockEstimate 2285 498 882 128 = 23789529417 := rfl
private theorem moment_2285_498_part4 :
    blockEstimate 2285 498 1010 128 = 35672256512 := rfl
private theorem moment_2285_498_part5 :
    blockEstimate 2285 498 1138 128 = 45924478976 := rfl
private theorem moment_2285_498_part6 :
    blockEstimate 2285 498 1266 128 = 54083743744 := rfl
private theorem moment_2285_498_part7 :
    blockEstimate 2285 498 1394 128 = 60150050816 := rfl
private theorem moment_2285_498_part8 :
    blockEstimate 2285 498 1522 128 = 64123400192 := rfl
private theorem moment_2285_498_part9 :
    blockEstimate 2285 498 1650 128 = 66003791872 := rfl
private theorem moment_2285_498_part10 :
    blockEstimate 2285 498 1778 128 = 65791225856 := rfl
private theorem moment_2285_498_part11 :
    blockEstimate 2285 498 1906 128 = 63485702144 := rfl
private theorem moment_2285_498_part12 :
    blockEstimate 2285 498 2034 128 = 59087220736 := rfl
private theorem moment_2285_498_part13 :
    blockEstimate 2285 498 2162 128 = 52595798457 := rfl
private theorem moment_2285_498_part14 :
    blockEstimate 2285 498 2290 128 = 44296056302 := rfl
private theorem moment_2285_498_part15 :
    blockEstimate 2285 498 2418 128 = 35392420168 := rfl
private theorem moment_2285_498_part16 :
    blockEstimate 2285 498 2546 128 = 26610909096 := rfl
private theorem moment_2285_498_part17 :
    blockEstimate 2285 498 2674 128 = 18448620482 := rfl
private theorem moment_2285_498_part18 :
    blockEstimate 2285 498 2802 128 = 11312632000 := rfl
private theorem moment_2285_498_part19 :
    blockEstimate 2285 498 2930 128 = 5685571776 := rfl
private theorem moment_2285_498_part20 :
    blockEstimate 2285 498 3058 128 = 1888735424 := rfl
private theorem moment_2285_498_part21 :
    blockEstimate 2285 498 3186 95 = 167798160 := rfl
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

private theorem receipt_0_5_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 0) 0 128 = 32780760519429442864364160 := rfl
private theorem receipt_0_5_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 0) 128 128 = 16798798546043959325649897 := rfl
private theorem receipt_0_5_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 0) 256 101 = 3754130068453881626069235 := rfl
private theorem receipt_0_5_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 0) 128 229 = 20552928614497840951719132 :=
  phaseBlock_append receipt_0_5_2339_0_part1 receipt_0_5_2339_0_part2 rfl rfl rfl
private theorem receipt_0_5_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 0) 0 357 = 53333689133927283816083292 :=
  phaseBlock_append receipt_0_5_2339_0_part0 receipt_0_5_2339_0_join0 rfl rfl rfl

private theorem receipt_0_5_2339_0 : fastPhase (bank 0 5).shape 179827 2339 5 1 0 1 0 = 53333689133927283816083292 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2339_0_join1

private theorem receipt_0_5_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 1) 0 128 = 32646374529070577905743360 := rfl
private theorem receipt_0_5_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 1) 128 128 = 16685736128762643606857145 := rfl
private theorem receipt_0_5_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 1) 256 101 = 3678728159003401376158725 := rfl
private theorem receipt_0_5_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 1) 128 229 = 20364464287766044983015870 :=
  phaseBlock_append receipt_0_5_2339_1_part1 receipt_0_5_2339_1_part2 rfl rfl rfl
private theorem receipt_0_5_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2339 5 1 0 1 1) 0 357 = 53010838816836622888759230 :=
  phaseBlock_append receipt_0_5_2339_1_part0 receipt_0_5_2339_1_join0 rfl rfl rfl

private theorem receipt_0_5_2339_1 : fastPhase (bank 0 5).shape 179827 2339 5 1 0 1 1 = 53010838816836622888759230 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2339_1_join1

private theorem receipt_0_5_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 0) 0 128 = 32781038657624292392287840 := rfl
private theorem receipt_0_5_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 0) 128 128 = 16798909056522810886262834 := rfl
private theorem receipt_0_5_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 0) 256 101 = 3754147901878895809659171 := rfl
private theorem receipt_0_5_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 0) 128 229 = 20553056958401706695922005 :=
  phaseBlock_append receipt_0_5_2340_0_part1 receipt_0_5_2340_0_part2 rfl rfl rfl
private theorem receipt_0_5_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 0) 0 357 = 53334095616025999088209845 :=
  phaseBlock_append receipt_0_5_2340_0_part0 receipt_0_5_2340_0_join0 rfl rfl rfl

private theorem receipt_0_5_2340_0 : fastPhase (bank 0 5).shape 179827 2340 5 1 0 1 0 = 53334095616025999088209845 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2340_0_join1

private theorem receipt_0_5_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 1) 0 128 = 32646651722002414653779040 := rfl
private theorem receipt_0_5_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 1) 128 128 = 16685845995969178840693349 := rfl
private theorem receipt_0_5_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 1) 256 101 = 3678745673209553406962346 := rfl
private theorem receipt_0_5_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 1) 128 229 = 20364591669178732247655695 :=
  phaseBlock_append receipt_0_5_2340_1_part1 receipt_0_5_2340_1_part2 rfl rfl rfl
private theorem receipt_0_5_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 5).shape 179827 2340 5 1 0 1 1) 0 357 = 53011243391181146901434735 :=
  phaseBlock_append receipt_0_5_2340_1_part0 receipt_0_5_2340_1_join0 rfl rfl rfl

private theorem receipt_0_5_2340_1 : fastPhase (bank 0 5).shape 179827 2340 5 1 0 1 1 = 53011243391181146901434735 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_0_5_2340_1_join1

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_5_2339_0 receipt_0_5_2339_1 receipt_0_5_2340_0 receipt_0_5_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_5_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 0) 0 128 = 29481933117378117072345408 := rfl
private theorem receipt_1_5_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 0) 128 128 = 15070351909450588880604355 := rfl
private theorem receipt_1_5_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 0) 256 101 = 3360590660173237063051565 := rfl
private theorem receipt_1_5_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 0) 128 229 = 18430942569623825943655920 :=
  phaseBlock_append receipt_1_5_2339_0_part1 receipt_1_5_2339_0_part2 rfl rfl rfl
private theorem receipt_1_5_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 0) 0 357 = 47912875687001943016001328 :=
  phaseBlock_append receipt_1_5_2339_0_part0 receipt_1_5_2339_0_join0 rfl rfl rfl

private theorem receipt_1_5_2339_0 : fastPhase (bank 1 5).shape 179827 2339 5 1 0 2 0 = 47912875687001943016001328 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2339_0_join1

private theorem receipt_1_5_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 1) 0 128 = 29360488027809094780868352 := rfl
private theorem receipt_1_5_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 1) 128 128 = 14968634659679717322002319 := rfl
private theorem receipt_1_5_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 1) 256 101 = 3293047841386759075737585 := rfl
private theorem receipt_1_5_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 1) 128 229 = 18261682501066476397739904 :=
  phaseBlock_append receipt_1_5_2339_1_part1 receipt_1_5_2339_1_part2 rfl rfl rfl
private theorem receipt_1_5_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2339 5 1 0 2 1) 0 357 = 47622170528875571178608256 :=
  phaseBlock_append receipt_1_5_2339_1_part0 receipt_1_5_2339_1_join0 rfl rfl rfl

private theorem receipt_1_5_2339_1 : fastPhase (bank 1 5).shape 179827 2339 5 1 0 2 1 = 47622170528875571178608256 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2339_1_join1

private theorem receipt_1_5_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 0) 0 128 = 29482183277236968850829280 := rfl
private theorem receipt_1_5_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 0) 128 128 = 15070451055797512850988963 := rfl
private theorem receipt_1_5_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 0) 256 101 = 3360606624851813172511412 := rfl
private theorem receipt_1_5_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 0) 128 229 = 18431057680649326023500375 :=
  phaseBlock_append receipt_1_5_2340_0_part1 receipt_1_5_2340_0_part2 rfl rfl rfl
private theorem receipt_1_5_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 0) 0 357 = 47913240957886294874329655 :=
  phaseBlock_append receipt_1_5_2340_0_part0 receipt_1_5_2340_0_join0 rfl rfl rfl

private theorem receipt_1_5_2340_0 : fastPhase (bank 1 5).shape 179827 2340 5 1 0 2 0 = 47913240957886294874329655 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2340_0_join1

private theorem receipt_1_5_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 1) 0 128 = 29360737332535691606881760 := rfl
private theorem receipt_1_5_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 1) 128 128 = 14968733226999588447598765 := rfl
private theorem receipt_1_5_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 1) 256 101 = 3293063520067075294498650 := rfl
private theorem receipt_1_5_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 1) 128 229 = 18261796747066663742097415 :=
  phaseBlock_append receipt_1_5_2340_1_part1 receipt_1_5_2340_1_part2 rfl rfl rfl
private theorem receipt_1_5_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 5).shape 179827 2340 5 1 0 2 1) 0 357 = 47622534079602355348979175 :=
  phaseBlock_append receipt_1_5_2340_1_part0 receipt_1_5_2340_1_join0 rfl rfl rfl

private theorem receipt_1_5_2340_1 : fastPhase (bank 1 5).shape 179827 2340 5 1 0 2 1 = 47622534079602355348979175 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_1_5_2340_1_join1

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_5_2339_0 receipt_1_5_2339_1 receipt_1_5_2340_0 receipt_1_5_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_5_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 0) 0 128 = 15705839074693207689269248 := rfl
private theorem receipt_2_5_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 0) 128 128 = 7883288877640149351723187 := rfl
private theorem receipt_2_5_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 0) 256 101 = 1730292806968331380105531 := rfl
private theorem receipt_2_5_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 0) 128 229 = 9613581684608480731828718 :=
  phaseBlock_append receipt_2_5_2339_0_part1 receipt_2_5_2339_0_part2 rfl rfl rfl
private theorem receipt_2_5_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 0) 0 357 = 25319420759301688421097966 :=
  phaseBlock_append receipt_2_5_2339_0_part0 receipt_2_5_2339_0_join0 rfl rfl rfl

private theorem receipt_2_5_2339_0 : fastPhase (bank 2 5).shape 179827 2339 5 1 0 7 0 = 25319420759301688421097966 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2339_0_join1

private theorem receipt_2_5_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 1) 0 128 = 15638901200363371949212544 := rfl
private theorem receipt_2_5_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 1) 128 128 = 7828982154846713329936139 := rfl
private theorem receipt_2_5_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 1) 256 101 = 1695345260921493525572955 := rfl
private theorem receipt_2_5_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 1) 128 229 = 9524327415768206855509094 :=
  phaseBlock_append receipt_2_5_2339_1_part1 receipt_2_5_2339_1_part2 rfl rfl rfl
private theorem receipt_2_5_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2339 5 1 0 7 1) 0 357 = 25163228616131578804721638 :=
  phaseBlock_append receipt_2_5_2339_1_part0 receipt_2_5_2339_1_join0 rfl rfl rfl

private theorem receipt_2_5_2339_1 : fastPhase (bank 2 5).shape 179827 2339 5 1 0 7 1 = 25163228616131578804721638 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2339_1_join1

private theorem receipt_2_5_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 0) 0 128 = 15705972386166108234062464 := rfl
private theorem receipt_2_5_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 0) 128 128 = 7883340765461363208815865 := rfl
private theorem receipt_2_5_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 0) 256 101 = 1730301029484724235160995 := rfl
private theorem receipt_2_5_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 0) 128 229 = 9613641794946087443976860 :=
  phaseBlock_append receipt_2_5_2340_0_part1 receipt_2_5_2340_0_part2 rfl rfl rfl
private theorem receipt_2_5_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 0) 0 357 = 25319614181112195678039324 :=
  phaseBlock_append receipt_2_5_2340_0_part0 receipt_2_5_2340_0_join0 rfl rfl rfl

private theorem receipt_2_5_2340_0 : fastPhase (bank 2 5).shape 179827 2340 5 1 0 7 0 = 25319614181112195678039324 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2340_0_join1

private theorem receipt_2_5_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 1) 0 128 = 15639034037078676254199040 := rfl
private theorem receipt_2_5_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 1) 128 128 = 7829033732369810917452630 := rfl
private theorem receipt_2_5_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 1) 256 101 = 1695353335263986515781451 := rfl
private theorem receipt_2_5_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 1) 128 229 = 9524387067633797433234081 :=
  phaseBlock_append receipt_2_5_2340_1_part1 receipt_2_5_2340_1_part2 rfl rfl rfl
private theorem receipt_2_5_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 5).shape 179827 2340 5 1 0 7 1) 0 357 = 25163421104712473687433121 :=
  phaseBlock_append receipt_2_5_2340_1_part0 receipt_2_5_2340_1_join0 rfl rfl rfl

private theorem receipt_2_5_2340_1 : fastPhase (bank 2 5).shape 179827 2340 5 1 0 7 1 = 25163421104712473687433121 :=
  phase_of_block (n := 357) (by decide +kernel) receipt_2_5_2340_1_join1

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_356)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_5_2339_0 receipt_2_5_2339_1 receipt_2_5_2340_0 receipt_2_5_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_5_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 0) 0 128 = 3788339010864777011569248 := rfl
private theorem receipt_3_5_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 0) 128 128 = 1968647066836965970457184 := rfl
private theorem receipt_3_5_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 0) 256 115 = 506048976688791565930257 := rfl
private theorem receipt_3_5_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 0) 128 243 = 2474696043525757536387441 :=
  phaseBlock_append receipt_3_5_2339_0_part1 receipt_3_5_2339_0_part2 rfl rfl rfl
private theorem receipt_3_5_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 0) 0 371 = 6263035054390534547956689 :=
  phaseBlock_append receipt_3_5_2339_0_part0 receipt_3_5_2339_0_join0 rfl rfl rfl

private theorem receipt_3_5_2339_0 : fastPhase (bank 3 5).shape 179827 2339 5 1 1 1 0 = 6263035054390534547956689 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2339_0_join1

private theorem receipt_3_5_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 1) 0 128 = 3773017437866048774455200 := rfl
private theorem receipt_3_5_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 1) 128 128 = 1955862806050049180135328 := rfl
private theorem receipt_3_5_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 1) 256 115 = 496948220506092239314569 := rfl
private theorem receipt_3_5_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 1) 128 243 = 2452811026556141419449897 :=
  phaseBlock_append receipt_3_5_2339_1_part1 receipt_3_5_2339_1_part2 rfl rfl rfl
private theorem receipt_3_5_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2339 5 1 1 1 1) 0 371 = 6225828464422190193905097 :=
  phaseBlock_append receipt_3_5_2339_1_part0 receipt_3_5_2339_1_join0 rfl rfl rfl

private theorem receipt_3_5_2339_1 : fastPhase (bank 3 5).shape 179827 2339 5 1 1 1 1 = 6225828464422190193905097 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2339_1_join1

private theorem receipt_3_5_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 0) 0 128 = 3788369169843613708178784 := rfl
private theorem receipt_3_5_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 0) 128 128 = 1968656946682645030053216 := rfl
private theorem receipt_3_5_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 0) 256 115 = 506050266572603687985153 := rfl
private theorem receipt_3_5_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 0) 128 243 = 2474707213255248718038369 :=
  phaseBlock_append receipt_3_5_2340_0_part1 receipt_3_5_2340_0_part2 rfl rfl rfl
private theorem receipt_3_5_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 0) 0 371 = 6263076383098862426217153 :=
  phaseBlock_append receipt_3_5_2340_0_part0 receipt_3_5_2340_0_join0 rfl rfl rfl

private theorem receipt_3_5_2340_0 : fastPhase (bank 3 5).shape 179827 2340 5 1 1 1 0 = 6263076383098862426217153 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2340_0_join1

private theorem receipt_3_5_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 1) 0 128 = 3773047458434797999778784 := rfl
private theorem receipt_3_5_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 1) 128 128 = 1955872616260172542106592 := rfl
private theorem receipt_3_5_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 1) 256 115 = 496949489089266160840398 := rfl
private theorem receipt_3_5_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 1) 128 243 = 2452822105349438702946990 :=
  phaseBlock_append receipt_3_5_2340_1_part1 receipt_3_5_2340_1_part2 rfl rfl rfl
private theorem receipt_3_5_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 5).shape 179827 2340 5 1 1 1 1) 0 371 = 6225869563784236702725774 :=
  phaseBlock_append receipt_3_5_2340_1_part0 receipt_3_5_2340_1_join0 rfl rfl rfl

private theorem receipt_3_5_2340_1 : fastPhase (bank 3 5).shape 179827 2340 5 1 1 1 1 = 6225869563784236702725774 :=
  phase_of_block (n := 371) (by decide +kernel) receipt_3_5_2340_1_join1

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1696_370)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_5_2339_0 receipt_3_5_2339_1 receipt_3_5_2340_0 receipt_3_5_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_6_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 0) 0 128 = 60195048204230626565476638 := rfl
private theorem receipt_0_6_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 0) 128 128 = 32845720987403297376408455 := rfl
private theorem receipt_0_6_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 0) 256 125 = 9807437492149549368761169 := rfl
private theorem receipt_0_6_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 0) 128 253 = 42653158479552846745169624 :=
  phaseBlock_append receipt_0_6_2339_0_part1 receipt_0_6_2339_0_part2 rfl rfl rfl
private theorem receipt_0_6_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 0) 0 381 = 102848206683783473310646262 :=
  phaseBlock_append receipt_0_6_2339_0_part0 receipt_0_6_2339_0_join0 rfl rfl rfl

private theorem receipt_0_6_2339_0 : fastPhase (bank 0 6).shape 179827 2339 7 1 0 1 0 = 102848206683783473310646262 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2339_0_join1

private theorem receipt_0_6_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 1) 0 128 = 59966454267733994200859576 := rfl
private theorem receipt_0_6_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 1) 128 128 = 32651041754553078166101636 := rfl
private theorem receipt_0_6_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 1) 256 125 = 9647384758103626599099370 := rfl
private theorem receipt_0_6_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 1) 128 253 = 42298426512656704765201006 :=
  phaseBlock_append receipt_0_6_2339_1_part1 receipt_0_6_2339_1_part2 rfl rfl rfl
private theorem receipt_0_6_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2339 7 1 0 1 1) 0 381 = 102264880780390698966060582 :=
  phaseBlock_append receipt_0_6_2339_1_part0 receipt_0_6_2339_1_join0 rfl rfl rfl

private theorem receipt_0_6_2339_1 : fastPhase (bank 0 6).shape 179827 2339 7 1 0 1 1 = 102264880780390698966060582 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2339_1_join1

private theorem receipt_0_6_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 0) 0 128 = 60195563529980994210857448 := rfl
private theorem receipt_0_6_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 0) 128 128 = 32845942038094536466153376 := rfl
private theorem receipt_0_6_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 0) 256 125 = 9807485648765018469225642 := rfl
private theorem receipt_0_6_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 0) 128 253 = 42653427686859554935379018 :=
  phaseBlock_append receipt_0_6_2340_0_part1 receipt_0_6_2340_0_part2 rfl rfl rfl
private theorem receipt_0_6_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 0) 0 381 = 102848991216840549146236466 :=
  phaseBlock_append receipt_0_6_2340_0_part0 receipt_0_6_2340_0_join0 rfl rfl rfl

private theorem receipt_0_6_2340_0 : fastPhase (bank 0 6).shape 179827 2340 7 1 0 1 0 = 102848991216840549146236466 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2340_0_join1

private theorem receipt_0_6_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 1) 0 128 = 59966967972870584079618549 := rfl
private theorem receipt_0_6_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 1) 128 128 = 32651261675096379780135578 := rfl
private theorem receipt_0_6_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 1) 256 125 = 9647432224517520476404886 := rfl
private theorem receipt_0_6_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 1) 128 253 = 42298693899613900256540464 :=
  phaseBlock_append receipt_0_6_2340_1_part1 receipt_0_6_2340_1_part2 rfl rfl rfl
private theorem receipt_0_6_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 6).shape 179827 2340 7 1 0 1 1) 0 381 = 102265661872484484336159013 :=
  phaseBlock_append receipt_0_6_2340_1_part0 receipt_0_6_2340_1_join0 rfl rfl rfl

private theorem receipt_0_6_2340_1 : fastPhase (bank 0 6).shape 179827 2340 7 1 0 1 1 = 102265661872484484336159013 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_0_6_2340_1_join1

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_6_2339_0 receipt_0_6_2339_1 receipt_0_6_2340_0 receipt_0_6_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_6_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 0) 0 128 = 54214598739560073816389022 := rfl
private theorem receipt_1_6_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 0) 128 128 = 29521303306985251289969888 := rfl
private theorem receipt_1_6_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 0) 256 125 = 8798237837900470075317882 := rfl
private theorem receipt_1_6_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 0) 128 253 = 38319541144885721365287770 :=
  phaseBlock_append receipt_1_6_2339_0_part1 receipt_1_6_2339_0_part2 rfl rfl rfl
private theorem receipt_1_6_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 0) 0 381 = 92534139884445795181676792 :=
  phaseBlock_append receipt_1_6_2339_0_part0 receipt_1_6_2339_0_join0 rfl rfl rfl

private theorem receipt_1_6_2339_0 : fastPhase (bank 1 6).shape 179827 2339 7 1 0 2 0 = 92534139884445795181676792 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2339_0_join1

private theorem receipt_1_6_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 1) 0 128 = 54007835904372851528803799 := rfl
private theorem receipt_1_6_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 1) 128 128 = 29345860446351775288499616 := rfl
private theorem receipt_1_6_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 1) 256 125 = 8654557448753571170798374 := rfl
private theorem receipt_1_6_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 1) 128 253 = 38000417895105346459297990 :=
  phaseBlock_append receipt_1_6_2339_1_part1 receipt_1_6_2339_1_part2 rfl rfl rfl
private theorem receipt_1_6_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2339 7 1 0 2 1) 0 381 = 92008253799478197988101789 :=
  phaseBlock_append receipt_1_6_2339_1_part0 receipt_1_6_2339_1_join0 rfl rfl rfl

private theorem receipt_1_6_2339_1 : fastPhase (bank 1 6).shape 179827 2339 7 1 0 2 1 = 92008253799478197988101789 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2339_1_join1

private theorem receipt_1_6_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 0) 0 128 = 54215062883814027113528202 := rfl
private theorem receipt_1_6_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 0) 128 128 = 29521501994291479531893521 := rfl
private theorem receipt_1_6_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 0) 256 125 = 8798281041267422694717102 := rfl
private theorem receipt_1_6_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 0) 128 253 = 38319783035558902226610623 :=
  phaseBlock_append receipt_1_6_2340_0_part1 receipt_1_6_2340_0_part2 rfl rfl rfl
private theorem receipt_1_6_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 0) 0 381 = 92534845919372929340138825 :=
  phaseBlock_append receipt_1_6_2340_0_part0 receipt_1_6_2340_0_join0 rfl rfl rfl

private theorem receipt_1_6_2340_0 : fastPhase (bank 1 6).shape 179827 2340 7 1 0 2 0 = 92534845919372929340138825 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2340_0_join1

private theorem receipt_1_6_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 1) 0 128 = 54008298581423644149090429 := rfl
private theorem receipt_1_6_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 1) 128 128 = 29346058114685462681956058 := rfl
private theorem receipt_1_6_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 1) 256 125 = 8654600032394828874728618 := rfl
private theorem receipt_1_6_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 1) 128 253 = 38000658147080291556684676 :=
  phaseBlock_append receipt_1_6_2340_1_part1 receipt_1_6_2340_1_part2 rfl rfl rfl
private theorem receipt_1_6_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 6).shape 179827 2340 7 1 0 2 1) 0 381 = 92008956728503935705775105 :=
  phaseBlock_append receipt_1_6_2340_1_part0 receipt_1_6_2340_1_join0 rfl rfl rfl

private theorem receipt_1_6_2340_1 : fastPhase (bank 1 6).shape 179827 2340 7 1 0 2 1 = 92008956728503935705775105 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_1_6_2340_1_join1

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1817_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_6_2339_0 receipt_1_6_2339_1 receipt_1_6_2340_0 receipt_1_6_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_6_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 0) 0 128 = 29276105656958259272780960 := rfl
private theorem receipt_2_6_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 0) 128 128 = 15706396462410683644329120 := rfl
private theorem receipt_2_6_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 0) 256 125 = 4617611253327970427754012 := rfl
private theorem receipt_2_6_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 0) 128 253 = 20324007715738654072083132 :=
  phaseBlock_append receipt_2_6_2339_0_part1 receipt_2_6_2339_0_part2 rfl rfl rfl
private theorem receipt_2_6_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 0) 0 381 = 49600113372696913344864092 :=
  phaseBlock_append receipt_2_6_2339_0_part0 receipt_2_6_2339_0_join0 rfl rfl rfl

private theorem receipt_2_6_2339_0 : fastPhase (bank 2 6).shape 179827 2339 7 1 0 7 0 = 49600113372696913344864092 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2339_0_join1

private theorem receipt_2_6_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 1) 0 128 = 29161049879268728748918112 := rfl
private theorem receipt_2_6_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 1) 128 128 = 15611257455575141073220960 := rfl
private theorem receipt_2_6_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 1) 256 125 = 4541830992072871829860234 := rfl
private theorem receipt_2_6_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 1) 128 253 = 20153088447648012903081194 :=
  phaseBlock_append receipt_2_6_2339_1_part1 receipt_2_6_2339_1_part2 rfl rfl rfl
private theorem receipt_2_6_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2339 7 1 0 7 1) 0 381 = 49314138326916741651999306 :=
  phaseBlock_append receipt_2_6_2339_1_part0 receipt_2_6_2339_1_join0 rfl rfl rfl

private theorem receipt_2_6_2339_1 : fastPhase (bank 2 6).shape 179827 2339 7 1 0 7 1 = 49314138326916741651999306 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2339_1_join1

private theorem receipt_2_6_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 0) 0 128 = 29276354331438820888834880 := rfl
private theorem receipt_2_6_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 0) 128 128 = 15706501853209843752268608 := rfl
private theorem receipt_2_6_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 0) 256 125 = 4617633936068558647399902 := rfl
private theorem receipt_2_6_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 0) 128 253 = 20324135789278402399668510 :=
  phaseBlock_append receipt_2_6_2340_0_part1 receipt_2_6_2340_0_part2 rfl rfl rfl
private theorem receipt_2_6_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 0) 0 381 = 49600490120717223288503390 :=
  phaseBlock_append receipt_2_6_2340_0_part0 receipt_2_6_2340_0_join0 rfl rfl rfl

private theorem receipt_2_6_2340_0 : fastPhase (bank 2 6).shape 179827 2340 7 1 0 7 0 = 49600490120717223288503390 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2340_0_join1

private theorem receipt_2_6_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 1) 0 128 = 29161297738598564750444288 := rfl
private theorem receipt_2_6_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 1) 128 128 = 15611362293618545904510720 := rfl
private theorem receipt_2_6_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 1) 256 125 = 4541853347470320461574113 := rfl
private theorem receipt_2_6_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 1) 128 253 = 20153215641088866366084833 :=
  phaseBlock_append receipt_2_6_2340_1_part1 receipt_2_6_2340_1_part2 rfl rfl rfl
private theorem receipt_2_6_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 6).shape 179827 2340 7 1 0 7 1) 0 381 = 49314513379687431116529121 :=
  phaseBlock_append receipt_2_6_2340_1_part0 receipt_2_6_2340_1_join0 rfl rfl rfl

private theorem receipt_2_6_2340_1 : fastPhase (bank 2 6).shape 179827 2340 7 1 0 7 1 = 49314513379687431116529121 :=
  phase_of_block (n := 381) (by decide +kernel) receipt_2_6_2340_1_join1

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_380)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_6_2339_0 receipt_2_6_2339_1 receipt_2_6_2340_0 receipt_2_6_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_6_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 0 128 = 5809661079747021964686240 := rfl
private theorem receipt_3_6_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 128 128 = 3206630181956158519133088 := rfl
private theorem receipt_3_6_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 256 128 = 1065104015411682361660320 := rfl
private theorem receipt_3_6_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 384 12 = 7664654497416366643089 := rfl
private theorem receipt_3_6_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 0 256 = 9016291261703180483819328 :=
  phaseBlock_append receipt_3_6_2339_0_part0 receipt_3_6_2339_0_part1 rfl rfl rfl
private theorem receipt_3_6_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 256 140 = 1072768669909098728303409 :=
  phaseBlock_append receipt_3_6_2339_0_part2 receipt_3_6_2339_0_part3 rfl rfl rfl
private theorem receipt_3_6_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 0) 0 396 = 10089059931612279212122737 :=
  phaseBlock_append receipt_3_6_2339_0_join0 receipt_3_6_2339_0_join1 rfl rfl rfl

private theorem receipt_3_6_2339_0 : fastPhase (bank 3 6).shape 179827 2339 7 1 1 1 0 = 10089059931612279212122737 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2339_0_join2

private theorem receipt_3_6_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 0 128 = 5787892627490291640396000 := rfl
private theorem receipt_3_6_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 128 128 = 3188194286735997221091552 := rfl
private theorem receipt_3_6_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 256 128 = 1050337784850947030714592 := rfl
private theorem receipt_3_6_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 384 12 = 6480262374004813963239 := rfl
private theorem receipt_3_6_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 0 256 = 8976086914226288861487552 :=
  phaseBlock_append receipt_3_6_2339_1_part0 receipt_3_6_2339_1_part1 rfl rfl rfl
private theorem receipt_3_6_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 256 140 = 1056818047224951844677831 :=
  phaseBlock_append receipt_3_6_2339_1_part2 receipt_3_6_2339_1_part3 rfl rfl rfl
private theorem receipt_3_6_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2339 7 1 1 1 1) 0 396 = 10032904961451240706165383 :=
  phaseBlock_append receipt_3_6_2339_1_join0 receipt_3_6_2339_1_join1 rfl rfl rfl

private theorem receipt_3_6_2339_1 : fastPhase (bank 3 6).shape 179827 2339 7 1 1 1 1 = 10032904961451240706165383 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2339_1_join2

private theorem receipt_3_6_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 0 128 = 5809707557227289559073440 := rfl
private theorem receipt_3_6_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 128 128 = 3206646929833471192306336 := rfl
private theorem receipt_3_6_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 256 128 = 1065106962083047811883680 := rfl
private theorem receipt_3_6_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 384 12 = 7664662255612847891913 := rfl
private theorem receipt_3_6_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 0 256 = 9016354487060760751379776 :=
  phaseBlock_append receipt_3_6_2340_0_part0 receipt_3_6_2340_0_part1 rfl rfl rfl
private theorem receipt_3_6_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 256 140 = 1072771624338660659775593 :=
  phaseBlock_append receipt_3_6_2340_0_part2 receipt_3_6_2340_0_part3 rfl rfl rfl
private theorem receipt_3_6_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 0) 0 396 = 10089126111399421411155369 :=
  phaseBlock_append receipt_3_6_2340_0_join0 receipt_3_6_2340_0_join1 rfl rfl rfl

private theorem receipt_3_6_2340_0 : fastPhase (bank 3 6).shape 179827 2340 7 1 1 1 0 = 10089126111399421411155369 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2340_0_join2

private theorem receipt_3_6_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 0 128 = 5787938906842268151162400 := rfl
private theorem receipt_3_6_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 128 128 = 3188210929118654855632416 := rfl
private theorem receipt_3_6_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 256 128 = 1050340692472397028263456 := rfl
private theorem receipt_3_6_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 384 12 = 6480268959844505069937 := rfl
private theorem receipt_3_6_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 0 256 = 8976149835960923006794816 :=
  phaseBlock_append receipt_3_6_2340_1_part0 receipt_3_6_2340_1_part1 rfl rfl rfl
private theorem receipt_3_6_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 256 140 = 1056820961432241533333393 :=
  phaseBlock_append receipt_3_6_2340_1_part2 receipt_3_6_2340_1_part3 rfl rfl rfl
private theorem receipt_3_6_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 6).shape 179827 2340 7 1 1 1 1) 0 396 = 10032970797393164540128209 :=
  phaseBlock_append receipt_3_6_2340_1_join0 receipt_3_6_2340_1_join1 rfl rfl rfl

private theorem receipt_3_6_2340_1 : fastPhase (bank 3 6).shape 179827 2340 7 1 1 1 1 = 10032970797393164540128209 :=
  phase_of_block (n := 396) (by decide +kernel) receipt_3_6_2340_1_join2

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1809_395)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_6_2339_0 receipt_3_6_2339_1 receipt_3_6_2340_0 receipt_3_6_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_7_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 0 128 = 144844855803441277616982048 := rfl
private theorem receipt_0_7_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 128 128 = 93491065088842644876376096 := rfl
private theorem receipt_0_7_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 256 128 = 48519218160174058663405374 := rfl
private theorem receipt_0_7_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 384 97 = 10478837906419924226110364 := rfl
private theorem receipt_0_7_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 0 256 = 238335920892283922493358144 :=
  phaseBlock_append receipt_0_7_2339_0_part0 receipt_0_7_2339_0_part1 rfl rfl rfl
private theorem receipt_0_7_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 256 225 = 58998056066593982889515738 :=
  phaseBlock_append receipt_0_7_2339_0_part2 receipt_0_7_2339_0_part3 rfl rfl rfl
private theorem receipt_0_7_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 0) 0 481 = 297333976958877905382873882 :=
  phaseBlock_append receipt_0_7_2339_0_join0 receipt_0_7_2339_0_join1 rfl rfl rfl

private theorem receipt_0_7_2339_0 : fastPhase (bank 0 7).shape 179827 2339 10 1 0 1 0 = 297333976958877905382873882 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2339_0_join2

private theorem receipt_0_7_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 0 128 = 144422969116457643851113952 := rfl
private theorem receipt_0_7_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 128 128 = 93118987581672004625176032 := rfl
private theorem receipt_0_7_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 256 128 = 48193733929376705994502280 := rfl
private theorem receipt_0_7_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 384 97 = 10261257431154169518597024 := rfl
private theorem receipt_0_7_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 0 256 = 237541956698129648476289984 :=
  phaseBlock_append receipt_0_7_2339_1_part0 receipt_0_7_2339_1_part1 rfl rfl rfl
private theorem receipt_0_7_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 256 225 = 58454991360530875513099304 :=
  phaseBlock_append receipt_0_7_2339_1_part2 receipt_0_7_2339_1_part3 rfl rfl rfl
private theorem receipt_0_7_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2339 10 1 0 1 1) 0 481 = 295996948058660523989389288 :=
  phaseBlock_append receipt_0_7_2339_1_join0 receipt_0_7_2339_1_join1 rfl rfl rfl

private theorem receipt_0_7_2339_1 : fastPhase (bank 0 7).shape 179827 2339 10 1 0 1 1 = 295996948058660523989389288 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2339_1_join2

private theorem receipt_0_7_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 0 128 = 144846106510100265740709888 := rfl
private theorem receipt_0_7_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 128 128 = 93491741223531135035314176 := rfl
private theorem receipt_0_7_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 256 128 = 48519496199196651308536656 := rfl
private theorem receipt_0_7_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 384 97 = 10478883399787929480626684 := rfl
private theorem receipt_0_7_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 0 256 = 238337847733631400776024064 :=
  phaseBlock_append receipt_0_7_2340_0_part0 receipt_0_7_2340_0_part1 rfl rfl rfl
private theorem receipt_0_7_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 256 225 = 58998379598984580789163340 :=
  phaseBlock_append receipt_0_7_2340_0_part2 receipt_0_7_2340_0_part3 rfl rfl rfl
private theorem receipt_0_7_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 0) 0 481 = 297336227332615981565187404 :=
  phaseBlock_append receipt_0_7_2340_0_join0 receipt_0_7_2340_0_join1 rfl rfl rfl

private theorem receipt_0_7_2340_0 : fastPhase (bank 0 7).shape 179827 2340 10 1 0 1 0 = 297336227332615981565187404 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2340_0_join2

private theorem receipt_0_7_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 0 128 = 144424216811279442051774144 := rfl
private theorem receipt_0_7_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 128 128 = 93119661415893061699499712 := rfl
private theorem receipt_0_7_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 256 128 = 48194010312483177206917564 := rfl
private theorem receipt_0_7_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 384 97 = 10261302060539761064801439 := rfl
private theorem receipt_0_7_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 0 256 = 237543878227172503751273856 :=
  phaseBlock_append receipt_0_7_2340_1_part0 receipt_0_7_2340_1_part1 rfl rfl rfl
private theorem receipt_0_7_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 256 225 = 58455312373022938271719003 :=
  phaseBlock_append receipt_0_7_2340_1_part2 receipt_0_7_2340_1_part3 rfl rfl rfl
private theorem receipt_0_7_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 7).shape 179827 2340 10 1 0 1 1) 0 481 = 295999190600195442022992859 :=
  phaseBlock_append receipt_0_7_2340_1_join0 receipt_0_7_2340_1_join1 rfl rfl rfl

private theorem receipt_0_7_2340_1 : fastPhase (bank 0 7).shape 179827 2340 10 1 0 1 1 = 295999190600195442022992859 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_0_7_2340_1_join2

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_7_2339_0 receipt_0_7_2339_1 receipt_0_7_2340_0 receipt_0_7_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_7_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 0 128 = 130292260735175058977294304 := rfl
private theorem receipt_1_7_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 128 128 = 83933017578658072629155808 := rfl
private theorem receipt_1_7_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 256 128 = 43474712091597011301169884 := rfl
private theorem receipt_1_7_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 384 97 = 9373936666784250540363884 := rfl
private theorem receipt_1_7_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 0 256 = 214225278313833131606450112 :=
  phaseBlock_append receipt_1_7_2339_0_part0 receipt_1_7_2339_0_part1 rfl rfl rfl
private theorem receipt_1_7_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 256 225 = 52848648758381261841533768 :=
  phaseBlock_append receipt_1_7_2339_0_part2 receipt_1_7_2339_0_part3 rfl rfl rfl
private theorem receipt_1_7_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 0) 0 481 = 267073927072214393447983880 :=
  phaseBlock_append receipt_1_7_2339_0_join0 receipt_1_7_2339_0_join1 rfl rfl rfl

private theorem receipt_1_7_2339_0 : fastPhase (bank 1 7).shape 179827 2339 10 1 0 2 0 = 267073927072214393447983880 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2339_0_join2

private theorem receipt_1_7_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 0 128 = 129910763890888851434811552 := rfl
private theorem receipt_1_7_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 128 128 = 83597701582280212399628448 := rfl
private theorem receipt_1_7_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 256 128 = 43182430517661589980869136 := rfl
private theorem receipt_1_7_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 384 97 = 9179201649217328863001910 := rfl
private theorem receipt_1_7_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 0 256 = 213508465473169063834440000 :=
  phaseBlock_append receipt_1_7_2339_1_part0 receipt_1_7_2339_1_part1 rfl rfl rfl
private theorem receipt_1_7_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 256 225 = 52361632166878918843871046 :=
  phaseBlock_append receipt_1_7_2339_1_part2 receipt_1_7_2339_1_part3 rfl rfl rfl
private theorem receipt_1_7_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2339 10 1 0 2 1) 0 481 = 265870097640047982678311046 :=
  phaseBlock_append receipt_1_7_2339_1_join0 receipt_1_7_2339_1_join1 rfl rfl rfl

private theorem receipt_1_7_2339_1 : fastPhase (bank 1 7).shape 179827 2339 10 1 0 2 1 = 265870097640047982678311046 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2339_1_join2

private theorem receipt_1_7_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 0 128 = 130293385812118018675997504 := rfl
private theorem receipt_1_7_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 128 128 = 83933624608999354501585728 := rfl
private theorem receipt_1_7_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 256 128 = 43474961234239288939586982 := rfl
private theorem receipt_1_7_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 384 97 = 9373977364329915882759968 := rfl
private theorem receipt_1_7_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 0 256 = 214227010421117373177583232 :=
  phaseBlock_append receipt_1_7_2340_0_part0 receipt_1_7_2340_0_part1 rfl rfl rfl
private theorem receipt_1_7_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 256 225 = 52848938598569204822346950 :=
  phaseBlock_append receipt_1_7_2340_0_part2 receipt_1_7_2340_0_part3 rfl rfl rfl
private theorem receipt_1_7_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 0) 0 481 = 267075949019686577999930182 :=
  phaseBlock_append receipt_1_7_2340_0_join0 receipt_1_7_2340_0_join1 rfl rfl rfl

private theorem receipt_1_7_2340_0 : fastPhase (bank 1 7).shape 179827 2340 10 1 0 2 0 = 267075949019686577999930182 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2340_0_join2

private theorem receipt_1_7_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 0 128 = 129911886241260136186113984 := rfl
private theorem receipt_1_7_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 128 128 = 83598306538016977857875904 := rfl
private theorem receipt_1_7_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 256 128 = 43182678172814802373510312 := rfl
private theorem receipt_1_7_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 384 97 = 9179241573417429078864152 := rfl
private theorem receipt_1_7_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 0 256 = 213510192779277114043989888 :=
  phaseBlock_append receipt_1_7_2340_1_part0 receipt_1_7_2340_1_part1 rfl rfl rfl
private theorem receipt_1_7_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 256 225 = 52361919746232231452374464 :=
  phaseBlock_append receipt_1_7_2340_1_part2 receipt_1_7_2340_1_part3 rfl rfl rfl
private theorem receipt_1_7_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 7).shape 179827 2340 10 1 0 2 1) 0 481 = 265872112525509345496364352 :=
  phaseBlock_append receipt_1_7_2340_1_join0 receipt_1_7_2340_1_join1 rfl rfl rfl

private theorem receipt_1_7_2340_1 : fastPhase (bank 1 7).shape 179827 2340 10 1 0 2 1 = 265872112525509345496364352 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_1_7_2340_1_join2

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_7_2339_0 receipt_1_7_2339_1 receipt_1_7_2340_0 receipt_1_7_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_7_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 0 128 = 69516179668916647100796768 := rfl
private theorem receipt_2_7_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 128 128 = 44149439188408378419470176 := rfl
private theorem receipt_2_7_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 256 128 = 22547534058355683081134430 := rfl
private theorem receipt_2_7_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 384 97 = 4803218215742223271436750 := rfl
private theorem receipt_2_7_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 0 256 = 113665618857325025520266944 :=
  phaseBlock_append receipt_2_7_2339_0_part0 receipt_2_7_2339_0_part1 rfl rfl rfl
private theorem receipt_2_7_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 256 225 = 27350752274097906352571180 :=
  phaseBlock_append receipt_2_7_2339_0_part2 receipt_2_7_2339_0_part3 rfl rfl rfl
private theorem receipt_2_7_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 0) 0 481 = 141016371131422931872838124 :=
  phaseBlock_append receipt_2_7_2339_0_join0 receipt_2_7_2339_0_join1 rfl rfl rfl

private theorem receipt_2_7_2339_0 : fastPhase (bank 2 7).shape 179827 2339 10 1 0 7 0 = 141016371131422931872838124 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2339_0_join2

private theorem receipt_2_7_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 0 128 = 69304951531083312475340000 := rfl
private theorem receipt_2_7_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 128 128 = 43968174068409160064503008 := rfl
private theorem receipt_2_7_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 256 128 = 22393522656526305445833518 := rfl
private theorem receipt_2_7_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 384 97 = 4703070711555427602141828 := rfl
private theorem receipt_2_7_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 0 256 = 113273125599492472539843008 :=
  phaseBlock_append receipt_2_7_2339_1_part0 receipt_2_7_2339_1_part1 rfl rfl rfl
private theorem receipt_2_7_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 256 225 = 27096593368081733047975346 :=
  phaseBlock_append receipt_2_7_2339_1_part2 receipt_2_7_2339_1_part3 rfl rfl rfl
private theorem receipt_2_7_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2339 10 1 0 7 1) 0 481 = 140369718967574205587818354 :=
  phaseBlock_append receipt_2_7_2339_1_join0 receipt_2_7_2339_1_join1 rfl rfl rfl

private theorem receipt_2_7_2339_1 : fastPhase (bank 2 7).shape 179827 2339 10 1 0 7 1 = 140369718967574205587818354 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2339_1_join2

private theorem receipt_2_7_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 0 128 = 69516780054672796712031648 := rfl
private theorem receipt_2_7_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 128 128 = 44149758568454114966472096 := rfl
private theorem receipt_2_7_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 256 128 = 22547663314870934329780698 := rfl
private theorem receipt_2_7_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 384 97 = 4803239073200896220039147 := rfl
private theorem receipt_2_7_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 0 256 = 113666538623126911678503744 :=
  phaseBlock_append receipt_2_7_2340_0_part0 receipt_2_7_2340_0_part1 rfl rfl rfl
private theorem receipt_2_7_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 256 225 = 27350902388071830549819845 :=
  phaseBlock_append receipt_2_7_2340_0_part2 receipt_2_7_2340_0_part3 rfl rfl rfl
private theorem receipt_2_7_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 0) 0 481 = 141017441011198742228323589 :=
  phaseBlock_append receipt_2_7_2340_0_join0 receipt_2_7_2340_0_join1 rfl rfl rfl

private theorem receipt_2_7_2340_0 : fastPhase (bank 2 7).shape 179827 2340 10 1 0 7 0 = 141017441011198742228323589 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2340_0_join2

private theorem receipt_2_7_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 0 128 = 69305550395402831130085920 := rfl
private theorem receipt_2_7_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 128 128 = 43968492321532595257629216 := rfl
private theorem receipt_2_7_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 256 128 = 22393651127369347428151549 := rfl
private theorem receipt_2_7_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 384 97 = 4703091171001175468121774 := rfl
private theorem receipt_2_7_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 0 256 = 113274042716935426387715136 :=
  phaseBlock_append receipt_2_7_2340_1_part0 receipt_2_7_2340_1_part1 rfl rfl rfl
private theorem receipt_2_7_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 256 225 = 27096742298370522896273323 :=
  phaseBlock_append receipt_2_7_2340_1_part2 receipt_2_7_2340_1_part3 rfl rfl rfl
private theorem receipt_2_7_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 7).shape 179827 2340 10 1 0 7 1) 0 481 = 140370785015305949283988459 :=
  phaseBlock_append receipt_2_7_2340_1_join0 receipt_2_7_2340_1_join1 rfl rfl rfl

private theorem receipt_2_7_2340_1 : fastPhase (bank 2 7).shape 179827 2340 10 1 0 7 1 = 140370785015305949283988459 :=
  phase_of_block (n := 481) (by decide +kernel) receipt_2_7_2340_1_join2

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_480)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_7_2339_0 receipt_2_7_2339_1 receipt_2_7_2340_0 receipt_2_7_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_7_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 0 128 = 17357969404539881780732832 := rfl
private theorem receipt_3_7_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 128 128 = 11267691563979392677794720 := rfl
private theorem receipt_3_7_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 256 128 = 5984009768284807186203552 := rfl
private theorem receipt_3_7_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 384 115 = 1579513170591578340303471 := rfl
private theorem receipt_3_7_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 0 256 = 28625660968519274458527552 :=
  phaseBlock_append receipt_3_7_2339_0_part0 receipt_3_7_2339_0_part1 rfl rfl rfl
private theorem receipt_3_7_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 256 243 = 7563522938876385526507023 :=
  phaseBlock_append receipt_3_7_2339_0_part2 receipt_3_7_2339_0_part3 rfl rfl rfl
private theorem receipt_3_7_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 0) 0 499 = 36189183907395659985034575 :=
  phaseBlock_append receipt_3_7_2339_0_join0 receipt_3_7_2339_0_join1 rfl rfl rfl

private theorem receipt_3_7_2339_0 : fastPhase (bank 3 7).shape 179827 2339 10 1 1 1 0 = 36189183907395659985034575 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2339_0_join2

private theorem receipt_3_7_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 0 128 = 17308009858908104859077856 := rfl
private theorem receipt_3_7_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 128 128 = 11223594040223496014888160 := rfl
private theorem receipt_3_7_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 256 128 = 5946250772372922120973536 := rfl
private theorem receipt_3_7_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 384 115 = 1551378214156495420612728 := rfl
private theorem receipt_3_7_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 0 256 = 28531603899131600873966016 :=
  phaseBlock_append receipt_3_7_2339_1_part0 receipt_3_7_2339_1_part1 rfl rfl rfl
private theorem receipt_3_7_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 256 243 = 7497628986529417541586264 :=
  phaseBlock_append receipt_3_7_2339_1_part2 receipt_3_7_2339_1_part3 rfl rfl rfl
private theorem receipt_3_7_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2339 10 1 1 1 1) 0 499 = 36029232885661018415552280 :=
  phaseBlock_append receipt_3_7_2339_1_join0 receipt_3_7_2339_1_join1 rfl rfl rfl

private theorem receipt_3_7_2339_1 : fastPhase (bank 3 7).shape 179827 2339 10 1 1 1 1 = 36029232885661018415552280 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2339_1_join2

private theorem receipt_3_7_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 0 128 = 17358112433029809684834848 := rfl
private theorem receipt_3_7_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 128 128 = 11267759095678578034252320 := rfl
private theorem receipt_3_7_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 256 128 = 5984032966436145294854688 := rfl
private theorem receipt_3_7_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 384 115 = 1579516449748571702121819 := rfl
private theorem receipt_3_7_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 0 256 = 28625871528708387719087168 :=
  phaseBlock_append receipt_3_7_2340_0_part0 receipt_3_7_2340_0_part1 rfl rfl rfl
private theorem receipt_3_7_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 256 243 = 7563549416184716996976507 :=
  phaseBlock_append receipt_3_7_2340_0_part2 receipt_3_7_2340_0_part3 rfl rfl rfl
private theorem receipt_3_7_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 0) 0 499 = 36189420944893104716063675 :=
  phaseBlock_append receipt_3_7_2340_0_join0 receipt_3_7_2340_0_join1 rfl rfl rfl

private theorem receipt_3_7_2340_0 : fastPhase (bank 3 7).shape 179827 2340 10 1 1 1 0 = 36189420944893104716063675 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2340_0_join2

private theorem receipt_3_7_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 0 128 = 17308152416161026852377568 := rfl
private theorem receipt_3_7_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 128 128 = 11223661276421605352195040 := rfl
private theorem receipt_3_7_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 256 128 = 5946273813183602146391008 := rfl
private theorem receipt_3_7_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 384 115 = 1551381439478385678153884 := rfl
private theorem receipt_3_7_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 0 256 = 28531813692582632204572608 :=
  phaseBlock_append receipt_3_7_2340_1_part0 receipt_3_7_2340_1_part1 rfl rfl rfl
private theorem receipt_3_7_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 256 243 = 7497655252661987824544892 :=
  phaseBlock_append receipt_3_7_2340_1_part2 receipt_3_7_2340_1_part3 rfl rfl rfl
private theorem receipt_3_7_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 7).shape 179827 2340 10 1 1 1 1) 0 499 = 36029468945244620029117500 :=
  phaseBlock_append receipt_3_7_2340_1_join0 receipt_3_7_2340_1_join1 rfl rfl rfl

private theorem receipt_3_7_2340_1 : fastPhase (bank 3 7).shape 179827 2340 10 1 1 1 1 = 36029468945244620029117500 :=
  phase_of_block (n := 499) (by decide +kernel) receipt_3_7_2340_1_join2

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2285_498)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_7_2339_0 receipt_3_7_2339_1 receipt_3_7_2340_0 receipt_3_7_2340_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group2_stage i)).shape
      (cutoff h rect (group2_stage i)), ¬ G∣Q :=
  (group2_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group2_avoids

end Lower6960.RescueSource
