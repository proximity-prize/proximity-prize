import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_2091_456_part0 :
    blockEstimate 2091 456 456 128 = 713999520 := by decide +kernel
private theorem moment_2091_456_part1 :
    blockEstimate 2091 456 584 128 = 4660499616 := by decide +kernel
private theorem moment_2091_456_part2 :
    blockEstimate 2091 456 712 128 = 11781039264 := by decide +kernel
private theorem moment_2091_456_part3 :
    blockEstimate 2091 456 840 128 = 21223686286 := by decide +kernel
private theorem moment_2091_456_part4 :
    blockEstimate 2091 456 968 128 = 30814903104 := by decide +kernel
private theorem moment_2091_456_part5 :
    blockEstimate 2091 456 1096 128 = 38594403136 := by decide +kernel
private theorem moment_2091_456_part6 :
    blockEstimate 2091 456 1224 128 = 44457106240 := by decide +kernel
private theorem moment_2091_456_part7 :
    blockEstimate 2091 456 1352 128 = 48403012416 := by decide +kernel
private theorem moment_2091_456_part8 :
    blockEstimate 2091 456 1480 128 = 50432121664 := by decide +kernel
private theorem moment_2091_456_part9 :
    blockEstimate 2091 456 1608 128 = 50544433984 := by decide +kernel
private theorem moment_2091_456_part10 :
    blockEstimate 2091 456 1736 128 = 48739949376 := by decide +kernel
private theorem moment_2091_456_part11 :
    blockEstimate 2091 456 1864 128 = 45018667840 := by decide +kernel
private theorem moment_2091_456_part12 :
    blockEstimate 2091 456 1992 128 = 39383175281 := by decide +kernel
private theorem moment_2091_456_part13 :
    blockEstimate 2091 456 2120 128 = 32263153930 := by decide +kernel
private theorem moment_2091_456_part14 :
    blockEstimate 2091 456 2248 128 = 24796295029 := by decide +kernel
private theorem moment_2091_456_part15 :
    blockEstimate 2091 456 2376 128 = 17602076717 := by decide +kernel
private theorem moment_2091_456_part16 :
    blockEstimate 2091 456 2504 128 = 11142425823 := by decide +kernel
private theorem moment_2091_456_part17 :
    blockEstimate 2091 456 2632 128 = 5851247200 := by decide +kernel
private theorem moment_2091_456_part18 :
    blockEstimate 2091 456 2760 128 = 2140420704 := by decide +kernel
private theorem moment_2091_456_part19 :
    blockEstimate 2091 456 2888 115 = 268468747 := by decide +kernel
private theorem moment_2091_456_join0 :
    blockEstimate 2091 456 456 256 = 5374499136 :=
  block_append moment_2091_456_part0 moment_2091_456_part1 rfl rfl rfl
private theorem moment_2091_456_join1 :
    blockEstimate 2091 456 840 256 = 52038589390 :=
  block_append moment_2091_456_part3 moment_2091_456_part4 rfl rfl rfl
private theorem moment_2091_456_join2 :
    blockEstimate 2091 456 712 384 = 63819628654 :=
  block_append moment_2091_456_part2 moment_2091_456_join1 rfl rfl rfl
private theorem moment_2091_456_join3 :
    blockEstimate 2091 456 456 640 = 69194127790 :=
  block_append moment_2091_456_join0 moment_2091_456_join2 rfl rfl rfl
private theorem moment_2091_456_join4 :
    blockEstimate 2091 456 1096 256 = 83051509376 :=
  block_append moment_2091_456_part5 moment_2091_456_part6 rfl rfl rfl
private theorem moment_2091_456_join5 :
    blockEstimate 2091 456 1480 256 = 100976555648 :=
  block_append moment_2091_456_part8 moment_2091_456_part9 rfl rfl rfl
private theorem moment_2091_456_join6 :
    blockEstimate 2091 456 1352 384 = 149379568064 :=
  block_append moment_2091_456_part7 moment_2091_456_join5 rfl rfl rfl
private theorem moment_2091_456_join7 :
    blockEstimate 2091 456 1096 640 = 232431077440 :=
  block_append moment_2091_456_join4 moment_2091_456_join6 rfl rfl rfl
private theorem moment_2091_456_join8 :
    blockEstimate 2091 456 456 1280 = 301625205230 :=
  block_append moment_2091_456_join3 moment_2091_456_join7 rfl rfl rfl
private theorem moment_2091_456_join9 :
    blockEstimate 2091 456 1736 256 = 93758617216 :=
  block_append moment_2091_456_part10 moment_2091_456_part11 rfl rfl rfl
private theorem moment_2091_456_join10 :
    blockEstimate 2091 456 2120 256 = 57059448959 :=
  block_append moment_2091_456_part13 moment_2091_456_part14 rfl rfl rfl
private theorem moment_2091_456_join11 :
    blockEstimate 2091 456 1992 384 = 96442624240 :=
  block_append moment_2091_456_part12 moment_2091_456_join10 rfl rfl rfl
private theorem moment_2091_456_join12 :
    blockEstimate 2091 456 1736 640 = 190201241456 :=
  block_append moment_2091_456_join9 moment_2091_456_join11 rfl rfl rfl
private theorem moment_2091_456_join13 :
    blockEstimate 2091 456 2376 256 = 28744502540 :=
  block_append moment_2091_456_part15 moment_2091_456_part16 rfl rfl rfl
private theorem moment_2091_456_join14 :
    blockEstimate 2091 456 2760 243 = 2408889451 :=
  block_append moment_2091_456_part18 moment_2091_456_part19 rfl rfl rfl
private theorem moment_2091_456_join15 :
    blockEstimate 2091 456 2632 371 = 8260136651 :=
  block_append moment_2091_456_part17 moment_2091_456_join14 rfl rfl rfl
private theorem moment_2091_456_join16 :
    blockEstimate 2091 456 2376 627 = 37004639191 :=
  block_append moment_2091_456_join13 moment_2091_456_join15 rfl rfl rfl
private theorem moment_2091_456_join17 :
    blockEstimate 2091 456 1736 1267 = 227205880647 :=
  block_append moment_2091_456_join12 moment_2091_456_join16 rfl rfl rfl
private theorem moment_2091_456_join18 :
    blockEstimate 2091 456 456 2547 = 528831085877 :=
  block_append moment_2091_456_join8 moment_2091_456_join17 rfl rfl rfl

theorem moment_2091_456 : momentEstimate 2091 456 = 528831085877 := moment_2091_456_join18

private theorem moment_2100_439_part0 :
    blockEstimate 2100 439 439 128 = 717219360 := by decide +kernel
private theorem moment_2100_439_part1 :
    blockEstimate 2100 439 567 128 = 4682741280 := by decide +kernel
private theorem moment_2100_439_part2 :
    blockEstimate 2100 439 695 128 = 11841177120 := by decide +kernel
private theorem moment_2100_439_part3 :
    blockEstimate 2100 439 823 128 = 21283064550 := by decide +kernel
private theorem moment_2100_439_part4 :
    blockEstimate 2100 439 951 128 = 30575072000 := by decide +kernel
private theorem moment_2100_439_part5 :
    blockEstimate 2100 439 1079 128 = 38068785920 := by decide +kernel
private theorem moment_2100_439_part6 :
    blockEstimate 2100 439 1207 128 = 43717006080 := by decide +kernel
private theorem moment_2100_439_part7 :
    blockEstimate 2100 439 1335 128 = 47519732480 := by decide +kernel
private theorem moment_2100_439_part8 :
    blockEstimate 2100 439 1463 128 = 49476965120 := by decide +kernel
private theorem moment_2100_439_part9 :
    blockEstimate 2100 439 1591 128 = 49588704000 := by decide +kernel
private theorem moment_2100_439_part10 :
    blockEstimate 2100 439 1719 128 = 47854949120 := by decide +kernel
private theorem moment_2100_439_part11 :
    blockEstimate 2100 439 1847 128 = 44275700480 := by decide +kernel
private theorem moment_2100_439_part12 :
    blockEstimate 2100 439 1975 128 = 38850961755 := by decide +kernel
private theorem moment_2100_439_part13 :
    blockEstimate 2100 439 2103 128 = 31839629831 := by decide +kernel
private theorem moment_2100_439_part14 :
    blockEstimate 2100 439 2231 128 = 24393218274 := by decide +kernel
private theorem moment_2100_439_part15 :
    blockEstimate 2100 439 2359 128 = 17228999980 := by decide +kernel
private theorem moment_2100_439_part16 :
    blockEstimate 2100 439 2487 128 = 10819779729 := by decide +kernel
private theorem moment_2100_439_part17 :
    blockEstimate 2100 439 2615 128 = 5596600704 := by decide +kernel
private theorem moment_2100_439_part18 :
    blockEstimate 2100 439 2743 128 = 1975910784 := by decide +kernel
private theorem moment_2100_439_part19 :
    blockEstimate 2100 439 2871 107 = 218225466 := by decide +kernel
private theorem moment_2100_439_join0 :
    blockEstimate 2100 439 439 256 = 5399960640 :=
  block_append moment_2100_439_part0 moment_2100_439_part1 rfl rfl rfl
private theorem moment_2100_439_join1 :
    blockEstimate 2100 439 823 256 = 51858136550 :=
  block_append moment_2100_439_part3 moment_2100_439_part4 rfl rfl rfl
private theorem moment_2100_439_join2 :
    blockEstimate 2100 439 695 384 = 63699313670 :=
  block_append moment_2100_439_part2 moment_2100_439_join1 rfl rfl rfl
private theorem moment_2100_439_join3 :
    blockEstimate 2100 439 439 640 = 69099274310 :=
  block_append moment_2100_439_join0 moment_2100_439_join2 rfl rfl rfl
private theorem moment_2100_439_join4 :
    blockEstimate 2100 439 1079 256 = 81785792000 :=
  block_append moment_2100_439_part5 moment_2100_439_part6 rfl rfl rfl
private theorem moment_2100_439_join5 :
    blockEstimate 2100 439 1463 256 = 99065669120 :=
  block_append moment_2100_439_part8 moment_2100_439_part9 rfl rfl rfl
private theorem moment_2100_439_join6 :
    blockEstimate 2100 439 1335 384 = 146585401600 :=
  block_append moment_2100_439_part7 moment_2100_439_join5 rfl rfl rfl
private theorem moment_2100_439_join7 :
    blockEstimate 2100 439 1079 640 = 228371193600 :=
  block_append moment_2100_439_join4 moment_2100_439_join6 rfl rfl rfl
private theorem moment_2100_439_join8 :
    blockEstimate 2100 439 439 1280 = 297470467910 :=
  block_append moment_2100_439_join3 moment_2100_439_join7 rfl rfl rfl
private theorem moment_2100_439_join9 :
    blockEstimate 2100 439 1719 256 = 92130649600 :=
  block_append moment_2100_439_part10 moment_2100_439_part11 rfl rfl rfl
private theorem moment_2100_439_join10 :
    blockEstimate 2100 439 2103 256 = 56232848105 :=
  block_append moment_2100_439_part13 moment_2100_439_part14 rfl rfl rfl
private theorem moment_2100_439_join11 :
    blockEstimate 2100 439 1975 384 = 95083809860 :=
  block_append moment_2100_439_part12 moment_2100_439_join10 rfl rfl rfl
private theorem moment_2100_439_join12 :
    blockEstimate 2100 439 1719 640 = 187214459460 :=
  block_append moment_2100_439_join9 moment_2100_439_join11 rfl rfl rfl
private theorem moment_2100_439_join13 :
    blockEstimate 2100 439 2359 256 = 28048779709 :=
  block_append moment_2100_439_part15 moment_2100_439_part16 rfl rfl rfl
private theorem moment_2100_439_join14 :
    blockEstimate 2100 439 2743 235 = 2194136250 :=
  block_append moment_2100_439_part18 moment_2100_439_part19 rfl rfl rfl
private theorem moment_2100_439_join15 :
    blockEstimate 2100 439 2615 363 = 7790736954 :=
  block_append moment_2100_439_part17 moment_2100_439_join14 rfl rfl rfl
private theorem moment_2100_439_join16 :
    blockEstimate 2100 439 2359 619 = 35839516663 :=
  block_append moment_2100_439_join13 moment_2100_439_join15 rfl rfl rfl
private theorem moment_2100_439_join17 :
    blockEstimate 2100 439 1719 1259 = 223053976123 :=
  block_append moment_2100_439_join12 moment_2100_439_join16 rfl rfl rfl
private theorem moment_2100_439_join18 :
    blockEstimate 2100 439 439 2539 = 520524444033 :=
  block_append moment_2100_439_join8 moment_2100_439_join17 rfl rfl rfl

theorem moment_2100_439 : momentEstimate 2100 439 = 520524444033 := moment_2100_439_join18

private theorem moment_2678_563_part0 :
    blockEstimate 2678 563 563 128 = 924004640 := by decide +kernel
private theorem moment_2678_563_part1 :
    blockEstimate 2678 563 691 128 = 6111150368 := by decide +kernel
private theorem moment_2678_563_part2 :
    blockEstimate 2678 563 819 128 = 15703363872 := by decide +kernel
private theorem moment_2678_563_part3 :
    blockEstimate 2678 563 947 128 = 28895338784 := by decide +kernel
private theorem moment_2678_563_part4 :
    blockEstimate 2678 563 1075 128 = 44725223347 := by decide +kernel
private theorem moment_2678_563_part5 :
    blockEstimate 2678 563 1203 128 = 60197172864 := by decide +kernel
private theorem moment_2678_563_part6 :
    blockEstimate 2678 563 1331 128 = 73351132800 := by decide +kernel
private theorem moment_2678_563_part7 :
    blockEstimate 2678 563 1459 128 = 84139505280 := by decide +kernel
private theorem moment_2678_563_part8 :
    blockEstimate 2678 563 1587 128 = 92562290304 := by decide +kernel
private theorem moment_2678_563_part9 :
    blockEstimate 2678 563 1715 128 = 98619487872 := by decide +kernel
private theorem moment_2678_563_part10 :
    blockEstimate 2678 563 1843 128 = 102311097984 := by decide +kernel
private theorem moment_2678_563_part11 :
    blockEstimate 2678 563 1971 128 = 103637120640 := by decide +kernel
private theorem moment_2678_563_part12 :
    blockEstimate 2678 563 2099 128 = 102597555840 := by decide +kernel
private theorem moment_2678_563_part13 :
    blockEstimate 2678 563 2227 128 = 99192403584 := by decide +kernel
private theorem moment_2678_563_part14 :
    blockEstimate 2678 563 2355 128 = 93421663872 := by decide +kernel
private theorem moment_2678_563_part15 :
    blockEstimate 2678 563 2483 128 = 85285336704 := by decide +kernel
private theorem moment_2678_563_part16 :
    blockEstimate 2678 563 2611 128 = 74814810745 := by decide +kernel
private theorem moment_2678_563_part17 :
    blockEstimate 2678 563 2739 128 = 62882490764 := by decide +kernel
private theorem moment_2678_563_part18 :
    blockEstimate 2678 563 2867 128 = 50739802930 := by decide +kernel
private theorem moment_2678_563_part19 :
    blockEstimate 2678 563 2995 128 = 38959239188 := by decide +kernel
private theorem moment_2678_563_part20 :
    blockEstimate 2678 563 3123 128 = 28030913412 := by decide +kernel
private theorem moment_2678_563_part21 :
    blockEstimate 2678 563 3251 128 = 18344851056 := by decide +kernel
private theorem moment_2678_563_part22 :
    blockEstimate 2678 563 3379 128 = 10401395312 := by decide +kernel
private theorem moment_2678_563_part23 :
    blockEstimate 2678 563 3507 128 = 4554763888 := by decide +kernel
private theorem moment_2678_563_part24 :
    blockEstimate 2678 563 3635 128 = 1056615024 := by decide +kernel
private theorem moment_2678_563_part25 :
    blockEstimate 2678 563 3763 41 = 16996463 := by decide +kernel
private theorem moment_2678_563_join0 :
    blockEstimate 2678 563 691 256 = 21814514240 :=
  block_append moment_2678_563_part1 moment_2678_563_part2 rfl rfl rfl
private theorem moment_2678_563_join1 :
    blockEstimate 2678 563 563 384 = 22738518880 :=
  block_append moment_2678_563_part0 moment_2678_563_join0 rfl rfl rfl
private theorem moment_2678_563_join2 :
    blockEstimate 2678 563 1075 256 = 104922396211 :=
  block_append moment_2678_563_part4 moment_2678_563_part5 rfl rfl rfl
private theorem moment_2678_563_join3 :
    blockEstimate 2678 563 947 384 = 133817734995 :=
  block_append moment_2678_563_part3 moment_2678_563_join2 rfl rfl rfl
private theorem moment_2678_563_join4 :
    blockEstimate 2678 563 563 768 = 156556253875 :=
  block_append moment_2678_563_join1 moment_2678_563_join3 rfl rfl rfl
private theorem moment_2678_563_join5 :
    blockEstimate 2678 563 1459 256 = 176701795584 :=
  block_append moment_2678_563_part7 moment_2678_563_part8 rfl rfl rfl
private theorem moment_2678_563_join6 :
    blockEstimate 2678 563 1331 384 = 250052928384 :=
  block_append moment_2678_563_part6 moment_2678_563_join5 rfl rfl rfl
private theorem moment_2678_563_join7 :
    blockEstimate 2678 563 1715 256 = 200930585856 :=
  block_append moment_2678_563_part9 moment_2678_563_part10 rfl rfl rfl
private theorem moment_2678_563_join8 :
    blockEstimate 2678 563 1971 256 = 206234676480 :=
  block_append moment_2678_563_part11 moment_2678_563_part12 rfl rfl rfl
private theorem moment_2678_563_join9 :
    blockEstimate 2678 563 1715 512 = 407165262336 :=
  block_append moment_2678_563_join7 moment_2678_563_join8 rfl rfl rfl
private theorem moment_2678_563_join10 :
    blockEstimate 2678 563 1331 896 = 657218190720 :=
  block_append moment_2678_563_join6 moment_2678_563_join9 rfl rfl rfl
private theorem moment_2678_563_join11 :
    blockEstimate 2678 563 563 1664 = 813774444595 :=
  block_append moment_2678_563_join4 moment_2678_563_join10 rfl rfl rfl
private theorem moment_2678_563_join12 :
    blockEstimate 2678 563 2355 256 = 178707000576 :=
  block_append moment_2678_563_part14 moment_2678_563_part15 rfl rfl rfl
private theorem moment_2678_563_join13 :
    blockEstimate 2678 563 2227 384 = 277899404160 :=
  block_append moment_2678_563_part13 moment_2678_563_join12 rfl rfl rfl
private theorem moment_2678_563_join14 :
    blockEstimate 2678 563 2739 256 = 113622293694 :=
  block_append moment_2678_563_part17 moment_2678_563_part18 rfl rfl rfl
private theorem moment_2678_563_join15 :
    blockEstimate 2678 563 2611 384 = 188437104439 :=
  block_append moment_2678_563_part16 moment_2678_563_join14 rfl rfl rfl
private theorem moment_2678_563_join16 :
    blockEstimate 2678 563 2227 768 = 466336508599 :=
  block_append moment_2678_563_join13 moment_2678_563_join15 rfl rfl rfl
private theorem moment_2678_563_join17 :
    blockEstimate 2678 563 3123 256 = 46375764468 :=
  block_append moment_2678_563_part20 moment_2678_563_part21 rfl rfl rfl
private theorem moment_2678_563_join18 :
    blockEstimate 2678 563 2995 384 = 85335003656 :=
  block_append moment_2678_563_part19 moment_2678_563_join17 rfl rfl rfl
private theorem moment_2678_563_join19 :
    blockEstimate 2678 563 3379 256 = 14956159200 :=
  block_append moment_2678_563_part22 moment_2678_563_part23 rfl rfl rfl
private theorem moment_2678_563_join20 :
    blockEstimate 2678 563 3635 169 = 1073611487 :=
  block_append moment_2678_563_part24 moment_2678_563_part25 rfl rfl rfl
private theorem moment_2678_563_join21 :
    blockEstimate 2678 563 3379 425 = 16029770687 :=
  block_append moment_2678_563_join19 moment_2678_563_join20 rfl rfl rfl
private theorem moment_2678_563_join22 :
    blockEstimate 2678 563 2995 809 = 101364774343 :=
  block_append moment_2678_563_join18 moment_2678_563_join21 rfl rfl rfl
private theorem moment_2678_563_join23 :
    blockEstimate 2678 563 2227 1577 = 567701282942 :=
  block_append moment_2678_563_join16 moment_2678_563_join22 rfl rfl rfl
private theorem moment_2678_563_join24 :
    blockEstimate 2678 563 563 3241 = 1381475727537 :=
  block_append moment_2678_563_join11 moment_2678_563_join23 rfl rfl rfl

theorem moment_2678_563 : momentEstimate 2678 563 = 1381475727537 := moment_2678_563_join24

private theorem moment_2678_584_part0 :
    blockEstimate 2678 584 584 128 = 924004640 := by decide +kernel
private theorem moment_2678_584_part1 :
    blockEstimate 2678 584 712 128 = 6111150368 := by decide +kernel
private theorem moment_2678_584_part2 :
    blockEstimate 2678 584 840 128 = 15703363872 := by decide +kernel
private theorem moment_2678_584_part3 :
    blockEstimate 2678 584 968 128 = 28895338784 := by decide +kernel
private theorem moment_2678_584_part4 :
    blockEstimate 2678 584 1096 128 = 44821712586 := by decide +kernel
private theorem moment_2678_584_part5 :
    blockEstimate 2678 584 1224 128 = 60886126080 := by decide +kernel
private theorem moment_2678_584_part6 :
    blockEstimate 2678 584 1352 128 = 74630499840 := by decide +kernel
private theorem moment_2678_584_part7 :
    blockEstimate 2678 584 1480 128 = 85921205760 := by decide +kernel
private theorem moment_2678_584_part8 :
    blockEstimate 2678 584 1608 128 = 94758243840 := by decide +kernel
private theorem moment_2678_584_part9 :
    blockEstimate 2678 584 1736 128 = 101141614080 := by decide +kernel
private theorem moment_2678_584_part10 :
    blockEstimate 2678 584 1864 128 = 105071316480 := by decide +kernel
private theorem moment_2678_584_part11 :
    blockEstimate 2678 584 1992 128 = 106547351040 := by decide +kernel
private theorem moment_2678_584_part12 :
    blockEstimate 2678 584 2120 128 = 105569717760 := by decide +kernel
private theorem moment_2678_584_part13 :
    blockEstimate 2678 584 2248 128 = 102138416640 := by decide +kernel
private theorem moment_2678_584_part14 :
    blockEstimate 2678 584 2376 128 = 96253447680 := by decide +kernel
private theorem moment_2678_584_part15 :
    blockEstimate 2678 584 2504 128 = 87914810880 := by decide +kernel
private theorem moment_2678_584_part16 :
    blockEstimate 2678 584 2632 128 = 77197419775 := by decide +kernel
private theorem moment_2678_584_part17 :
    blockEstimate 2678 584 2760 128 = 65154508826 := by decide +kernel
private theorem moment_2678_584_part18 :
    blockEstimate 2678 584 2888 128 = 52886238116 := by decide +kernel
private theorem moment_2678_584_part19 :
    blockEstimate 2678 584 3016 128 = 40935577062 := by decide +kernel
private theorem moment_2678_584_part20 :
    blockEstimate 2678 584 3144 128 = 29789439866 := by decide +kernel
private theorem moment_2678_584_part21 :
    blockEstimate 2678 584 3272 128 = 19830964336 := by decide +kernel
private theorem moment_2678_584_part22 :
    blockEstimate 2678 584 3400 128 = 11567529072 := by decide +kernel
private theorem moment_2678_584_part23 :
    blockEstimate 2678 584 3528 128 = 5359630448 := by decide +kernel
private theorem moment_2678_584_part24 :
    blockEstimate 2678 584 3656 128 = 1458926704 := by decide +kernel
private theorem moment_2678_584_part25 :
    blockEstimate 2678 584 3784 62 = 56510648 := by decide +kernel
private theorem moment_2678_584_join0 :
    blockEstimate 2678 584 712 256 = 21814514240 :=
  block_append moment_2678_584_part1 moment_2678_584_part2 rfl rfl rfl
private theorem moment_2678_584_join1 :
    blockEstimate 2678 584 584 384 = 22738518880 :=
  block_append moment_2678_584_part0 moment_2678_584_join0 rfl rfl rfl
private theorem moment_2678_584_join2 :
    blockEstimate 2678 584 1096 256 = 105707838666 :=
  block_append moment_2678_584_part4 moment_2678_584_part5 rfl rfl rfl
private theorem moment_2678_584_join3 :
    blockEstimate 2678 584 968 384 = 134603177450 :=
  block_append moment_2678_584_part3 moment_2678_584_join2 rfl rfl rfl
private theorem moment_2678_584_join4 :
    blockEstimate 2678 584 584 768 = 157341696330 :=
  block_append moment_2678_584_join1 moment_2678_584_join3 rfl rfl rfl
private theorem moment_2678_584_join5 :
    blockEstimate 2678 584 1480 256 = 180679449600 :=
  block_append moment_2678_584_part7 moment_2678_584_part8 rfl rfl rfl
private theorem moment_2678_584_join6 :
    blockEstimate 2678 584 1352 384 = 255309949440 :=
  block_append moment_2678_584_part6 moment_2678_584_join5 rfl rfl rfl
private theorem moment_2678_584_join7 :
    blockEstimate 2678 584 1736 256 = 206212930560 :=
  block_append moment_2678_584_part9 moment_2678_584_part10 rfl rfl rfl
private theorem moment_2678_584_join8 :
    blockEstimate 2678 584 1992 256 = 212117068800 :=
  block_append moment_2678_584_part11 moment_2678_584_part12 rfl rfl rfl
private theorem moment_2678_584_join9 :
    blockEstimate 2678 584 1736 512 = 418329999360 :=
  block_append moment_2678_584_join7 moment_2678_584_join8 rfl rfl rfl
private theorem moment_2678_584_join10 :
    blockEstimate 2678 584 1352 896 = 673639948800 :=
  block_append moment_2678_584_join6 moment_2678_584_join9 rfl rfl rfl
private theorem moment_2678_584_join11 :
    blockEstimate 2678 584 584 1664 = 830981645130 :=
  block_append moment_2678_584_join4 moment_2678_584_join10 rfl rfl rfl
private theorem moment_2678_584_join12 :
    blockEstimate 2678 584 2376 256 = 184168258560 :=
  block_append moment_2678_584_part14 moment_2678_584_part15 rfl rfl rfl
private theorem moment_2678_584_join13 :
    blockEstimate 2678 584 2248 384 = 286306675200 :=
  block_append moment_2678_584_part13 moment_2678_584_join12 rfl rfl rfl
private theorem moment_2678_584_join14 :
    blockEstimate 2678 584 2760 256 = 118040746942 :=
  block_append moment_2678_584_part17 moment_2678_584_part18 rfl rfl rfl
private theorem moment_2678_584_join15 :
    blockEstimate 2678 584 2632 384 = 195238166717 :=
  block_append moment_2678_584_part16 moment_2678_584_join14 rfl rfl rfl
private theorem moment_2678_584_join16 :
    blockEstimate 2678 584 2248 768 = 481544841917 :=
  block_append moment_2678_584_join13 moment_2678_584_join15 rfl rfl rfl
private theorem moment_2678_584_join17 :
    blockEstimate 2678 584 3144 256 = 49620404202 :=
  block_append moment_2678_584_part20 moment_2678_584_part21 rfl rfl rfl
private theorem moment_2678_584_join18 :
    blockEstimate 2678 584 3016 384 = 90555981264 :=
  block_append moment_2678_584_part19 moment_2678_584_join17 rfl rfl rfl
private theorem moment_2678_584_join19 :
    blockEstimate 2678 584 3400 256 = 16927159520 :=
  block_append moment_2678_584_part22 moment_2678_584_part23 rfl rfl rfl
private theorem moment_2678_584_join20 :
    blockEstimate 2678 584 3656 190 = 1515437352 :=
  block_append moment_2678_584_part24 moment_2678_584_part25 rfl rfl rfl
private theorem moment_2678_584_join21 :
    blockEstimate 2678 584 3400 446 = 18442596872 :=
  block_append moment_2678_584_join19 moment_2678_584_join20 rfl rfl rfl
private theorem moment_2678_584_join22 :
    blockEstimate 2678 584 3016 830 = 108998578136 :=
  block_append moment_2678_584_join18 moment_2678_584_join21 rfl rfl rfl
private theorem moment_2678_584_join23 :
    blockEstimate 2678 584 2248 1598 = 590543420053 :=
  block_append moment_2678_584_join16 moment_2678_584_join22 rfl rfl rfl
private theorem moment_2678_584_join24 :
    blockEstimate 2678 584 584 3262 = 1421525065183 :=
  block_append moment_2678_584_join11 moment_2678_584_join23 rfl rfl rfl

theorem moment_2678_584 : momentEstimate 2678 584 = 1421525065183 := moment_2678_584_join24

private theorem moment_2726_570_part0 :
    blockEstimate 2726 570 570 128 = 941177120 := by decide +kernel
private theorem moment_2726_570_part1 :
    blockEstimate 2726 570 698 128 = 6229772576 := by decide +kernel
private theorem moment_2726_570_part2 :
    blockEstimate 2726 570 826 128 = 16024099104 := by decide +kernel
private theorem moment_2726_570_part3 :
    blockEstimate 2726 570 954 128 = 29518850336 := by decide +kernel
private theorem moment_2726_570_part4 :
    blockEstimate 2726 570 1082 128 = 45788465784 := by decide +kernel
private theorem moment_2726_570_part5 :
    blockEstimate 2726 570 1210 128 = 61910907968 := by decide +kernel
private theorem moment_2726_570_part6 :
    blockEstimate 2726 570 1338 128 = 75709922368 := by decide +kernel
private theorem moment_2726_570_part7 :
    blockEstimate 2726 570 1466 128 = 87113989184 := by decide +kernel
private theorem moment_2726_570_part8 :
    blockEstimate 2726 570 1594 128 = 96123108416 := by decide +kernel
private theorem moment_2726_570_part9 :
    blockEstimate 2726 570 1722 128 = 102737280064 := by decide +kernel
private theorem moment_2726_570_part10 :
    blockEstimate 2726 570 1850 128 = 106956504128 := by decide +kernel
private theorem moment_2726_570_part11 :
    blockEstimate 2726 570 1978 128 = 108780780608 := by decide +kernel
private theorem moment_2726_570_part12 :
    blockEstimate 2726 570 2106 128 = 108210109504 := by decide +kernel
private theorem moment_2726_570_part13 :
    blockEstimate 2726 570 2234 128 = 105244490816 := by decide +kernel
private theorem moment_2726_570_part14 :
    blockEstimate 2726 570 2362 128 = 99883924544 := by decide +kernel
private theorem moment_2726_570_part15 :
    blockEstimate 2726 570 2490 128 = 92128410688 := by decide +kernel
private theorem moment_2726_570_part16 :
    blockEstimate 2726 570 2618 128 = 81979099023 := by decide +kernel
private theorem moment_2726_570_part17 :
    blockEstimate 2726 570 2746 128 = 69908824467 := by decide +kernel
private theorem moment_2726_570_part18 :
    blockEstimate 2726 570 2874 128 = 57337933609 := by decide +kernel
private theorem moment_2726_570_part19 :
    blockEstimate 2726 570 3002 128 = 44969478669 := by decide +kernel
private theorem moment_2726_570_part20 :
    blockEstimate 2726 570 3130 128 = 33309949796 := by decide +kernel
private theorem moment_2726_570_part21 :
    blockEstimate 2726 570 3258 128 = 22790468361 := by decide +kernel
private theorem moment_2726_570_part22 :
    blockEstimate 2726 570 3386 128 = 13842204672 := by decide +kernel
private theorem moment_2726_570_part23 :
    blockEstimate 2726 570 3514 128 = 6924756992 := by decide +kernel
private theorem moment_2726_570_part24 :
    blockEstimate 2726 570 3642 128 = 2297989120 := by decide +kernel
private theorem moment_2726_570_part25 :
    blockEstimate 2726 570 3770 96 = 207088896 := by decide +kernel
private theorem moment_2726_570_join0 :
    blockEstimate 2726 570 698 256 = 22253871680 :=
  block_append moment_2726_570_part1 moment_2726_570_part2 rfl rfl rfl
private theorem moment_2726_570_join1 :
    blockEstimate 2726 570 570 384 = 23195048800 :=
  block_append moment_2726_570_part0 moment_2726_570_join0 rfl rfl rfl
private theorem moment_2726_570_join2 :
    blockEstimate 2726 570 1082 256 = 107699373752 :=
  block_append moment_2726_570_part4 moment_2726_570_part5 rfl rfl rfl
private theorem moment_2726_570_join3 :
    blockEstimate 2726 570 954 384 = 137218224088 :=
  block_append moment_2726_570_part3 moment_2726_570_join2 rfl rfl rfl
private theorem moment_2726_570_join4 :
    blockEstimate 2726 570 570 768 = 160413272888 :=
  block_append moment_2726_570_join1 moment_2726_570_join3 rfl rfl rfl
private theorem moment_2726_570_join5 :
    blockEstimate 2726 570 1466 256 = 183237097600 :=
  block_append moment_2726_570_part7 moment_2726_570_part8 rfl rfl rfl
private theorem moment_2726_570_join6 :
    blockEstimate 2726 570 1338 384 = 258947019968 :=
  block_append moment_2726_570_part6 moment_2726_570_join5 rfl rfl rfl
private theorem moment_2726_570_join7 :
    blockEstimate 2726 570 1722 256 = 209693784192 :=
  block_append moment_2726_570_part9 moment_2726_570_part10 rfl rfl rfl
private theorem moment_2726_570_join8 :
    blockEstimate 2726 570 1978 256 = 216990890112 :=
  block_append moment_2726_570_part11 moment_2726_570_part12 rfl rfl rfl
private theorem moment_2726_570_join9 :
    blockEstimate 2726 570 1722 512 = 426684674304 :=
  block_append moment_2726_570_join7 moment_2726_570_join8 rfl rfl rfl
private theorem moment_2726_570_join10 :
    blockEstimate 2726 570 1338 896 = 685631694272 :=
  block_append moment_2726_570_join6 moment_2726_570_join9 rfl rfl rfl
private theorem moment_2726_570_join11 :
    blockEstimate 2726 570 570 1664 = 846044967160 :=
  block_append moment_2726_570_join4 moment_2726_570_join10 rfl rfl rfl
private theorem moment_2726_570_join12 :
    blockEstimate 2726 570 2362 256 = 192012335232 :=
  block_append moment_2726_570_part14 moment_2726_570_part15 rfl rfl rfl
private theorem moment_2726_570_join13 :
    blockEstimate 2726 570 2234 384 = 297256826048 :=
  block_append moment_2726_570_part13 moment_2726_570_join12 rfl rfl rfl
private theorem moment_2726_570_join14 :
    blockEstimate 2726 570 2746 256 = 127246758076 :=
  block_append moment_2726_570_part17 moment_2726_570_part18 rfl rfl rfl
private theorem moment_2726_570_join15 :
    blockEstimate 2726 570 2618 384 = 209225857099 :=
  block_append moment_2726_570_part16 moment_2726_570_join14 rfl rfl rfl
private theorem moment_2726_570_join16 :
    blockEstimate 2726 570 2234 768 = 506482683147 :=
  block_append moment_2726_570_join13 moment_2726_570_join15 rfl rfl rfl
private theorem moment_2726_570_join17 :
    blockEstimate 2726 570 3130 256 = 56100418157 :=
  block_append moment_2726_570_part20 moment_2726_570_part21 rfl rfl rfl
private theorem moment_2726_570_join18 :
    blockEstimate 2726 570 3002 384 = 101069896826 :=
  block_append moment_2726_570_part19 moment_2726_570_join17 rfl rfl rfl
private theorem moment_2726_570_join19 :
    blockEstimate 2726 570 3386 256 = 20766961664 :=
  block_append moment_2726_570_part22 moment_2726_570_part23 rfl rfl rfl
private theorem moment_2726_570_join20 :
    blockEstimate 2726 570 3642 224 = 2505078016 :=
  block_append moment_2726_570_part24 moment_2726_570_part25 rfl rfl rfl
private theorem moment_2726_570_join21 :
    blockEstimate 2726 570 3386 480 = 23272039680 :=
  block_append moment_2726_570_join19 moment_2726_570_join20 rfl rfl rfl
private theorem moment_2726_570_join22 :
    blockEstimate 2726 570 3002 864 = 124341936506 :=
  block_append moment_2726_570_join18 moment_2726_570_join21 rfl rfl rfl
private theorem moment_2726_570_join23 :
    blockEstimate 2726 570 2234 1632 = 630824619653 :=
  block_append moment_2726_570_join16 moment_2726_570_join22 rfl rfl rfl
private theorem moment_2726_570_join24 :
    blockEstimate 2726 570 570 3296 = 1476869586813 :=
  block_append moment_2726_570_join11 moment_2726_570_join23 rfl rfl rfl

theorem moment_2726_570 : momentEstimate 2726 570 = 1476869586813 := moment_2726_570_join24

private theorem moment_3438_750_part0 :
    blockEstimate 3438 750 750 128 = 1195902240 := by decide +kernel
private theorem moment_3438_750_part1 :
    blockEstimate 3438 750 878 128 = 7989335328 := by decide +kernel
private theorem moment_3438_750_part2 :
    blockEstimate 3438 750 1006 128 = 20781671712 := by decide +kernel
private theorem moment_3438_750_part3 :
    blockEstimate 3438 750 1134 128 = 38767605024 := by decide +kernel
private theorem moment_3438_750_part4 :
    blockEstimate 3438 750 1262 128 = 61141828896 := by decide +kernel
private theorem moment_3438_750_part5 :
    blockEstimate 3438 750 1390 128 = 87096444885 := by decide +kernel
private theorem moment_3438_750_part6 :
    blockEstimate 3438 750 1518 128 = 114498877888 := by decide +kernel
private theorem moment_3438_750_part7 :
    blockEstimate 3438 750 1646 128 = 139366037952 := by decide +kernel
private theorem moment_3438_750_part8 :
    blockEstimate 3438 750 1774 128 = 161083275712 := by decide +kernel
private theorem moment_3438_750_part9 :
    blockEstimate 3438 750 1902 128 = 179650591168 := by decide +kernel
private theorem moment_3438_750_part10 :
    blockEstimate 3438 750 2030 128 = 195067984320 := by decide +kernel
private theorem moment_3438_750_part11 :
    blockEstimate 3438 750 2158 128 = 207335455168 := by decide +kernel
private theorem moment_3438_750_part12 :
    blockEstimate 3438 750 2286 128 = 216453003712 := by decide +kernel
private theorem moment_3438_750_part13 :
    blockEstimate 3438 750 2414 128 = 222420629952 := by decide +kernel
private theorem moment_3438_750_part14 :
    blockEstimate 3438 750 2542 128 = 225238333888 := by decide +kernel
private theorem moment_3438_750_part15 :
    blockEstimate 3438 750 2670 128 = 224906115520 := by decide +kernel
private theorem moment_3438_750_part16 :
    blockEstimate 3438 750 2798 128 = 221423974848 := by decide +kernel
private theorem moment_3438_750_part17 :
    blockEstimate 3438 750 2926 128 = 214791911872 := by decide +kernel
private theorem moment_3438_750_part18 :
    blockEstimate 3438 750 3054 128 = 205009926592 := by decide +kernel
private theorem moment_3438_750_part19 :
    blockEstimate 3438 750 3182 128 = 192078019008 := by decide +kernel
private theorem moment_3438_750_part20 :
    blockEstimate 3438 750 3310 128 = 175996189120 := by decide +kernel
private theorem moment_3438_750_part21 :
    blockEstimate 3438 750 3438 128 = 157132247091 := by decide +kernel
private theorem moment_3438_750_part22 :
    blockEstimate 3438 750 3566 128 = 137136148062 := by decide +kernel
private theorem moment_3438_750_part23 :
    blockEstimate 3438 750 3694 128 = 116886978890 := by decide +kernel
private theorem moment_3438_750_part24 :
    blockEstimate 3438 750 3822 128 = 96919956452 := by decide +kernel
private theorem moment_3438_750_part25 :
    blockEstimate 3438 750 3950 128 = 77735984777 := by decide +kernel
private theorem moment_3438_750_part26 :
    blockEstimate 3438 750 4078 128 = 59798769904 := by decide +kernel
private theorem moment_3438_750_part27 :
    blockEstimate 3438 750 4206 128 = 43425779232 := by decide +kernel
private theorem moment_3438_750_part28 :
    blockEstimate 3438 750 4334 128 = 29202290208 := by decide +kernel
private theorem moment_3438_750_part29 :
    blockEstimate 3438 750 4462 128 = 17520614944 := by decide +kernel
private theorem moment_3438_750_part30 :
    blockEstimate 3438 750 4590 128 = 8632411680 := by decide +kernel
private theorem moment_3438_750_part31 :
    blockEstimate 3438 750 4718 128 = 2789338656 := by decide +kernel
private theorem moment_3438_750_part32 :
    blockEstimate 3438 750 4846 92 = 231246439 := by decide +kernel
private theorem moment_3438_750_join0 :
    blockEstimate 3438 750 750 256 = 9185237568 :=
  block_append moment_3438_750_part0 moment_3438_750_part1 rfl rfl rfl
private theorem moment_3438_750_join1 :
    blockEstimate 3438 750 1006 256 = 59549276736 :=
  block_append moment_3438_750_part2 moment_3438_750_part3 rfl rfl rfl
private theorem moment_3438_750_join2 :
    blockEstimate 3438 750 750 512 = 68734514304 :=
  block_append moment_3438_750_join0 moment_3438_750_join1 rfl rfl rfl
private theorem moment_3438_750_join3 :
    blockEstimate 3438 750 1262 256 = 148238273781 :=
  block_append moment_3438_750_part4 moment_3438_750_part5 rfl rfl rfl
private theorem moment_3438_750_join4 :
    blockEstimate 3438 750 1518 256 = 253864915840 :=
  block_append moment_3438_750_part6 moment_3438_750_part7 rfl rfl rfl
private theorem moment_3438_750_join5 :
    blockEstimate 3438 750 1262 512 = 402103189621 :=
  block_append moment_3438_750_join3 moment_3438_750_join4 rfl rfl rfl
private theorem moment_3438_750_join6 :
    blockEstimate 3438 750 750 1024 = 470837703925 :=
  block_append moment_3438_750_join2 moment_3438_750_join5 rfl rfl rfl
private theorem moment_3438_750_join7 :
    blockEstimate 3438 750 1774 256 = 340733866880 :=
  block_append moment_3438_750_part8 moment_3438_750_part9 rfl rfl rfl
private theorem moment_3438_750_join8 :
    blockEstimate 3438 750 2030 256 = 402403439488 :=
  block_append moment_3438_750_part10 moment_3438_750_part11 rfl rfl rfl
private theorem moment_3438_750_join9 :
    blockEstimate 3438 750 1774 512 = 743137306368 :=
  block_append moment_3438_750_join7 moment_3438_750_join8 rfl rfl rfl
private theorem moment_3438_750_join10 :
    blockEstimate 3438 750 2286 256 = 438873633664 :=
  block_append moment_3438_750_part12 moment_3438_750_part13 rfl rfl rfl
private theorem moment_3438_750_join11 :
    blockEstimate 3438 750 2542 256 = 450144449408 :=
  block_append moment_3438_750_part14 moment_3438_750_part15 rfl rfl rfl
private theorem moment_3438_750_join12 :
    blockEstimate 3438 750 2286 512 = 889018083072 :=
  block_append moment_3438_750_join10 moment_3438_750_join11 rfl rfl rfl
private theorem moment_3438_750_join13 :
    blockEstimate 3438 750 1774 1024 = 1632155389440 :=
  block_append moment_3438_750_join9 moment_3438_750_join12 rfl rfl rfl
private theorem moment_3438_750_join14 :
    blockEstimate 3438 750 750 2048 = 2102993093365 :=
  block_append moment_3438_750_join6 moment_3438_750_join13 rfl rfl rfl
private theorem moment_3438_750_join15 :
    blockEstimate 3438 750 2798 256 = 436215886720 :=
  block_append moment_3438_750_part16 moment_3438_750_part17 rfl rfl rfl
private theorem moment_3438_750_join16 :
    blockEstimate 3438 750 3054 256 = 397087945600 :=
  block_append moment_3438_750_part18 moment_3438_750_part19 rfl rfl rfl
private theorem moment_3438_750_join17 :
    blockEstimate 3438 750 2798 512 = 833303832320 :=
  block_append moment_3438_750_join15 moment_3438_750_join16 rfl rfl rfl
private theorem moment_3438_750_join18 :
    blockEstimate 3438 750 3310 256 = 333128436211 :=
  block_append moment_3438_750_part20 moment_3438_750_part21 rfl rfl rfl
private theorem moment_3438_750_join19 :
    blockEstimate 3438 750 3566 256 = 254023126952 :=
  block_append moment_3438_750_part22 moment_3438_750_part23 rfl rfl rfl
private theorem moment_3438_750_join20 :
    blockEstimate 3438 750 3310 512 = 587151563163 :=
  block_append moment_3438_750_join18 moment_3438_750_join19 rfl rfl rfl
private theorem moment_3438_750_join21 :
    blockEstimate 3438 750 2798 1024 = 1420455395483 :=
  block_append moment_3438_750_join17 moment_3438_750_join20 rfl rfl rfl
private theorem moment_3438_750_join22 :
    blockEstimate 3438 750 3822 256 = 174655941229 :=
  block_append moment_3438_750_part24 moment_3438_750_part25 rfl rfl rfl
private theorem moment_3438_750_join23 :
    blockEstimate 3438 750 4078 256 = 103224549136 :=
  block_append moment_3438_750_part26 moment_3438_750_part27 rfl rfl rfl
private theorem moment_3438_750_join24 :
    blockEstimate 3438 750 3822 512 = 277880490365 :=
  block_append moment_3438_750_join22 moment_3438_750_join23 rfl rfl rfl
private theorem moment_3438_750_join25 :
    blockEstimate 3438 750 4334 256 = 46722905152 :=
  block_append moment_3438_750_part28 moment_3438_750_part29 rfl rfl rfl
private theorem moment_3438_750_join26 :
    blockEstimate 3438 750 4718 220 = 3020585095 :=
  block_append moment_3438_750_part31 moment_3438_750_part32 rfl rfl rfl
private theorem moment_3438_750_join27 :
    blockEstimate 3438 750 4590 348 = 11652996775 :=
  block_append moment_3438_750_part30 moment_3438_750_join26 rfl rfl rfl
private theorem moment_3438_750_join28 :
    blockEstimate 3438 750 4334 604 = 58375901927 :=
  block_append moment_3438_750_join25 moment_3438_750_join27 rfl rfl rfl
private theorem moment_3438_750_join29 :
    blockEstimate 3438 750 3822 1116 = 336256392292 :=
  block_append moment_3438_750_join24 moment_3438_750_join28 rfl rfl rfl
private theorem moment_3438_750_join30 :
    blockEstimate 3438 750 2798 2140 = 1756711787775 :=
  block_append moment_3438_750_join21 moment_3438_750_join29 rfl rfl rfl
private theorem moment_3438_750_join31 :
    blockEstimate 3438 750 750 4188 = 3859704881140 :=
  block_append moment_3438_750_join14 moment_3438_750_join30 rfl rfl rfl

theorem moment_3438_750 : momentEstimate 3438 750 = 3859704881140 := moment_3438_750_join31

private theorem receipt_0_8_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 0 128 = 540282902352303847317231168 := by decide +kernel
private theorem receipt_0_8_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 128 128 = 378339497741208581602022976 := by decide +kernel
private theorem receipt_0_8_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 256 128 = 233436195317189425752975912 := by decide +kernel
private theorem receipt_0_8_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 384 128 = 104629834890805578946081001 := by decide +kernel
private theorem receipt_0_8_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 512 52 = 9217610243435056499124541 := by decide +kernel
private theorem receipt_0_8_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 0 256 = 918622400093512428919254144 :=
  phaseBlock_append receipt_0_8_2402_0_part0 receipt_0_8_2402_0_part1 rfl rfl rfl
private theorem receipt_0_8_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 384 180 = 113847445134240635445205542 :=
  phaseBlock_append receipt_0_8_2402_0_part3 receipt_0_8_2402_0_part4 rfl rfl rfl
private theorem receipt_0_8_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 256 308 = 347283640451430061198181454 :=
  phaseBlock_append receipt_0_8_2402_0_part2 receipt_0_8_2402_0_join1 rfl rfl rfl
private theorem receipt_0_8_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 0) 0 564 = 1265906040544942490117435598 :=
  phaseBlock_append receipt_0_8_2402_0_join0 receipt_0_8_2402_0_join2 rfl rfl rfl

private theorem receipt_0_8_2402_0 : fastPhase (bank 0 8).shape 179798 2402 16 1 0 1 0 = 1265906040544942490117435598 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2402_0_join3

private theorem receipt_0_8_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 0 128 = 538966020362940435276440128 := by decide +kernel
private theorem receipt_0_8_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 128 128 = 377154759433511695319900736 := by decide +kernel
private theorem receipt_0_8_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 256 128 = 232376457196843044483937625 := by decide +kernel
private theorem receipt_0_8_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 384 128 = 103687984013442256532292843 := by decide +kernel
private theorem receipt_0_8_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 512 52 = 8867032652541039723427095 := by decide +kernel
private theorem receipt_0_8_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 0 256 = 916120779796452130596340864 :=
  phaseBlock_append receipt_0_8_2402_1_part0 receipt_0_8_2402_1_part1 rfl rfl rfl
private theorem receipt_0_8_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 384 180 = 112555016665983296255719938 :=
  phaseBlock_append receipt_0_8_2402_1_part3 receipt_0_8_2402_1_part4 rfl rfl rfl
private theorem receipt_0_8_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 256 308 = 344931473862826340739657563 :=
  phaseBlock_append receipt_0_8_2402_1_part2 receipt_0_8_2402_1_join1 rfl rfl rfl
private theorem receipt_0_8_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2402 16 1 0 1 1) 0 564 = 1261052253659278471335998427 :=
  phaseBlock_append receipt_0_8_2402_1_join0 receipt_0_8_2402_1_join2 rfl rfl rfl

private theorem receipt_0_8_2402_1 : fastPhase (bank 0 8).shape 179798 2402 16 1 0 1 1 = 1261052253659278471335998427 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2402_1_join3

private theorem receipt_0_8_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 0 128 = 540287584287735795098659968 := by decide +kernel
private theorem receipt_0_8_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 128 128 = 378342326482970719266434176 := by decide +kernel
private theorem receipt_0_8_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 256 128 = 233437645023006707584784638 := by decide +kernel
private theorem receipt_0_8_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 384 128 = 104630345715512939841834021 := by decide +kernel
private theorem receipt_0_8_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 512 52 = 9217645200077520019734486 := by decide +kernel
private theorem receipt_0_8_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 0 256 = 918629910770706514365094144 :=
  phaseBlock_append receipt_0_8_2403_0_part0 receipt_0_8_2403_0_part1 rfl rfl rfl
private theorem receipt_0_8_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 384 180 = 113847990915590459861568507 :=
  phaseBlock_append receipt_0_8_2403_0_part3 receipt_0_8_2403_0_part4 rfl rfl rfl
private theorem receipt_0_8_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 256 308 = 347285635938597167446353145 :=
  phaseBlock_append receipt_0_8_2403_0_part2 receipt_0_8_2403_0_join1 rfl rfl rfl
private theorem receipt_0_8_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 0) 0 564 = 1265915546709303681811447289 :=
  phaseBlock_append receipt_0_8_2403_0_join0 receipt_0_8_2403_0_join2 rfl rfl rfl

private theorem receipt_0_8_2403_0 : fastPhase (bank 0 8).shape 179798 2403 16 1 0 1 0 = 1265915546709303681811447289 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2403_0_join3

private theorem receipt_0_8_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 0 128 = 538970692884168337779118720 := by decide +kernel
private theorem receipt_0_8_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 128 128 = 377157580656694160536015488 := by decide +kernel
private theorem receipt_0_8_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 256 128 = 232377901126183393660783561 := by decide +kernel
private theorem receipt_0_8_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 384 128 = 103688490665870827432224742 := by decide +kernel
private theorem receipt_0_8_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 512 52 = 8867066338981150969290272 := by decide +kernel
private theorem receipt_0_8_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 0 256 = 916128273540862498315134208 :=
  phaseBlock_append receipt_0_8_2403_1_part0 receipt_0_8_2403_1_part1 rfl rfl rfl
private theorem receipt_0_8_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 384 180 = 112555557004851978401515014 :=
  phaseBlock_append receipt_0_8_2403_1_part3 receipt_0_8_2403_1_part4 rfl rfl rfl
private theorem receipt_0_8_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 256 308 = 344933458131035372062298575 :=
  phaseBlock_append receipt_0_8_2403_1_part2 receipt_0_8_2403_1_join1 rfl rfl rfl
private theorem receipt_0_8_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179798 2403 16 1 0 1 1) 0 564 = 1261061731671897870377432783 :=
  phaseBlock_append receipt_0_8_2403_1_join0 receipt_0_8_2403_1_join2 rfl rfl rfl

private theorem receipt_0_8_2403_1 : fastPhase (bank 0 8).shape 179798 2403 16 1 0 1 1 = 1261061731671897870377432783 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2403_1_join3

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2402_0 receipt_0_8_2402_1 receipt_0_8_2403_0 receipt_0_8_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 0 128 = 486050705569496476638590304 := by decide +kernel
private theorem receipt_1_8_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 128 128 = 339916410858005436275484000 := by decide +kernel
private theorem receipt_1_8_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 256 128 = 209455650166565859751950426 := by decide +kernel
private theorem receipt_1_8_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 384 128 = 93762810148700821847526414 := by decide +kernel
private theorem receipt_1_8_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 512 52 = 8252217266308862093197347 := by decide +kernel
private theorem receipt_1_8_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 0 256 = 825967116427501912914074304 :=
  phaseBlock_append receipt_1_8_2402_0_part0 receipt_1_8_2402_0_part1 rfl rfl rfl
private theorem receipt_1_8_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 384 180 = 102015027415009683940723761 :=
  phaseBlock_append receipt_1_8_2402_0_part3 receipt_1_8_2402_0_part4 rfl rfl rfl
private theorem receipt_1_8_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 256 308 = 311470677581575543692674187 :=
  phaseBlock_append receipt_1_8_2402_0_part2 receipt_1_8_2402_0_join1 rfl rfl rfl
private theorem receipt_1_8_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 0) 0 564 = 1137437794009077456606748491 :=
  phaseBlock_append receipt_1_8_2402_0_join0 receipt_1_8_2402_0_join2 rfl rfl rfl

private theorem receipt_1_8_2402_0 : fastPhase (bank 1 8).shape 179798 2402 16 1 0 2 0 = 1137437794009077456606748491 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2402_0_join3

private theorem receipt_1_8_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 0 128 = 484861033170848284493779680 := by decide +kernel
private theorem receipt_1_8_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 128 128 = 338848522934960480968049376 := by decide +kernel
private theorem receipt_1_8_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 256 128 = 208502667314971962555913251 := by decide +kernel
private theorem receipt_1_8_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 384 128 = 92917914104019820472879064 := by decide +kernel
private theorem receipt_1_8_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 512 52 = 7938301681295581658975940 := by decide +kernel
private theorem receipt_1_8_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 0 256 = 823709556105808765461829056 :=
  phaseBlock_append receipt_1_8_2402_1_part0 receipt_1_8_2402_1_part1 rfl rfl rfl
private theorem receipt_1_8_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 384 180 = 100856215785315402131855004 :=
  phaseBlock_append receipt_1_8_2402_1_part3 receipt_1_8_2402_1_part4 rfl rfl rfl
private theorem receipt_1_8_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 256 308 = 309358883100287364687768255 :=
  phaseBlock_append receipt_1_8_2402_1_part2 receipt_1_8_2402_1_join1 rfl rfl rfl
private theorem receipt_1_8_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2402 16 1 0 2 1) 0 564 = 1133068439206096130149597311 :=
  phaseBlock_append receipt_1_8_2402_1_join0 receipt_1_8_2402_1_join2 rfl rfl rfl

private theorem receipt_1_8_2402_1 : fastPhase (bank 1 8).shape 179798 2402 16 1 0 2 1 = 1133068439206096130149597311 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2402_1_join3

private theorem receipt_1_8_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 0 128 = 486054917605864565859691264 := by decide +kernel
private theorem receipt_1_8_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 128 128 = 339918952366771122474003200 := by decide +kernel
private theorem receipt_1_8_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 256 128 = 209456950976404813532290320 := by decide +kernel
private theorem receipt_1_8_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 384 128 = 93763267931850448527968175 := by decide +kernel
private theorem receipt_1_8_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 512 52 = 8252248561974358513206552 := by decide +kernel
private theorem receipt_1_8_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 0 256 = 825973869972635688333694464 :=
  phaseBlock_append receipt_1_8_2403_0_part0 receipt_1_8_2403_0_part1 rfl rfl rfl
private theorem receipt_1_8_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 384 180 = 102015516493824807041174727 :=
  phaseBlock_append receipt_1_8_2403_0_part3 receipt_1_8_2403_0_part4 rfl rfl rfl
private theorem receipt_1_8_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 256 308 = 311472467470229620573465047 :=
  phaseBlock_append receipt_1_8_2403_0_part2 receipt_1_8_2403_0_join1 rfl rfl rfl
private theorem receipt_1_8_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 0) 0 564 = 1137446337442865308907159511 :=
  phaseBlock_append receipt_1_8_2403_0_join0 receipt_1_8_2403_0_join2 rfl rfl rfl

private theorem receipt_1_8_2403_0 : fastPhase (bank 1 8).shape 179798 2403 16 1 0 2 0 = 1137446337442865308907159511 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2403_0_join3

private theorem receipt_1_8_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 0 128 = 484865236694708854478292288 := by decide +kernel
private theorem receipt_1_8_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 128 128 = 338851057662629812598596928 := by decide +kernel
private theorem receipt_1_8_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 256 128 = 208503962928494366033262171 := by decide +kernel
private theorem receipt_1_8_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 384 128 = 92918368143846206134037766 := by decide +kernel
private theorem receipt_1_8_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 512 52 = 7938331839570111227297070 := by decide +kernel
private theorem receipt_1_8_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 0 256 = 823716294357338667076889216 :=
  phaseBlock_append receipt_1_8_2403_1_part0 receipt_1_8_2403_1_part1 rfl rfl rfl
private theorem receipt_1_8_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 384 180 = 100856699983416317361334836 :=
  phaseBlock_append receipt_1_8_2403_1_part3 receipt_1_8_2403_1_part4 rfl rfl rfl
private theorem receipt_1_8_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 256 308 = 309360662911910683394597007 :=
  phaseBlock_append receipt_1_8_2403_1_part2 receipt_1_8_2403_1_join1 rfl rfl rfl
private theorem receipt_1_8_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179798 2403 16 1 0 2 1) 0 564 = 1133076957269249350471486223 :=
  phaseBlock_append receipt_1_8_2403_1_join0 receipt_1_8_2403_1_join2 rfl rfl rfl

private theorem receipt_1_8_2403_1 : fastPhase (bank 1 8).shape 179798 2403 16 1 0 2 1 = 1133076957269249350471486223 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2403_1_join3

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2402_0 receipt_1_8_2402_1 receipt_1_8_2403_0 receipt_1_8_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 0 128 = 259154203550808527594691456 := by decide +kernel
private theorem receipt_2_8_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 128 128 = 179525416080948722619382656 := by decide +kernel
private theorem receipt_2_8_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 256 128 = 109578404418483267833412994 := by decide +kernel
private theorem receipt_2_8_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 384 128 = 48601577656252661227599719 := by decide +kernel
private theorem receipt_2_8_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 512 52 = 4247015407293303846969355 := by decide +kernel
private theorem receipt_2_8_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 0 256 = 438679619631757250214074112 :=
  phaseBlock_append receipt_2_8_2402_0_part0 receipt_2_8_2402_0_part1 rfl rfl rfl
private theorem receipt_2_8_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 384 180 = 52848593063545965074569074 :=
  phaseBlock_append receipt_2_8_2402_0_part3 receipt_2_8_2402_0_part4 rfl rfl rfl
private theorem receipt_2_8_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 256 308 = 162426997482029232907982068 :=
  phaseBlock_append receipt_2_8_2402_0_part2 receipt_2_8_2402_0_join1 rfl rfl rfl
private theorem receipt_2_8_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 0) 0 564 = 601106617113786483122056180 :=
  phaseBlock_append receipt_2_8_2402_0_join0 receipt_2_8_2402_0_join2 rfl rfl rfl

private theorem receipt_2_8_2402_0 : fastPhase (bank 2 8).shape 179798 2402 16 1 0 7 0 = 601106617113786483122056180 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2402_0_join3

private theorem receipt_2_8_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 0 128 = 258500750038047159440347008 := by decide +kernel
private theorem receipt_2_8_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 128 128 = 178948128482799834030288768 := by decide +kernel
private theorem receipt_2_8_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 256 128 = 109071793219604235926024637 := by decide +kernel
private theorem receipt_2_8_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 384 128 = 48160332944766061908638781 := by decide +kernel
private theorem receipt_2_8_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 512 52 = 4085249035206657175307595 := by decide +kernel
private theorem receipt_2_8_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 0 256 = 437448878520846993470635776 :=
  phaseBlock_append receipt_2_8_2402_1_part0 receipt_2_8_2402_1_part1 rfl rfl rfl
private theorem receipt_2_8_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 384 180 = 52245581979972719083946376 :=
  phaseBlock_append receipt_2_8_2402_1_part3 receipt_2_8_2402_1_part4 rfl rfl rfl
private theorem receipt_2_8_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 256 308 = 161317375199576955009971013 :=
  phaseBlock_append receipt_2_8_2402_1_part2 receipt_2_8_2402_1_join1 rfl rfl rfl
private theorem receipt_2_8_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2402 16 1 0 7 1) 0 564 = 598766253720423948480606789 :=
  phaseBlock_append receipt_2_8_2402_1_join0 receipt_2_8_2402_1_join2 rfl rfl rfl

private theorem receipt_2_8_2402_1 : fastPhase (bank 2 8).shape 179798 2402 16 1 0 7 1 = 598766253720423948480606789 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2402_1_join3

private theorem receipt_2_8_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 0 128 = 259156449575449706242082176 := by decide +kernel
private theorem receipt_2_8_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 128 128 = 179526758544267413739881856 := by decide +kernel
private theorem receipt_2_8_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 256 128 = 109579085062395685707338948 := by decide +kernel
private theorem receipt_2_8_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 384 128 = 48601814997707490707467791 := by decide +kernel
private theorem receipt_2_8_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 512 52 = 4247031514243355639441610 := by decide +kernel
private theorem receipt_2_8_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 0 256 = 438683208119717119981964032 :=
  phaseBlock_append receipt_2_8_2403_0_part0 receipt_2_8_2403_0_part1 rfl rfl rfl
private theorem receipt_2_8_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 384 180 = 52848846511950846346909401 :=
  phaseBlock_append receipt_2_8_2403_0_part3 receipt_2_8_2403_0_part4 rfl rfl rfl
private theorem receipt_2_8_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 256 308 = 162427931574346532054248349 :=
  phaseBlock_append receipt_2_8_2403_0_part2 receipt_2_8_2403_0_join1 rfl rfl rfl
private theorem receipt_2_8_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 0) 0 564 = 601111139694063652036212381 :=
  phaseBlock_append receipt_2_8_2403_0_join0 receipt_2_8_2403_0_join2 rfl rfl rfl

private theorem receipt_2_8_2403_0 : fastPhase (bank 2 8).shape 179798 2403 16 1 0 7 0 = 601111139694063652036212381 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2403_0_join3

private theorem receipt_2_8_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 0 128 = 258502991357475415815872896 := by decide +kernel
private theorem receipt_2_8_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 128 128 = 178949467264781411986841984 := by decide +kernel
private theorem receipt_2_8_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 256 128 = 109072471094469479286711873 := by decide +kernel
private theorem receipt_2_8_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 384 128 = 48160568329220891257379324 := by decide +kernel
private theorem receipt_2_8_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 512 52 = 4085264555957864708724312 := by decide +kernel
private theorem receipt_2_8_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 0 256 = 437452458622256827802714880 :=
  phaseBlock_append receipt_2_8_2403_1_part0 receipt_2_8_2403_1_part1 rfl rfl rfl
private theorem receipt_2_8_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 384 180 = 52245832885178755966103636 :=
  phaseBlock_append receipt_2_8_2403_1_part3 receipt_2_8_2403_1_part4 rfl rfl rfl
private theorem receipt_2_8_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 256 308 = 161318303979648235252815509 :=
  phaseBlock_append receipt_2_8_2403_1_part2 receipt_2_8_2403_1_join1 rfl rfl rfl
private theorem receipt_2_8_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179798 2403 16 1 0 7 1) 0 564 = 598770762601905063055530389 :=
  phaseBlock_append receipt_2_8_2403_1_join0 receipt_2_8_2403_1_join2 rfl rfl rfl

private theorem receipt_2_8_2403_1 : fastPhase (bank 2 8).shape 179798 2403 16 1 0 7 1 = 598770762601905063055530389 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2403_1_join3

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2402_0 receipt_2_8_2402_1 receipt_2_8_2403_0 receipt_2_8_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 0 128 = 46532711522471885172125120 := by decide +kernel
private theorem receipt_3_8_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 128 128 = 32721330631875882172329408 := by decide +kernel
private theorem receipt_3_8_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 256 128 = 20413630009235046197964224 := by decide +kernel
private theorem receipt_3_8_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 384 128 = 9701354699076173660794304 := by decide +kernel
private theorem receipt_3_8_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 512 73 = 1378967989982462446128420 := by decide +kernel
private theorem receipt_3_8_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 0 256 = 79254042154347767344454528 :=
  phaseBlock_append receipt_3_8_2402_0_part0 receipt_3_8_2402_0_part1 rfl rfl rfl
private theorem receipt_3_8_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 384 201 = 11080322689058636106922724 :=
  phaseBlock_append receipt_3_8_2402_0_part3 receipt_3_8_2402_0_part4 rfl rfl rfl
private theorem receipt_3_8_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 256 329 = 31493952698293682304886948 :=
  phaseBlock_append receipt_3_8_2402_0_part2 receipt_3_8_2402_0_join1 rfl rfl rfl
private theorem receipt_3_8_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 0) 0 585 = 110747994852641449649341476 :=
  phaseBlock_append receipt_3_8_2402_0_join0 receipt_3_8_2402_0_join2 rfl rfl rfl

private theorem receipt_3_8_2402_0 : fastPhase (bank 3 8).shape 179798 2402 16 1 1 1 0 = 110747994852641449649341476 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2402_0_join3

private theorem receipt_3_8_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 0 128 = 46420636423620108274428672 := by decide +kernel
private theorem receipt_3_8_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 128 128 = 32620202376932244859669248 := by decide +kernel
private theorem receipt_3_8_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 256 128 = 20324233477862954091129600 := by decide +kernel
private theorem receipt_3_8_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 384 128 = 9624460398610527376313088 := by decide +kernel
private theorem receipt_3_8_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 512 73 = 1341003219946474749825312 := by decide +kernel
private theorem receipt_3_8_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 0 256 = 79040838800552353134097920 :=
  phaseBlock_append receipt_3_8_2402_1_part0 receipt_3_8_2402_1_part1 rfl rfl rfl
private theorem receipt_3_8_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 384 201 = 10965463618557002126138400 :=
  phaseBlock_append receipt_3_8_2402_1_part3 receipt_3_8_2402_1_part4 rfl rfl rfl
private theorem receipt_3_8_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 256 329 = 31289697096419956217268000 :=
  phaseBlock_append receipt_3_8_2402_1_part2 receipt_3_8_2402_1_join1 rfl rfl rfl
private theorem receipt_3_8_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2402 16 1 1 1 1) 0 585 = 110330535896972309351365920 :=
  phaseBlock_append receipt_3_8_2402_1_join0 receipt_3_8_2402_1_join2 rfl rfl rfl

private theorem receipt_3_8_2402_1 : fastPhase (bank 3 8).shape 179798 2402 16 1 1 1 1 = 110330535896972309351365920 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2402_1_join3

private theorem receipt_3_8_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 0 128 = 46533099211363461704149056 := by decide +kernel
private theorem receipt_3_8_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 128 128 = 32721539978349573023000640 := by decide +kernel
private theorem receipt_3_8_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 256 128 = 20413722874498078562740288 := by decide +kernel
private theorem receipt_3_8_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 384 128 = 9701381975145211285203008 := by decide +kernel
private theorem receipt_3_8_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 512 73 = 1378969998461998901237940 := by decide +kernel
private theorem receipt_3_8_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 0 256 = 79254639189713034727149696 :=
  phaseBlock_append receipt_3_8_2403_0_part0 receipt_3_8_2403_0_part1 rfl rfl rfl
private theorem receipt_3_8_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 384 201 = 11080351973607210186440948 :=
  phaseBlock_append receipt_3_8_2403_0_part3 receipt_3_8_2403_0_part4 rfl rfl rfl
private theorem receipt_3_8_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 256 329 = 31494074848105288749181236 :=
  phaseBlock_append receipt_3_8_2403_0_part2 receipt_3_8_2403_0_join1 rfl rfl rfl
private theorem receipt_3_8_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 0) 0 585 = 110748714037818323476330932 :=
  phaseBlock_append receipt_3_8_2403_0_join0 receipt_3_8_2403_0_join2 rfl rfl rfl

private theorem receipt_3_8_2403_0 : fastPhase (bank 3 8).shape 179798 2403 16 1 1 1 0 = 110748714037818323476330932 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2403_0_join3

private theorem receipt_3_8_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 0 128 = 46421023039848883229565120 := by decide +kernel
private theorem receipt_3_8_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 128 128 = 32620410993571876334313664 := by decide +kernel
private theorem receipt_3_8_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 256 128 = 20324325895292772463091904 := by decide +kernel
private theorem receipt_3_8_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 384 128 = 9624487449067342997528768 := by decide +kernel
private theorem receipt_3_8_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 512 73 = 1341005176686305005632492 := by decide +kernel
private theorem receipt_3_8_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 0 256 = 79041434033420759563878784 :=
  phaseBlock_append receipt_3_8_2403_1_part0 receipt_3_8_2403_1_part1 rfl rfl rfl
private theorem receipt_3_8_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 384 201 = 10965492625753648003161260 :=
  phaseBlock_append receipt_3_8_2403_1_part3 receipt_3_8_2403_1_part4 rfl rfl rfl
private theorem receipt_3_8_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 256 329 = 31289818521046420466253164 :=
  phaseBlock_append receipt_3_8_2403_1_part2 receipt_3_8_2403_1_join1 rfl rfl rfl
private theorem receipt_3_8_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179798 2403 16 1 1 1 1) 0 585 = 110331252554467180030131948 :=
  phaseBlock_append receipt_3_8_2403_1_join0 receipt_3_8_2403_1_join2 rfl rfl rfl

private theorem receipt_3_8_2403_1 : fastPhase (bank 3 8).shape 179798 2403 16 1 1 1 1 = 110331252554467180030131948 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2403_1_join3

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2402_0 receipt_3_8_2402_1 receipt_3_8_2403_0 receipt_3_8_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 0 128 = 137179994605235101891389879 := by decide +kernel
private theorem receipt_0_9_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 128 128 = 83751361373495524470253146 := by decide +kernel
private theorem receipt_0_9_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 256 128 = 37575239638187877033654732 := by decide +kernel
private theorem receipt_0_9_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 384 56 = 3656008605832690625410270 := by decide +kernel
private theorem receipt_0_9_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 0 256 = 220931355978730626361643025 :=
  phaseBlock_append receipt_0_9_2402_0_part0 receipt_0_9_2402_0_part1 rfl rfl rfl
private theorem receipt_0_9_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 256 184 = 41231248244020567659065002 :=
  phaseBlock_append receipt_0_9_2402_0_part2 receipt_0_9_2402_0_part3 rfl rfl rfl
private theorem receipt_0_9_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 0) 0 440 = 262162604222751194020708027 :=
  phaseBlock_append receipt_0_9_2402_0_join0 receipt_0_9_2402_0_join1 rfl rfl rfl

private theorem receipt_0_9_2402_0 : fastPhase (bank 0 9).shape 179798 2402 10 1 0 1 0 = 262162604222751194020708027 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2402_0_join2

private theorem receipt_0_9_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 0 128 = 136738606525828890983502369 := by decide +kernel
private theorem receipt_0_9_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 128 128 = 83366674954187588222296879 := by decide +kernel
private theorem receipt_0_9_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 256 128 = 37243266277146009989667590 := by decide +kernel
private theorem receipt_0_9_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 384 56 = 3526332333000128159034464 := by decide +kernel
private theorem receipt_0_9_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 0 256 = 220105281480016479205799248 :=
  phaseBlock_append receipt_0_9_2402_1_part0 receipt_0_9_2402_1_part1 rfl rfl rfl
private theorem receipt_0_9_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 256 184 = 40769598610146138148702054 :=
  phaseBlock_append receipt_0_9_2402_1_part2 receipt_0_9_2402_1_part3 rfl rfl rfl
private theorem receipt_0_9_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2402 10 1 0 1 1) 0 440 = 260874880090162617354501302 :=
  phaseBlock_append receipt_0_9_2402_1_join0 receipt_0_9_2402_1_join1 rfl rfl rfl

private theorem receipt_0_9_2402_1 : fastPhase (bank 0 9).shape 179798 2402 10 1 0 1 1 = 260874880090162617354501302 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2402_1_join2

private theorem receipt_0_9_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 0 128 = 137181178529153957310067459 := by decide +kernel
private theorem receipt_0_9_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 128 128 = 83751952207192291762155961 := by decide +kernel
private theorem receipt_0_9_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 256 128 = 37575442130056688780690746 := by decide +kernel
private theorem receipt_0_9_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 384 56 = 3656023236557232259208455 := by decide +kernel
private theorem receipt_0_9_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 0 256 = 220933130736346249072223420 :=
  phaseBlock_append receipt_0_9_2403_0_part0 receipt_0_9_2403_0_part1 rfl rfl rfl
private theorem receipt_0_9_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 256 184 = 41231465366613921039899201 :=
  phaseBlock_append receipt_0_9_2403_0_part2 receipt_0_9_2403_0_part3 rfl rfl rfl
private theorem receipt_0_9_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 0) 0 440 = 262164596102960170112122621 :=
  phaseBlock_append receipt_0_9_2403_0_join0 receipt_0_9_2403_0_join1 rfl rfl rfl

private theorem receipt_0_9_2403_0 : fastPhase (bank 0 9).shape 179798 2403 10 1 0 1 0 = 262164596102960170112122621 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2403_0_join2

private theorem receipt_0_9_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 0 128 = 136739787298762754059354930 := by decide +kernel
private theorem receipt_0_9_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 128 128 = 83367263460034145922345460 := by decide +kernel
private theorem receipt_0_9_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 256 128 = 37243467176077940097370960 := by decide +kernel
private theorem receipt_0_9_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 384 56 = 3526346475079386509248311 := by decide +kernel
private theorem receipt_0_9_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 0 256 = 220107050758796899981700390 :=
  phaseBlock_append receipt_0_9_2403_1_part0 receipt_0_9_2403_1_part1 rfl rfl rfl
private theorem receipt_0_9_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 256 184 = 40769813651157326606619271 :=
  phaseBlock_append receipt_0_9_2403_1_part2 receipt_0_9_2403_1_part3 rfl rfl rfl
private theorem receipt_0_9_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179798 2403 10 1 0 1 1) 0 440 = 260876864409954226588319661 :=
  phaseBlock_append receipt_0_9_2403_1_join0 receipt_0_9_2403_1_join1 rfl rfl rfl

private theorem receipt_0_9_2403_1 : fastPhase (bank 0 9).shape 179798 2403 10 1 0 1 1 = 260876864409954226588319661 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2403_1_join2

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2402_0 receipt_0_9_2402_1 receipt_0_9_2403_0 receipt_0_9_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 0 128 = 123580228274310584207704086 := by decide +kernel
private theorem receipt_1_9_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 128 128 = 75316979119200442730182036 := by decide +kernel
private theorem receipt_1_9_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 256 128 = 33733959242429443615066325 := by decide +kernel
private theorem receipt_1_9_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 384 56 = 3277938422925255249877749 := by decide +kernel
private theorem receipt_1_9_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 0 256 = 198897207393511026937886122 :=
  phaseBlock_append receipt_1_9_2402_0_part0 receipt_1_9_2402_0_part1 rfl rfl rfl
private theorem receipt_1_9_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 256 184 = 37011897665354698864944074 :=
  phaseBlock_append receipt_1_9_2402_0_part2 receipt_1_9_2402_0_part3 rfl rfl rfl
private theorem receipt_1_9_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 0) 0 440 = 235909105058865725802830196 :=
  phaseBlock_append receipt_1_9_2402_0_join0 receipt_1_9_2402_0_join1 rfl rfl rfl

private theorem receipt_1_9_2402_0 : fastPhase (bank 1 9).shape 179798 2402 10 1 0 2 0 = 235909105058865725802830196 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2402_0_join2

private theorem receipt_1_9_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 0 128 = 123180914382084274879013280 := by decide +kernel
private theorem receipt_1_9_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 128 128 = 74970018828379045566353017 := by decide +kernel
private theorem receipt_1_9_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 256 128 = 33435502706191217068980496 := by decide +kernel
private theorem receipt_1_9_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 384 56 = 3161642580275562361456683 := by decide +kernel
private theorem receipt_1_9_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 0 256 = 198150933210463320445366297 :=
  phaseBlock_append receipt_1_9_2402_1_part0 receipt_1_9_2402_1_part1 rfl rfl rfl
private theorem receipt_1_9_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 256 184 = 36597145286466779430437179 :=
  phaseBlock_append receipt_1_9_2402_1_part2 receipt_1_9_2402_1_part3 rfl rfl rfl
private theorem receipt_1_9_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2402 10 1 0 2 1) 0 440 = 234748078496930099875803476 :=
  phaseBlock_append receipt_1_9_2402_1_join0 receipt_1_9_2402_1_join1 rfl rfl rfl

private theorem receipt_1_9_2402_1 : fastPhase (bank 1 9).shape 179798 2402 10 1 0 2 1 = 234748078496930099875803476 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2402_1_join2

private theorem receipt_1_9_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 0 128 = 123581294853549537481771931 := by decide +kernel
private theorem receipt_1_9_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 128 128 = 75317510469719268200001009 := by decide +kernel
private theorem receipt_1_9_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 256 128 = 33734141041944765917964690 := by decide +kernel
private theorem receipt_1_9_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 384 56 = 3277951540799752156233209 := by decide +kernel
private theorem receipt_1_9_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 0 256 = 198898805323268805681772940 :=
  phaseBlock_append receipt_1_9_2403_0_part0 receipt_1_9_2403_0_part1 rfl rfl rfl
private theorem receipt_1_9_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 256 184 = 37012092582744518074197899 :=
  phaseBlock_append receipt_1_9_2403_0_part2 receipt_1_9_2403_0_part3 rfl rfl rfl
private theorem receipt_1_9_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 0) 0 440 = 235910897906013323755970839 :=
  phaseBlock_append receipt_1_9_2403_0_join0 receipt_1_9_2403_0_join1 rfl rfl rfl

private theorem receipt_1_9_2403_0 : fastPhase (bank 1 9).shape 179798 2403 10 1 0 2 0 = 235910897906013323755970839 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2403_0_join2

private theorem receipt_1_9_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 0 128 = 123181978108093902316079136 := by decide +kernel
private theorem receipt_1_9_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 128 128 = 74970548078234139492588594 := by decide +kernel
private theorem receipt_1_9_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 256 128 = 33435683073260651840397514 := by decide +kernel
private theorem receipt_1_9_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 384 56 = 3161655259909212422583501 := by decide +kernel
private theorem receipt_1_9_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 0 256 = 198152526186328041808667730 :=
  phaseBlock_append receipt_1_9_2403_1_part0 receipt_1_9_2403_1_part1 rfl rfl rfl
private theorem receipt_1_9_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 256 184 = 36597338333169864262981015 :=
  phaseBlock_append receipt_1_9_2403_1_part2 receipt_1_9_2403_1_part3 rfl rfl rfl
private theorem receipt_1_9_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179798 2403 10 1 0 2 1) 0 440 = 234749864519497906071648745 :=
  phaseBlock_append receipt_1_9_2403_1_join0 receipt_1_9_2403_1_join1 rfl rfl rfl

private theorem receipt_1_9_2403_1 : fastPhase (bank 1 9).shape 179798 2403 10 1 0 2 1 = 234749864519497906071648745 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2403_1_join2

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2402_0 receipt_1_9_2402_1 receipt_1_9_2403_0 receipt_1_9_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 0 128 = 66553090152466651890490215 := by decide +kernel
private theorem receipt_2_9_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 128 128 = 40055366995783141384331754 := by decide +kernel
private theorem receipt_2_9_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 256 128 = 17721584174098021691553576 := by decide +kernel
private theorem receipt_2_9_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 384 56 = 1705539036049819013221906 := by decide +kernel
private theorem receipt_2_9_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 0 256 = 106608457148249793274821969 :=
  phaseBlock_append receipt_2_9_2402_0_part0 receipt_2_9_2402_0_part1 rfl rfl rfl
private theorem receipt_2_9_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 256 184 = 19427123210147840704775482 :=
  phaseBlock_append receipt_2_9_2402_0_part2 receipt_2_9_2402_0_part3 rfl rfl rfl
private theorem receipt_2_9_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 0) 0 440 = 126035580358397633979597451 :=
  phaseBlock_append receipt_2_9_2402_0_join0 receipt_2_9_2402_0_join1 rfl rfl rfl

private theorem receipt_2_9_2402_0 : fastPhase (bank 2 9).shape 179798 2402 10 1 0 7 0 = 126035580358397633979597451 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2402_0_join2

private theorem receipt_2_9_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 0 128 = 66331536500289416188015869 := by decide +kernel
private theorem receipt_2_9_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 128 128 = 39866946489290309254018027 := by decide +kernel
private theorem receipt_2_9_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 256 128 = 17563187608862527689388982 := by decide +kernel
private theorem receipt_2_9_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 384 56 = 1644917100426043183491164 := by decide +kernel
private theorem receipt_2_9_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 0 256 = 106198482989579725442033896 :=
  phaseBlock_append receipt_2_9_2402_1_part0 receipt_2_9_2402_1_part1 rfl rfl rfl
private theorem receipt_2_9_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 256 184 = 19208104709288570872880146 :=
  phaseBlock_append receipt_2_9_2402_1_part2 receipt_2_9_2402_1_part3 rfl rfl rfl
private theorem receipt_2_9_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2402 10 1 0 7 1) 0 440 = 125406587698868296314914042 :=
  phaseBlock_append receipt_2_9_2402_1_join0 receipt_2_9_2402_1_join1 rfl rfl rfl

private theorem receipt_2_9_2402_1 : fastPhase (bank 2 9).shape 179798 2402 10 1 0 7 1 = 125406587698868296314914042 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2402_1_join2

private theorem receipt_2_9_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 0 128 = 66553664655207716799930859 := by decide +kernel
private theorem receipt_2_9_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 128 128 = 40055649650398323607800505 := by decide +kernel
private theorem receipt_2_9_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 256 128 = 17721679710810829465457242 := by decide +kernel
private theorem receipt_2_9_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 384 56 = 1705545861856920547180843 := by decide +kernel
private theorem receipt_2_9_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 0 256 = 106609314305606040407731364 :=
  phaseBlock_append receipt_2_9_2403_0_part0 receipt_2_9_2403_0_part1 rfl rfl rfl
private theorem receipt_2_9_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 256 184 = 19427225572667750012638085 :=
  phaseBlock_append receipt_2_9_2403_0_part2 receipt_2_9_2403_0_part3 rfl rfl rfl
private theorem receipt_2_9_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 0) 0 440 = 126036539878273790420369449 :=
  phaseBlock_append receipt_2_9_2403_0_join0 receipt_2_9_2403_0_join1 rfl rfl rfl

private theorem receipt_2_9_2403_0 : fastPhase (bank 2 9).shape 179798 2403 10 1 0 7 0 = 126036539878273790420369449 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2403_0_join2

private theorem receipt_2_9_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 0 128 = 66332109409933601360564830 := by decide +kernel
private theorem receipt_2_9_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 128 128 = 39867227998878709345713832 := by decide +kernel
private theorem receipt_2_9_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 256 128 = 17563282384066009131905056 := by decide +kernel
private theorem receipt_2_9_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 384 56 = 1644923697730394434742487 := by decide +kernel
private theorem receipt_2_9_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 0 256 = 106199337408812310706278662 :=
  phaseBlock_append receipt_2_9_2403_1_part0 receipt_2_9_2403_1_part1 rfl rfl rfl
private theorem receipt_2_9_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 256 184 = 19208206081796403566647543 :=
  phaseBlock_append receipt_2_9_2403_1_part2 receipt_2_9_2403_1_part3 rfl rfl rfl
private theorem receipt_2_9_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179798 2403 10 1 0 7 1) 0 440 = 125407543490608714272926205 :=
  phaseBlock_append receipt_2_9_2403_1_join0 receipt_2_9_2403_1_join1 rfl rfl rfl

private theorem receipt_2_9_2403_1 : fastPhase (bank 2 9).shape 179798 2403 10 1 0 7 1 = 125407543490608714272926205 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2403_1_join2

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2402_0 receipt_2_9_2402_1 receipt_2_9_2403_0 receipt_2_9_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 0 128 = 12668306539379705734538688 := by decide +kernel
private theorem receipt_3_9_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 128 128 = 7792728424845173874369984 := by decide +kernel
private theorem receipt_3_9_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 256 128 = 3636420859547277015360960 := by decide +kernel
private theorem receipt_3_9_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 384 73 = 507242813281515746076150 := by decide +kernel
private theorem receipt_3_9_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 0 256 = 20461034964224879608908672 :=
  phaseBlock_append receipt_3_9_2402_0_part0 receipt_3_9_2402_0_part1 rfl rfl rfl
private theorem receipt_3_9_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 256 201 = 4143663672828792761437110 :=
  phaseBlock_append receipt_3_9_2402_0_part2 receipt_3_9_2402_0_part3 rfl rfl rfl
private theorem receipt_3_9_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 0) 0 457 = 24604698637053672370345782 :=
  phaseBlock_append receipt_3_9_2402_0_join0 receipt_3_9_2402_0_join1 rfl rfl rfl

private theorem receipt_3_9_2402_0 : fastPhase (bank 3 9).shape 179798 2402 10 1 1 1 0 = 24604698637053672370345782 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2402_0_join2

private theorem receipt_3_9_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 0 128 = 12628061254455033564338112 := by decide +kernel
private theorem receipt_3_9_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 128 128 = 7757692536765964111321024 := by decide +kernel
private theorem receipt_3_9_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 256 128 = 3607057839011068671334336 := by decide +kernel
private theorem receipt_3_9_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 384 73 = 493210957564222121696604 := by decide +kernel
private theorem receipt_3_9_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 0 256 = 20385753791220997675659136 :=
  phaseBlock_append receipt_3_9_2402_1_part0 receipt_3_9_2402_1_part1 rfl rfl rfl
private theorem receipt_3_9_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 256 201 = 4100268796575290793030940 :=
  phaseBlock_append receipt_3_9_2402_1_part2 receipt_3_9_2402_1_part3 rfl rfl rfl
private theorem receipt_3_9_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2402 10 1 1 1 1) 0 457 = 24486022587796288468690076 :=
  phaseBlock_append receipt_3_9_2402_1_join0 receipt_3_9_2402_1_join1 rfl rfl rfl

private theorem receipt_3_9_2402_1 : fastPhase (bank 3 9).shape 179798 2402 10 1 1 1 1 = 24486022587796288468690076 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2402_1_join2

private theorem receipt_3_9_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 0 128 = 12668409509780404229484800 := by decide +kernel
private theorem receipt_3_9_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 128 128 = 7792772792853048203940096 := by decide +kernel
private theorem receipt_3_9_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 256 128 = 3636433331749221101367552 := by decide +kernel
private theorem receipt_3_9_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 384 73 = 507243663954463540619488 := by decide +kernel
private theorem receipt_3_9_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 0 256 = 20461182302633452433424896 :=
  phaseBlock_append receipt_3_9_2403_0_part0 receipt_3_9_2403_0_part1 rfl rfl rfl
private theorem receipt_3_9_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 256 201 = 4143676995703684641987040 :=
  phaseBlock_append receipt_3_9_2403_0_part2 receipt_3_9_2403_0_part3 rfl rfl rfl
private theorem receipt_3_9_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 0) 0 457 = 24604859298337137075411936 :=
  phaseBlock_append receipt_3_9_2403_0_join0 receipt_3_9_2403_0_join1 rfl rfl rfl

private theorem receipt_3_9_2403_0 : fastPhase (bank 3 9).shape 179798 2403 10 1 1 1 0 = 24604859298337137075411936 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2403_0_join2

private theorem receipt_3_9_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 0 128 = 12628163851101544839024960 := by decide +kernel
private theorem receipt_3_9_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 128 128 = 7757736683070525781971264 := by decide +kernel
private theorem receipt_3_9_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 256 128 = 3607070205514698158084416 := by decide +kernel
private theorem receipt_3_9_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 384 73 = 493211786348915025157044 := by decide +kernel
private theorem receipt_3_9_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 0 256 = 20385900534172070620996224 :=
  phaseBlock_append receipt_3_9_2403_1_part0 receipt_3_9_2403_1_part1 rfl rfl rfl
private theorem receipt_3_9_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 256 201 = 4100281991863613183241460 :=
  phaseBlock_append receipt_3_9_2403_1_part2 receipt_3_9_2403_1_part3 rfl rfl rfl
private theorem receipt_3_9_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179798 2403 10 1 1 1 1) 0 457 = 24486182526035683804237684 :=
  phaseBlock_append receipt_3_9_2403_1_join0 receipt_3_9_2403_1_join1 rfl rfl rfl

private theorem receipt_3_9_2403_1 : fastPhase (bank 3 9).shape 179798 2403 10 1 1 1 1 = 24486182526035683804237684 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2403_1_join2

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2402_0 receipt_3_9_2402_1 receipt_3_9_2403_0 receipt_3_9_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 0 128 = 1596841238229864546739494144 := by decide +kernel
private theorem receipt_0_10_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 128 128 = 1238895914146172663477058816 := by decide +kernel
private theorem receipt_0_10_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 256 128 = 910179575399259741315882240 := by decide +kernel
private theorem receipt_0_10_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 384 128 = 609445754104302016922849787 := by decide +kernel
private theorem receipt_0_10_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 512 128 = 335453434481474929156214793 := by decide +kernel
private theorem receipt_0_10_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 640 111 = 88842214215793593652062543 := by decide +kernel
private theorem receipt_0_10_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 128 256 = 2149075489545432404792941056 :=
  phaseBlock_append receipt_0_10_2402_0_part1 receipt_0_10_2402_0_part2 rfl rfl rfl
private theorem receipt_0_10_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 0 384 = 3745916727775296951532435200 :=
  phaseBlock_append receipt_0_10_2402_0_part0 receipt_0_10_2402_0_join0 rfl rfl rfl
private theorem receipt_0_10_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 512 239 = 424295648697268522808277336 :=
  phaseBlock_append receipt_0_10_2402_0_part4 receipt_0_10_2402_0_part5 rfl rfl rfl
private theorem receipt_0_10_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 384 367 = 1033741402801570539731127123 :=
  phaseBlock_append receipt_0_10_2402_0_part3 receipt_0_10_2402_0_join2 rfl rfl rfl
private theorem receipt_0_10_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 0) 0 751 = 4779658130576867491263562323 :=
  phaseBlock_append receipt_0_10_2402_0_join1 receipt_0_10_2402_0_join3 rfl rfl rfl

private theorem receipt_0_10_2402_0 : fastPhase (bank 0 10).shape 179798 2402 20 1 0 1 0 = 4779658130576867491263562323 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2402_0_join4

private theorem receipt_0_10_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 0 128 = 1593966970753114571230651008 := by decide +kernel
private theorem receipt_0_10_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 128 128 = 1236246935786293601415643776 := by decide +kernel
private theorem receipt_0_10_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 256 128 = 907746449164300364921299584 := by decide +kernel
private theorem receipt_0_10_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 384 128 = 607219080457189182869395839 := by decide +kernel
private theorem receipt_0_10_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 512 128 = 333423847672918107722941623 := by decide +kernel
private theorem receipt_0_10_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 640 111 = 87234519416399428174754184 := by decide +kernel
private theorem receipt_0_10_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 128 256 = 2143993384950593966336943360 :=
  phaseBlock_append receipt_0_10_2402_1_part1 receipt_0_10_2402_1_part2 rfl rfl rfl
private theorem receipt_0_10_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 0 384 = 3737960355703708537567594368 :=
  phaseBlock_append receipt_0_10_2402_1_part0 receipt_0_10_2402_1_join0 rfl rfl rfl
private theorem receipt_0_10_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 512 239 = 420658367089317535897695807 :=
  phaseBlock_append receipt_0_10_2402_1_part4 receipt_0_10_2402_1_part5 rfl rfl rfl
private theorem receipt_0_10_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 384 367 = 1027877447546506718767091646 :=
  phaseBlock_append receipt_0_10_2402_1_part3 receipt_0_10_2402_1_join2 rfl rfl rfl
private theorem receipt_0_10_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2402 20 1 0 1 1) 0 751 = 4765837803250215256334686014 :=
  phaseBlock_append receipt_0_10_2402_1_join1 receipt_0_10_2402_1_join3 rfl rfl rfl

private theorem receipt_0_10_2402_1 : fastPhase (bank 0 10).shape 179798 2402 20 1 0 1 1 = 4765837803250215256334686014 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2402_1_join4

private theorem receipt_0_10_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 0 128 = 1596855374017446311843066240 := by decide +kernel
private theorem receipt_0_10_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 128 128 = 1238905745360760100812730752 := by decide +kernel
private theorem receipt_0_10_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 256 128 = 910185917796962315300204928 := by decide +kernel
private theorem receipt_0_10_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 384 128 = 609449380125528592661836345 := by decide +kernel
private theorem receipt_0_10_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 512 128 = 335455069823340058561298574 := by decide +kernel
private theorem receipt_0_10_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 640 111 = 88842559032434866518316091 := by decide +kernel
private theorem receipt_0_10_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 128 256 = 2149091663157722416112935680 :=
  phaseBlock_append receipt_0_10_2403_0_part1 receipt_0_10_2403_0_part2 rfl rfl rfl
private theorem receipt_0_10_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 0 384 = 3745947037175168727956001920 :=
  phaseBlock_append receipt_0_10_2403_0_part0 receipt_0_10_2403_0_join0 rfl rfl rfl
private theorem receipt_0_10_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 512 239 = 424297628855774925079614665 :=
  phaseBlock_append receipt_0_10_2403_0_part4 receipt_0_10_2403_0_part5 rfl rfl rfl
private theorem receipt_0_10_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 384 367 = 1033747008981303517741451010 :=
  phaseBlock_append receipt_0_10_2403_0_part3 receipt_0_10_2403_0_join2 rfl rfl rfl
private theorem receipt_0_10_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 0) 0 751 = 4779694046156472245697452930 :=
  phaseBlock_append receipt_0_10_2403_0_join1 receipt_0_10_2403_0_join3 rfl rfl rfl

private theorem receipt_0_10_2403_0 : fastPhase (bank 0 10).shape 179798 2403 20 1 0 1 0 = 4779694046156472245697452930 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2403_0_join4

private theorem receipt_0_10_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 0 128 = 1593981085742619270394641920 := by decide +kernel
private theorem receipt_0_10_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 128 128 = 1236256749451399351908761088 := by decide +kernel
private theorem receipt_0_10_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 256 128 = 907752777058153564843703808 := by decide +kernel
private theorem receipt_0_10_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 384 128 = 607222694819618665967642263 := by decide +kernel
private theorem receipt_0_10_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 512 128 = 333425474028151792724081078 := by decide +kernel
private theorem receipt_0_10_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 640 111 = 87234858451331785230661734 := by decide +kernel
private theorem receipt_0_10_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 128 256 = 2144009526509552916752464896 :=
  phaseBlock_append receipt_0_10_2403_1_part1 receipt_0_10_2403_1_part2 rfl rfl rfl
private theorem receipt_0_10_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 0 384 = 3737990612252172187147106816 :=
  phaseBlock_append receipt_0_10_2403_1_part0 receipt_0_10_2403_1_join0 rfl rfl rfl
private theorem receipt_0_10_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 512 239 = 420660332479483577954742812 :=
  phaseBlock_append receipt_0_10_2403_1_part4 receipt_0_10_2403_1_part5 rfl rfl rfl
private theorem receipt_0_10_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 384 367 = 1027883027299102243922385075 :=
  phaseBlock_append receipt_0_10_2403_1_part3 receipt_0_10_2403_1_join2 rfl rfl rfl
private theorem receipt_0_10_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179798 2403 20 1 0 1 1) 0 751 = 4765873639551274431069491891 :=
  phaseBlock_append receipt_0_10_2403_1_join1 receipt_0_10_2403_1_join3 rfl rfl rfl

private theorem receipt_0_10_2403_1 : fastPhase (bank 0 10).shape 179798 2403 20 1 0 1 1 = 4765873639551274431069491891 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2403_1_join4

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2402_0 receipt_0_10_2402_1 receipt_0_10_2403_0 receipt_0_10_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 0 128 = 1424120936878031631579598176 := by decide +kernel
private theorem receipt_1_10_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 128 128 = 1103610484485887664311401824 := by decide +kernel
private theorem receipt_1_10_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 256 128 = 809849272908407017759124832 := by decide +kernel
private theorem receipt_1_10_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 384 128 = 541638939285379530583050687 := by decide +kernel
private theorem receipt_1_10_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 512 128 = 297791061028879220143509429 := by decide +kernel
private theorem receipt_1_10_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 640 111 = 78788795320786747296410115 := by decide +kernel
private theorem receipt_1_10_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 128 256 = 1913459757394294682070526656 :=
  phaseBlock_append receipt_1_10_2402_0_part1 receipt_1_10_2402_0_part2 rfl rfl rfl
private theorem receipt_1_10_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 0 384 = 3337580694272326313650124832 :=
  phaseBlock_append receipt_1_10_2402_0_part0 receipt_1_10_2402_0_join0 rfl rfl rfl
private theorem receipt_1_10_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 512 239 = 376579856349665967439919544 :=
  phaseBlock_append receipt_1_10_2402_0_part4 receipt_1_10_2402_0_part5 rfl rfl rfl
private theorem receipt_1_10_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 384 367 = 918218795635045498022970231 :=
  phaseBlock_append receipt_1_10_2402_0_part3 receipt_1_10_2402_0_join2 rfl rfl rfl
private theorem receipt_1_10_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 0) 0 751 = 4255799489907371811673095063 :=
  phaseBlock_append receipt_1_10_2402_0_join1 receipt_1_10_2402_0_join3 rfl rfl rfl

private theorem receipt_1_10_2402_0 : fastPhase (bank 1 10).shape 179798 2402 20 1 0 2 0 = 4255799489907371811673095063 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2402_0_join4

private theorem receipt_1_10_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 0 128 = 1421544670838213461120698336 := by decide +kernel
private theorem receipt_1_10_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 128 128 = 1101240783237151316435744736 := by decide +kernel
private theorem receipt_1_10_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 256 128 = 807677038712691722318096352 := by decide +kernel
private theorem receipt_1_10_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 384 128 = 539655146589313470811233899 := by decide +kernel
private theorem receipt_1_10_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 512 128 = 295986753055226778757568263 := by decide +kernel
private theorem receipt_1_10_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 640 111 = 77362551646961323726833223 := by decide +kernel
private theorem receipt_1_10_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 128 256 = 1908917821949843038753841088 :=
  phaseBlock_append receipt_1_10_2402_1_part1 receipt_1_10_2402_1_part2 rfl rfl rfl
private theorem receipt_1_10_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 0 384 = 3330462492788056499874539424 :=
  phaseBlock_append receipt_1_10_2402_1_part0 receipt_1_10_2402_1_join0 rfl rfl rfl
private theorem receipt_1_10_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 512 239 = 373349304702188102484401486 :=
  phaseBlock_append receipt_1_10_2402_1_part4 receipt_1_10_2402_1_part5 rfl rfl rfl
private theorem receipt_1_10_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 384 367 = 913004451291501573295635385 :=
  phaseBlock_append receipt_1_10_2402_1_part3 receipt_1_10_2402_1_join2 rfl rfl rfl
private theorem receipt_1_10_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2402 20 1 0 2 1) 0 751 = 4243466944079558073170174809 :=
  phaseBlock_append receipt_1_10_2402_1_join1 receipt_1_10_2402_1_join3 rfl rfl rfl

private theorem receipt_1_10_2402_1 : fastPhase (bank 1 10).shape 179798 2402 20 1 0 2 1 = 4243466944079558073170174809 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2402_1_join4

private theorem receipt_1_10_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 0 128 = 1424133543809368284886466880 := by decide +kernel
private theorem receipt_1_10_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 128 128 = 1103619242248673762813681984 := by decide +kernel
private theorem receipt_1_10_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 256 128 = 809854916253387826022072640 := by decide +kernel
private theorem receipt_1_10_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 384 128 = 541642161931346593614755763 := by decide +kernel
private theorem receipt_1_10_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 512 128 = 297792512797580100225604889 := by decide +kernel
private theorem receipt_1_10_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 640 111 = 78789101122485759412288223 := by decide +kernel
private theorem receipt_1_10_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 128 256 = 1913474158502061588835754624 :=
  phaseBlock_append receipt_1_10_2403_0_part1 receipt_1_10_2403_0_part2 rfl rfl rfl
private theorem receipt_1_10_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 0 384 = 3337607702311429873722221504 :=
  phaseBlock_append receipt_1_10_2403_0_part0 receipt_1_10_2403_0_join0 rfl rfl rfl
private theorem receipt_1_10_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 512 239 = 376581613920065859637893112 :=
  phaseBlock_append receipt_1_10_2403_0_part4 receipt_1_10_2403_0_part5 rfl rfl rfl
private theorem receipt_1_10_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 384 367 = 918223775851412453252648875 :=
  phaseBlock_append receipt_1_10_2403_0_part3 receipt_1_10_2403_0_join2 rfl rfl rfl
private theorem receipt_1_10_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 0) 0 751 = 4255831478162842326974870379 :=
  phaseBlock_append receipt_1_10_2403_0_join1 receipt_1_10_2403_0_join3 rfl rfl rfl

private theorem receipt_1_10_2403_0 : fastPhase (bank 1 10).shape 179798 2403 20 1 0 2 0 = 4255831478162842326974870379 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2403_0_join4

private theorem receipt_1_10_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 0 128 = 1421557259106718658313894656 := by decide +kernel
private theorem receipt_1_10_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 128 128 = 1101249525287347038726273792 := by decide +kernel
private theorem receipt_1_10_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 256 128 = 807682669101410285006863104 := by decide +kernel
private theorem receipt_1_10_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 384 128 = 539658358844521515849015759 := by decide +kernel
private theorem receipt_1_10_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 512 128 = 295988196833420165995345354 := by decide +kernel
private theorem receipt_1_10_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 640 111 = 77362852319195854557738791 := by decide +kernel
private theorem receipt_1_10_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 128 256 = 1908932194388757323733136896 :=
  phaseBlock_append receipt_1_10_2403_1_part1 receipt_1_10_2403_1_part2 rfl rfl rfl
private theorem receipt_1_10_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 0 384 = 3330489453495475982047031552 :=
  phaseBlock_append receipt_1_10_2403_1_part0 receipt_1_10_2403_1_join0 rfl rfl rfl
private theorem receipt_1_10_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 512 239 = 373351049152616020553084145 :=
  phaseBlock_append receipt_1_10_2403_1_part4 receipt_1_10_2403_1_part5 rfl rfl rfl
private theorem receipt_1_10_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 384 367 = 913009407997137536402099904 :=
  phaseBlock_append receipt_1_10_2403_1_part3 receipt_1_10_2403_1_join2 rfl rfl rfl
private theorem receipt_1_10_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179798 2403 20 1 0 2 1) 0 751 = 4243498861492613518449131456 :=
  phaseBlock_append receipt_1_10_2403_1_join1 receipt_1_10_2403_1_join3 rfl rfl rfl

private theorem receipt_1_10_2403_1 : fastPhase (bank 1 10).shape 179798 2403 20 1 0 2 1 = 4243498861492613518449131456 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2403_1_join4

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2402_0 receipt_1_10_2402_1 receipt_1_10_2403_0 receipt_1_10_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 0 128 = 713458754306069968228382016 := by decide +kernel
private theorem receipt_2_10_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 128 128 = 548101028683408213469246784 := by decide +kernel
private theorem receipt_2_10_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 256 128 = 398708014312575206419035456 := by decide +kernel
private theorem receipt_2_10_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 384 128 = 264338167973589715153691355 := by decide +kernel
private theorem receipt_2_10_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 512 128 = 144076910385675084577455063 := by decide +kernel
private theorem receipt_2_10_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 640 111 = 37829341177846096259631441 := by decide +kernel
private theorem receipt_2_10_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 128 256 = 946809042995983419888282240 :=
  phaseBlock_append receipt_2_10_2402_0_part1 receipt_2_10_2402_0_part2 rfl rfl rfl
private theorem receipt_2_10_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 0 384 = 1660267797302053388116664256 :=
  phaseBlock_append receipt_2_10_2402_0_part0 receipt_2_10_2402_0_join0 rfl rfl rfl
private theorem receipt_2_10_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 512 239 = 181906251563521180837086504 :=
  phaseBlock_append receipt_2_10_2402_0_part4 receipt_2_10_2402_0_part5 rfl rfl rfl
private theorem receipt_2_10_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 384 367 = 446244419537110895990777859 :=
  phaseBlock_append receipt_2_10_2402_0_part3 receipt_2_10_2402_0_join2 rfl rfl rfl
private theorem receipt_2_10_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 0) 0 751 = 2106512216839164284107442115 :=
  phaseBlock_append receipt_2_10_2402_0_join1 receipt_2_10_2402_0_join3 rfl rfl rfl

private theorem receipt_2_10_2402_0 : fastPhase (bank 2 10).shape 179798 2402 20 1 0 7 0 = 2106512216839164284107442115 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2402_0_join4

private theorem receipt_2_10_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 0 128 = 712119827933103427001555904 := by decide +kernel
private theorem receipt_2_10_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 128 128 = 546886878307850834776382400 := by decide +kernel
private theorem receipt_2_10_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 256 128 = 397611389834380478020983744 := by decide +kernel
private theorem receipt_2_10_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 384 128 = 263352024327057524478685595 := by decide +kernel
private theorem receipt_2_10_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 512 128 = 143194403611193860432704745 := by decide +kernel
private theorem receipt_2_10_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 640 111 = 37142798967260551251307012 := by decide +kernel
private theorem receipt_2_10_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 128 256 = 944498268142231312797366144 :=
  phaseBlock_append receipt_2_10_2402_1_part1 receipt_2_10_2402_1_part2 rfl rfl rfl
private theorem receipt_2_10_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 0 384 = 1656618096075334739798922048 :=
  phaseBlock_append receipt_2_10_2402_1_part0 receipt_2_10_2402_1_join0 rfl rfl rfl
private theorem receipt_2_10_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 512 239 = 180337202578454411684011757 :=
  phaseBlock_append receipt_2_10_2402_1_part4 receipt_2_10_2402_1_part5 rfl rfl rfl
private theorem receipt_2_10_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 384 367 = 443689226905511936162697352 :=
  phaseBlock_append receipt_2_10_2402_1_part3 receipt_2_10_2402_1_join2 rfl rfl rfl
private theorem receipt_2_10_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2402 20 1 0 7 1) 0 751 = 2100307322980846675961619400 :=
  phaseBlock_append receipt_2_10_2402_1_join1 receipt_2_10_2402_1_join3 rfl rfl rfl

private theorem receipt_2_10_2402_1 : fastPhase (bank 2 10).shape 179798 2402 20 1 0 7 1 = 2100307322980846675961619400 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2402_1_join4

private theorem receipt_2_10_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 0 128 = 713465070611382909867957120 := by decide +kernel
private theorem receipt_2_10_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 128 128 = 548105378546265847467203456 := by decide +kernel
private theorem receipt_2_10_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 256 128 = 398710792955777199426182016 := by decide +kernel
private theorem receipt_2_10_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 384 128 = 264339740938235388740222049 := by decide +kernel
private theorem receipt_2_10_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 512 128 = 144077612895252207820022780 := by decide +kernel
private theorem receipt_2_10_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 640 111 = 37829488021319994436120811 := by decide +kernel
private theorem receipt_2_10_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 128 256 = 946816171502043046893385472 :=
  phaseBlock_append receipt_2_10_2403_0_part1 receipt_2_10_2403_0_part2 rfl rfl rfl
private theorem receipt_2_10_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 0 384 = 1660281242113425956761342592 :=
  phaseBlock_append receipt_2_10_2403_0_part0 receipt_2_10_2403_0_join0 rfl rfl rfl
private theorem receipt_2_10_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 512 239 = 181907100916572202256143591 :=
  phaseBlock_append receipt_2_10_2403_0_part4 receipt_2_10_2403_0_part5 rfl rfl rfl
private theorem receipt_2_10_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 384 367 = 446246841854807590996365640 :=
  phaseBlock_append receipt_2_10_2403_0_part3 receipt_2_10_2403_0_join2 rfl rfl rfl
private theorem receipt_2_10_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 0) 0 751 = 2106528083968233547757708232 :=
  phaseBlock_append receipt_2_10_2403_0_join1 receipt_2_10_2403_0_join3 rfl rfl rfl

private theorem receipt_2_10_2403_0 : fastPhase (bank 2 10).shape 179798 2403 20 1 0 7 0 = 2106528083968233547757708232 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2403_0_join4

private theorem receipt_2_10_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 0 128 = 712126134460494125890965248 := by decide +kernel
private theorem receipt_2_10_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 128 128 = 546891220070648192403017472 := by decide +kernel
private theorem receipt_2_10_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 256 128 = 397614161908664104519634688 := by decide +kernel
private theorem receipt_2_10_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 384 128 = 263353592112859771484356563 := by decide +kernel
private theorem receipt_2_10_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 512 128 = 143195102207481403745785318 := by decide +kernel
private theorem receipt_2_10_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 640 111 = 37142943340480543758901496 := by decide +kernel
private theorem receipt_2_10_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 128 256 = 944505381979312296922652160 :=
  phaseBlock_append receipt_2_10_2403_1_part1 receipt_2_10_2403_1_part2 rfl rfl rfl
private theorem receipt_2_10_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 0 384 = 1656631516439806422813617408 :=
  phaseBlock_append receipt_2_10_2403_1_part0 receipt_2_10_2403_1_join0 rfl rfl rfl
private theorem receipt_2_10_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 512 239 = 180338045547961947504686814 :=
  phaseBlock_append receipt_2_10_2403_1_part4 receipt_2_10_2403_1_part5 rfl rfl rfl
private theorem receipt_2_10_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 384 367 = 443691637660821718989043377 :=
  phaseBlock_append receipt_2_10_2403_1_part3 receipt_2_10_2403_1_join2 rfl rfl rfl
private theorem receipt_2_10_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179798 2403 20 1 0 7 1) 0 751 = 2100323154100628141802660785 :=
  phaseBlock_append receipt_2_10_2403_1_join1 receipt_2_10_2403_1_join3 rfl rfl rfl

private theorem receipt_2_10_2403_1 : fastPhase (bank 2 10).shape 179798 2403 20 1 0 7 1 = 2100323154100628141802660785 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2403_1_join4

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2402_0 receipt_2_10_2402_1 receipt_2_10_2403_0 receipt_2_10_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 0 128 = 67163562224261018346422592 := by decide +kernel
private theorem receipt_3_10_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 128 128 = 46928821149916051048726848 := by decide +kernel
private theorem receipt_3_10_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 256 128 = 28846410742676698214269248 := by decide +kernel
private theorem receipt_3_10_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 384 128 = 13051846525312191953600832 := by decide +kernel
private theorem receipt_3_10_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 512 59 = 1361888341937810833003710 := by decide +kernel
private theorem receipt_3_10_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 0 256 = 114092383374177069395149440 :=
  phaseBlock_append receipt_3_10_2402_0_part0 receipt_3_10_2402_0_part1 rfl rfl rfl
private theorem receipt_3_10_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 384 187 = 14413734867250002786604542 :=
  phaseBlock_append receipt_3_10_2402_0_part3 receipt_3_10_2402_0_part4 rfl rfl rfl
private theorem receipt_3_10_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 256 315 = 43260145609926701000873790 :=
  phaseBlock_append receipt_3_10_2402_0_part2 receipt_3_10_2402_0_join1 rfl rfl rfl
private theorem receipt_3_10_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 0) 0 571 = 157352528984103770396023230 :=
  phaseBlock_append receipt_3_10_2402_0_join0 receipt_3_10_2402_0_join2 rfl rfl rfl

private theorem receipt_3_10_2402_0 : fastPhase (bank 3 10).shape 179798 2402 20 1 1 1 0 = 157352528984103770396023230 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2402_0_join3

private theorem receipt_3_10_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 0 128 = 66999505931135912375799552 := by decide +kernel
private theorem receipt_3_10_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 128 128 = 46780412642462039031279360 := by decide +kernel
private theorem receipt_3_10_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 256 128 = 28714803974604451394817792 := by decide +kernel
private theorem receipt_3_10_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 384 128 = 12938178144823952175542016 := by decide +kernel
private theorem receipt_3_10_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 512 59 = 1315844008238250432402348 := by decide +kernel
private theorem receipt_3_10_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 0 256 = 113779918573597951407078912 :=
  phaseBlock_append receipt_3_10_2402_1_part0 receipt_3_10_2402_1_part1 rfl rfl rfl
private theorem receipt_3_10_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 384 187 = 14254022153062202607944364 :=
  phaseBlock_append receipt_3_10_2402_1_part3 receipt_3_10_2402_1_part4 rfl rfl rfl
private theorem receipt_3_10_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 256 315 = 42968826127666654002762156 :=
  phaseBlock_append receipt_3_10_2402_1_part2 receipt_3_10_2402_1_join1 rfl rfl rfl
private theorem receipt_3_10_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2402 20 1 1 1 1) 0 571 = 156748744701264605409841068 :=
  phaseBlock_append receipt_3_10_2402_1_join0 receipt_3_10_2402_1_join2 rfl rfl rfl

private theorem receipt_3_10_2402_1 : fastPhase (bank 3 10).shape 179798 2402 20 1 1 1 1 = 156748744701264605409841068 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2402_1_join3

private theorem receipt_3_10_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 0 128 = 67164120356264250529228928 := by decide +kernel
private theorem receipt_3_10_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 128 128 = 46929121494626122676340864 := by decide +kernel
private theorem receipt_3_10_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 256 128 = 28846542703611914415106176 := by decide +kernel
private theorem receipt_3_10_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 384 128 = 13051883949378955173644416 := by decide +kernel
private theorem receipt_3_10_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 512 59 = 1361890484231398076484704 := by decide +kernel
private theorem receipt_3_10_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 0 256 = 114093241850890373205569792 :=
  phaseBlock_append receipt_3_10_2403_0_part0 receipt_3_10_2403_0_part1 rfl rfl rfl
private theorem receipt_3_10_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 384 187 = 14413774433610353250129120 :=
  phaseBlock_append receipt_3_10_2403_0_part3 receipt_3_10_2403_0_part4 rfl rfl rfl
private theorem receipt_3_10_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 256 315 = 43260317137222267665235296 :=
  phaseBlock_append receipt_3_10_2403_0_part2 receipt_3_10_2403_0_join1 rfl rfl rfl
private theorem receipt_3_10_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 0) 0 571 = 157353558988112640870805088 :=
  phaseBlock_append receipt_3_10_2403_0_join0 receipt_3_10_2403_0_join2 rfl rfl rfl

private theorem receipt_3_10_2403_0 : fastPhase (bank 3 10).shape 179798 2403 20 1 1 1 0 = 157353558988112640870805088 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2403_0_join3

private theorem receipt_3_10_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 0 128 = 67000062501803701168876032 := by decide +kernel
private theorem receipt_3_10_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 128 128 = 46780711920074769380510208 := by decide +kernel
private theorem receipt_3_10_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 256 128 = 28714935276596312491256320 := by decide +kernel
private theorem receipt_3_10_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 384 128 = 12938215233268076938873344 := by decide +kernel
private theorem receipt_3_10_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 512 59 = 1315846081559814326673956 := by decide +kernel
private theorem receipt_3_10_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 0 256 = 113780774421878470549386240 :=
  phaseBlock_append receipt_3_10_2403_1_part0 receipt_3_10_2403_1_part1 rfl rfl rfl
private theorem receipt_3_10_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 384 187 = 14254061314827891265547300 :=
  phaseBlock_append receipt_3_10_2403_1_part3 receipt_3_10_2403_1_part4 rfl rfl rfl
private theorem receipt_3_10_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 256 315 = 42968996591424203756803620 :=
  phaseBlock_append receipt_3_10_2403_1_part2 receipt_3_10_2403_1_join1 rfl rfl rfl
private theorem receipt_3_10_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179798 2403 20 1 1 1 1) 0 571 = 156749771013302674306189860 :=
  phaseBlock_append receipt_3_10_2403_1_join0 receipt_3_10_2403_1_join2 rfl rfl rfl

private theorem receipt_3_10_2403_1 : fastPhase (bank 3 10).shape 179798 2403 20 1 1 1 1 = 156749771013302674306189860 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2403_1_join3

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2726_570)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_10_2402_0 receipt_3_10_2402_1 receipt_3_10_2403_0 receipt_3_10_2403_1 (by decide +kernel) (by decide +kernel)

def group3_stage (i : Fin 3) : Fin 17 :=
  ⟨8+i.val, by have := i.isLt; omega⟩

theorem group3_checked (rect : Fin 4) (i : Fin 3) :
    Checked (bank rect (group3_stage i)) (reserve (group3_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_8
    · exact receipt_1_8
    · exact receipt_2_8
    · exact receipt_3_8
  · fin_cases rect
    · exact receipt_0_9
    · exact receipt_1_9
    · exact receipt_2_9
    · exact receipt_3_9
  · fin_cases rect
    · exact receipt_0_10
    · exact receipt_1_10
    · exact receipt_2_10
    · exact receipt_3_10

theorem group3_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group3_stage i)).shape
      (cutoff h rect (group3_stage i)), ¬ G∣Q :=
  (group3_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group3_avoids

end Lower6960.RescueSource
