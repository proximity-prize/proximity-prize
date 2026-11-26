import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

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

private theorem receipt_0_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 0 128 = 525856775702927980658442368 := by decide +kernel
private theorem receipt_0_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 128 128 = 368253393045625592464703616 := by decide +kernel
private theorem receipt_0_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 256 128 = 227223763833173951540654584 := by decide +kernel
private theorem receipt_0_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 384 128 = 101850431499216355258641714 := by decide +kernel
private theorem receipt_0_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 512 52 = 8973124892866384456484490 := by decide +kernel
private theorem receipt_0_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 0 256 = 894110168748553573123145984 :=
  phaseBlock_append receipt_0_8_2359_0_part0 receipt_0_8_2359_0_part1 rfl rfl rfl
private theorem receipt_0_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 384 180 = 110823556392082739715126204 :=
  phaseBlock_append receipt_0_8_2359_0_part3 receipt_0_8_2359_0_part4 rfl rfl rfl
private theorem receipt_0_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 256 308 = 338047320225256691255780788 :=
  phaseBlock_append receipt_0_8_2359_0_part2 receipt_0_8_2359_0_join1 rfl rfl rfl
private theorem receipt_0_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 0) 0 564 = 1232157488973810264378926772 :=
  phaseBlock_append receipt_0_8_2359_0_join0 receipt_0_8_2359_0_join2 rfl rfl rfl

private theorem receipt_0_8_2359_0 : fastPhase (bank 0 8).shape 179818 2359 16 1 0 1 0 = 1232157488973810264378926772 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2359_0_join3

private theorem receipt_0_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 0 128 = 524574935357150421879720512 := by decide +kernel
private theorem receipt_0_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 128 128 = 367100157747075655619160640 := by decide +kernel
private theorem receipt_0_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 256 128 = 226192180387871483389814282 := by decide +kernel
private theorem receipt_0_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 384 128 = 100933576557325787331361738 := by decide +kernel
private theorem receipt_0_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 512 52 = 8631843077382732228752884 := by decide +kernel
private theorem receipt_0_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 0 256 = 891675093104226077498881152 :=
  phaseBlock_append receipt_0_8_2359_1_part0 receipt_0_8_2359_1_part1 rfl rfl rfl
private theorem receipt_0_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 384 180 = 109565419634708519560114622 :=
  phaseBlock_append receipt_0_8_2359_1_part3 receipt_0_8_2359_1_part4 rfl rfl rfl
private theorem receipt_0_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 256 308 = 335757600022580002949928904 :=
  phaseBlock_append receipt_0_8_2359_1_part2 receipt_0_8_2359_1_join1 rfl rfl rfl
private theorem receipt_0_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2359 16 1 0 1 1) 0 564 = 1227432693126806080448810056 :=
  phaseBlock_append receipt_0_8_2359_1_join0 receipt_0_8_2359_1_join2 rfl rfl rfl

private theorem receipt_0_8_2359_1 : fastPhase (bank 0 8).shape 179818 2359 16 1 0 1 1 = 1227432693126806080448810056 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2359_1_join3

private theorem receipt_0_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 0 128 = 525861333186702714169851168 := by decide +kernel
private theorem receipt_0_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 128 128 = 368256146551849968989334816 := by decide +kernel
private theorem receipt_0_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 256 128 = 227225174886282310245107012 := by decide +kernel
private theorem receipt_0_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 384 128 = 101850928556833924600259972 := by decide +kernel
private theorem receipt_0_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 512 52 = 8973158910426486934446745 := by decide +kernel
private theorem receipt_0_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 0 256 = 894117479738552683159185984 :=
  phaseBlock_append receipt_0_8_2360_0_part0 receipt_0_8_2360_0_part1 rfl rfl rfl
private theorem receipt_0_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 384 180 = 110824087467260411534706717 :=
  phaseBlock_append receipt_0_8_2360_0_part3 receipt_0_8_2360_0_part4 rfl rfl rfl
private theorem receipt_0_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 256 308 = 338049262353542721779813729 :=
  phaseBlock_append receipt_0_8_2360_0_part2 receipt_0_8_2360_0_join1 rfl rfl rfl
private theorem receipt_0_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 0) 0 564 = 1232166742092095404938999713 :=
  phaseBlock_append receipt_0_8_2360_0_join0 receipt_0_8_2360_0_join2 rfl rfl rfl

private theorem receipt_0_8_2360_0 : fastPhase (bank 0 8).shape 179818 2360 16 1 0 1 0 = 1232166742092095404938999713 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2360_0_join3

private theorem receipt_0_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 0 128 = 524579483676391155402499104 := by decide +kernel
private theorem receipt_0_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 128 128 = 367102903934346839803663392 := by decide +kernel
private theorem receipt_0_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 256 128 = 226193585818437530355965600 := by decide +kernel
private theorem receipt_0_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 384 128 = 100934069555133399009254536 := by decide +kernel
private theorem receipt_0_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 512 52 = 8631875858922868083351828 := by decide +kernel
private theorem receipt_0_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 0 256 = 891682387610737995206162496 :=
  phaseBlock_append receipt_0_8_2360_1_part0 receipt_0_8_2360_1_part1 rfl rfl rfl
private theorem receipt_0_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 384 180 = 109565945414056267092606364 :=
  phaseBlock_append receipt_0_8_2360_1_part3 receipt_0_8_2360_1_part4 rfl rfl rfl
private theorem receipt_0_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 256 308 = 335759531232493797448571964 :=
  phaseBlock_append receipt_0_8_2360_1_part2 receipt_0_8_2360_1_join1 rfl rfl rfl
private theorem receipt_0_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179818 2360 16 1 0 1 1) 0 564 = 1227441918843231792654734460 :=
  phaseBlock_append receipt_0_8_2360_1_join0 receipt_0_8_2360_1_join2 rfl rfl rfl

private theorem receipt_0_8_2360_1 : fastPhase (bank 0 8).shape 179818 2360 16 1 0 1 1 = 1227441918843231792654734460 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2360_1_join3

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2359_0 receipt_0_8_2359_1 receipt_0_8_2360_0 receipt_0_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 0 128 = 473072128141981128006662912 := by decide +kernel
private theorem receipt_1_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 128 128 = 330848373077588320295189248 := by decide +kernel
private theorem receipt_1_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 256 128 = 203873943919120236351359850 := by decide +kernel
private theorem receipt_1_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 384 128 = 91267165255744633758211614 := by decide +kernel
private theorem receipt_1_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 512 52 = 8032798478834866774387125 := by decide +kernel
private theorem receipt_1_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 0 256 = 803920501219569448301852160 :=
  phaseBlock_append receipt_1_8_2359_0_part0 receipt_1_8_2359_0_part1 rfl rfl rfl
private theorem receipt_1_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 384 180 = 99299963734579500532598739 :=
  phaseBlock_append receipt_1_8_2359_0_part3 receipt_1_8_2359_0_part4 rfl rfl rfl
private theorem receipt_1_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 256 308 = 303173907653699736883958589 :=
  phaseBlock_append receipt_1_8_2359_0_part2 receipt_1_8_2359_0_join1 rfl rfl rfl
private theorem receipt_1_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 0) 0 564 = 1107094408873269185185810749 :=
  phaseBlock_append receipt_1_8_2359_0_join0 receipt_1_8_2359_0_join2 rfl rfl rfl

private theorem receipt_1_8_2359_0 : fastPhase (bank 1 8).shape 179818 2359 16 1 0 2 0 = 1107094408873269185185810749 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2359_0_join3

private theorem receipt_1_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 0 128 = 471914048414699092027261632 := by decide +kernel
private theorem receipt_1_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 128 128 = 329808855032575781982642880 := by decide +kernel
private theorem receipt_1_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 256 128 = 202946285632585196129001903 := by decide +kernel
private theorem receipt_1_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 384 128 = 90444724844514073815098049 := by decide +kernel
private theorem receipt_1_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 512 52 = 7727226334138308343253856 := by decide +kernel
private theorem receipt_1_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 0 256 = 801722903447274874009904512 :=
  phaseBlock_append receipt_1_8_2359_1_part0 receipt_1_8_2359_1_part1 rfl rfl rfl
private theorem receipt_1_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 384 180 = 98171951178652382158351905 :=
  phaseBlock_append receipt_1_8_2359_1_part3 receipt_1_8_2359_1_part4 rfl rfl rfl
private theorem receipt_1_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 256 308 = 301118236811237578287353808 :=
  phaseBlock_append receipt_1_8_2359_1_part2 receipt_1_8_2359_1_join1 rfl rfl rfl
private theorem receipt_1_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2359 16 1 0 2 1) 0 564 = 1102841140258512452297258320 :=
  phaseBlock_append receipt_1_8_2359_1_join0 receipt_1_8_2359_1_join2 rfl rfl rfl

private theorem receipt_1_8_2359_1 : fastPhase (bank 1 8).shape 179818 2359 16 1 0 2 1 = 1102841140258512452297258320 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2359_1_join3

private theorem receipt_1_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 0 128 = 473076228213627952283337792 := by decide +kernel
private theorem receipt_1_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 128 128 = 330850846944198022767617088 := by decide +kernel
private theorem receipt_1_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 256 128 = 203875210000253249121977922 := by decide +kernel
private theorem receipt_1_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 384 128 = 91267610677515072302264457 := by decide +kernel
private theorem receipt_1_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 512 52 = 8032828931725192387773339 := by decide +kernel
private theorem receipt_1_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 0 256 = 803927075157825975050954880 :=
  phaseBlock_append receipt_1_8_2360_0_part0 receipt_1_8_2360_0_part1 rfl rfl rfl
private theorem receipt_1_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 384 180 = 99300439609240264690037796 :=
  phaseBlock_append receipt_1_8_2360_0_part3 receipt_1_8_2360_0_part4 rfl rfl rfl
private theorem receipt_1_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 256 308 = 303175649609493513812015718 :=
  phaseBlock_append receipt_1_8_2360_0_part2 receipt_1_8_2360_0_join1 rfl rfl rfl
private theorem receipt_1_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 0) 0 564 = 1107102724767319488862970598 :=
  phaseBlock_append receipt_1_8_2360_0_join0 receipt_1_8_2360_0_join2 rfl rfl rfl

private theorem receipt_1_8_2360_0 : fastPhase (bank 1 8).shape 179818 2360 16 1 0 2 0 = 1107102724767319488862970598 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2360_0_join3

private theorem receipt_1_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 0 128 = 471918140199035059135567680 := by decide +kernel
private theorem receipt_1_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 128 128 = 329811322297915480118359872 := by decide +kernel
private theorem receipt_1_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 256 128 = 202947546655885531321967343 := by decide +kernel
private theorem receipt_1_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 384 128 = 90445166624004931903976928 := by decide +kernel
private theorem receipt_1_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 512 52 = 7727255680317289388371200 := by decide +kernel
private theorem receipt_1_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 0 256 = 801729462496950539253927552 :=
  phaseBlock_append receipt_1_8_2360_1_part0 receipt_1_8_2360_1_part1 rfl rfl rfl
private theorem receipt_1_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 384 180 = 98172422304322221292348128 :=
  phaseBlock_append receipt_1_8_2360_1_part3 receipt_1_8_2360_1_part4 rfl rfl rfl
private theorem receipt_1_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 256 308 = 301119968960207752614315471 :=
  phaseBlock_append receipt_1_8_2360_1_part2 receipt_1_8_2360_1_join1 rfl rfl rfl
private theorem receipt_1_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179818 2360 16 1 0 2 1) 0 564 = 1102849431457158291868243023 :=
  phaseBlock_append receipt_1_8_2360_1_join0 receipt_1_8_2360_1_join2 rfl rfl rfl

private theorem receipt_1_8_2360_1 : fastPhase (bank 1 8).shape 179818 2360 16 1 0 2 1 = 1102849431457158291868243023 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2360_1_join3

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2359_0 receipt_1_8_2359_1 receipt_1_8_2360_0 receipt_1_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 0 128 = 252248805222111223602157952 := by decide +kernel
private theorem receipt_2_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 128 128 = 174723741147929117675641216 := by decide +kernel
private theorem receipt_2_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 256 128 = 106636865228084883583381488 := by decide +kernel
private theorem receipt_2_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 384 128 = 47292447523525475562375195 := by decide +kernel
private theorem receipt_2_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 512 52 = 4132325082752244032924430 := by decide +kernel
private theorem receipt_2_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 0 256 = 426972546370040341277799168 :=
  phaseBlock_append receipt_2_8_2359_0_part0 receipt_2_8_2359_0_part1 rfl rfl rfl
private theorem receipt_2_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 384 180 = 51424772606277719595299625 :=
  phaseBlock_append receipt_2_8_2359_0_part3 receipt_2_8_2359_0_part4 rfl rfl rfl
private theorem receipt_2_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 256 308 = 158061637834362603178681113 :=
  phaseBlock_append receipt_2_8_2359_0_part2 receipt_2_8_2359_0_join1 rfl rfl rfl
private theorem receipt_2_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 0) 0 564 = 585034184204402944456480281 :=
  phaseBlock_append receipt_2_8_2359_0_join0 receipt_2_8_2359_0_join2 rfl rfl rfl

private theorem receipt_2_8_2359_0 : fastPhase (bank 2 8).shape 179818 2359 16 1 0 7 0 = 585034184204402944456480281 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2359_0_join3

private theorem receipt_2_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 0 128 = 251612418778540322186416320 := by decide +kernel
private theorem receipt_2_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 128 128 = 174161655228466152920854720 := by decide +kernel
private theorem receipt_2_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 256 128 = 106143708852357176297520093 := by decide +kernel
private theorem receipt_2_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 384 128 = 46863026934371414324737593 := by decide +kernel
private theorem receipt_2_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 512 52 = 3974922680591845428905751 := by decide +kernel
private theorem receipt_2_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 0 256 = 425774074007006475107271040 :=
  phaseBlock_append receipt_2_8_2359_1_part0 receipt_2_8_2359_1_part1 rfl rfl rfl
private theorem receipt_2_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 384 180 = 50837949614963259753643344 :=
  phaseBlock_append receipt_2_8_2359_1_part3 receipt_2_8_2359_1_part4 rfl rfl rfl
private theorem receipt_2_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 256 308 = 156981658467320436051163437 :=
  phaseBlock_append receipt_2_8_2359_1_part2 receipt_2_8_2359_1_join1 rfl rfl rfl
private theorem receipt_2_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2359 16 1 0 7 1) 0 564 = 582755732474326911158434477 :=
  phaseBlock_append receipt_2_8_2359_1_join0 receipt_2_8_2359_1_join2 rfl rfl rfl

private theorem receipt_2_8_2359_1 : fastPhase (bank 2 8).shape 179818 2359 16 1 0 7 1 = 582755732474326911158434477 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2359_1_join3

private theorem receipt_2_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 0 128 = 252250991672185665821937792 := by decide +kernel
private theorem receipt_2_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 128 128 = 174725047791091567962615936 := by decide +kernel
private theorem receipt_2_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 256 128 = 106637527568990491290828240 := by decide +kernel
private theorem receipt_2_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 384 128 = 47292678381076318356173565 := by decide +kernel
private theorem receipt_2_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 512 52 = 4132340749264034679175212 := by decide +kernel
private theorem receipt_2_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 0 256 = 426976039463277233784553728 :=
  phaseBlock_append receipt_2_8_2360_0_part0 receipt_2_8_2360_0_part1 rfl rfl rfl
private theorem receipt_2_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 384 180 = 51425019130340353035348777 :=
  phaseBlock_append receipt_2_8_2360_0_part3 receipt_2_8_2360_0_part4 rfl rfl rfl
private theorem receipt_2_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 256 308 = 158062546699330844326177017 :=
  phaseBlock_append receipt_2_8_2360_0_part2 receipt_2_8_2360_0_join1 rfl rfl rfl
private theorem receipt_2_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 0) 0 564 = 585038586162608078110730745 :=
  phaseBlock_append receipt_2_8_2360_0_join0 receipt_2_8_2360_0_join2 rfl rfl rfl

private theorem receipt_2_8_2360_0 : fastPhase (bank 2 8).shape 179818 2360 16 1 0 7 0 = 585038586162608078110730745 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2360_0_join3

private theorem receipt_2_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 0 128 = 251614600645441716246883968 := by decide +kernel
private theorem receipt_2_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 128 128 = 174162958286855132575862400 := by decide +kernel
private theorem receipt_2_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 256 128 = 106144368497879443720642389 := by decide +kernel
private theorem receipt_2_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 384 128 = 46863255888148158343263846 := by decide +kernel
private theorem receipt_2_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 512 52 = 3974937776948946431367621 := by decide +kernel
private theorem receipt_2_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 0 256 = 425777558932296848822746368 :=
  phaseBlock_append receipt_2_8_2360_1_part0 receipt_2_8_2360_1_part1 rfl rfl rfl
private theorem receipt_2_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 384 180 = 50838193665097104774631467 :=
  phaseBlock_append receipt_2_8_2360_1_part3 receipt_2_8_2360_1_part4 rfl rfl rfl
private theorem receipt_2_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 256 308 = 156982562162976548495273856 :=
  phaseBlock_append receipt_2_8_2360_1_part2 receipt_2_8_2360_1_join1 rfl rfl rfl
private theorem receipt_2_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179818 2360 16 1 0 7 1) 0 564 = 582760121095273397318020224 :=
  phaseBlock_append receipt_2_8_2360_1_join0 receipt_2_8_2360_1_join2 rfl rfl rfl

private theorem receipt_2_8_2360_1 : fastPhase (bank 2 8).shape 179818 2360 16 1 0 7 1 = 582760121095273397318020224 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2360_1_join3

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2359_0 receipt_2_8_2359_1 receipt_2_8_2360_0 receipt_2_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 0 128 = 45880589008074990286834176 := by decide +kernel
private theorem receipt_3_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 128 128 = 32264358998452178889861632 := by decide +kernel
private theorem receipt_3_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 256 128 = 20129467981124712353450496 := by decide +kernel
private theorem receipt_3_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 384 128 = 9566711755115393475455488 := by decide +kernel
private theorem receipt_3_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 512 73 = 1359873009317688403996794 := by decide +kernel
private theorem receipt_3_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 0 256 = 78144948006527169176695808 :=
  phaseBlock_append receipt_3_8_2359_0_part0 receipt_3_8_2359_0_part1 rfl rfl rfl
private theorem receipt_3_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 384 201 = 10926584764433081879452282 :=
  phaseBlock_append receipt_3_8_2359_0_part3 receipt_3_8_2359_0_part4 rfl rfl rfl
private theorem receipt_3_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 256 329 = 31056052745557794232902778 :=
  phaseBlock_append receipt_3_8_2359_0_part2 receipt_3_8_2359_0_join1 rfl rfl rfl
private theorem receipt_3_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 0) 0 585 = 109201000752084963409598586 :=
  phaseBlock_append receipt_3_8_2359_0_join0 receipt_3_8_2359_0_join2 rfl rfl rfl

private theorem receipt_3_8_2359_0 : fastPhase (bank 3 8).shape 179818 2359 16 1 1 1 0 = 109201000752084963409598586 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2359_0_join3

private theorem receipt_3_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 0 128 = 45770078020298345583701952 := by decide +kernel
private theorem receipt_3_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 128 128 = 32164637881542881484435392 := by decide +kernel
private theorem receipt_3_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 256 128 = 20041312263347883969572800 := by decide +kernel
private theorem receipt_3_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 384 128 = 9490882652408121693269952 := by decide +kernel
private theorem receipt_3_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 512 73 = 1322433552832045977296028 := by decide +kernel
private theorem receipt_3_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 0 256 = 77934715901841227068137344 :=
  phaseBlock_append receipt_3_8_2359_1_part0 receipt_3_8_2359_1_part1 rfl rfl rfl
private theorem receipt_3_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 384 201 = 10813316205240167670565980 :=
  phaseBlock_append receipt_3_8_2359_1_part3 receipt_3_8_2359_1_part4 rfl rfl rfl
private theorem receipt_3_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 256 329 = 30854628468588051640138780 :=
  phaseBlock_append receipt_3_8_2359_1_part2 receipt_3_8_2359_1_join1 rfl rfl rfl
private theorem receipt_3_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2359 16 1 1 1 1) 0 585 = 108789344370429278708276124 :=
  phaseBlock_append receipt_3_8_2359_1_join0 receipt_3_8_2359_1_join2 rfl rfl rfl

private theorem receipt_3_8_2359_1 : fastPhase (bank 3 8).shape 179818 2359 16 1 1 1 1 = 108789344370429278708276124 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2359_1_join3

private theorem receipt_3_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 0 128 = 45880971307479554555586720 := by decide +kernel
private theorem receipt_3_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 128 128 = 32264565428760563488495776 := by decide +kernel
private theorem receipt_3_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 256 128 = 20129559550178457575229600 := by decide +kernel
private theorem receipt_3_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 384 128 = 9566738649721182909003936 := by decide +kernel
private theorem receipt_3_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 512 73 = 1359874989661503136847625 := by decide +kernel
private theorem receipt_3_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 0 256 = 78145536736240118044082496 :=
  phaseBlock_append receipt_3_8_2360_0_part0 receipt_3_8_2360_0_part1 rfl rfl rfl
private theorem receipt_3_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 384 201 = 10926613639382686045851561 :=
  phaseBlock_append receipt_3_8_2360_0_part3 receipt_3_8_2360_0_part4 rfl rfl rfl
private theorem receipt_3_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 256 329 = 31056173189561143621081161 :=
  phaseBlock_append receipt_3_8_2360_0_part2 receipt_3_8_2360_0_join1 rfl rfl rfl
private theorem receipt_3_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 0) 0 585 = 109201709925801261665163657 :=
  phaseBlock_append receipt_3_8_2360_0_join0 receipt_3_8_2360_0_join2 rfl rfl rfl

private theorem receipt_3_8_2360_0 : fastPhase (bank 3 8).shape 179818 2360 16 1 1 1 0 = 109201709925801261665163657 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2360_0_join3

private theorem receipt_3_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 0 128 = 45770459261866048688115360 := by decide +kernel
private theorem receipt_3_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 128 128 = 32164843592137408062496416 := by decide +kernel
private theorem receipt_3_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 256 128 = 20041403390798886315224736 := by decide +kernel
private theorem receipt_3_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 384 128 = 9490909324551232401620640 := by decide +kernel
private theorem receipt_3_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 512 73 = 1322435482160615110634850 := by decide +kernel
private theorem receipt_3_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 0 256 = 77935302854003456750611776 :=
  phaseBlock_append receipt_3_8_2360_1_part0 receipt_3_8_2360_1_part1 rfl rfl rfl
private theorem receipt_3_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 384 201 = 10813344806711847512255490 :=
  phaseBlock_append receipt_3_8_2360_1_part3 receipt_3_8_2360_1_part4 rfl rfl rfl
private theorem receipt_3_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 256 329 = 30854748197510733827480226 :=
  phaseBlock_append receipt_3_8_2360_1_part2 receipt_3_8_2360_1_join1 rfl rfl rfl
private theorem receipt_3_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179818 2360 16 1 1 1 1) 0 585 = 108790051051514190578092002 :=
  phaseBlock_append receipt_3_8_2360_1_join0 receipt_3_8_2360_1_join2 rfl rfl rfl

private theorem receipt_3_8_2360_1 : fastPhase (bank 3 8).shape 179818 2360 16 1 1 1 1 = 108790051051514190578092002 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2360_1_join3

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2359_0 receipt_3_8_2359_1 receipt_3_8_2360_0 receipt_3_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 0 128 = 135888818933834375379608720 := by decide +kernel
private theorem receipt_0_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 128 128 = 82968921164467395215175926 := by decide +kernel
private theorem receipt_0_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 256 128 = 37226980351255568178627248 := by decide +kernel
private theorem receipt_0_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 384 56 = 3622349967343907182180368 := by decide +kernel
private theorem receipt_0_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 0 256 = 218857740098301770594784646 :=
  phaseBlock_append receipt_0_9_2359_0_part0 receipt_0_9_2359_0_part1 rfl rfl rfl
private theorem receipt_0_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 256 184 = 40849330318599475360807616 :=
  phaseBlock_append receipt_0_9_2359_0_part2 receipt_0_9_2359_0_part3 rfl rfl rfl
private theorem receipt_0_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 0) 0 440 = 259707070416901245955592262 :=
  phaseBlock_append receipt_0_9_2359_0_join0 receipt_0_9_2359_0_join1 rfl rfl rfl

private theorem receipt_0_9_2359_0 : fastPhase (bank 0 9).shape 179818 2359 10 1 0 1 0 = 259707070416901245955592262 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2359_0_join2

private theorem receipt_0_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 0 128 = 135451559110264090631330102 := by decide +kernel
private theorem receipt_0_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 128 128 = 82587813663086087687053680 := by decide +kernel
private theorem receipt_0_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 256 128 = 36898076208333671486061486 := by decide +kernel
private theorem receipt_0_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 384 56 = 3493866308748228438644084 := by decide +kernel
private theorem receipt_0_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 0 256 = 218039372773350178318383782 :=
  phaseBlock_append receipt_0_9_2359_1_part0 receipt_0_9_2359_1_part1 rfl rfl rfl
private theorem receipt_0_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 256 184 = 40391942517081899924705570 :=
  phaseBlock_append receipt_0_9_2359_1_part2 receipt_0_9_2359_1_part3 rfl rfl rfl
private theorem receipt_0_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2359 10 1 0 1 1) 0 440 = 258431315290432078243089352 :=
  phaseBlock_append receipt_0_9_2359_1_join0 receipt_0_9_2359_1_join1 rfl rfl rfl

private theorem receipt_0_9_2359_1 : fastPhase (bank 0 9).shape 179818 2359 10 1 0 1 1 = 258431315290432078243089352 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2359_1_join2

private theorem receipt_0_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 0 128 = 135889991580852729540995198 := by decide +kernel
private theorem receipt_0_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 128 128 = 82969506290070519966201110 := by decide +kernel
private theorem receipt_0_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 256 128 = 37227180887027749862499925 := by decide +kernel
private theorem receipt_0_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 384 56 = 3622364455645587572452176 := by decide +kernel
private theorem receipt_0_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 0 256 = 218859497870923249507196308 :=
  phaseBlock_append receipt_0_9_2360_0_part0 receipt_0_9_2360_0_part1 rfl rfl rfl
private theorem receipt_0_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 256 184 = 40849545342673337434952101 :=
  phaseBlock_append receipt_0_9_2360_0_part2 receipt_0_9_2360_0_part3 rfl rfl rfl
private theorem receipt_0_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 0) 0 440 = 259709043213596586942148409 :=
  phaseBlock_append receipt_0_9_2360_0_join0 receipt_0_9_2360_0_join1 rfl rfl rfl

private theorem receipt_0_9_2360_0 : fastPhase (bank 0 9).shape 179818 2360 10 1 0 1 0 = 259709043213596586942148409 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2360_0_join2

private theorem receipt_0_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 0 128 = 135452728636306989341986356 := by decide +kernel
private theorem receipt_0_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 128 128 = 82588396483315436656235799 := by decide +kernel
private theorem receipt_0_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 256 128 = 36898275166535450613030948 := by decide +kernel
private theorem receipt_0_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 384 56 = 3493880313116888508707742 := by decide +kernel
private theorem receipt_0_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 0 256 = 218041125119622425998222155 :=
  phaseBlock_append receipt_0_9_2360_1_part0 receipt_0_9_2360_1_part1 rfl rfl rfl
private theorem receipt_0_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 256 184 = 40392155479652339121738690 :=
  phaseBlock_append receipt_0_9_2360_1_part2 receipt_0_9_2360_1_part3 rfl rfl rfl
private theorem receipt_0_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179818 2360 10 1 0 1 1) 0 440 = 258433280599274765119960845 :=
  phaseBlock_append receipt_0_9_2360_1_join0 receipt_0_9_2360_1_join1 rfl rfl rfl

private theorem receipt_0_9_2360_1 : fastPhase (bank 0 9).shape 179818 2360 10 1 0 1 1 = 258433280599274765119960845 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2360_1_join2

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2359_0 receipt_0_9_2359_1 receipt_0_9_2360_0 receipt_0_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 0 128 = 122418681222027075490320887 := by decide +kernel
private theorem receipt_1_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 128 128 = 74613718261226252948101185 := by decide +kernel
private theorem receipt_1_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 256 128 = 33421208087350652022092766 := by decide +kernel
private theorem receipt_1_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 384 56 = 3247731256664665337291174 := by decide +kernel
private theorem receipt_1_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 0 256 = 197032399483253328438422072 :=
  phaseBlock_append receipt_1_9_2359_0_part0 receipt_1_9_2359_0_part1 rfl rfl rfl
private theorem receipt_1_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 256 184 = 36668939344015317359383940 :=
  phaseBlock_append receipt_1_9_2359_0_part2 receipt_1_9_2359_0_part3 rfl rfl rfl
private theorem receipt_1_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 0) 0 440 = 233701338827268645797806012 :=
  phaseBlock_append receipt_1_9_2359_0_join0 receipt_1_9_2359_0_join1 rfl rfl rfl

private theorem receipt_1_9_2359_0 : fastPhase (bank 1 9).shape 179818 2359 10 1 0 2 0 = 233701338827268645797806012 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2359_0_join2

private theorem receipt_1_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 0 128 = 122023089136617515283369738 := by decide +kernel
private theorem receipt_1_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 128 128 = 74269979482447551895541892 := by decide +kernel
private theorem receipt_1_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 256 128 = 33125509782627091771359333 := by decide +kernel
private theorem receipt_1_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 384 56 = 3132505869197194918512463 := by decide +kernel
private theorem receipt_1_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 0 256 = 196293068619065067178911630 :=
  phaseBlock_append receipt_1_9_2359_1_part0 receipt_1_9_2359_1_part1 rfl rfl rfl
private theorem receipt_1_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 256 184 = 36258015651824286689871796 :=
  phaseBlock_append receipt_1_9_2359_1_part2 receipt_1_9_2359_1_part3 rfl rfl rfl
private theorem receipt_1_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2359 10 1 0 2 1) 0 440 = 232551084270889353868783426 :=
  phaseBlock_append receipt_1_9_2359_1_join0 receipt_1_9_2359_1_join1 rfl rfl rfl

private theorem receipt_1_9_2359_1 : fastPhase (bank 1 9).shape 179818 2359 10 1 0 2 1 = 232551084270889353868783426 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2359_1_join2

private theorem receipt_1_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 0 128 = 122419737656342541397331338 := by decide +kernel
private theorem receipt_1_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 128 128 = 74614244481117084399425078 := by decide +kernel
private theorem receipt_1_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 256 128 = 33421388130190478109083711 := by decide +kernel
private theorem receipt_1_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 384 56 = 3247744246726659369071273 := by decide +kernel
private theorem receipt_1_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 0 256 = 197033982137459625796756416 :=
  phaseBlock_append receipt_1_9_2360_0_part0 receipt_1_9_2360_0_part1 rfl rfl rfl
private theorem receipt_1_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 256 184 = 36669132376917137478154984 :=
  phaseBlock_append receipt_1_9_2360_0_part2 receipt_1_9_2360_0_part3 rfl rfl rfl
private theorem receipt_1_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 0) 0 440 = 233703114514376763274911400 :=
  phaseBlock_append receipt_1_9_2360_0_join0 receipt_1_9_2360_0_join1 rfl rfl rfl

private theorem receipt_1_9_2360_0 : fastPhase (bank 1 9).shape 179818 2360 10 1 0 2 0 = 233703114514376763274911400 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2360_0_join2

private theorem receipt_1_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 0 128 = 122024142744771976905029646 := by decide +kernel
private theorem receipt_1_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 128 128 = 74270503621913257875844281 := by decide +kernel
private theorem receipt_1_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 256 128 = 33125688406832419950141277 := by decide +kernel
private theorem receipt_1_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 384 56 = 3132518425247872582748549 := by decide +kernel
private theorem receipt_1_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 0 256 = 196294646366685234780873927 :=
  phaseBlock_append receipt_1_9_2360_1_part0 receipt_1_9_2360_1_part1 rfl rfl rfl
private theorem receipt_1_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 256 184 = 36258206832080292532889826 :=
  phaseBlock_append receipt_1_9_2360_1_part2 receipt_1_9_2360_1_part3 rfl rfl rfl
private theorem receipt_1_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179818 2360 10 1 0 2 1) 0 440 = 232552853198765527313763753 :=
  phaseBlock_append receipt_1_9_2360_1_join0 receipt_1_9_2360_1_join1 rfl rfl rfl

private theorem receipt_1_9_2360_1 : fastPhase (bank 1 9).shape 179818 2360 10 1 0 2 1 = 232552853198765527313763753 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2360_1_join2

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2359_0 receipt_1_9_2359_1 receipt_1_9_2360_0 receipt_1_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 0 128 = 65936520966250923607300611 := by decide +kernel
private theorem receipt_2_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 128 128 = 39684460283476939939836347 := by decide +kernel
private theorem receipt_2_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 256 128 = 17557655747052168537068104 := by decide +kernel
private theorem receipt_2_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 384 56 = 1689781511831202381266808 := by decide +kernel
private theorem receipt_2_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 0 256 = 105620981249727863547136958 :=
  phaseBlock_append receipt_2_9_2359_0_part0 receipt_2_9_2359_0_part1 rfl rfl rfl
private theorem receipt_2_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 256 184 = 19247437258883370918334912 :=
  phaseBlock_append receipt_2_9_2359_0_part2 receipt_2_9_2359_0_part3 rfl rfl rfl
private theorem receipt_2_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 0) 0 440 = 124868418508611234465471870 :=
  phaseBlock_append receipt_2_9_2359_0_join0 receipt_2_9_2359_0_join1 rfl rfl rfl

private theorem receipt_2_9_2359_0 : fastPhase (bank 2 9).shape 179818 2359 10 1 0 7 0 = 124868418508611234465471870 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2359_0_join2

private theorem receipt_2_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 0 128 = 65716973382406922812256768 := by decide +kernel
private theorem receipt_2_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 128 128 = 39497756967435677622579186 := by decide +kernel
private theorem receipt_2_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 256 128 = 17400712323033475021462921 := by decide +kernel
private theorem receipt_2_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 384 56 = 1629718493132144433853677 := by decide +kernel
private theorem receipt_2_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 0 256 = 105214730349842600434835954 :=
  phaseBlock_append receipt_2_9_2359_1_part0 receipt_2_9_2359_1_part1 rfl rfl rfl
private theorem receipt_2_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 256 184 = 19030430816165619455316598 :=
  phaseBlock_append receipt_2_9_2359_1_part2 receipt_2_9_2359_1_part3 rfl rfl rfl
private theorem receipt_2_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2359 10 1 0 7 1) 0 440 = 124245161166008219890152552 :=
  phaseBlock_append receipt_2_9_2359_1_join0 receipt_2_9_2359_1_join1 rfl rfl rfl

private theorem receipt_2_9_2359_1 : fastPhase (bank 2 9).shape 179818 2359 10 1 0 7 1 = 124245161166008219890152552 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2359_1_join2

private theorem receipt_2_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 0 128 = 65937090082934898153506880 := by decide +kernel
private theorem receipt_2_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 128 128 = 39684740231110518562562604 := by decide +kernel
private theorem receipt_2_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 256 128 = 17557750362758816234299128 := by decide +kernel
private theorem receipt_2_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 384 56 = 1689788270970909838473231 := by decide +kernel
private theorem receipt_2_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 0 256 = 105621830314045416716069484 :=
  phaseBlock_append receipt_2_9_2360_0_part0 receipt_2_9_2360_0_part1 rfl rfl rfl
private theorem receipt_2_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 256 184 = 19247538633729726072772359 :=
  phaseBlock_append receipt_2_9_2360_0_part2 receipt_2_9_2360_0_part3 rfl rfl rfl
private theorem receipt_2_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 0) 0 440 = 124869368947775142788841843 :=
  phaseBlock_append receipt_2_9_2360_0_join0 receipt_2_9_2360_0_join1 rfl rfl rfl

private theorem receipt_2_9_2360_0 : fastPhase (bank 2 9).shape 179818 2360 10 1 0 7 0 = 124869368947775142788841843 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2360_0_join2

private theorem receipt_2_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 0 128 = 65717540920636085252339910 := by decide +kernel
private theorem receipt_2_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 128 128 = 39498035780858011964161386 := by decide +kernel
private theorem receipt_2_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 256 128 = 17400806184515804377096227 := by decide +kernel
private theorem receipt_2_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 384 56 = 1629725025977713338069861 := by decide +kernel
private theorem receipt_2_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 0 256 = 105215576701494097216501296 :=
  phaseBlock_append receipt_2_9_2360_1_part0 receipt_2_9_2360_1_part1 rfl rfl rfl
private theorem receipt_2_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 256 184 = 19030531210493517715166088 :=
  phaseBlock_append receipt_2_9_2360_1_part2 receipt_2_9_2360_1_part3 rfl rfl rfl
private theorem receipt_2_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179818 2360 10 1 0 7 1) 0 440 = 124246107911987614931667384 :=
  phaseBlock_append receipt_2_9_2360_1_join0 receipt_2_9_2360_1_join1 rfl rfl rfl

private theorem receipt_2_9_2360_1 : fastPhase (bank 2 9).shape 179818 2360 10 1 0 7 1 = 124246107911987614931667384 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2360_1_join2

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2359_0 receipt_2_9_2359_1 receipt_2_9_2360_0 receipt_2_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 0 128 = 12532010027531974852577280 := by decide +kernel
private theorem receipt_3_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 128 128 = 7709428232332825285584896 := by decide +kernel
private theorem receipt_3_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 256 128 = 3597778473725725674391552 := by decide +kernel
private theorem receipt_3_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 384 73 = 501876798510914166387288 := by decide +kernel
private theorem receipt_3_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 0 256 = 20241438259864800138162176 :=
  phaseBlock_append receipt_3_9_2359_0_part0 receipt_3_9_2359_0_part1 rfl rfl rfl
private theorem receipt_3_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 256 201 = 4099655272236639840778840 :=
  phaseBlock_append receipt_3_9_2359_0_part2 receipt_3_9_2359_0_part3 rfl rfl rfl
private theorem receipt_3_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 0) 0 457 = 24341093532101439978941016 :=
  phaseBlock_append receipt_3_9_2359_0_join0 receipt_3_9_2359_0_join1 rfl rfl rfl

private theorem receipt_3_9_2359_0 : fastPhase (bank 3 9).shape 179818 2359 10 1 1 1 0 = 24341093532101439978941016 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2359_0_join2

private theorem receipt_3_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 0 128 = 12492196209410559644794944 := by decide +kernel
private theorem receipt_3_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 128 128 = 7674765679009418031398976 := by decide +kernel
private theorem receipt_3_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 256 128 = 3568726755901711327952960 := by decide +kernel
private theorem receipt_3_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 384 73 = 487993218803028239114340 := by decide +kernel
private theorem receipt_3_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 0 256 = 20166961888419977676193920 :=
  phaseBlock_append receipt_3_9_2359_1_part0 receipt_3_9_2359_1_part1 rfl rfl rfl
private theorem receipt_3_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 256 201 = 4056719974704739567067300 :=
  phaseBlock_append receipt_3_9_2359_1_part2 receipt_3_9_2359_1_part3 rfl rfl rfl
private theorem receipt_3_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2359 10 1 1 1 1) 0 457 = 24223681863124717243261220 :=
  phaseBlock_append receipt_3_9_2359_1_join0 receipt_3_9_2359_1_join1 rfl rfl rfl

private theorem receipt_3_9_2359_1 : fastPhase (bank 3 9).shape 179818 2359 10 1 1 1 1 = 24223681863124717243261220 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2359_1_join2

private theorem receipt_3_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 0 128 = 12532111900929779958838080 := by decide +kernel
private theorem receipt_3_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 128 128 = 7709472126429391146398528 := by decide +kernel
private theorem receipt_3_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 256 128 = 3597790812370381186134848 := by decide +kernel
private theorem receipt_3_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 384 73 = 501877640054902394528322 := by decide +kernel
private theorem receipt_3_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 0 256 = 20241584027359171105236608 :=
  phaseBlock_append receipt_3_9_2360_0_part0 receipt_3_9_2360_0_part1 rfl rfl rfl
private theorem receipt_3_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 256 201 = 4099668452425283580663170 :=
  phaseBlock_append receipt_3_9_2360_0_part2 receipt_3_9_2360_0_part3 rfl rfl rfl
private theorem receipt_3_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 0) 0 457 = 24341252479784454685899778 :=
  phaseBlock_append receipt_3_9_2360_0_join0 receipt_3_9_2360_0_join1 rfl rfl rfl

private theorem receipt_3_9_2360_0 : fastPhase (bank 3 9).shape 179818 2360 10 1 1 1 0 = 24341252479784454685899778 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2360_0_join2

private theorem receipt_3_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 0 128 = 12492297713013484932987328 := by decide +kernel
private theorem receipt_3_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 128 128 = 7674809353761134848735680 := by decide +kernel
private theorem receipt_3_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 256 128 = 3568738989977324716063168 := by decide +kernel
private theorem receipt_3_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 384 73 = 487994038693512181886652 := by decide +kernel
private theorem receipt_3_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 0 256 = 20167107066774619781723008 :=
  phaseBlock_append receipt_3_9_2360_1_part0 receipt_3_9_2360_1_part1 rfl rfl rfl
private theorem receipt_3_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 256 201 = 4056733028670836897949820 :=
  phaseBlock_append receipt_3_9_2360_1_part2 receipt_3_9_2360_1_part3 rfl rfl rfl
private theorem receipt_3_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179818 2360 10 1 1 1 1) 0 457 = 24223840095445456679672828 :=
  phaseBlock_append receipt_3_9_2360_1_join0 receipt_3_9_2360_1_join1 rfl rfl rfl

private theorem receipt_3_9_2360_1 : fastPhase (bank 3 9).shape 179818 2360 10 1 1 1 1 = 24223840095445456679672828 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2360_1_join2

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2359_0 receipt_3_9_2359_1 receipt_3_9_2360_0 receipt_3_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 0 128 = 1515173245431121479961524288 := by decide +kernel
private theorem receipt_0_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 128 128 = 1175556049176800476343212096 := by decide +kernel
private theorem receipt_0_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 256 128 = 863663639942910089720723520 := by decide +kernel
private theorem receipt_0_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 384 128 = 578312722854639857040404738 := by decide +kernel
private theorem receipt_0_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 512 128 = 318325360448124137749080624 := by decide +kernel
private theorem receipt_0_10_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 640 111 = 84308094494642221333589732 := by decide +kernel
private theorem receipt_0_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 128 256 = 2039219689119710566063935616 :=
  phaseBlock_append receipt_0_10_2359_0_part1 receipt_0_10_2359_0_part2 rfl rfl rfl
private theorem receipt_0_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 0 384 = 3554392934550832046025459904 :=
  phaseBlock_append receipt_0_10_2359_0_part0 receipt_0_10_2359_0_join0 rfl rfl rfl
private theorem receipt_0_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 512 239 = 402633454942766359082670356 :=
  phaseBlock_append receipt_0_10_2359_0_part4 receipt_0_10_2359_0_part5 rfl rfl rfl
private theorem receipt_0_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 384 367 = 980946177797406216123075094 :=
  phaseBlock_append receipt_0_10_2359_0_part3 receipt_0_10_2359_0_join2 rfl rfl rfl
private theorem receipt_0_10_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 0) 0 751 = 4535339112348238262148534998 :=
  phaseBlock_append receipt_0_10_2359_0_join1 receipt_0_10_2359_0_join3 rfl rfl rfl

private theorem receipt_0_10_2359_0 : fastPhase (bank 0 10).shape 179818 2359 20 1 0 1 0 = 4535339112348238262148534998 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2359_0_join4

private theorem receipt_0_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 0 128 = 1512445528477536288465642880 := by decide +kernel
private theorem receipt_0_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 128 128 = 1173042161529669766375941504 := by decide +kernel
private theorem receipt_0_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 256 128 = 861354617199499189799740800 := by decide +kernel
private theorem receipt_0_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 384 128 = 576199637036888427129155354 := by decide +kernel
private theorem receipt_0_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 512 128 = 316399316040096845825844714 := by decide +kernel
private theorem receipt_0_10_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 640 111 = 82782421496345158193972020 := by decide +kernel
private theorem receipt_0_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 128 256 = 2034396778729168956175682304 :=
  phaseBlock_append receipt_0_10_2359_1_part1 receipt_0_10_2359_1_part2 rfl rfl rfl
private theorem receipt_0_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 0 384 = 3546842307206705244641325184 :=
  phaseBlock_append receipt_0_10_2359_1_part0 receipt_0_10_2359_1_join0 rfl rfl rfl
private theorem receipt_0_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 512 239 = 399181737536442004019816734 :=
  phaseBlock_append receipt_0_10_2359_1_part4 receipt_0_10_2359_1_part5 rfl rfl rfl
private theorem receipt_0_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 384 367 = 975381374573330431148972088 :=
  phaseBlock_append receipt_0_10_2359_1_part3 receipt_0_10_2359_1_join2 rfl rfl rfl
private theorem receipt_0_10_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2359 20 1 0 1 1) 0 751 = 4522223681780035675790297272 :=
  phaseBlock_append receipt_0_10_2359_1_join1 receipt_0_10_2359_1_join3 rfl rfl rfl

private theorem receipt_0_10_2359_1 : fastPhase (bank 0 10).shape 179818 2359 20 1 0 1 1 = 4522223681780035675790297272 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2359_1_join4

private theorem receipt_0_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 0 128 = 1515186660022553838289216896 := by decide +kernel
private theorem receipt_0_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 128 128 = 1175565378554412412867052928 := by decide +kernel
private theorem receipt_0_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 256 128 = 863669658425971262494811520 := by decide +kernel
private theorem receipt_0_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 384 128 = 578316163324497262446154395 := by decide +kernel
private theorem receipt_0_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 512 128 = 318326911641125217519850881 := by decide +kernel
private theorem receipt_0_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 640 111 = 84308421556305431860946395 := by decide +kernel
private theorem receipt_0_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 128 256 = 2039235036980383675361864448 :=
  phaseBlock_append receipt_0_10_2360_0_part1 receipt_0_10_2360_0_part2 rfl rfl rfl
private theorem receipt_0_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 0 384 = 3554421697002937513651081344 :=
  phaseBlock_append receipt_0_10_2360_0_part0 receipt_0_10_2360_0_join0 rfl rfl rfl
private theorem receipt_0_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 512 239 = 402635333197430649380797276 :=
  phaseBlock_append receipt_0_10_2360_0_part4 receipt_0_10_2360_0_part5 rfl rfl rfl
private theorem receipt_0_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 384 367 = 980951496521927911826951671 :=
  phaseBlock_append receipt_0_10_2360_0_part3 receipt_0_10_2360_0_join2 rfl rfl rfl
private theorem receipt_0_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 0) 0 751 = 4535373193524865425478033015 :=
  phaseBlock_append receipt_0_10_2360_0_join1 receipt_0_10_2360_0_join3 rfl rfl rfl

private theorem receipt_0_10_2360_0 : fastPhase (bank 0 10).shape 179818 2360 20 1 0 1 0 = 4535373193524865425478033015 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2360_0_join4

private theorem receipt_0_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 0 128 = 1512458923329108963923272320 := by decide +kernel
private theorem receipt_0_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 128 128 = 1173051474251614146195980928 := by decide +kernel
private theorem receipt_0_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 256 128 = 861360621918152042002768512 := by decide +kernel
private theorem receipt_0_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 384 128 = 576203066444004083094259123 := by decide +kernel
private theorem receipt_0_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 512 128 = 316400858708538300735290657 := by decide +kernel
private theorem receipt_0_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 640 111 = 82782743073762621721479234 := by decide +kernel
private theorem receipt_0_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 128 256 = 2034412096169766188198749440 :=
  phaseBlock_append receipt_0_10_2360_1_part1 receipt_0_10_2360_1_part2 rfl rfl rfl
private theorem receipt_0_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 0 384 = 3546871019498875152122021760 :=
  phaseBlock_append receipt_0_10_2360_1_part0 receipt_0_10_2360_1_join0 rfl rfl rfl
private theorem receipt_0_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 512 239 = 399183601782300922456769891 :=
  phaseBlock_append receipt_0_10_2360_1_part4 receipt_0_10_2360_1_part5 rfl rfl rfl
private theorem receipt_0_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 384 367 = 975386668226305005551029014 :=
  phaseBlock_append receipt_0_10_2360_1_part3 receipt_0_10_2360_1_join2 rfl rfl rfl
private theorem receipt_0_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179818 2360 20 1 0 1 1) 0 751 = 4522257687725180157673050774 :=
  phaseBlock_append receipt_0_10_2360_1_join1 receipt_0_10_2360_1_join3 rfl rfl rfl

private theorem receipt_0_10_2360_1 : fastPhase (bank 0 10).shape 179818 2360 20 1 0 1 1 = 4522257687725180157673050774 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2360_1_join4

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2359_0 receipt_0_10_2359_1 receipt_0_10_2360_0 receipt_0_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 0 128 = 1351281530868473181838317504 := by decide +kernel
private theorem receipt_1_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 128 128 = 1047151132107290405247285184 := by decide +kernel
private theorem receipt_1_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 256 128 = 768410646083053904353810368 := by decide +kernel
private theorem receipt_1_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 384 128 = 513920348163458358284942039 := by decide +kernel
private theorem receipt_1_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 512 128 = 282550237396785570406020423 := by decide +kernel
private theorem receipt_1_10_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 640 111 = 74756295938531350836551564 := by decide +kernel
private theorem receipt_1_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 128 256 = 1815561778190344309601095552 :=
  phaseBlock_append receipt_1_10_2359_0_part1 receipt_1_10_2359_0_part2 rfl rfl rfl
private theorem receipt_1_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 0 384 = 3166843309058817491439413056 :=
  phaseBlock_append receipt_1_10_2359_0_part0 receipt_1_10_2359_0_join0 rfl rfl rfl
private theorem receipt_1_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 512 239 = 357306533335316921242571987 :=
  phaseBlock_append receipt_1_10_2359_0_part4 receipt_1_10_2359_0_part5 rfl rfl rfl
private theorem receipt_1_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 384 367 = 871226881498775279527514026 :=
  phaseBlock_append receipt_1_10_2359_0_part3 receipt_1_10_2359_0_join2 rfl rfl rfl
private theorem receipt_1_10_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 0) 0 751 = 4038070190557592770966927082 :=
  phaseBlock_append receipt_1_10_2359_0_join1 receipt_1_10_2359_0_join3 rfl rfl rfl

private theorem receipt_1_10_2359_0 : fastPhase (bank 1 10).shape 179818 2359 20 1 0 2 0 = 4038070190557592770966927082 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2359_0_join4

private theorem receipt_1_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 0 128 = 1348836307544482124209161856 := by decide +kernel
private theorem receipt_1_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 128 128 = 1044902106159436310766077568 := by decide +kernel
private theorem receipt_1_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 256 128 = 766349159030718816952780416 := by decide +kernel
private theorem receipt_1_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 384 128 = 512037811803166264304809331 := by decide +kernel
private theorem receipt_1_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 512 128 = 280838130131726896226152686 := by decide +kernel
private theorem receipt_1_10_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 640 111 = 73403012166411073071132742 := by decide +kernel
private theorem receipt_1_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 128 256 = 1811251265190155127718857984 :=
  phaseBlock_append receipt_1_10_2359_1_part1 receipt_1_10_2359_1_part2 rfl rfl rfl
private theorem receipt_1_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 0 384 = 3160087572734637251928019840 :=
  phaseBlock_append receipt_1_10_2359_1_part0 receipt_1_10_2359_1_join0 rfl rfl rfl
private theorem receipt_1_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 512 239 = 354241142298137969297285428 :=
  phaseBlock_append receipt_1_10_2359_1_part4 receipt_1_10_2359_1_part5 rfl rfl rfl
private theorem receipt_1_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 384 367 = 866278954101304233602094759 :=
  phaseBlock_append receipt_1_10_2359_1_part3 receipt_1_10_2359_1_join2 rfl rfl rfl
private theorem receipt_1_10_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2359 20 1 0 2 1) 0 751 = 4026366526835941485530114599 :=
  phaseBlock_append receipt_1_10_2359_1_join1 receipt_1_10_2359_1_join3 rfl rfl rfl

private theorem receipt_1_10_2359_1 : fastPhase (bank 1 10).shape 179818 2359 20 1 0 2 1 = 4026366526835941485530114599 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2359_1_join4

private theorem receipt_1_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 0 128 = 1351293494564164768644482208 := by decide +kernel
private theorem receipt_1_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 128 128 = 1047159442543835610065245344 := by decide +kernel
private theorem receipt_1_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 256 128 = 768416000867083631527126176 := by decide +kernel
private theorem receipt_1_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 384 128 = 513923405607188167254735459 := by decide +kernel
private theorem receipt_1_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 512 128 = 282551614289118670026337155 := by decide +kernel
private theorem receipt_1_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 640 111 = 74756585949820922680134934 := by decide +kernel
private theorem receipt_1_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 128 256 = 1815575443410919241592371520 :=
  phaseBlock_append receipt_1_10_2360_0_part1 receipt_1_10_2360_0_part2 rfl rfl rfl
private theorem receipt_1_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 0 384 = 3166868937975084010236853728 :=
  phaseBlock_append receipt_1_10_2360_0_part0 receipt_1_10_2360_0_join0 rfl rfl rfl
private theorem receipt_1_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 512 239 = 357308200238939592706472089 :=
  phaseBlock_append receipt_1_10_2360_0_part4 receipt_1_10_2360_0_part5 rfl rfl rfl
private theorem receipt_1_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 384 367 = 871231605846127759961207548 :=
  phaseBlock_append receipt_1_10_2360_0_part3 receipt_1_10_2360_0_join2 rfl rfl rfl
private theorem receipt_1_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 0) 0 751 = 4038100543821211770198061276 :=
  phaseBlock_append receipt_1_10_2360_0_join1 receipt_1_10_2360_0_join3 rfl rfl rfl

private theorem receipt_1_10_2360_0 : fastPhase (bank 1 10).shape 179818 2360 20 1 0 2 0 = 4038100543821211770198061276 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2360_0_join4

private theorem receipt_1_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 0 128 = 1348848253524118292770966176 := by decide +kernel
private theorem receipt_1_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 128 128 = 1044910401682168930657278624 := by decide +kernel
private theorem receipt_1_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 256 128 = 766354501518542349757803168 := by decide +kernel
private theorem receipt_1_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 384 128 = 512040859387576244182267306 := by decide +kernel
private theorem receipt_1_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 512 128 = 280839499445040908277719138 := by decide +kernel
private theorem receipt_1_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 640 111 = 73403297312836994379082203 := by decide +kernel
private theorem receipt_1_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 128 256 = 1811264903200711280415081792 :=
  phaseBlock_append receipt_1_10_2360_1_part1 receipt_1_10_2360_1_part2 rfl rfl rfl
private theorem receipt_1_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 0 384 = 3160113156724829573186047968 :=
  phaseBlock_append receipt_1_10_2360_1_part0 receipt_1_10_2360_1_join0 rfl rfl rfl
private theorem receipt_1_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 512 239 = 354242796757877902656801341 :=
  phaseBlock_append receipt_1_10_2360_1_part4 receipt_1_10_2360_1_part5 rfl rfl rfl
private theorem receipt_1_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 384 367 = 866283656145454146839068647 :=
  phaseBlock_append receipt_1_10_2360_1_part3 receipt_1_10_2360_1_join2 rfl rfl rfl
private theorem receipt_1_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179818 2360 20 1 0 2 1) 0 751 = 4026396812870283720025116615 :=
  phaseBlock_append receipt_1_10_2360_1_join1 receipt_1_10_2360_1_join3 rfl rfl rfl

private theorem receipt_1_10_2360_1 : fastPhase (bank 1 10).shape 179818 2360 20 1 0 2 1 = 4026396812870283720025116615 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2360_1_join4

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2359_0 receipt_1_10_2359_1 receipt_1_10_2360_0 receipt_1_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 0 128 = 677075863410120128380076416 := by decide +kernel
private theorem receipt_2_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 128 128 = 520024129706878719768134016 := by decide +kernel
private theorem receipt_2_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 256 128 = 378191866741514882524840320 := by decide +kernel
private theorem receipt_2_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 384 128 = 250675391278133461917712355 := by decide +kernel
private theorem receipt_2_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 512 128 = 136597379413511140416765657 := by decide +kernel
private theorem receipt_2_10_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 640 111 = 35857970272148997535499752 := by decide +kernel
private theorem receipt_2_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 128 256 = 898215996448393602292974336 :=
  phaseBlock_append receipt_2_10_2359_0_part1 receipt_2_10_2359_0_part2 rfl rfl rfl
private theorem receipt_2_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 0 384 = 1575291859858513730673050752 :=
  phaseBlock_append receipt_2_10_2359_0_part0 receipt_2_10_2359_0_join0 rfl rfl rfl
private theorem receipt_2_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 512 239 = 172455349685660137952265409 :=
  phaseBlock_append receipt_2_10_2359_0_part4 receipt_2_10_2359_0_part5 rfl rfl rfl
private theorem receipt_2_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 384 367 = 423130740963793599869977764 :=
  phaseBlock_append receipt_2_10_2359_0_part3 receipt_2_10_2359_0_join2 rfl rfl rfl
private theorem receipt_2_10_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 0) 0 751 = 1998422600822307330543028516 :=
  phaseBlock_append receipt_2_10_2359_0_join1 receipt_2_10_2359_0_join3 rfl rfl rfl

private theorem receipt_2_10_2359_0 : fastPhase (bank 2 10).shape 179818 2359 20 1 0 7 0 = 1998422600822307330543028516 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2359_0_join4

private theorem receipt_2_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 0 128 = 675803641804837860765717760 := by decide +kernel
private theorem receipt_2_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 128 128 = 518870958776741715810931968 := by decide +kernel
private theorem receipt_2_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 256 128 = 377150782116812169621853440 := by decide +kernel
private theorem receipt_2_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 384 128 = 249739628960433462543417407 := by decide +kernel
private theorem receipt_2_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 512 128 = 135760371723693934904932708 := by decide +kernel
private theorem receipt_2_10_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 640 111 = 35207142289002950738787390 := by decide +kernel
private theorem receipt_2_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 128 256 = 896021740893553885432785408 :=
  phaseBlock_append receipt_2_10_2359_1_part1 receipt_2_10_2359_1_part2 rfl rfl rfl
private theorem receipt_2_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 0 384 = 1571825382698391746198503168 :=
  phaseBlock_append receipt_2_10_2359_1_part0 receipt_2_10_2359_1_join0 rfl rfl rfl
private theorem receipt_2_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 512 239 = 170967514012696885643720098 :=
  phaseBlock_append receipt_2_10_2359_1_part4 receipt_2_10_2359_1_part5 rfl rfl rfl
private theorem receipt_2_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 384 367 = 420707142973130348187137505 :=
  phaseBlock_append receipt_2_10_2359_1_part3 receipt_2_10_2359_1_join2 rfl rfl rfl
private theorem receipt_2_10_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2359 20 1 0 7 1) 0 751 = 1992532525671522094385640673 :=
  phaseBlock_append receipt_2_10_2359_1_join1 receipt_2_10_2359_1_join3 rfl rfl rfl

private theorem receipt_2_10_2359_1 : fastPhase (bank 2 10).shape 179818 2359 20 1 0 7 1 = 1992532525671522094385640673 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2359_1_join4

private theorem receipt_2_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 0 128 = 677081858413454352423067872 := by decide +kernel
private theorem receipt_2_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 128 128 = 520028257106974078343803104 := by decide +kernel
private theorem receipt_2_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 256 128 = 378194502510957733107908832 := by decide +kernel
private theorem receipt_2_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 384 128 = 250676882809493746076274660 := by decide +kernel
private theorem receipt_2_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 512 128 = 136598045178092876965897218 := by decide +kernel
private theorem receipt_2_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 640 111 = 35858109396968958323750625 := by decide +kernel
private theorem receipt_2_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 128 256 = 898222759617931811451711936 :=
  phaseBlock_append receipt_2_10_2360_0_part1 receipt_2_10_2360_0_part2 rfl rfl rfl
private theorem receipt_2_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 0 384 = 1575304618031386163874779808 :=
  phaseBlock_append receipt_2_10_2360_0_part0 receipt_2_10_2360_0_join0 rfl rfl rfl
private theorem receipt_2_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 512 239 = 172456154575061835289647843 :=
  phaseBlock_append receipt_2_10_2360_0_part4 receipt_2_10_2360_0_part5 rfl rfl rfl
private theorem receipt_2_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 384 367 = 423133037384555581365922503 :=
  phaseBlock_append receipt_2_10_2360_0_part3 receipt_2_10_2360_0_join2 rfl rfl rfl
private theorem receipt_2_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 0) 0 751 = 1998437655415941745240702311 :=
  phaseBlock_append receipt_2_10_2360_0_join1 receipt_2_10_2360_0_join3 rfl rfl rfl

private theorem receipt_2_10_2360_0 : fastPhase (bank 2 10).shape 179818 2360 20 1 0 7 0 = 1998437655415941745240702311 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2360_0_join4

private theorem receipt_2_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 0 128 = 675809627514188234633268192 := by decide +kernel
private theorem receipt_2_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 128 128 = 518875078481686463139175392 := by decide +kernel
private theorem receipt_2_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 256 128 = 377153411649085348856228832 := by decide +kernel
private theorem receipt_2_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 384 128 = 249741115577726643924931941 := by decide +kernel
private theorem receipt_2_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 512 128 = 135761033778166560463763379 := by decide +kernel
private theorem receipt_2_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 640 111 = 35207279073103835009088447 := by decide +kernel
private theorem receipt_2_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 128 256 = 896028490130771811995404224 :=
  phaseBlock_append receipt_2_10_2360_1_part1 receipt_2_10_2360_1_part2 rfl rfl rfl
private theorem receipt_2_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 0 384 = 1571838117644960046628672416 :=
  phaseBlock_append receipt_2_10_2360_1_part0 receipt_2_10_2360_1_join0 rfl rfl rfl
private theorem receipt_2_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 512 239 = 170968312851270395472851826 :=
  phaseBlock_append receipt_2_10_2360_1_part4 receipt_2_10_2360_1_part5 rfl rfl rfl
private theorem receipt_2_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 384 367 = 420709428428997039397783767 :=
  phaseBlock_append receipt_2_10_2360_1_part3 receipt_2_10_2360_1_join2 rfl rfl rfl
private theorem receipt_2_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179818 2360 20 1 0 7 1) 0 751 = 1992547546073957086026456183 :=
  phaseBlock_append receipt_2_10_2360_1_join1 receipt_2_10_2360_1_join3 rfl rfl rfl

private theorem receipt_2_10_2360_1 : fastPhase (bank 2 10).shape 179818 2360 20 1 0 7 1 = 1992547546073957086026456183 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2360_1_join4

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2359_0 receipt_2_10_2359_1 receipt_2_10_2360_0 receipt_2_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 0 128 = 66874090523392123421200192 := by decide +kernel
private theorem receipt_3_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 128 128 = 46729833037835727145684800 := by decide +kernel
private theorem receipt_3_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 256 128 = 28726008568188300603592512 := by decide +kernel
private theorem receipt_3_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 384 128 = 12998174351443305936637760 := by decide +kernel
private theorem receipt_3_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 512 59 = 1356351307349571173325574 := by decide +kernel
private theorem receipt_3_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 0 256 = 113603923561227850566884992 :=
  phaseBlock_append receipt_3_10_2359_0_part0 receipt_3_10_2359_0_part1 rfl rfl rfl
private theorem receipt_3_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 384 187 = 14354525658792877109963334 :=
  phaseBlock_append receipt_3_10_2359_0_part3 receipt_3_10_2359_0_part4 rfl rfl rfl
private theorem receipt_3_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 256 315 = 43080534226981177713555846 :=
  phaseBlock_append receipt_3_10_2359_0_part2 receipt_3_10_2359_0_join1 rfl rfl rfl
private theorem receipt_3_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 0) 0 571 = 156684457788209028280440838 :=
  phaseBlock_append receipt_3_10_2359_0_join0 receipt_3_10_2359_0_join2 rfl rfl rfl

private theorem receipt_3_10_2359_0 : fastPhase (bank 3 10).shape 179818 2359 20 1 1 1 0 = 156684457788209028280440838 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2359_0_join3

private theorem receipt_3_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 0 128 = 66710742945391105577685696 := by decide +kernel
private theorem receipt_3_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 128 128 = 46582054134760694122173120 := by decide +kernel
private theorem receipt_3_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 256 128 = 28594950726029621743522496 := by decide +kernel
private theorem receipt_3_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 384 128 = 12884972634871166048654016 := by decide +kernel
private theorem receipt_3_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 512 59 = 1310493937800263206690426 := by decide +kernel
private theorem receipt_3_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 0 256 = 113292797080151799699858816 :=
  phaseBlock_append receipt_3_10_2359_1_part0 receipt_3_10_2359_1_part1 rfl rfl rfl
private theorem receipt_3_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 384 187 = 14195466572671429255344442 :=
  phaseBlock_append receipt_3_10_2359_1_part3 receipt_3_10_2359_1_part4 rfl rfl rfl
private theorem receipt_3_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 256 315 = 42790417298701050998866938 :=
  phaseBlock_append receipt_3_10_2359_1_part2 receipt_3_10_2359_1_join1 rfl rfl rfl
private theorem receipt_3_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2359 20 1 1 1 1) 0 571 = 156083214378852850698725754 :=
  phaseBlock_append receipt_3_10_2359_1_join0 receipt_3_10_2359_1_join2 rfl rfl rfl

private theorem receipt_3_10_2359_1 : fastPhase (bank 3 10).shape 179818 2359 20 1 1 1 1 = 156083214378852850698725754 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2359_1_join3

private theorem receipt_3_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 0 128 = 66874646312509603966419840 := by decide +kernel
private theorem receipt_3_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 128 128 = 46730132119632811894203264 := by decide +kernel
private theorem receipt_3_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 256 128 = 28726139973306965057979264 := by decide +kernel
private theorem receipt_3_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 384 128 = 12998211617623706423272320 := by decide +kernel
private theorem receipt_3_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 512 59 = 1356353440592936127183768 := by decide +kernel
private theorem receipt_3_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 0 256 = 113604778432142415860623104 :=
  phaseBlock_append receipt_3_10_2360_0_part0 receipt_3_10_2360_0_part1 rfl rfl rfl
private theorem receipt_3_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 384 187 = 14354565058216642550456088 :=
  phaseBlock_append receipt_3_10_2360_0_part3 receipt_3_10_2360_0_part4 rfl rfl rfl
private theorem receipt_3_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 256 315 = 43080705031523607608435352 :=
  phaseBlock_append receipt_3_10_2360_0_part2 receipt_3_10_2360_0_join1 rfl rfl rfl
private theorem receipt_3_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 0) 0 571 = 156685483463666023469058456 :=
  phaseBlock_append receipt_3_10_2360_0_join0 receipt_3_10_2360_0_join2 rfl rfl rfl

private theorem receipt_3_10_2360_0 : fastPhase (bank 3 10).shape 179818 2360 20 1 1 1 0 = 156685483463666023469058456 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2360_0_join3

private theorem receipt_3_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 0 128 = 66711297179695962862004544 := by decide +kernel
private theorem receipt_3_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 128 128 = 46582352153930670814751040 := by decide +kernel
private theorem receipt_3_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 256 128 = 28595081474973087786379584 := by decide +kernel
private theorem receipt_3_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 384 128 = 12885009566842922310953280 := by decide +kernel
private theorem receipt_3_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 512 59 = 1310496002362893942984798 := by decide +kernel
private theorem receipt_3_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 0 256 = 113293649333626633676755584 :=
  phaseBlock_append receipt_3_10_2360_1_part0 receipt_3_10_2360_1_part1 rfl rfl rfl
private theorem receipt_3_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 384 187 = 14195505569205816253938078 :=
  phaseBlock_append receipt_3_10_2360_1_part3 receipt_3_10_2360_1_part4 rfl rfl rfl
private theorem receipt_3_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 256 315 = 42790587044178904040317662 :=
  phaseBlock_append receipt_3_10_2360_1_part2 receipt_3_10_2360_1_join1 rfl rfl rfl
private theorem receipt_3_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179818 2360 20 1 1 1 1) 0 571 = 156084236377805537717073246 :=
  phaseBlock_append receipt_3_10_2360_1_join0 receipt_3_10_2360_1_join2 rfl rfl rfl

private theorem receipt_3_10_2360_1 : fastPhase (bank 3 10).shape 179818 2360 20 1 1 1 1 = 156084236377805537717073246 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2360_1_join3

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2726_570)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_10_2359_0 receipt_3_10_2359_1 receipt_3_10_2360_0 receipt_3_10_2360_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group3_stage i)).shape
      (cutoff h rect (group3_stage i)), ¬ G∣Q :=
  (group3_checked rect i).avoids Crt word lo hi irr seeded slope hs hj


end Lower6960.RescueSource
