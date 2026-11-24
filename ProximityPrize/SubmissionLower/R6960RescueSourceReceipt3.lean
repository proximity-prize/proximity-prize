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

private theorem receipt_0_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 0 128 = 567197020736526982615564608 := by decide +kernel
private theorem receipt_0_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 128 128 = 397210234347130825142624576 := by decide +kernel
private theorem receipt_0_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 256 128 = 245094602812817882753216124 := by decide +kernel
private theorem receipt_0_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 384 128 = 109862147348988687720250941 := by decide +kernel
private theorem receipt_0_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 512 52 = 9679041354818219918488715 := by decide +kernel
private theorem receipt_0_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 0 256 = 964407255083657807758189184 :=
  phaseBlock_append receipt_0_8_2359_0_part0 receipt_0_8_2359_0_part1 rfl rfl rfl
private theorem receipt_0_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 384 180 = 119541188703806907638739656 :=
  phaseBlock_append receipt_0_8_2359_0_part3 receipt_0_8_2359_0_part4 rfl rfl rfl
private theorem receipt_0_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 256 308 = 364635791516624790391955780 :=
  phaseBlock_append receipt_0_8_2359_0_part2 receipt_0_8_2359_0_join1 rfl rfl rfl
private theorem receipt_0_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 0) 0 564 = 1329043046600282598150144964 :=
  phaseBlock_append receipt_0_8_2359_0_join0 receipt_0_8_2359_0_join2 rfl rfl rfl

private theorem receipt_0_8_2359_0 : fastPhase (bank 0 8).shape 179808 2379 16 1 0 1 0 = 1329043046600282598150144964 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2359_0_join3

private theorem receipt_0_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 0 128 = 565814631793904508836077952 := by decide +kernel
private theorem receipt_0_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 128 128 = 395966470876815111547724160 := by decide +kernel
private theorem receipt_0_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 256 128 = 243981979988916594664352667 := by decide +kernel
private theorem receipt_0_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 384 128 = 108873211379414988170811133 := by decide +kernel
private theorem receipt_0_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 512 52 = 9310914110906472699754418 := by decide +kernel
private theorem receipt_0_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 0 256 = 961781102670719620383802112 :=
  phaseBlock_append receipt_0_8_2359_1_part0 receipt_0_8_2359_1_part1 rfl rfl rfl
private theorem receipt_0_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 384 180 = 118184125490321460870565551 :=
  phaseBlock_append receipt_0_8_2359_1_part3 receipt_0_8_2359_1_part4 rfl rfl rfl
private theorem receipt_0_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 256 308 = 362166105479238055534918218 :=
  phaseBlock_append receipt_0_8_2359_1_part2 receipt_0_8_2359_1_join1 rfl rfl rfl
private theorem receipt_0_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2379 16 1 0 1 1) 0 564 = 1323947208149957675918720330 :=
  phaseBlock_append receipt_0_8_2359_1_join0 receipt_0_8_2359_1_join2 rfl rfl rfl

private theorem receipt_0_8_2359_1 : fastPhase (bank 0 8).shape 179808 2379 16 1 0 1 1 = 1323947208149957675918720330 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2359_1_join3

private theorem receipt_0_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 0 128 = 567201936266355984913679808 := by decide +kernel
private theorem receipt_0_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 128 128 = 397213204306748475869693376 := by decide +kernel
private theorem receipt_0_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 256 128 = 245096124891397888741953576 := by decide +kernel
private theorem receipt_0_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 384 128 = 109862683600155150596525624 := by decide +kernel
private theorem receipt_0_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 512 52 = 9679078053829953495526527 := by decide +kernel
private theorem receipt_0_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 0 256 = 964415140573104460783373184 :=
  phaseBlock_append receipt_0_8_2360_0_part0 receipt_0_8_2360_0_part1 rfl rfl rfl
private theorem receipt_0_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 384 180 = 119541761653985104092052151 :=
  phaseBlock_append receipt_0_8_2360_0_part3 receipt_0_8_2360_0_part4 rfl rfl rfl
private theorem receipt_0_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 256 308 = 364637886545382992834005727 :=
  phaseBlock_append receipt_0_8_2360_0_part2 receipt_0_8_2360_0_join1 rfl rfl rfl
private theorem receipt_0_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 0) 0 564 = 1329053027118487453617378911 :=
  phaseBlock_append receipt_0_8_2360_0_join0 receipt_0_8_2360_0_join2 rfl rfl rfl

private theorem receipt_0_8_2360_0 : fastPhase (bank 0 8).shape 179808 2380 16 1 0 1 0 = 1329053027118487453617378911 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2360_0_join3

private theorem receipt_0_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 0 128 = 565819537440921933778756544 := by decide +kernel
private theorem receipt_0_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 128 128 = 395969432943164485648393152 := by decide +kernel
private theorem receipt_0_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 256 128 = 243983496003034763533099309 := by decide +kernel
private theorem receipt_0_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 384 128 = 108873743250786578340232266 := by decide +kernel
private theorem receipt_0_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 512 52 = 9310949476396018714018743 := by decide +kernel
private theorem receipt_0_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 0 256 = 961788970384086419427149696 :=
  phaseBlock_append receipt_0_8_2360_1_part0 receipt_0_8_2360_1_part1 rfl rfl rfl
private theorem receipt_0_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 384 180 = 118184692727182597054251009 :=
  phaseBlock_append receipt_0_8_2360_1_part3 receipt_0_8_2360_1_part4 rfl rfl rfl
private theorem receipt_0_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 256 308 = 362168188730217360587350318 :=
  phaseBlock_append receipt_0_8_2360_1_part2 receipt_0_8_2360_1_join1 rfl rfl rfl
private theorem receipt_0_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2380 16 1 0 1 1) 0 564 = 1323957159114303780014500014 :=
  phaseBlock_append receipt_0_8_2360_1_join0 receipt_0_8_2360_1_join2 rfl rfl rfl

private theorem receipt_0_8_2360_1 : fastPhase (bank 0 8).shape 179808 2380 16 1 0 1 1 = 1323957159114303780014500014 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2360_1_join3

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2359_0 receipt_0_8_2359_1 receipt_0_8_2360_0 receipt_0_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 0 128 = 510267040502795783499916992 := by decide +kernel
private theorem receipt_1_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 128 128 = 356884613147672517948049088 := by decide +kernel
private theorem receipt_1_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 256 128 = 219931908547621486228526925 := by decide +kernel
private theorem receipt_1_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 384 128 = 98461632298464817400854965 := by decide +kernel
private theorem receipt_1_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 512 52 = 8666400691023384955967822 := by decide +kernel
private theorem receipt_1_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 0 256 = 867151653650468301447966080 :=
  phaseBlock_append receipt_1_8_2359_0_part0 receipt_1_8_2359_0_part1 rfl rfl rfl
private theorem receipt_1_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 384 180 = 107128032989488202356822787 :=
  phaseBlock_append receipt_1_8_2359_0_part3 receipt_1_8_2359_0_part4 rfl rfl rfl
private theorem receipt_1_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 256 308 = 327059941537109688585349712 :=
  phaseBlock_append receipt_1_8_2359_0_part2 receipt_1_8_2359_0_join1 rfl rfl rfl
private theorem receipt_1_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 0) 0 564 = 1194211595187577990033315792 :=
  phaseBlock_append receipt_1_8_2359_0_join0 receipt_1_8_2359_0_join2 rfl rfl rfl

private theorem receipt_1_8_2359_0 : fastPhase (bank 1 8).shape 179808 2379 16 1 0 2 0 = 1194211595187577990033315792 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2359_0_join3

private theorem receipt_1_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 0 128 = 509018305105280477869296512 := by decide +kernel
private theorem receipt_1_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 128 128 = 355763565516426170887113600 := by decide +kernel
private theorem receipt_1_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 256 128 = 218931351342835352346816897 := by decide +kernel
private theorem receipt_1_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 384 128 = 97574430527373215636135938 := by decide +kernel
private theorem receipt_1_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 512 52 = 8336731061255391520033997 := by decide +kernel
private theorem receipt_1_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 0 256 = 864781870621706648756410112 :=
  phaseBlock_append receipt_1_8_2359_1_part0 receipt_1_8_2359_1_part1 rfl rfl rfl
private theorem receipt_1_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 384 180 = 105911161588628607156169935 :=
  phaseBlock_append receipt_1_8_2359_1_part3 receipt_1_8_2359_1_part4 rfl rfl rfl
private theorem receipt_1_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 256 308 = 324842512931463959502986832 :=
  phaseBlock_append receipt_1_8_2359_1_part2 receipt_1_8_2359_1_join1 rfl rfl rfl
private theorem receipt_1_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2379 16 1 0 2 1) 0 564 = 1189624383553170608259396944 :=
  phaseBlock_append receipt_1_8_2359_1_join0 receipt_1_8_2359_1_join2 rfl rfl rfl

private theorem receipt_1_8_2359_1 : fastPhase (bank 1 8).shape 179808 2379 16 1 0 2 1 = 1189624383553170608259396944 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2359_1_join3

private theorem receipt_1_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 0 128 = 510271462720301012572051872 := by decide +kernel
private theorem receipt_1_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 128 128 = 356887281637864174463936928 := by decide +kernel
private theorem receipt_1_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 256 128 = 219933274392517521209315253 := by decide +kernel
private theorem receipt_1_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 384 128 = 98462112916126576847185721 := by decide +kernel
private theorem receipt_1_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 512 52 = 8666433550671002907482214 := by decide +kernel
private theorem receipt_1_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 0 256 = 867158744358165187035988800 :=
  phaseBlock_append receipt_1_8_2360_0_part0 receipt_1_8_2360_0_part1 rfl rfl rfl
private theorem receipt_1_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 384 180 = 107128546466797579754667935 :=
  phaseBlock_append receipt_1_8_2360_0_part3 receipt_1_8_2360_0_part4 rfl rfl rfl
private theorem receipt_1_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 256 308 = 327061820859315100963983188 :=
  phaseBlock_append receipt_1_8_2360_0_part2 receipt_1_8_2360_0_join1 rfl rfl rfl
private theorem receipt_1_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 0) 0 564 = 1194220565217480287999971988 :=
  phaseBlock_append receipt_1_8_2360_0_join0 receipt_1_8_2360_0_join2 rfl rfl rfl

private theorem receipt_1_8_2360_0 : fastPhase (bank 1 8).shape 179808 2380 16 1 0 2 0 = 1194220565217480287999971988 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2360_0_join3

private theorem receipt_1_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 0 128 = 509022718387575800441382560 := by decide +kernel
private theorem receipt_1_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 128 128 = 355766226887965294364882592 := by decide +kernel
private theorem receipt_1_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 256 128 = 218932711732303965463233391 := by decide +kernel
private theorem receipt_1_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 384 128 = 97574907215244669101013447 := by decide +kernel
private theorem receipt_1_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 512 52 = 8336762726669742815302164 := by decide +kernel
private theorem receipt_1_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 0 256 = 864788945275541094806265152 :=
  phaseBlock_append receipt_1_8_2360_1_part0 receipt_1_8_2360_1_part1 rfl rfl rfl
private theorem receipt_1_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 384 180 = 105911669941914411916315611 :=
  phaseBlock_append receipt_1_8_2360_1_part3 receipt_1_8_2360_1_part4 rfl rfl rfl
private theorem receipt_1_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 256 308 = 324844381674218377379549002 :=
  phaseBlock_append receipt_1_8_2360_1_part2 receipt_1_8_2360_1_join1 rfl rfl rfl
private theorem receipt_1_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2380 16 1 0 2 1) 0 564 = 1189633326949759472185814154 :=
  phaseBlock_append receipt_1_8_2360_1_join0 receipt_1_8_2360_1_join2 rfl rfl rfl

private theorem receipt_1_8_2360_1 : fastPhase (bank 1 8).shape 179808 2380 16 1 0 2 1 = 1189633326949759472185814154 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2360_1_join3

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2359_0 receipt_1_8_2359_1 receipt_1_8_2360_0 receipt_1_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 0 128 = 272059629524442036911476864 := by decide +kernel
private theorem receipt_2_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 128 128 = 188525890574743797803978880 := by decide +kernel
private theorem receipt_2_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 256 128 = 115109355042464331106598999 := by decide +kernel
private theorem receipt_2_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 384 128 = 51071010176323641356516706 := by decide +kernel
private theorem receipt_2_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 512 52 = 4463916949398671446588935 := by decide +kernel
private theorem receipt_2_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 0 256 = 460585520099185834715455744 :=
  phaseBlock_append receipt_2_8_2359_0_part0 receipt_2_8_2359_0_part1 rfl rfl rfl
private theorem receipt_2_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 384 180 = 55534927125722312803105641 :=
  phaseBlock_append receipt_2_8_2359_0_part3 receipt_2_8_2359_0_part4 rfl rfl rfl
private theorem receipt_2_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 256 308 = 170644282168186643909704640 :=
  phaseBlock_append receipt_2_8_2359_0_part2 receipt_2_8_2359_0_join1 rfl rfl rfl
private theorem receipt_2_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 0) 0 564 = 631229802267372478625160384 :=
  phaseBlock_append receipt_2_8_2359_0_join0 receipt_2_8_2359_0_join2 rfl rfl rfl

private theorem receipt_2_8_2359_0 : fastPhase (bank 2 8).shape 179808 2379 16 1 0 7 0 = 631229802267372478625160384 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2359_0_join3

private theorem receipt_2_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 0 128 = 271374229951674232982238976 := by decide +kernel
private theorem receipt_2_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 128 128 = 187920076703399184377542400 := by decide +kernel
private theorem receipt_2_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 256 128 = 114577426334172477441080196 := by decide +kernel
private theorem receipt_2_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 384 128 = 50607449300689073474971149 := by decide +kernel
private theorem receipt_2_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 512 52 = 4293895152969169651130493 := by decide +kernel
private theorem receipt_2_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 0 256 = 459294306655073417359781376 :=
  phaseBlock_append receipt_2_8_2359_1_part0 receipt_2_8_2359_1_part1 rfl rfl rfl
private theorem receipt_2_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 384 180 = 54901344453658243126101642 :=
  phaseBlock_append receipt_2_8_2359_1_part3 receipt_2_8_2359_1_part4 rfl rfl rfl
private theorem receipt_2_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 256 308 = 169478770787830720567181838 :=
  phaseBlock_append receipt_2_8_2359_1_part2 receipt_2_8_2359_1_join1 rfl rfl rfl
private theorem receipt_2_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2379 16 1 0 7 1) 0 564 = 628773077442904137926963214 :=
  phaseBlock_append receipt_2_8_2359_1_join0 receipt_2_8_2359_1_join2 rfl rfl rfl

private theorem receipt_2_8_2359_1 : fastPhase (bank 2 8).shape 179808 2379 16 1 0 7 1 = 628773077442904137926963214 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2359_1_join3

private theorem receipt_2_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 0 128 = 272061987565270890196541024 := by decide +kernel
private theorem receipt_2_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 128 128 = 188527300397205334733827680 := by decide +kernel
private theorem receipt_2_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 256 128 = 115110070024789515429465187 := by decide +kernel
private theorem receipt_2_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 384 128 = 51071259520325038894520103 := by decide +kernel
private theorem receipt_2_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 512 52 = 4463933875455278751797823 := by decide +kernel
private theorem receipt_2_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 0 256 = 460589287962476224930368704 :=
  phaseBlock_append receipt_2_8_2360_0_part0 receipt_2_8_2360_0_part1 rfl rfl rfl
private theorem receipt_2_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 384 180 = 55535193395780317646317926 :=
  phaseBlock_append receipt_2_8_2360_0_part3 receipt_2_8_2360_0_part4 rfl rfl rfl
private theorem receipt_2_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 256 308 = 170645263420569833075783113 :=
  phaseBlock_append receipt_2_8_2360_0_part2 receipt_2_8_2360_0_join1 rfl rfl rfl
private theorem receipt_2_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 0) 0 564 = 631234551383046058006151817 :=
  phaseBlock_append receipt_2_8_2360_0_join0 receipt_2_8_2360_0_join2 rfl rfl rfl

private theorem receipt_2_8_2360_0 : fastPhase (bank 2 8).shape 179808 2380 16 1 0 7 0 = 631234551383046058006151817 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2360_0_join3

private theorem receipt_2_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 0 128 = 271376583057921222784291424 := by decide +kernel
private theorem receipt_2_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 128 128 = 187921482662997295838880352 := by decide +kernel
private theorem receipt_2_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 256 128 = 114578138409392665519883700 := by decide +kernel
private theorem receipt_2_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 384 128 = 50607696589273115010752649 := by decide +kernel
private theorem receipt_2_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 512 52 = 4293911463036500214449085 := by decide +kernel
private theorem receipt_2_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 0 256 = 459298065720918518623171776 :=
  phaseBlock_append receipt_2_8_2360_1_part0 receipt_2_8_2360_1_part1 rfl rfl rfl
private theorem receipt_2_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 384 180 = 54901608052309615225201734 :=
  phaseBlock_append receipt_2_8_2360_1_part3 receipt_2_8_2360_1_part4 rfl rfl rfl
private theorem receipt_2_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 256 308 = 169479746461702280745085434 :=
  phaseBlock_append receipt_2_8_2360_1_part2 receipt_2_8_2360_1_join1 rfl rfl rfl
private theorem receipt_2_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2380 16 1 0 7 1) 0 564 = 628777812182620799368257210 :=
  phaseBlock_append receipt_2_8_2360_1_join0 receipt_2_8_2360_1_join2 rfl rfl rfl

private theorem receipt_2_8_2360_1 : fastPhase (bank 2 8).shape 179808 2380 16 1 0 7 1 = 628777812182620799368257210 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2360_1_join3

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2359_0 receipt_2_8_2359_1 receipt_2_8_2360_0 receipt_2_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 0 128 = 47028526270238901990508416 := by decide +kernel
private theorem receipt_3_8_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 128 128 = 33072093787283605593139072 := by decide +kernel
private theorem receipt_3_8_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 256 128 = 20633735617110265521342336 := by decide +kernel
private theorem receipt_3_8_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 384 128 = 9806536238647870726137728 := by decide +kernel
private theorem receipt_3_8_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 512 73 = 1393983624819746301806544 := by decide +kernel
private theorem receipt_3_8_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 0 256 = 80100620057522507583647488 :=
  phaseBlock_append receipt_3_8_2359_0_part0 receipt_3_8_2359_0_part1 rfl rfl rfl
private theorem receipt_3_8_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 384 201 = 11200519863467617027944272 :=
  phaseBlock_append receipt_3_8_2359_0_part3 receipt_3_8_2359_0_part4 rfl rfl rfl
private theorem receipt_3_8_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 256 329 = 31834255480577882549286608 :=
  phaseBlock_append receipt_3_8_2359_0_part2 receipt_3_8_2359_0_join1 rfl rfl rfl
private theorem receipt_3_8_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 0) 0 585 = 111934875538100390132934096 :=
  phaseBlock_append receipt_3_8_2359_0_join0 receipt_3_8_2359_0_join2 rfl rfl rfl

private theorem receipt_3_8_2359_0 : fastPhase (bank 3 8).shape 179808 2379 16 1 1 1 0 = 111934875538100390132934096 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2359_0_join3

private theorem receipt_3_8_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 0 128 = 46915267123888052928231552 := by decide +kernel
private theorem receipt_3_8_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 128 128 = 32969888271442815308847232 := by decide +kernel
private theorem receipt_3_8_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 256 128 = 20543379176752091151071360 := by decide +kernel
private theorem receipt_3_8_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 384 128 = 9728809842098819495041152 := by decide +kernel
private theorem receipt_3_8_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 512 73 = 1355605510276759731266328 := by decide +kernel
private theorem receipt_3_8_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 0 256 = 79885155395330868237078784 :=
  phaseBlock_append receipt_3_8_2359_1_part0 receipt_3_8_2359_1_part1 rfl rfl rfl
private theorem receipt_3_8_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 384 201 = 11084415352375579226307480 :=
  phaseBlock_append receipt_3_8_2359_1_part3 receipt_3_8_2359_1_part4 rfl rfl rfl
private theorem receipt_3_8_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 256 329 = 31627794529127670377378840 :=
  phaseBlock_append receipt_3_8_2359_1_part2 receipt_3_8_2359_1_join1 rfl rfl rfl
private theorem receipt_3_8_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2379 16 1 1 1 1) 0 585 = 111512949924458538614457624 :=
  phaseBlock_append receipt_3_8_2359_1_join0 receipt_3_8_2359_1_join2 rfl rfl rfl

private theorem receipt_3_8_2359_1 : fastPhase (bank 3 8).shape 179808 2379 16 1 1 1 1 = 111512949924458538614457624 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2359_1_join3

private theorem receipt_3_8_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 0 128 = 47028918117036536078641920 := by decide +kernel
private theorem receipt_3_8_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 128 128 = 33072305383562144191859456 := by decide +kernel
private theorem receipt_3_8_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 256 128 = 20633829482403857651854080 := by decide +kernel
private theorem receipt_3_8_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 384 128 = 9806563809020882384325376 := by decide +kernel
private theorem receipt_3_8_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 512 73 = 1393985655006590735465610 := by decide +kernel
private theorem receipt_3_8_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 0 256 = 80101223500598680270501376 :=
  phaseBlock_append receipt_3_8_2360_0_part0 receipt_3_8_2360_0_part1 rfl rfl rfl
private theorem receipt_3_8_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 384 201 = 11200549464027473119790986 :=
  phaseBlock_append receipt_3_8_2360_0_part3 receipt_3_8_2360_0_part4 rfl rfl rfl
private theorem receipt_3_8_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 256 329 = 31834378946431330771645066 :=
  phaseBlock_append receipt_3_8_2360_0_part2 receipt_3_8_2360_0_join1 rfl rfl rfl
private theorem receipt_3_8_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 0) 0 585 = 111935602447030011042146442 :=
  phaseBlock_append receipt_3_8_2360_0_join0 receipt_3_8_2360_0_join2 rfl rfl rfl

private theorem receipt_3_8_2360_0 : fastPhase (bank 3 8).shape 179808 2380 16 1 1 1 0 = 111935602447030011042146442 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2360_0_join3

private theorem receipt_3_8_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 0 128 = 46915657886585310673859520 := by decide +kernel
private theorem receipt_3_8_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 128 128 = 32970099130079838496650176 := by decide +kernel
private theorem receipt_3_8_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 256 128 = 20543472589405733963002816 := by decide +kernel
private theorem receipt_3_8_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 384 128 = 9728837184429721987216320 := by decide +kernel
private theorem receipt_3_8_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 512 73 = 1355607488164962801939420 := by decide +kernel
private theorem receipt_3_8_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 0 256 = 79885757016665149170509696 :=
  phaseBlock_append receipt_3_8_2360_1_part0 receipt_3_8_2360_1_part1 rfl rfl rfl
private theorem receipt_3_8_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 384 201 = 11084444672594684789155740 :=
  phaseBlock_append receipt_3_8_2360_1_part3 receipt_3_8_2360_1_part4 rfl rfl rfl
private theorem receipt_3_8_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 256 329 = 31627917262000418752158556 :=
  phaseBlock_append receipt_3_8_2360_1_part2 receipt_3_8_2360_1_join1 rfl rfl rfl
private theorem receipt_3_8_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2380 16 1 1 1 1) 0 585 = 111513674278665567922668252 :=
  phaseBlock_append receipt_3_8_2360_1_join0 receipt_3_8_2360_1_join2 rfl rfl rfl

private theorem receipt_3_8_2360_1 : fastPhase (bank 3 8).shape 179808 2380 16 1 1 1 1 = 111513674278665567922668252 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2360_1_join3

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2359_0 receipt_3_8_2359_1 receipt_3_8_2360_0 receipt_3_8_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 0 128 = 144896699544330845091932860 := by decide +kernel
private theorem receipt_0_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 128 128 = 88469994612780028358175726 := by decide +kernel
private theorem receipt_0_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 256 128 = 39695629633356199640294171 := by decide +kernel
private theorem receipt_0_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 384 56 = 3862582443233632989033756 := by decide +kernel
private theorem receipt_0_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 0 256 = 233366694157110873450108586 :=
  phaseBlock_append receipt_0_9_2359_0_part0 receipt_0_9_2359_0_part1 rfl rfl rfl
private theorem receipt_0_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 256 184 = 43558212076589832629327927 :=
  phaseBlock_append receipt_0_9_2359_0_part2 receipt_0_9_2359_0_part3 rfl rfl rfl
private theorem receipt_0_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 0) 0 440 = 276924906233700706079436513 :=
  phaseBlock_append receipt_0_9_2359_0_join0 receipt_0_9_2359_0_join1 rfl rfl rfl

private theorem receipt_0_9_2359_0 : fastPhase (bank 0 9).shape 179808 2379 10 1 0 1 0 = 276924906233700706079436513 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2359_0_join2

private theorem receipt_0_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 0 128 = 144430519685386993973292193 := by decide +kernel
private theorem receipt_0_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 128 128 = 88063657571113011909440873 := by decide +kernel
private theorem receipt_0_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 256 128 = 39344931575399897084631735 := by decide +kernel
private theorem receipt_0_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 384 56 = 3725579341200740830612413 := by decide +kernel
private theorem receipt_0_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 0 256 = 232494177256500005882733066 :=
  phaseBlock_append receipt_0_9_2359_1_part0 receipt_0_9_2359_1_part1 rfl rfl rfl
private theorem receipt_0_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 256 184 = 43070510916600637915244148 :=
  phaseBlock_append receipt_0_9_2359_1_part2 receipt_0_9_2359_1_part3 rfl rfl rfl
private theorem receipt_0_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2379 10 1 0 1 1) 0 440 = 275564688173100643797977214 :=
  phaseBlock_append receipt_0_9_2359_1_join0 receipt_0_9_2359_1_join1 rfl rfl rfl

private theorem receipt_0_9_2359_1 : fastPhase (bank 0 9).shape 179808 2379 10 1 0 1 1 = 275564688173100643797977214 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2359_1_join2

private theorem receipt_0_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 0 128 = 144897949997668252826167247 := by decide +kernel
private theorem receipt_0_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 128 128 = 88470618630370159567795965 := by decide +kernel
private theorem receipt_0_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 256 128 = 39695843498291060124719584 := by decide +kernel
private theorem receipt_0_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 384 56 = 3862597896410210022609381 := by decide +kernel
private theorem receipt_0_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 0 256 = 233368568628038412393963212 :=
  phaseBlock_append receipt_0_9_2360_0_part0 receipt_0_9_2360_0_part1 rfl rfl rfl
private theorem receipt_0_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 256 184 = 43558441394701270147328965 :=
  phaseBlock_append receipt_0_9_2360_0_part2 receipt_0_9_2360_0_part3 rfl rfl rfl
private theorem receipt_0_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 0) 0 440 = 276927010022739682541292177 :=
  phaseBlock_append receipt_0_9_2360_0_join0 receipt_0_9_2360_0_join1 rfl rfl rfl

private theorem receipt_0_9_2360_0 : fastPhase (bank 0 9).shape 179808 2380 10 1 0 1 0 = 276927010022739682541292177 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2360_0_join2

private theorem receipt_0_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 0 128 = 144431766811129199298469412 := by decide +kernel
private theorem receipt_0_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 128 128 = 88064279130323464418866482 := by decide +kernel
private theorem receipt_0_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 256 128 = 39345143757979613694050452 := by decide +kernel
private theorem receipt_0_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 384 56 = 3725594278244115991349405 := by decide +kernel
private theorem receipt_0_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 0 256 = 232496045941452663717335894 :=
  phaseBlock_append receipt_0_9_2360_1_part0 receipt_0_9_2360_1_part1 rfl rfl rfl
private theorem receipt_0_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 256 184 = 43070738036223729685399857 :=
  phaseBlock_append receipt_0_9_2360_1_part2 receipt_0_9_2360_1_part3 rfl rfl rfl
private theorem receipt_0_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2380 10 1 0 1 1) 0 440 = 275566783977676393402735751 :=
  phaseBlock_append receipt_0_9_2360_1_join0 receipt_0_9_2360_1_join1 rfl rfl rfl

private theorem receipt_0_9_2360_1 : fastPhase (bank 0 9).shape 179808 2380 10 1 0 1 1 = 275566783977676393402735751 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2360_1_join2

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2359_0 receipt_0_9_2359_1 receipt_0_9_2360_0 receipt_0_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 0 128 = 130534570033678058322962893 := by decide +kernel
private theorem receipt_1_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 128 128 = 79565786522148298910536747 := by decide +kernel
private theorem receipt_1_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 256 128 = 35641629887392341814642492 := by decide +kernel
private theorem receipt_1_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 384 56 = 3463667610832457471621749 := by decide +kernel
private theorem receipt_1_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 0 256 = 210100356555826357233499640 :=
  phaseBlock_append receipt_1_9_2359_0_part0 receipt_1_9_2359_0_part1 rfl rfl rfl
private theorem receipt_1_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 256 184 = 39105297498224799286264241 :=
  phaseBlock_append receipt_1_9_2359_0_part2 receipt_1_9_2359_0_part3 rfl rfl rfl
private theorem receipt_1_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 0) 0 440 = 249205654054051156519763881 :=
  phaseBlock_append receipt_1_9_2359_0_join0 receipt_1_9_2359_0_join1 rfl rfl rfl

private theorem receipt_1_9_2359_0 : fastPhase (bank 1 9).shape 179808 2379 10 1 0 2 0 = 249205654054051156519763881 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2359_0_join2

private theorem receipt_1_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 0 128 = 130112866964451785486295000 := by decide +kernel
private theorem receipt_1_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 128 128 = 79199303119145144731616690 := by decide +kernel
private theorem receipt_1_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 256 128 = 35326315410227053385652459 := by decide +kernel
private theorem receipt_1_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 384 56 = 3340783441337369713644266 := by decide +kernel
private theorem receipt_1_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 0 256 = 209312170083596930217911690 :=
  phaseBlock_append receipt_1_9_2359_1_part0 receipt_1_9_2359_1_part1 rfl rfl rfl
private theorem receipt_1_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 256 184 = 38667098851564423099296725 :=
  phaseBlock_append receipt_1_9_2359_1_part2 receipt_1_9_2359_1_part3 rfl rfl rfl
private theorem receipt_1_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2379 10 1 0 2 1) 0 440 = 247979268935161353317208415 :=
  phaseBlock_append receipt_1_9_2359_1_join0 receipt_1_9_2359_1_join1 rfl rfl rfl

private theorem receipt_1_9_2359_1 : fastPhase (bank 1 9).shape 179808 2379 10 1 0 2 1 = 247979268935161353317208415 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2359_1_join2

private theorem receipt_1_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 0 128 = 130535696570490585778574433 := by decide +kernel
private theorem receipt_1_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 128 128 = 79566347753121697203973751 := by decide +kernel
private theorem receipt_1_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 256 128 = 35641821919337660925899286 := by decide +kernel
private theorem receipt_1_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 384 56 = 3463681468181460432822580 := by decide +kernel
private theorem receipt_1_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 0 256 = 210102044323612282982548184 :=
  phaseBlock_append receipt_1_9_2360_0_part0 receipt_1_9_2360_0_part1 rfl rfl rfl
private theorem receipt_1_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 256 184 = 39105503387519121358721866 :=
  phaseBlock_append receipt_1_9_2360_0_part2 receipt_1_9_2360_0_part3 rfl rfl rfl
private theorem receipt_1_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 0) 0 440 = 249207547711131404341270050 :=
  phaseBlock_append receipt_1_9_2360_0_join0 receipt_1_9_2360_0_join1 rfl rfl rfl

private theorem receipt_1_9_2360_0 : fastPhase (bank 1 9).shape 179808 2380 10 1 0 2 0 = 249207547711131404341270050 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2360_0_join2

private theorem receipt_1_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 0 128 = 130113990488467953423037638 := by decide +kernel
private theorem receipt_1_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 128 128 = 79199862131721256616501776 := by decide +kernel
private theorem receipt_1_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 256 128 = 35326505929213002151568130 := by decide +kernel
private theorem receipt_1_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 384 56 = 3340796835727541744800813 := by decide +kernel
private theorem receipt_1_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 0 256 = 209313852620189210039539414 :=
  phaseBlock_append receipt_1_9_2360_1_part0 receipt_1_9_2360_1_part1 rfl rfl rfl
private theorem receipt_1_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 256 184 = 38667302764940543896368943 :=
  phaseBlock_append receipt_1_9_2360_1_part2 receipt_1_9_2360_1_part3 rfl rfl rfl
private theorem receipt_1_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2380 10 1 0 2 1) 0 440 = 247981155385129753935908357 :=
  phaseBlock_append receipt_1_9_2360_1_join0 receipt_1_9_2360_1_join1 rfl rfl rfl

private theorem receipt_1_9_2360_1 : fastPhase (bank 1 9).shape 179808 2380 10 1 0 2 1 = 247981155385129753935908357 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2360_1_join2

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2359_0 receipt_1_9_2359_1 receipt_1_9_2360_0 receipt_1_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 0 128 = 70301706467763327404709298 := by decide +kernel
private theorem receipt_2_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 128 128 = 42331486626947935067854402 := by decide +kernel
private theorem receipt_2_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 256 128 = 18737363349848812425786922 := by decide +kernel
private theorem receipt_2_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 384 56 = 1803965948052907664525224 := by decide +kernel
private theorem receipt_2_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 0 256 = 112633193094711262472563700 :=
  phaseBlock_append receipt_2_9_2359_0_part0 receipt_2_9_2359_0_part1 rfl rfl rfl
private theorem receipt_2_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 256 184 = 20541329297901720090312146 :=
  phaseBlock_append receipt_2_9_2359_0_part2 receipt_2_9_2359_0_part3 rfl rfl rfl
private theorem receipt_2_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 0) 0 440 = 133174522392612982562875846 :=
  phaseBlock_append receipt_2_9_2359_0_join0 receipt_2_9_2359_0_join1 rfl rfl rfl

private theorem receipt_2_9_2359_0 : fastPhase (bank 2 9).shape 179808 2379 10 1 0 7 0 = 133174522392612982562875846 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2359_0_join2

private theorem receipt_2_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 0 128 = 70067903831227053133536450 := by decide +kernel
private theorem receipt_2_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 128 128 = 42132498276142752345808490 := by decide +kernel
private theorem receipt_2_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 256 128 = 18569945014768062773250174 := by decide +kernel
private theorem receipt_2_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 384 56 = 1739849349450827462885036 := by decide +kernel
private theorem receipt_2_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 0 256 = 112200402107369805479344940 :=
  phaseBlock_append receipt_2_9_2359_1_part0 receipt_2_9_2359_1_part1 rfl rfl rfl
private theorem receipt_2_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 256 184 = 20309794364218890236135210 :=
  phaseBlock_append receipt_2_9_2359_1_part2 receipt_2_9_2359_1_part3 rfl rfl rfl
private theorem receipt_2_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2379 10 1 0 7 1) 0 440 = 132510196471588695715480150 :=
  phaseBlock_append receipt_2_9_2359_1_join0 receipt_2_9_2359_1_join1 rfl rfl rfl

private theorem receipt_2_9_2359_1 : fastPhase (bank 2 9).shape 179808 2379 10 1 0 7 1 = 132510196471588695715480150 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2359_1_join2

private theorem receipt_2_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 0 128 = 70302313292830584797632593 := by decide +kernel
private theorem receipt_2_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 128 128 = 42331785291074965029433091 := by decide +kernel
private theorem receipt_2_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 256 128 = 18737464336222209035713971 := by decide +kernel
private theorem receipt_2_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 384 56 = 1803973165790583348668245 := by decide +kernel
private theorem receipt_2_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 0 256 = 112634098583905549827065684 :=
  phaseBlock_append receipt_2_9_2360_0_part0 receipt_2_9_2360_0_part1 rfl rfl rfl
private theorem receipt_2_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 256 184 = 20541437502012792384382216 :=
  phaseBlock_append receipt_2_9_2360_0_part2 receipt_2_9_2360_0_part3 rfl rfl rfl
private theorem receipt_2_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 0) 0 440 = 133175536085918342211447900 :=
  phaseBlock_append receipt_2_9_2360_0_join0 receipt_2_9_2360_0_join1 rfl rfl rfl

private theorem receipt_2_9_2360_0 : fastPhase (bank 2 9).shape 179808 2380 10 1 0 7 0 = 133175536085918342211447900 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2360_0_join2

private theorem receipt_2_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 0 128 = 70068508975620346079837718 := by decide +kernel
private theorem receipt_2_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 128 128 = 42132795731395886311952356 := by decide +kernel
private theorem receipt_2_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 256 128 = 18570045196506756351850125 := by decide +kernel
private theorem receipt_2_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 384 56 = 1739856325571973321813163 := by decide +kernel
private theorem receipt_2_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 0 256 = 112201304707016232391790074 :=
  phaseBlock_append receipt_2_9_2360_1_part0 receipt_2_9_2360_1_part1 rfl rfl rfl
private theorem receipt_2_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 256 184 = 20309901522078729673663288 :=
  phaseBlock_append receipt_2_9_2360_1_part2 receipt_2_9_2360_1_part3 rfl rfl rfl
private theorem receipt_2_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2380 10 1 0 7 1) 0 440 = 132511206229094962065453362 :=
  phaseBlock_append receipt_2_9_2360_1_join0 receipt_2_9_2360_1_join1 rfl rfl rfl

private theorem receipt_2_9_2360_1 : fastPhase (bank 2 9).shape 179808 2380 10 1 0 7 1 = 132511206229094962065453362 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2360_1_join2

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2359_0 receipt_2_9_2359_1 receipt_2_9_2360_0 receipt_2_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 0 128 = 12823903044703685609913472 := by decide +kernel
private theorem receipt_3_9_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 128 128 = 7889113493432736931486848 := by decide +kernel
private theorem receipt_3_9_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 256 128 = 3681695755867857708727424 := by decide +kernel
private theorem receipt_3_9_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 384 73 = 513590880473977975646496 := by decide +kernel
private theorem receipt_3_9_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 0 256 = 20713016538136422541400320 :=
  phaseBlock_append receipt_3_9_2359_0_part0 receipt_3_9_2359_0_part1 rfl rfl rfl
private theorem receipt_3_9_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 256 201 = 4195286636341835684373920 :=
  phaseBlock_append receipt_3_9_2359_0_part2 receipt_3_9_2359_0_part3 rfl rfl rfl
private theorem receipt_3_9_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 0) 0 457 = 24908303174478258225774240 :=
  phaseBlock_append receipt_3_9_2359_0_join0 receipt_3_9_2359_0_join1 rfl rfl rfl

private theorem receipt_3_9_2359_0 : fastPhase (bank 3 9).shape 179808 2379 10 1 1 1 0 = 24908303174478258225774240 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2359_0_join2

private theorem receipt_3_9_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 0 128 = 12783167392778478949447168 := by decide +kernel
private theorem receipt_3_9_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 128 128 = 7853646531215374070633984 := by decide +kernel
private theorem receipt_3_9_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 256 128 = 3651968048387262907577856 := by decide +kernel
private theorem receipt_3_9_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 384 73 = 499383457345294918810224 := by decide +kernel
private theorem receipt_3_9_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 0 256 = 20636813923993853020081152 :=
  phaseBlock_append receipt_3_9_2359_1_part0 receipt_3_9_2359_1_part1 rfl rfl rfl
private theorem receipt_3_9_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 256 201 = 4151351505732557826388080 :=
  phaseBlock_append receipt_3_9_2359_1_part2 receipt_3_9_2359_1_part3 rfl rfl rfl
private theorem receipt_3_9_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2379 10 1 1 1 1) 0 457 = 24788165429726410846469232 :=
  phaseBlock_append receipt_3_9_2359_1_join0 receipt_3_9_2359_1_join1 rfl rfl rfl

private theorem receipt_3_9_2359_1 : fastPhase (bank 3 9).shape 179808 2379 10 1 1 1 1 = 24788165429726410846469232 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2359_1_join2

private theorem receipt_3_9_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 0 128 = 12824007286514319021294944 := by decide +kernel
private theorem receipt_3_9_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 128 128 = 7889158410704981827908960 := by decide +kernel
private theorem receipt_3_9_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 256 128 = 3681708382865289242748256 := by decide +kernel
private theorem receipt_3_9_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 384 73 = 513591741727698857502144 := by decide +kernel
private theorem receipt_3_9_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 0 256 = 20713165697219300849203904 :=
  phaseBlock_append receipt_3_9_2360_0_part0 receipt_3_9_2360_0_part1 rfl rfl rfl
private theorem receipt_3_9_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 256 201 = 4195300124592988100250400 :=
  phaseBlock_append receipt_3_9_2360_0_part2 receipt_3_9_2360_0_part3 rfl rfl rfl
private theorem receipt_3_9_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 0) 0 457 = 24908465821812288949454304 :=
  phaseBlock_append receipt_3_9_2360_0_join0 receipt_3_9_2360_0_join1 rfl rfl rfl

private theorem receipt_3_9_2360_0 : fastPhase (bank 3 9).shape 179808 2380 10 1 1 1 0 = 24908465821812288949454304 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2360_0_join2

private theorem receipt_3_9_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 0 128 = 12783271256246297426094176 := by decide +kernel
private theorem receipt_3_9_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 128 128 = 7853691224050905671047264 := by decide +kernel
private theorem receipt_3_9_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 256 128 = 3651980568377548506777696 := by decide +kernel
private theorem receipt_3_9_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 384 73 = 499384296438677969568654 := by decide +kernel
private theorem receipt_3_9_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 0 256 = 20636962480297203097141440 :=
  phaseBlock_append receipt_3_9_2360_1_part0 receipt_3_9_2360_1_part1 rfl rfl rfl
private theorem receipt_3_9_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 256 201 = 4151364864816226476346350 :=
  phaseBlock_append receipt_3_9_2360_1_part2 receipt_3_9_2360_1_part3 rfl rfl rfl
private theorem receipt_3_9_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2380 10 1 1 1 1) 0 457 = 24788327345113429573487790 :=
  phaseBlock_append receipt_3_9_2360_1_join0 receipt_3_9_2360_1_join1 rfl rfl rfl

private theorem receipt_3_9_2360_1 : fastPhase (bank 3 9).shape 179808 2380 10 1 1 1 1 = 24788327345113429573487790 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2360_1_join2

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2359_0 receipt_3_9_2359_1 receipt_3_9_2360_0 receipt_3_9_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 0 128 = 1642335482417291310130250688 := by decide +kernel
private theorem receipt_0_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 128 128 = 1274241730444061453594158016 := by decide +kernel
private theorem receipt_0_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 256 128 = 936184631863720156306146240 := by decide +kernel
private theorem receipt_0_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 384 128 = 626884365616747774999495158 := by decide +kernel
private theorem receipt_0_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 512 128 = 345066684716284789713347066 := by decide +kernel
private theorem receipt_0_10_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 640 111 = 91391714297434077450653352 := by decide +kernel
private theorem receipt_0_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 128 256 = 2210426362307781609900304256 :=
  phaseBlock_append receipt_0_10_2359_0_part1 receipt_0_10_2359_0_part2 rfl rfl rfl
private theorem receipt_0_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 0 384 = 3852761844725072920030554944 :=
  phaseBlock_append receipt_0_10_2359_0_part0 receipt_0_10_2359_0_join0 rfl rfl rfl
private theorem receipt_0_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 512 239 = 436458399013718867164000418 :=
  phaseBlock_append receipt_0_10_2359_0_part4 receipt_0_10_2359_0_part5 rfl rfl rfl
private theorem receipt_0_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 384 367 = 1063342764630466642163495576 :=
  phaseBlock_append receipt_0_10_2359_0_part3 receipt_0_10_2359_0_join2 rfl rfl rfl
private theorem receipt_0_10_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 0) 0 751 = 4916104609355539562194050520 :=
  phaseBlock_append receipt_0_10_2359_0_join1 receipt_0_10_2359_0_join3 rfl rfl rfl

private theorem receipt_0_10_2359_0 : fastPhase (bank 0 10).shape 179808 2379 20 1 0 1 0 = 4916104609355539562194050520 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2359_0_join4

private theorem receipt_0_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 0 128 = 1639379438269478321638161920 := by decide +kernel
private theorem receipt_0_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 128 128 = 1271517267213133607329119744 := by decide +kernel
private theorem receipt_0_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 256 128 = 933682057460602692460101120 := by decide +kernel
private theorem receipt_0_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 384 128 = 624594025884766576012919014 := by decide +kernel
private theorem receipt_0_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 512 128 = 342978959357033478127958988 := by decide +kernel
private theorem receipt_0_10_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 640 111 = 89737881146788119755732442 := by decide +kernel
private theorem receipt_0_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 128 256 = 2205199324673736299789220864 :=
  phaseBlock_append receipt_0_10_2359_1_part1 receipt_0_10_2359_1_part2 rfl rfl rfl
private theorem receipt_0_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 0 384 = 3844578762943214621427382784 :=
  phaseBlock_append receipt_0_10_2359_1_part0 receipt_0_10_2359_1_join0 rfl rfl rfl
private theorem receipt_0_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 512 239 = 432716840503821597883691430 :=
  phaseBlock_append receipt_0_10_2359_1_part4 receipt_0_10_2359_1_part5 rfl rfl rfl
private theorem receipt_0_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 384 367 = 1057310866388588173896610444 :=
  phaseBlock_append receipt_0_10_2359_1_part3 receipt_0_10_2359_1_join2 rfl rfl rfl
private theorem receipt_0_10_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2379 20 1 0 1 1) 0 751 = 4901889629331802795323993228 :=
  phaseBlock_append receipt_0_10_2359_1_join1 receipt_0_10_2359_1_join3 rfl rfl rfl

private theorem receipt_0_10_2359_1 : fastPhase (bank 0 10).shape 179808 2379 20 1 0 1 1 = 4901889629331802795323993228 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2359_1_join4

private theorem receipt_0_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 0 128 = 1642350022077338880731836416 := by decide +kernel
private theorem receipt_0_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 128 128 = 1274251842692112409489788928 := by decide +kernel
private theorem receipt_0_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 256 128 = 936191155658582458414510080 := by decide +kernel
private theorem receipt_0_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 384 128 = 626888095278170825049780508 := by decide +kernel
private theorem receipt_0_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 512 128 = 345068366519235064877767897 := by decide +kernel
private theorem receipt_0_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 640 111 = 91392068918163617977924125 := by decide +kernel
private theorem receipt_0_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 128 256 = 2210442998350694867904299008 :=
  phaseBlock_append receipt_0_10_2360_0_part1 receipt_0_10_2360_0_part2 rfl rfl rfl
private theorem receipt_0_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 0 384 = 3852793020428033748636135424 :=
  phaseBlock_append receipt_0_10_2360_0_part0 receipt_0_10_2360_0_join0 rfl rfl rfl
private theorem receipt_0_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 512 239 = 436460435437398682855692022 :=
  phaseBlock_append receipt_0_10_2360_0_part4 receipt_0_10_2360_0_part5 rfl rfl rfl
private theorem receipt_0_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 384 367 = 1063348530715569507905472530 :=
  phaseBlock_append receipt_0_10_2360_0_part3 receipt_0_10_2360_0_join2 rfl rfl rfl
private theorem receipt_0_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 0) 0 751 = 4916141551143603256541607954 :=
  phaseBlock_append receipt_0_10_2360_0_join1 receipt_0_10_2360_0_join3 rfl rfl rfl

private theorem receipt_0_10_2360_0 : fastPhase (bank 0 10).shape 179808 2380 20 1 0 1 0 = 4916141551143603256541607954 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2360_0_join4

private theorem receipt_0_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 0 128 = 1639393956538876183593940480 := by decide +kernel
private theorem receipt_0_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 128 128 = 1271527361411181395559618048 := by decide +kernel
private theorem receipt_0_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 256 128 = 933688566337532056628639232 := by decide +kernel
private theorem receipt_0_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 384 128 = 624597743554651589745962186 := by decide +kernel
private theorem receipt_0_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 512 128 = 342980631918175601532022389 := by decide +kernel
private theorem receipt_0_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 640 111 = 89738229821358557096211509 := by decide +kernel
private theorem receipt_0_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 128 256 = 2205215927748713452188257280 :=
  phaseBlock_append receipt_0_10_2360_1_part1 receipt_0_10_2360_1_part2 rfl rfl rfl
private theorem receipt_0_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 0 384 = 3844609884287589635782197760 :=
  phaseBlock_append receipt_0_10_2360_1_part0 receipt_0_10_2360_1_join0 rfl rfl rfl
private theorem receipt_0_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 512 239 = 432718861739534158628233898 :=
  phaseBlock_append receipt_0_10_2360_1_part4 receipt_0_10_2360_1_part5 rfl rfl rfl
private theorem receipt_0_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 384 367 = 1057316605294185748374196084 :=
  phaseBlock_append receipt_0_10_2360_1_part3 receipt_0_10_2360_1_join2 rfl rfl rfl
private theorem receipt_0_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2380 20 1 0 1 1) 0 751 = 4901926489581775384156393844 :=
  phaseBlock_append receipt_0_10_2360_1_join1 receipt_0_10_2360_1_join3 rfl rfl rfl

private theorem receipt_0_10_2360_1 : fastPhase (bank 0 10).shape 179808 2380 20 1 0 1 1 = 4901926489581775384156393844 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2360_1_join4

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2359_0 receipt_0_10_2359_1 receipt_0_10_2360_0 receipt_0_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 0 128 = 1464694086607828994912759360 := by decide +kernel
private theorem receipt_1_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 128 128 = 1135114831207209580471668288 := by decide +kernel
private theorem receipt_1_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 256 128 = 833014690133228753033064000 := by decide +kernel
private theorem receipt_1_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 384 128 = 557164396521363765052175053 := by decide +kernel
private theorem receipt_1_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 512 128 = 306344796611593944049837325 := by decide +kernel
private theorem receipt_1_10_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 640 111 = 81056172148456142442928623 := by decide +kernel
private theorem receipt_1_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 128 256 = 1968129521340438333504732288 :=
  phaseBlock_append receipt_1_10_2359_0_part1 receipt_1_10_2359_0_part2 rfl rfl rfl
private theorem receipt_1_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 0 384 = 3432823607948267328417491648 :=
  phaseBlock_append receipt_1_10_2359_0_part0 receipt_1_10_2359_0_join0 rfl rfl rfl
private theorem receipt_1_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 512 239 = 387400968760050086492765948 :=
  phaseBlock_append receipt_1_10_2359_0_part4 receipt_1_10_2359_0_part5 rfl rfl rfl
private theorem receipt_1_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 384 367 = 944565365281413851544941001 :=
  phaseBlock_append receipt_1_10_2359_0_part3 receipt_1_10_2359_0_join2 rfl rfl rfl
private theorem receipt_1_10_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 0) 0 751 = 4377388973229681179962432649 :=
  phaseBlock_append receipt_1_10_2359_0_join1 receipt_1_10_2359_0_join3 rfl rfl rfl

private theorem receipt_1_10_2359_0 : fastPhase (bank 1 10).shape 179808 2379 20 1 0 2 0 = 4377388973229681179962432649 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2359_0_join4

private theorem receipt_1_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 0 128 = 1462044707830858662971932800 := by decide +kernel
private theorem receipt_1_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 128 128 = 1132677707723885186829893760 := by decide +kernel
private theorem receipt_1_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 256 128 = 830780487471404355820716160 := by decide +kernel
private theorem receipt_1_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 384 128 = 555123853317711117462175740 := by decide +kernel
private theorem receipt_1_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 512 128 = 304488720841302465403161803 := by decide +kernel
private theorem receipt_1_10_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 640 111 = 79588888922518357881352458 := by decide +kernel
private theorem receipt_1_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 128 256 = 1963458195195289542650609920 :=
  phaseBlock_append receipt_1_10_2359_1_part1 receipt_1_10_2359_1_part2 rfl rfl rfl
private theorem receipt_1_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 0 384 = 3425502903026148205622542720 :=
  phaseBlock_append receipt_1_10_2359_1_part0 receipt_1_10_2359_1_join0 rfl rfl rfl
private theorem receipt_1_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 512 239 = 384077609763820823284514261 :=
  phaseBlock_append receipt_1_10_2359_1_part4 receipt_1_10_2359_1_part5 rfl rfl rfl
private theorem receipt_1_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 384 367 = 939201463081531940746690001 :=
  phaseBlock_append receipt_1_10_2359_1_part3 receipt_1_10_2359_1_join2 rfl rfl rfl
private theorem receipt_1_10_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2379 20 1 0 2 1) 0 751 = 4364704366107680146369232721 :=
  phaseBlock_append receipt_1_10_2359_1_join1 receipt_1_10_2359_1_join3 rfl rfl rfl

private theorem receipt_1_10_2359_1 : fastPhase (bank 1 10).shape 179808 2379 20 1 0 2 1 = 4364704366107680146369232721 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2359_1_join4

private theorem receipt_1_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 0 128 = 1464707053726690105152191520 := by decide +kernel
private theorem receipt_1_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 128 128 = 1135123839461235670296382496 := by decide +kernel
private theorem receipt_1_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 256 128 = 833020495068524670822341664 := by decide +kernel
private theorem receipt_1_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 384 128 = 557167711438383353648686942 := by decide +kernel
private theorem receipt_1_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 512 128 = 306346289721951949144003161 := by decide +kernel
private theorem receipt_1_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 640 111 = 81056486669626111696516225 := by decide +kernel
private theorem receipt_1_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 128 256 = 1968144334529760341118724160 :=
  phaseBlock_append receipt_1_10_2360_0_part1 receipt_1_10_2360_0_part2 rfl rfl rfl
private theorem receipt_1_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 0 384 = 3432851388256450446270915680 :=
  phaseBlock_append receipt_1_10_2360_0_part0 receipt_1_10_2360_0_join0 rfl rfl rfl
private theorem receipt_1_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 512 239 = 387402776391578060840519386 :=
  phaseBlock_append receipt_1_10_2360_0_part4 receipt_1_10_2360_0_part5 rfl rfl rfl
private theorem receipt_1_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 384 367 = 944570487829961414489206328 :=
  phaseBlock_append receipt_1_10_2360_0_part3 receipt_1_10_2360_0_join2 rfl rfl rfl
private theorem receipt_1_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 0) 0 751 = 4377421876086411860760122008 :=
  phaseBlock_append receipt_1_10_2360_0_join1 receipt_1_10_2360_0_join3 rfl rfl rfl

private theorem receipt_1_10_2360_0 : fastPhase (bank 1 10).shape 179808 2380 20 1 0 2 0 = 4377421876086411860760122008 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2360_0_join4

private theorem receipt_1_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 0 128 = 1462057655756791920086897184 := by decide +kernel
private theorem receipt_1_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 128 128 = 1132686699818069080622359072 := by decide +kernel
private theorem receipt_1_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 256 128 = 830786279080843264325415456 := by decide +kernel
private theorem receipt_1_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 384 128 = 555127157547320790790682260 := by decide +kernel
private theorem receipt_1_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 512 128 = 304490205733916024302599703 := by decide +kernel
private theorem receipt_1_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 640 111 = 79589198167939659072120132 := by decide +kernel
private theorem receipt_1_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 128 256 = 1963472978898912344947774528 :=
  phaseBlock_append receipt_1_10_2360_1_part1 receipt_1_10_2360_1_part2 rfl rfl rfl
private theorem receipt_1_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 0 384 = 3425530634655704265034671712 :=
  phaseBlock_append receipt_1_10_2360_1_part0 receipt_1_10_2360_1_join0 rfl rfl rfl
private theorem receipt_1_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 512 239 = 384079403901855683374719835 :=
  phaseBlock_append receipt_1_10_2360_1_part4 receipt_1_10_2360_1_part5 rfl rfl rfl
private theorem receipt_1_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 384 367 = 939206561449176474165402095 :=
  phaseBlock_append receipt_1_10_2360_1_part3 receipt_1_10_2360_1_join2 rfl rfl rfl
private theorem receipt_1_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2380 20 1 0 2 1) 0 751 = 4364737196104880739200073807 :=
  phaseBlock_append receipt_1_10_2360_1_join1 receipt_1_10_2360_1_join3 rfl rfl rfl

private theorem receipt_1_10_2360_1 : fastPhase (bank 1 10).shape 179808 2380 20 1 0 2 1 = 4364737196104880739200073807 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2360_1_join4

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2359_0 receipt_1_10_2359_1 receipt_1_10_2360_0 receipt_1_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 0 128 = 733751773343030973185641280 := by decide +kernel
private theorem receipt_2_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 128 128 = 563790465116762864905743168 := by decide +kernel
private theorem receipt_2_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 256 128 = 410194687440995318672919360 := by decide +kernel
private theorem receipt_2_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 384 128 = 272003110858148395217795023 := by decide +kernel
private theorem receipt_2_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 512 128 = 148281694056785259173799960 := by decide +kernel
private theorem receipt_2_10_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 640 111 = 38939680144679144397200963 := by decide +kernel
private theorem receipt_2_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 128 256 = 973985152557758183578662528 :=
  phaseBlock_append receipt_2_10_2359_0_part1 receipt_2_10_2359_0_part2 rfl rfl rfl
private theorem receipt_2_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 0 384 = 1707736925900789156764303808 :=
  phaseBlock_append receipt_2_10_2359_0_part0 receipt_2_10_2359_0_join0 rfl rfl rfl
private theorem receipt_2_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 512 239 = 187221374201464403571000923 :=
  phaseBlock_append receipt_2_10_2359_0_part4 receipt_2_10_2359_0_part5 rfl rfl rfl
private theorem receipt_2_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 384 367 = 459224485059612798788795946 :=
  phaseBlock_append receipt_2_10_2359_0_part3 receipt_2_10_2359_0_join2 rfl rfl rfl
private theorem receipt_2_10_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 0) 0 751 = 2166961410960401955553099754 :=
  phaseBlock_append receipt_2_10_2359_0_join1 receipt_2_10_2359_0_join3 rfl rfl rfl

private theorem receipt_2_10_2359_0 : fastPhase (bank 2 10).shape 179808 2379 20 1 0 7 0 = 2166961410960401955553099754 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2359_0_join4

private theorem receipt_2_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 0 128 = 732375599265687880564987520 := by decide +kernel
private theorem receipt_2_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 128 128 = 562542209532927984573978240 := by decide +kernel
private theorem receipt_2_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 256 128 = 409066947355388806670014080 := by decide +kernel
private theorem receipt_2_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 384 128 = 270988690624381955323425355 := by decide +kernel
private theorem receipt_2_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 512 128 = 147373601273721064331901308 := by decide +kernel
private theorem receipt_2_10_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 640 111 = 38233015320441879649155423 := by decide +kernel
private theorem receipt_2_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 128 256 = 971609156888316791243992320 :=
  phaseBlock_append receipt_2_10_2359_1_part1 receipt_2_10_2359_1_part2 rfl rfl rfl
private theorem receipt_2_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 0 384 = 1703984756154004671808979840 :=
  phaseBlock_append receipt_2_10_2359_1_part0 receipt_2_10_2359_1_join0 rfl rfl rfl
private theorem receipt_2_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 512 239 = 185606616594162943981056731 :=
  phaseBlock_append receipt_2_10_2359_1_part4 receipt_2_10_2359_1_part5 rfl rfl rfl
private theorem receipt_2_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 384 367 = 456595307218544899304482086 :=
  phaseBlock_append receipt_2_10_2359_1_part3 receipt_2_10_2359_1_join2 rfl rfl rfl
private theorem receipt_2_10_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2379 20 1 0 7 1) 0 751 = 2160580063372549571113461926 :=
  phaseBlock_append receipt_2_10_2359_1_join1 receipt_2_10_2359_1_join3 rfl rfl rfl

private theorem receipt_2_10_2359_1 : fastPhase (bank 2 10).shape 179808 2379 20 1 0 7 1 = 2160580063372549571113461926 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2359_1_join4

private theorem receipt_2_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 0 128 = 733758269806775343408412960 := by decide +kernel
private theorem receipt_2_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 128 128 = 563794939731210429348538656 := by decide +kernel
private theorem receipt_2_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 256 128 = 410197546213101717797984544 := by decide +kernel
private theorem receipt_2_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 384 128 = 272004729380850629748814292 := by decide +kernel
private theorem receipt_2_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 512 128 = 148282416893093466767716611 := by decide +kernel
private theorem receipt_2_10_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 640 111 = 38939831259088657879257955 := by decide +kernel
private theorem receipt_2_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 128 256 = 973992485944312147146523200 :=
  phaseBlock_append receipt_2_10_2360_0_part1 receipt_2_10_2360_0_part2 rfl rfl rfl
private theorem receipt_2_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 0 384 = 1707750755751087490554936160 :=
  phaseBlock_append receipt_2_10_2360_0_part0 receipt_2_10_2360_0_join0 rfl rfl rfl
private theorem receipt_2_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 512 239 = 187222248152182124646974566 :=
  phaseBlock_append receipt_2_10_2360_0_part4 receipt_2_10_2360_0_part5 rfl rfl rfl
private theorem receipt_2_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 384 367 = 459226977533032754395788858 :=
  phaseBlock_append receipt_2_10_2360_0_part3 receipt_2_10_2360_0_join2 rfl rfl rfl
private theorem receipt_2_10_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 0) 0 751 = 2166977733284120244950725018 :=
  phaseBlock_append receipt_2_10_2360_0_join1 receipt_2_10_2360_0_join3 rfl rfl rfl

private theorem receipt_2_10_2360_0 : fastPhase (bank 2 10).shape 179808 2380 20 1 0 7 0 = 2166977733284120244950725018 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2360_0_join4

private theorem receipt_2_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 0 128 = 732382085680312583275605664 := by decide +kernel
private theorem receipt_2_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 128 128 = 562546675820359249858944672 := by decide +kernel
private theorem receipt_2_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 256 128 = 409069799372589280594874016 := by decide +kernel
private theorem receipt_2_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 384 128 = 270990303820232667880579475 := by decide +kernel
private theorem receipt_2_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 512 128 = 147374320084347255595784998 := by decide +kernel
private theorem receipt_2_10_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 640 111 = 38233163892843940185403392 := by decide +kernel
private theorem receipt_2_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 128 256 = 971616475192948530453818688 :=
  phaseBlock_append receipt_2_10_2360_1_part1 receipt_2_10_2360_1_part2 rfl rfl rfl
private theorem receipt_2_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 0 384 = 1703998560873261113729424352 :=
  phaseBlock_append receipt_2_10_2360_1_part0 receipt_2_10_2360_1_join0 rfl rfl rfl
private theorem receipt_2_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 512 239 = 185607483977191195781188390 :=
  phaseBlock_append receipt_2_10_2360_1_part4 receipt_2_10_2360_1_part5 rfl rfl rfl
private theorem receipt_2_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 384 367 = 456597787797423863661767865 :=
  phaseBlock_append receipt_2_10_2360_1_part3 receipt_2_10_2360_1_join2 rfl rfl rfl
private theorem receipt_2_10_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2380 20 1 0 7 1) 0 751 = 2160596348670684977391192217 :=
  phaseBlock_append receipt_2_10_2360_1_join1 receipt_2_10_2360_1_join3 rfl rfl rfl

private theorem receipt_2_10_2360_1 : fastPhase (bank 2 10).shape 179808 2380 20 1 0 7 1 = 2160596348670684977391192217 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2360_1_join4

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2359_0 receipt_2_10_2359_1 receipt_2_10_2360_0 receipt_2_10_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 0 128 = 68436769393051426553775680 := by decide +kernel
private theorem receipt_3_10_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 128 128 = 47821963602750842587039296 := by decide +kernel
private theorem receipt_3_10_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 256 128 = 29397517589610145612613184 := by decide +kernel
private theorem receipt_3_10_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 384 128 = 13302107489006587388216896 := by decide +kernel
private theorem receipt_3_10_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 512 59 = 1388074534595111843180390 := by decide +kernel
private theorem receipt_3_10_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 0 256 = 116258732995802269140814976 :=
  phaseBlock_append receipt_3_10_2359_0_part0 receipt_3_10_2359_0_part1 rfl rfl rfl
private theorem receipt_3_10_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 384 187 = 14690182023601699231397286 :=
  phaseBlock_append receipt_3_10_2359_0_part3 receipt_3_10_2359_0_part4 rfl rfl rfl
private theorem receipt_3_10_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 256 315 = 44087699613211844844010470 :=
  phaseBlock_append receipt_3_10_2359_0_part2 receipt_3_10_2359_0_join1 rfl rfl rfl
private theorem receipt_3_10_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 0) 0 571 = 160346432609014113984825446 :=
  phaseBlock_append receipt_3_10_2359_0_join0 receipt_3_10_2359_0_join2 rfl rfl rfl

private theorem receipt_3_10_2359_0 : fastPhase (bank 3 10).shape 179808 2379 20 1 1 1 0 = 160346432609014113984825446 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2359_0_join3

private theorem receipt_3_10_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 0 128 = 68269623330595322590921472 := by decide +kernel
private theorem receipt_3_10_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 128 128 = 47670744256431359490024192 := by decide +kernel
private theorem receipt_3_10_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 256 128 = 29263404475546852354474752 := by decide +kernel
private theorem receipt_3_10_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 384 128 = 13186262619090714838246144 := by decide +kernel
private theorem receipt_3_10_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 512 59 = 1341144996128158752204476 := by decide +kernel
private theorem receipt_3_10_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 0 256 = 115940367587026682080945664 :=
  phaseBlock_append receipt_3_10_2359_1_part0 receipt_3_10_2359_1_part1 rfl rfl rfl
private theorem receipt_3_10_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 384 187 = 14527407615218873590450620 :=
  phaseBlock_append receipt_3_10_2359_1_part3 receipt_3_10_2359_1_part4 rfl rfl rfl
private theorem receipt_3_10_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 256 315 = 43790812090765725944925372 :=
  phaseBlock_append receipt_3_10_2359_1_part2 receipt_3_10_2359_1_join1 rfl rfl rfl
private theorem receipt_3_10_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2379 20 1 1 1 1) 0 571 = 159731179677792408025871036 :=
  phaseBlock_append receipt_3_10_2359_1_join0 receipt_3_10_2359_1_join2 rfl rfl rfl

private theorem receipt_3_10_2359_1 : fastPhase (bank 3 10).shape 179808 2379 20 1 1 1 1 = 159731179677792408025871036 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2359_1_join3

private theorem receipt_3_10_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 0 128 = 68437338144197945940932512 := by decide +kernel
private theorem receipt_3_10_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 128 128 = 47822269671677632427624352 := by decide +kernel
private theorem receipt_3_10_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 256 128 = 29397652069836458488928160 := by decide +kernel
private theorem receipt_3_10_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 384 128 = 13302145628714979472222112 := by decide +kernel
private theorem receipt_3_10_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 512 59 = 1388076717910396364693869 := by decide +kernel
private theorem receipt_3_10_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 0 256 = 116259607815875578368556864 :=
  phaseBlock_append receipt_3_10_2360_0_part0 receipt_3_10_2360_0_part1 rfl rfl rfl
private theorem receipt_3_10_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 384 187 = 14690222346625375836915981 :=
  phaseBlock_append receipt_3_10_2360_0_part3 receipt_3_10_2360_0_part4 rfl rfl rfl
private theorem receipt_3_10_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 256 315 = 44087874416461834325844141 :=
  phaseBlock_append receipt_3_10_2360_0_part2 receipt_3_10_2360_0_join1 rfl rfl rfl
private theorem receipt_3_10_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 0) 0 571 = 160347482232337412694401005 :=
  phaseBlock_append receipt_3_10_2360_0_join0 receipt_3_10_2360_0_join2 rfl rfl rfl

private theorem receipt_3_10_2360_0 : fastPhase (bank 3 10).shape 179808 2380 20 1 1 1 0 = 160347482232337412694401005 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2360_0_join3

private theorem receipt_3_10_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 0 128 = 68270190490842495386413600 := by decide +kernel
private theorem receipt_3_10_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 128 128 = 47671049237999690430077472 := by decide +kernel
private theorem receipt_3_10_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 256 128 = 29263538284283069573974560 := by decide +kernel
private theorem receipt_3_10_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 384 128 = 13186300416767396500584992 := by decide +kernel
private theorem receipt_3_10_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 512 59 = 1341147109151103848766469 := by decide +kernel
private theorem receipt_3_10_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 0 256 = 115941239728842185816491072 :=
  phaseBlock_append receipt_3_10_2360_1_part0 receipt_3_10_2360_1_part1 rfl rfl rfl
private theorem receipt_3_10_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 384 187 = 14527447525918500349351461 :=
  phaseBlock_append receipt_3_10_2360_1_part3 receipt_3_10_2360_1_part4 rfl rfl rfl
private theorem receipt_3_10_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 256 315 = 43790985810201569923326021 :=
  phaseBlock_append receipt_3_10_2360_1_part2 receipt_3_10_2360_1_join1 rfl rfl rfl
private theorem receipt_3_10_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2380 20 1 1 1 1) 0 571 = 159732225539043755739817093 :=
  phaseBlock_append receipt_3_10_2360_1_join0 receipt_3_10_2360_1_join2 rfl rfl rfl

private theorem receipt_3_10_2360_1 : fastPhase (bank 3 10).shape 179808 2380 20 1 1 1 1 = 159732225539043755739817093 :=
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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group3_stage i)).shape
      (cutoff h rect (group3_stage i)), ¬ G∣Q :=
  (group3_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group3_avoids

end Lower6960.RescueSource
