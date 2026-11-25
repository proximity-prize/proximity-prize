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

private theorem receipt_0_8_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 0 128 = 525900490587702221348072768 := by decide +kernel
private theorem receipt_0_8_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 128 128 = 368271974502900841925119296 := by decide +kernel
private theorem receipt_0_8_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 256 128 = 227227340297852532254167012 := by decide +kernel
private theorem receipt_0_8_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 384 128 = 101848356085354616590566912 := by decide +kernel
private theorem receipt_0_8_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 512 52 = 8972677984614644789311758 := by decide +kernel
private theorem receipt_0_8_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 0 256 = 894172465090603063273192064 :=
  phaseBlock_append receipt_0_8_2383_0_part0 receipt_0_8_2383_0_part1 rfl rfl rfl
private theorem receipt_0_8_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 384 180 = 110821034069969261379878670 :=
  phaseBlock_append receipt_0_8_2383_0_part3 receipt_0_8_2383_0_part4 rfl rfl rfl
private theorem receipt_0_8_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 256 308 = 338048374367821793634045682 :=
  phaseBlock_append receipt_0_8_2383_0_part2 receipt_0_8_2383_0_join1 rfl rfl rfl
private theorem receipt_0_8_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 0) 0 564 = 1232220839458424856907237746 :=
  phaseBlock_append receipt_0_8_2383_0_join0 receipt_0_8_2383_0_join2 rfl rfl rfl

private theorem receipt_0_8_2383_0 : fastPhase (bank 0 8).shape 179808 2383 16 1 0 1 0 = 1232220839458424856907237746 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2383_0_join3

private theorem receipt_0_8_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 0 128 = 524618575872981829628508800 := by decide +kernel
private theorem receipt_0_8_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 128 128 = 367118701697651197971069568 := by decide +kernel
private theorem receipt_0_8_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 256 128 = 226195752646286494664867324 := by decide +kernel
private theorem receipt_0_8_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 384 128 = 100931526880716302587322350 := by decide +kernel
private theorem receipt_0_8_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 512 52 = 8631414368580962672496770 := by decide +kernel
private theorem receipt_0_8_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 0 256 = 891737277570633027599578368 :=
  phaseBlock_append receipt_0_8_2383_1_part0 receipt_0_8_2383_1_part1 rfl rfl rfl
private theorem receipt_0_8_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 384 180 = 109562941249297265259819120 :=
  phaseBlock_append receipt_0_8_2383_1_part3 receipt_0_8_2383_1_part4 rfl rfl rfl
private theorem receipt_0_8_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 256 308 = 335758693895583759924686444 :=
  phaseBlock_append receipt_0_8_2383_1_part2 receipt_0_8_2383_1_join1 rfl rfl rfl
private theorem receipt_0_8_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2383 16 1 0 1 1) 0 564 = 1227495971466216787524264812 :=
  phaseBlock_append receipt_0_8_2383_1_join0 receipt_0_8_2383_1_join2 rfl rfl rfl

private theorem receipt_0_8_2383_1 : fastPhase (bank 0 8).shape 179808 2383 16 1 0 1 1 = 1227495971466216787524264812 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2383_1_join3

private theorem receipt_0_8_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 0 128 = 525905048071476954859481568 := by decide +kernel
private theorem receipt_0_8_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 128 128 = 368274728009125218449750496 := by decide +kernel
private theorem receipt_0_8_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 256 128 = 227228751399898984222085004 := by decide +kernel
private theorem receipt_0_8_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 384 128 = 101848853252145555015071637 := by decide +kernel
private theorem receipt_0_8_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 512 52 = 8972712006379614566170422 := by decide +kernel
private theorem receipt_0_8_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 0 256 = 894179776080602173309232064 :=
  phaseBlock_append receipt_0_8_2384_0_part0 receipt_0_8_2384_0_part1 rfl rfl rfl
private theorem receipt_0_8_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 384 180 = 110821565258525169581242059 :=
  phaseBlock_append receipt_0_8_2384_0_part3 receipt_0_8_2384_0_part4 rfl rfl rfl
private theorem receipt_0_8_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 256 308 = 338050316658424153803327063 :=
  phaseBlock_append receipt_0_8_2384_0_part2 receipt_0_8_2384_0_join1 rfl rfl rfl
private theorem receipt_0_8_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 0) 0 564 = 1232230092739026327112559127 :=
  phaseBlock_append receipt_0_8_2384_0_join0 receipt_0_8_2384_0_join2 rfl rfl rfl

private theorem receipt_0_8_2384_0 : fastPhase (bank 0 8).shape 179808 2384 16 1 0 1 0 = 1232230092739026327112559127 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2384_0_join3

private theorem receipt_0_8_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 0 128 = 524623124192222563151287392 := by decide +kernel
private theorem receipt_0_8_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 128 128 = 367121447884922382155572320 := by decide +kernel
private theorem receipt_0_8_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 256 128 = 226197158125534627667131664 := by decide +kernel
private theorem receipt_0_8_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 384 128 = 100932019986741395513483824 := by decide +kernel
private theorem receipt_0_8_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 512 52 = 8631447154083886502360120 := by decide +kernel
private theorem receipt_0_8_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 0 256 = 891744572077144945306859712 :=
  phaseBlock_append receipt_0_8_2384_1_part0 receipt_0_8_2384_1_part1 rfl rfl rfl
private theorem receipt_0_8_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 384 180 = 109563467140825282015843944 :=
  phaseBlock_append receipt_0_8_2384_1_part3 receipt_0_8_2384_1_part4 rfl rfl rfl
private theorem receipt_0_8_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 256 308 = 335760625266359909682975608 :=
  phaseBlock_append receipt_0_8_2384_1_part2 receipt_0_8_2384_1_join1 rfl rfl rfl
private theorem receipt_0_8_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179808 2384 16 1 0 1 1) 0 564 = 1227505197343504854989835320 :=
  phaseBlock_append receipt_0_8_2384_1_join0 receipt_0_8_2384_1_join2 rfl rfl rfl

private theorem receipt_0_8_2384_1 : fastPhase (bank 0 8).shape 179808 2384 16 1 0 1 1 = 1227505197343504854989835320 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2384_1_join3

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2383_0 receipt_0_8_2383_1 receipt_0_8_2384_0 receipt_0_8_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 0 128 = 473111456666138726615448512 := by decide +kernel
private theorem receipt_1_8_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 128 128 = 330865068384892851516480448 := by decide +kernel
private theorem receipt_1_8_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 256 128 = 203877153674444523143883222 := by decide +kernel
private theorem receipt_1_8_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 384 128 = 91265305858759287992837631 := by decide +kernel
private theorem receipt_1_8_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 512 52 = 8032398407887253456427813 := by decide +kernel
private theorem receipt_1_8_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 0 256 = 803976525051031578131928960 :=
  phaseBlock_append receipt_1_8_2383_0_part0 receipt_1_8_2383_0_part1 rfl rfl rfl
private theorem receipt_1_8_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 384 180 = 99297704266646541449265444 :=
  phaseBlock_append receipt_1_8_2383_0_part3 receipt_1_8_2383_0_part4 rfl rfl rfl
private theorem receipt_1_8_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 256 308 = 303174857941091064593148666 :=
  phaseBlock_append receipt_1_8_2383_0_part2 receipt_1_8_2383_0_join1 rfl rfl rfl
private theorem receipt_1_8_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 0) 0 564 = 1107151382992122642725077626 :=
  phaseBlock_append receipt_1_8_2383_0_join0 receipt_1_8_2383_0_join2 rfl rfl rfl

private theorem receipt_1_8_2383_0 : fastPhase (bank 1 8).shape 179808 2383 16 1 0 2 0 = 1107151382992122642725077626 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2383_0_join3

private theorem receipt_1_8_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 0 128 = 471953309622811737180232704 := by decide +kernel
private theorem receipt_1_8_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 128 128 = 329825516466322981678701568 := by decide +kernel
private theorem receipt_1_8_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 256 128 = 202949491577320282587414066 := by decide +kernel
private theorem receipt_1_8_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 384 128 = 90442888523913280160575530 := by decide +kernel
private theorem receipt_1_8_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 512 52 = 7726842557851347868321410 := by decide +kernel
private theorem receipt_1_8_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 0 256 = 801778826089134718858934272 :=
  phaseBlock_append receipt_1_8_2383_1_part0 receipt_1_8_2383_1_part1 rfl rfl rfl
private theorem receipt_1_8_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 384 180 = 98169731081764628028896940 :=
  phaseBlock_append receipt_1_8_2383_1_part3 receipt_1_8_2383_1_part4 rfl rfl rfl
private theorem receipt_1_8_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 256 308 = 301119222659084910616311006 :=
  phaseBlock_append receipt_1_8_2383_1_part2 receipt_1_8_2383_1_join1 rfl rfl rfl
private theorem receipt_1_8_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2383 16 1 0 2 1) 0 564 = 1102898048748219629475245278 :=
  phaseBlock_append receipt_1_8_2383_1_join0 receipt_1_8_2383_1_join2 rfl rfl rfl

private theorem receipt_1_8_2383_1 : fastPhase (bank 1 8).shape 179808 2383 16 1 0 2 1 = 1102898048748219629475245278 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2383_1_join3

private theorem receipt_1_8_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 0 128 = 473115556737785550892123392 := by decide +kernel
private theorem receipt_1_8_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 128 128 = 330867542251502553988908288 := by decide +kernel
private theorem receipt_1_8_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 256 128 = 203878419799459381912443774 := by decide +kernel
private theorem receipt_1_8_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 384 128 = 91265751378357238489007259 := by decide +kernel
private theorem receipt_1_8_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 512 52 = 8032428864541493772556131 := by decide +kernel
private theorem receipt_1_8_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 0 256 = 803983098989288104881031680 :=
  phaseBlock_append receipt_1_8_2384_0_part0 receipt_1_8_2384_0_part1 rfl rfl rfl
private theorem receipt_1_8_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 384 180 = 99298180242898732261563390 :=
  phaseBlock_append receipt_1_8_2384_0_part3 receipt_1_8_2384_0_part4 rfl rfl rfl
private theorem receipt_1_8_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 256 308 = 303176600042358114174007164 :=
  phaseBlock_append receipt_1_8_2384_0_part2 receipt_1_8_2384_0_join1 rfl rfl rfl
private theorem receipt_1_8_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 0) 0 564 = 1107159699031646219055038844 :=
  phaseBlock_append receipt_1_8_2384_0_join0 receipt_1_8_2384_0_join2 rfl rfl rfl

private theorem receipt_1_8_2384_0 : fastPhase (bank 1 8).shape 179808 2384 16 1 0 2 0 = 1107159699031646219055038844 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2384_0_join3

private theorem receipt_1_8_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 0 128 = 471957401407147704288538752 := by decide +kernel
private theorem receipt_1_8_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 128 128 = 329827983731662679814418560 := by decide +kernel
private theorem receipt_1_8_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 256 128 = 202950752644272448402768650 := by decide +kernel
private theorem receipt_1_8_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 384 128 = 90443330400374195238269202 := by decide +kernel
private theorem receipt_1_8_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 512 52 = 7726871907577535712781470 := by decide +kernel
private theorem receipt_1_8_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 0 256 = 801785385138810384102957312 :=
  phaseBlock_append receipt_1_8_2384_1_part0 receipt_1_8_2384_1_part1 rfl rfl rfl
private theorem receipt_1_8_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 384 180 = 98170202307951730951050672 :=
  phaseBlock_append receipt_1_8_2384_1_part3 receipt_1_8_2384_1_part4 rfl rfl rfl
private theorem receipt_1_8_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 256 308 = 301120954952224179353819322 :=
  phaseBlock_append receipt_1_8_2384_1_part2 receipt_1_8_2384_1_join1 rfl rfl rfl
private theorem receipt_1_8_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179808 2384 16 1 0 2 1) 0 564 = 1102906340091034563456776634 :=
  phaseBlock_append receipt_1_8_2384_1_join0 receipt_1_8_2384_1_join2 rfl rfl rfl

private theorem receipt_1_8_2384_1 : fastPhase (bank 1 8).shape 179808 2384 16 1 0 2 1 = 1102906340091034563456776634 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2384_1_join3

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2383_0 receipt_1_8_2383_1 receipt_1_8_2384_0 receipt_1_8_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 0 128 = 252269782169588858032703552 := by decide +kernel
private theorem receipt_2_8_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 128 128 = 174732562847600379241408576 := by decide +kernel
private theorem receipt_2_8_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 256 128 = 106638547201099281823451640 := by decide +kernel
private theorem receipt_2_8_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 384 128 = 47291485399558830554284722 := by decide +kernel
private theorem receipt_2_8_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 512 52 = 4132119289391449838385930 := by decide +kernel
private theorem receipt_2_8_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 0 256 = 427002345017189237274112128 :=
  phaseBlock_append receipt_2_8_2383_0_part0 receipt_2_8_2383_0_part1 rfl rfl rfl
private theorem receipt_2_8_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 384 180 = 51423604688950280392670652 :=
  phaseBlock_append receipt_2_8_2383_0_part3 receipt_2_8_2383_0_part4 rfl rfl rfl
private theorem receipt_2_8_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 256 308 = 158062151890049562216122292 :=
  phaseBlock_append receipt_2_8_2383_0_part2 receipt_2_8_2383_0_join1 rfl rfl rfl
private theorem receipt_2_8_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 0) 0 564 = 585064496907238799490234420 :=
  phaseBlock_append receipt_2_8_2383_0_join0 receipt_2_8_2383_0_join2 rfl rfl rfl

private theorem receipt_2_8_2383_0 : fastPhase (bank 2 8).shape 179808 2383 16 1 0 7 0 = 585064496907238799490234420 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2383_0_join3

private theorem receipt_2_8_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 0 128 = 251633358246460268781566592 := by decide +kernel
private theorem receipt_2_8_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 128 128 = 174170458362614776254413440 := by decide +kernel
private theorem receipt_2_8_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 256 128 = 106145388692595645344599836 := by decide +kernel
private theorem receipt_2_8_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 384 128 = 46862076819229943244922515 := by decide +kernel
private theorem receipt_2_8_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 512 52 = 3974725278800920141251195 := by decide +kernel
private theorem receipt_2_8_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 0 256 = 425803816609075045035980032 :=
  phaseBlock_append receipt_2_8_2383_1_part0 receipt_2_8_2383_1_part1 rfl rfl rfl
private theorem receipt_2_8_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 384 180 = 50836802098030863386173710 :=
  phaseBlock_append receipt_2_8_2383_1_part3 receipt_2_8_2383_1_part4 rfl rfl rfl
private theorem receipt_2_8_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 256 308 = 156982190790626508730773546 :=
  phaseBlock_append receipt_2_8_2383_1_part2 receipt_2_8_2383_1_join1 rfl rfl rfl
private theorem receipt_2_8_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2383 16 1 0 7 1) 0 564 = 582786007399701553766753578 :=
  phaseBlock_append receipt_2_8_2383_1_join0 receipt_2_8_2383_1_join2 rfl rfl rfl

private theorem receipt_2_8_2383_1 : fastPhase (bank 2 8).shape 179808 2383 16 1 0 7 1 = 582786007399701553766753578 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2383_1_join3

private theorem receipt_2_8_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 0 128 = 252271968619663300252483392 := by decide +kernel
private theorem receipt_2_8_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 128 128 = 174733869490762829528383296 := by decide +kernel
private theorem receipt_2_8_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 256 128 = 106639209564853337622341280 := by decide +kernel
private theorem receipt_2_8_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 384 128 = 47291716307795206145614641 := by decide +kernel
private theorem receipt_2_8_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 512 52 = 4132134957838345429812867 := by decide +kernel
private theorem receipt_2_8_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 0 256 = 427005838110426129780866688 :=
  phaseBlock_append receipt_2_8_2384_0_part0 receipt_2_8_2384_0_part1 rfl rfl rfl
private theorem receipt_2_8_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 384 180 = 51423851265633551575427508 :=
  phaseBlock_append receipt_2_8_2384_0_part3 receipt_2_8_2384_0_part4 rfl rfl rfl
private theorem receipt_2_8_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 256 308 = 158063060830486889197768788 :=
  phaseBlock_append receipt_2_8_2384_0_part2 receipt_2_8_2384_0_join1 rfl rfl rfl
private theorem receipt_2_8_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 0) 0 564 = 585068898940913018978635476 :=
  phaseBlock_append receipt_2_8_2384_0_join0 receipt_2_8_2384_0_join2 rfl rfl rfl

private theorem receipt_2_8_2384_0 : fastPhase (bank 2 8).shape 179808 2384 16 1 0 7 0 = 585068898940913018978635476 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2384_0_join3

private theorem receipt_2_8_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 0 128 = 251635540113361662842034240 := by decide +kernel
private theorem receipt_2_8_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 128 128 = 174171761421003755909421120 := by decide +kernel
private theorem receipt_2_8_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 256 128 = 106146048360844849957767048 := by decide +kernel
private theorem receipt_2_8_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 384 128 = 46862305823244513206698164 := by decide +kernel
private theorem receipt_2_8_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 512 52 = 3974740376981656228970400 := by decide +kernel
private theorem receipt_2_8_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 0 256 = 425807301534365418751455360 :=
  phaseBlock_append receipt_2_8_2384_1_part0 receipt_2_8_2384_1_part1 rfl rfl rfl
private theorem receipt_2_8_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 384 180 = 50837046200226169435668564 :=
  phaseBlock_append receipt_2_8_2384_1_part3 receipt_2_8_2384_1_part4 rfl rfl rfl
private theorem receipt_2_8_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 256 308 = 156983094561071019393435612 :=
  phaseBlock_append receipt_2_8_2384_1_part2 receipt_2_8_2384_1_join1 rfl rfl rfl
private theorem receipt_2_8_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179808 2384 16 1 0 7 1) 0 564 = 582790396095436438144890972 :=
  phaseBlock_append receipt_2_8_2384_1_join0 receipt_2_8_2384_1_join2 rfl rfl rfl

private theorem receipt_2_8_2384_1 : fastPhase (bank 2 8).shape 179808 2384 16 1 0 7 1 = 582790396095436438144890972 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2384_1_join3

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2383_0 receipt_2_8_2383_1 receipt_2_8_2384_0 receipt_2_8_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 0 128 = 45884153875704668089555392 := by decide +kernel
private theorem receipt_3_8_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 128 128 = 32265447721296306951608768 := by decide +kernel
private theorem receipt_3_8_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 256 128 = 20129301983820966872521152 := by decide +kernel
private theorem receipt_3_8_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 384 128 = 9566255656879894915602880 := by decide +kernel
private theorem receipt_3_8_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 512 73 = 1359766407082377163791828 := by decide +kernel
private theorem receipt_3_8_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 0 256 = 78149601597000975041164160 :=
  phaseBlock_append receipt_3_8_2383_0_part0 receipt_3_8_2383_0_part1 rfl rfl rfl
private theorem receipt_3_8_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 384 201 = 10926022063962272079394708 :=
  phaseBlock_append receipt_3_8_2383_0_part3 receipt_3_8_2383_0_part4 rfl rfl rfl
private theorem receipt_3_8_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 256 329 = 31055324047783238951915860 :=
  phaseBlock_append receipt_3_8_2383_0_part2 receipt_3_8_2383_0_join1 rfl rfl rfl
private theorem receipt_3_8_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 0) 0 585 = 109204925644784213993080020 :=
  phaseBlock_append receipt_3_8_2383_0_join0 receipt_3_8_2383_0_join2 rfl rfl rfl

private theorem receipt_3_8_2383_0 : fastPhase (bank 3 8).shape 179808 2383 16 1 1 1 0 = 109204925644784213993080020 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2383_0_join3

private theorem receipt_3_8_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 0 128 = 45773632078789602226015104 := by decide +kernel
private theorem receipt_3_8_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 128 128 = 32165722002342326390926208 := by decide +kernel
private theorem receipt_3_8_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 256 128 = 20041146453505752134863744 := by decide +kernel
private theorem receipt_3_8_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 384 128 = 9490430138440070994455424 := by decide +kernel
private theorem receipt_3_8_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 512 73 = 1322329989958252554373896 := by decide +kernel
private theorem receipt_3_8_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 0 256 = 77939354081131928616941312 :=
  phaseBlock_append receipt_3_8_2383_1_part0 receipt_3_8_2383_1_part1 rfl rfl rfl
private theorem receipt_3_8_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 384 201 = 10812760128398323548829320 :=
  phaseBlock_append receipt_3_8_2383_1_part3 receipt_3_8_2383_1_part4 rfl rfl rfl
private theorem receipt_3_8_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 256 329 = 30853906581904075683693064 :=
  phaseBlock_append receipt_3_8_2383_1_part2 receipt_3_8_2383_1_join1 rfl rfl rfl
private theorem receipt_3_8_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2383 16 1 1 1 1) 0 585 = 108793260663036004300634376 :=
  phaseBlock_append receipt_3_8_2383_1_join0 receipt_3_8_2383_1_join2 rfl rfl rfl

private theorem receipt_3_8_2383_1 : fastPhase (bank 3 8).shape 179808 2383 16 1 1 1 1 = 108793260663036004300634376 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2383_1_join3

private theorem receipt_3_8_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 0 128 = 45884536175109232358307936 := by decide +kernel
private theorem receipt_3_8_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 128 128 = 32265654151604691550242912 := by decide +kernel
private theorem receipt_3_8_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 256 128 = 20129393552874712094300256 := by decide +kernel
private theorem receipt_3_8_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 384 128 = 9566282551485684349151328 := by decide +kernel
private theorem receipt_3_8_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 512 73 = 1359768387426191896642659 := by decide +kernel
private theorem receipt_3_8_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 0 256 = 78150190326713923908550848 :=
  phaseBlock_append receipt_3_8_2384_0_part0 receipt_3_8_2384_0_part1 rfl rfl rfl
private theorem receipt_3_8_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 384 201 = 10926050938911876245793987 :=
  phaseBlock_append receipt_3_8_2384_0_part3 receipt_3_8_2384_0_part4 rfl rfl rfl
private theorem receipt_3_8_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 256 329 = 31055444491786588340094243 :=
  phaseBlock_append receipt_3_8_2384_0_part2 receipt_3_8_2384_0_join1 rfl rfl rfl
private theorem receipt_3_8_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 0) 0 585 = 109205634818500512248645091 :=
  phaseBlock_append receipt_3_8_2384_0_join0 receipt_3_8_2384_0_join2 rfl rfl rfl

private theorem receipt_3_8_2384_0 : fastPhase (bank 3 8).shape 179808 2384 16 1 1 1 0 = 109205634818500512248645091 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2384_0_join3

private theorem receipt_3_8_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 0 128 = 45774013320357305330428512 := by decide +kernel
private theorem receipt_3_8_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 128 128 = 32165927712936852968987232 := by decide +kernel
private theorem receipt_3_8_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 256 128 = 20041237580956754480515680 := by decide +kernel
private theorem receipt_3_8_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 384 128 = 9490456810583181702806112 := by decide +kernel
private theorem receipt_3_8_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 512 73 = 1322331919286821687712718 := by decide +kernel
private theorem receipt_3_8_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 0 256 = 77939941033294158299415744 :=
  phaseBlock_append receipt_3_8_2384_1_part0 receipt_3_8_2384_1_part1 rfl rfl rfl
private theorem receipt_3_8_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 384 201 = 10812788729870003390518830 :=
  phaseBlock_append receipt_3_8_2384_1_part3 receipt_3_8_2384_1_part4 rfl rfl rfl
private theorem receipt_3_8_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 256 329 = 30854026310826757871034510 :=
  phaseBlock_append receipt_3_8_2384_1_part2 receipt_3_8_2384_1_join1 rfl rfl rfl
private theorem receipt_3_8_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179808 2384 16 1 1 1 1) 0 585 = 108793967344120916170450254 :=
  phaseBlock_append receipt_3_8_2384_1_join0 receipt_3_8_2384_1_join2 rfl rfl rfl

private theorem receipt_3_8_2384_1 : fastPhase (bank 3 8).shape 179808 2384 16 1 1 1 1 = 108793967344120916170450254 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2384_1_join3

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2383_0 receipt_3_8_2383_1 receipt_3_8_2384_0 receipt_3_8_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 0 128 = 135899862166086343263449552 := by decide +kernel
private theorem receipt_0_9_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 128 128 = 82972105393893734695637772 := by decide +kernel
private theorem receipt_0_9_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 256 128 = 37226728862862384299676766 := by decide +kernel
private theorem receipt_0_9_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 384 56 = 3622189677677262350334966 := by decide +kernel
private theorem receipt_0_9_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 0 256 = 218871967559980077959087324 :=
  phaseBlock_append receipt_0_9_2383_0_part0 receipt_0_9_2383_0_part1 rfl rfl rfl
private theorem receipt_0_9_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 256 184 = 40848918540539646650011732 :=
  phaseBlock_append receipt_0_9_2383_0_part2 receipt_0_9_2383_0_part3 rfl rfl rfl
private theorem receipt_0_9_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 0) 0 440 = 259720886100519724609099056 :=
  phaseBlock_append receipt_0_9_2383_0_join0 receipt_0_9_2383_0_join1 rfl rfl rfl

private theorem receipt_0_9_2383_0 : fastPhase (bank 0 9).shape 179808 2383 10 1 0 1 0 = 259720886100519724609099056 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2383_0_join2

private theorem receipt_0_9_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 0 128 = 135462577630674408588947228 := by decide +kernel
private theorem receipt_0_9_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 128 128 = 82590989353533619628169496 := by decide +kernel
private theorem receipt_0_9_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 256 128 = 36897830256435567223652802 := by decide +kernel
private theorem receipt_0_9_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 384 56 = 3493712328644583160910858 := by decide +kernel
private theorem receipt_0_9_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 0 256 = 218053566984208028217116724 :=
  phaseBlock_append receipt_0_9_2383_1_part0 receipt_0_9_2383_1_part1 rfl rfl rfl
private theorem receipt_0_9_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 256 184 = 40391542585080150384563660 :=
  phaseBlock_append receipt_0_9_2383_1_part2 receipt_0_9_2383_1_part3 rfl rfl rfl
private theorem receipt_0_9_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2383 10 1 0 1 1) 0 440 = 258445109569288178601680384 :=
  phaseBlock_append receipt_0_9_2383_1_join0 receipt_0_9_2383_1_join1 rfl rfl rfl

private theorem receipt_0_9_2383_1 : fastPhase (bank 0 9).shape 179808 2383 10 1 0 1 1 = 258445109569288178601680384 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2383_1_join2

private theorem receipt_0_9_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 0 128 = 135901034981366349321359910 := by decide +kernel
private theorem receipt_0_9_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 128 128 = 82972690658804534341916804 := by decide +kernel
private theorem receipt_0_9_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 256 128 = 37226929439380237343968699 := by decide +kernel
private theorem receipt_0_9_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 384 56 = 3622204170320521773189699 := by decide +kernel
private theorem receipt_0_9_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 0 256 = 218873725640170883663276714 :=
  phaseBlock_append receipt_0_9_2384_0_part0 receipt_0_9_2384_0_part1 rfl rfl rfl
private theorem receipt_0_9_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 256 184 = 40849133609700759117158398 :=
  phaseBlock_append receipt_0_9_2384_0_part2 receipt_0_9_2384_0_part3 rfl rfl rfl
private theorem receipt_0_9_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 0) 0 440 = 259722859249871642780435112 :=
  phaseBlock_append receipt_0_9_2384_0_join0 receipt_0_9_2384_0_join1 rfl rfl rfl

private theorem receipt_0_9_2384_0 : fastPhase (bank 0 9).shape 179808 2384 10 1 0 1 0 = 259722859249871642780435112 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2384_0_join2

private theorem receipt_0_9_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 0 128 = 135463747324500751824127038 := by decide +kernel
private theorem receipt_0_9_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 128 128 = 82591572312508734532396893 := by decide +kernel
private theorem receipt_0_9_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 256 128 = 36898029255061296940911921 := by decide +kernel
private theorem receipt_0_9_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 384 56 = 3493726337241624387240571 := by decide +kernel
private theorem receipt_0_9_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 0 256 = 218055319637009486356523931 :=
  phaseBlock_append receipt_0_9_2384_1_part0 receipt_0_9_2384_1_part1 rfl rfl rfl
private theorem receipt_0_9_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 256 184 = 40391755592302921328152492 :=
  phaseBlock_append receipt_0_9_2384_1_part2 receipt_0_9_2384_1_part3 rfl rfl rfl
private theorem receipt_0_9_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179808 2384 10 1 0 1 1) 0 440 = 258447075229312407684676423 :=
  phaseBlock_append receipt_0_9_2384_1_join0 receipt_0_9_2384_1_join1 rfl rfl rfl

private theorem receipt_0_9_2384_1 : fastPhase (bank 0 9).shape 179808 2384 10 1 0 1 1 = 258447075229312407684676423 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2384_1_join2

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2383_0 receipt_0_9_2383_1 receipt_0_9_2384_0 receipt_0_9_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 0 128 = 122428630525897395318489585 := by decide +kernel
private theorem receipt_1_9_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 128 128 = 74616582320208737281029047 := by decide +kernel
private theorem receipt_1_9_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 256 128 = 33420982529603981229204324 := by decide +kernel
private theorem receipt_1_9_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 384 56 = 3247587547230898602664993 := by decide +kernel
private theorem receipt_1_9_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 0 256 = 197045212846106132599518632 :=
  phaseBlock_append receipt_1_9_2383_0_part0 receipt_1_9_2383_0_part1 rfl rfl rfl
private theorem receipt_1_9_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 256 184 = 36668570076834879831869317 :=
  phaseBlock_append receipt_1_9_2383_0_part2 receipt_1_9_2383_0_part3 rfl rfl rfl
private theorem receipt_1_9_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 0) 0 440 = 233713782922941012431387949 :=
  phaseBlock_append receipt_1_9_2383_0_join0 receipt_1_9_2383_0_join1 rfl rfl rfl

private theorem receipt_1_9_2383_0 : fastPhase (bank 1 9).shape 179808 2383 10 1 0 2 0 = 233713782922941012431387949 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2383_0_join2

private theorem receipt_1_9_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 0 128 = 122033016039629338042249908 := by decide +kernel
private theorem receipt_1_9_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 128 128 = 74272835821296734226294574 := by decide +kernel
private theorem receipt_1_9_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 256 128 = 33125289195872391367729743 := by decide +kernel
private theorem receipt_1_9_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 384 56 = 3132367817865525831943246 := by decide +kernel
private theorem receipt_1_9_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 0 256 = 196305851860926072268544482 :=
  phaseBlock_append receipt_1_9_2383_1_part0 receipt_1_9_2383_1_part1 rfl rfl rfl
private theorem receipt_1_9_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 256 184 = 36257657013737917199672989 :=
  phaseBlock_append receipt_1_9_2383_1_part2 receipt_1_9_2383_1_part3 rfl rfl rfl
private theorem receipt_1_9_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2383 10 1 0 2 1) 0 440 = 232563508874663989468217471 :=
  phaseBlock_append receipt_1_9_2383_1_join0 receipt_1_9_2383_1_join1 rfl rfl rfl

private theorem receipt_1_9_2383_1 : fastPhase (bank 1 9).shape 179808 2383 10 1 0 2 1 = 232563508874663989468217471 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2383_1_join2

private theorem receipt_1_9_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 0 128 = 122429687111733406873914161 := by decide +kernel
private theorem receipt_1_9_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 128 128 = 74617108665373632090593867 := by decide +kernel
private theorem receipt_1_9_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 256 128 = 33421162609024625632672782 := by decide +kernel
private theorem receipt_1_9_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 384 56 = 3247600541185760467096641 := by decide +kernel
private theorem receipt_1_9_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 0 256 = 197046795777107038964508028 :=
  phaseBlock_append receipt_1_9_2384_0_part0 receipt_1_9_2384_0_part1 rfl rfl rfl
private theorem receipt_1_9_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 256 184 = 36668763150210386099769423 :=
  phaseBlock_append receipt_1_9_2384_0_part2 receipt_1_9_2384_0_part3 rfl rfl rfl
private theorem receipt_1_9_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 0) 0 440 = 233715558927317425064277451 :=
  phaseBlock_append receipt_1_9_2384_0_join0 receipt_1_9_2384_0_join1 rfl rfl rfl

private theorem receipt_1_9_2384_0 : fastPhase (bank 1 9).shape 179808 2384 10 1 0 2 0 = 233715558927317425064277451 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2384_0_join2

private theorem receipt_1_9_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 0 128 = 122034069798871628542796835 := by decide +kernel
private theorem receipt_1_9_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 128 128 = 74273360085529505007027240 := by decide +kernel
private theorem receipt_1_9_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 256 128 = 33125467856369230275848160 := by decide +kernel
private theorem receipt_1_9_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 384 56 = 3132380377707526626579885 := by decide +kernel
private theorem receipt_1_9_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 0 256 = 196307429884401133549824075 :=
  phaseBlock_append receipt_1_9_2384_1_part0 receipt_1_9_2384_1_part1 rfl rfl rfl
private theorem receipt_1_9_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 256 184 = 36257848234076756902428045 :=
  phaseBlock_append receipt_1_9_2384_1_part2 receipt_1_9_2384_1_part3 rfl rfl rfl
private theorem receipt_1_9_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179808 2384 10 1 0 2 1) 0 440 = 232565278118477890452252120 :=
  phaseBlock_append receipt_1_9_2384_1_join0 receipt_1_9_2384_1_join1 rfl rfl rfl

private theorem receipt_1_9_2384_1 : fastPhase (bank 1 9).shape 179808 2384 10 1 0 2 1 = 232565278118477890452252120 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2384_1_join2

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2383_0 receipt_1_9_2383_1 receipt_1_9_2384_0 receipt_1_9_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 0 128 = 65941882686689526163439709 := by decide +kernel
private theorem receipt_2_9_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 128 128 = 39685985461518426923383715 := by decide +kernel
private theorem receipt_2_9_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 256 128 = 17557538094322678181963764 := by decide +kernel
private theorem receipt_2_9_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 384 56 = 1689706752890307265369431 := by decide +kernel
private theorem receipt_2_9_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 0 256 = 105627868148207953086823424 :=
  phaseBlock_append receipt_2_9_2383_0_part0 receipt_2_9_2383_0_part1 rfl rfl rfl
private theorem receipt_2_9_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 256 184 = 19247244847212985447333195 :=
  phaseBlock_append receipt_2_9_2383_0_part2 receipt_2_9_2383_0_part3 rfl rfl rfl
private theorem receipt_2_9_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 0) 0 440 = 124875112995420938534156619 :=
  phaseBlock_append receipt_2_9_2383_0_join0 receipt_2_9_2383_0_join1 rfl rfl rfl

private theorem receipt_2_9_2383_0 : fastPhase (bank 2 9).shape 179808 2383 10 1 0 7 0 = 124875112995420938534156619 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2383_0_join2

private theorem receipt_2_9_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 0 128 = 65722322501741798394611510 := by decide +kernel
private theorem receipt_2_9_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 128 128 = 39499277881547811934763904 := by decide +kernel
private theorem receipt_2_9_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 256 128 = 17400597283663297566034033 := by decide +kernel
private theorem receipt_2_9_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 384 56 = 1629646682137194912485574 := by decide +kernel
private theorem receipt_2_9_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 0 256 = 105221600383289610329375414 :=
  phaseBlock_append receipt_2_9_2383_1_part0 receipt_2_9_2383_1_part1 rfl rfl rfl
private theorem receipt_2_9_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 256 184 = 19030243965800492478519607 :=
  phaseBlock_append receipt_2_9_2383_1_part2 receipt_2_9_2383_1_part3 rfl rfl rfl
private theorem receipt_2_9_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2383 10 1 0 7 1) 0 440 = 124251844349090102807895021 :=
  phaseBlock_append receipt_2_9_2383_1_join0 receipt_2_9_2383_1_join1 rfl rfl rfl

private theorem receipt_2_9_2383_1 : fastPhase (bank 2 9).shape 179808 2383 10 1 0 7 1 = 124251844349090102807895021 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2383_1_join2

private theorem receipt_2_9_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 0 128 = 65942451884745277665845793 := by decide +kernel
private theorem receipt_2_9_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 128 128 = 39686265475761972087142509 := by decide +kernel
private theorem receipt_2_9_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 256 128 = 17557632729249298544896929 := by decide +kernel
private theorem receipt_2_9_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 384 56 = 1689713514056559185449626 := by decide +kernel
private theorem receipt_2_9_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 0 256 = 105628717360507249752988302 :=
  phaseBlock_append receipt_2_9_2384_0_part0 receipt_2_9_2384_0_part1 rfl rfl rfl
private theorem receipt_2_9_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 256 184 = 19247346243305857730346555 :=
  phaseBlock_append receipt_2_9_2384_0_part2 receipt_2_9_2384_0_part3 rfl rfl rfl
private theorem receipt_2_9_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 0) 0 440 = 124876063603813107483334857 :=
  phaseBlock_append receipt_2_9_2384_0_join0 receipt_2_9_2384_0_join1 rfl rfl rfl

private theorem receipt_2_9_2384_0 : fastPhase (bank 2 9).shape 179808 2384 10 1 0 7 0 = 124876063603813107483334857 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2384_0_join2

private theorem receipt_2_9_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 0 128 = 65722890121102295603388201 := by decide +kernel
private theorem receipt_2_9_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 128 128 = 39499556761304020934650821 := by decide +kernel
private theorem receipt_2_9_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 256 128 = 17400691164211790740780647 := by decide +kernel
private theorem receipt_2_9_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 384 56 = 1629653216956270885799022 := by decide +kernel
private theorem receipt_2_9_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 0 256 = 105222446882406316538039022 :=
  phaseBlock_append receipt_2_9_2384_1_part0 receipt_2_9_2384_1_part1 rfl rfl rfl
private theorem receipt_2_9_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 256 184 = 19030344381168061626579669 :=
  phaseBlock_append receipt_2_9_2384_1_part2 receipt_2_9_2384_1_part3 rfl rfl rfl
private theorem receipt_2_9_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179808 2384 10 1 0 7 1) 0 440 = 124252791263574378164618691 :=
  phaseBlock_append receipt_2_9_2384_1_join0 receipt_2_9_2384_1_join1 rfl rfl rfl

private theorem receipt_2_9_2384_1 : fastPhase (bank 2 9).shape 179808 2384 10 1 0 7 1 = 124252791263574378164618691 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2384_1_join2

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2383_0 receipt_2_9_2383_1 receipt_2_9_2384_0 receipt_2_9_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 0 128 = 12532926988242870298356480 := by decide +kernel
private theorem receipt_3_9_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 128 128 = 7709565721979895609297664 := by decide +kernel
private theorem receipt_3_9_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 256 128 = 3597657730020383107443456 := by decide +kernel
private theorem receipt_3_9_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 384 73 = 501840008351841703448304 := by decide +kernel
private theorem receipt_3_9_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 0 256 = 20242492710222765907654144 :=
  phaseBlock_append receipt_3_9_2383_0_part0 receipt_3_9_2383_0_part1 rfl rfl rfl
private theorem receipt_3_9_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 256 201 = 4099497738372224810891760 :=
  phaseBlock_append receipt_3_9_2383_0_part2 receipt_3_9_2383_0_part3 rfl rfl rfl
private theorem receipt_3_9_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 0) 0 457 = 24341990448594990718545904 :=
  phaseBlock_append receipt_3_9_2383_0_join0 receipt_3_9_2383_0_join1 rfl rfl rfl

private theorem receipt_3_9_2383_0 : fastPhase (bank 3 9).shape 179808 2383 10 1 1 1 0 = 24341990448594990718545904 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2383_0_join2

private theorem receipt_3_9_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 0 128 = 12493109518766441483264960 := by decide +kernel
private theorem receipt_3_9_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 128 128 = 7674902239002197107188672 := by decide +kernel
private theorem receipt_3_9_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 256 128 = 3568606961752041098863552 := by decide +kernel
private theorem receipt_3_9_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 384 73 = 487957495024875038823228 := by decide +kernel
private theorem receipt_3_9_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 0 256 = 20168011757768638590453632 :=
  phaseBlock_append receipt_3_9_2383_1_part0 receipt_3_9_2383_1_part1 rfl rfl rfl
private theorem receipt_3_9_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 256 201 = 4056564456776916137686780 :=
  phaseBlock_append receipt_3_9_2383_1_part2 receipt_3_9_2383_1_part3 rfl rfl rfl
private theorem receipt_3_9_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2383 10 1 1 1 1) 0 457 = 24224576214545554728140412 :=
  phaseBlock_append receipt_3_9_2383_1_join0 receipt_3_9_2383_1_join1 rfl rfl rfl

private theorem receipt_3_9_2383_1 : fastPhase (bank 3 9).shape 179808 2383 10 1 1 1 1 = 24224576214545554728140412 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2383_1_join2

private theorem receipt_3_9_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 0 128 = 12533028861640675404617280 := by decide +kernel
private theorem receipt_3_9_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 128 128 = 7709609616076461470111296 := by decide +kernel
private theorem receipt_3_9_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 256 128 = 3597670068665038619186752 := by decide +kernel
private theorem receipt_3_9_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 384 73 = 501840849895829931589338 := by decide +kernel
private theorem receipt_3_9_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 0 256 = 20242638477717136874728576 :=
  phaseBlock_append receipt_3_9_2384_0_part0 receipt_3_9_2384_0_part1 rfl rfl rfl
private theorem receipt_3_9_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 256 201 = 4099510918560868550776090 :=
  phaseBlock_append receipt_3_9_2384_0_part2 receipt_3_9_2384_0_part3 rfl rfl rfl
private theorem receipt_3_9_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 0) 0 457 = 24342149396278005425504666 :=
  phaseBlock_append receipt_3_9_2384_0_join0 receipt_3_9_2384_0_join1 rfl rfl rfl

private theorem receipt_3_9_2384_0 : fastPhase (bank 3 9).shape 179808 2384 10 1 1 1 0 = 24342149396278005425504666 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2384_0_join2

private theorem receipt_3_9_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 0 128 = 12493211022369366771457344 := by decide +kernel
private theorem receipt_3_9_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 128 128 = 7674945913753913924525376 := by decide +kernel
private theorem receipt_3_9_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 256 128 = 3568619195827654486973760 := by decide +kernel
private theorem receipt_3_9_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 384 73 = 487958314915358981595540 := by decide +kernel
private theorem receipt_3_9_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 0 256 = 20168156936123280695982720 :=
  phaseBlock_append receipt_3_9_2384_1_part0 receipt_3_9_2384_1_part1 rfl rfl rfl
private theorem receipt_3_9_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 256 201 = 4056577510743013468569300 :=
  phaseBlock_append receipt_3_9_2384_1_part2 receipt_3_9_2384_1_part3 rfl rfl rfl
private theorem receipt_3_9_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179808 2384 10 1 1 1 1) 0 457 = 24224734446866294164552020 :=
  phaseBlock_append receipt_3_9_2384_1_join0 receipt_3_9_2384_1_join1 rfl rfl rfl

private theorem receipt_3_9_2384_1 : fastPhase (bank 3 9).shape 179808 2384 10 1 1 1 1 = 24224734446866294164552020 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2384_1_join2

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2383_0 receipt_3_9_2383_1 receipt_3_9_2384_0 receipt_3_9_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 0 128 = 1515305845241110872386577600 := by decide +kernel
private theorem receipt_0_10_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 128 128 = 1175629257932287035026425024 := by decide +kernel
private theorem receipt_0_10_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 256 128 = 863694474501823576563606720 := by decide +kernel
private theorem receipt_0_10_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 384 128 = 578317218109277645370875974 := by decide +kernel
private theorem receipt_0_10_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 512 128 = 318318534199654624382348392 := by decide +kernel
private theorem receipt_0_10_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 640 111 = 84304021151507926724014560 := by decide +kernel
private theorem receipt_0_10_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 128 256 = 2039323732434110611590031744 :=
  phaseBlock_append receipt_0_10_2383_0_part1 receipt_0_10_2383_0_part2 rfl rfl rfl
private theorem receipt_0_10_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 0 384 = 3554629577675221483976609344 :=
  phaseBlock_append receipt_0_10_2383_0_part0 receipt_0_10_2383_0_join0 rfl rfl rfl
private theorem receipt_0_10_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 512 239 = 402622555351162551106362952 :=
  phaseBlock_append receipt_0_10_2383_0_part4 receipt_0_10_2383_0_part5 rfl rfl rfl
private theorem receipt_0_10_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 384 367 = 980939773460440196477238926 :=
  phaseBlock_append receipt_0_10_2383_0_part3 receipt_0_10_2383_0_join2 rfl rfl rfl
private theorem receipt_0_10_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 0) 0 751 = 4535569351135661680453848270 :=
  phaseBlock_append receipt_0_10_2383_0_join1 receipt_0_10_2383_0_join3 rfl rfl rfl

private theorem receipt_0_10_2383_0 : fastPhase (bank 0 10).shape 179808 2383 20 1 0 1 0 = 4535569351135661680453848270 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2383_0_join4

private theorem receipt_0_10_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 0 128 = 1512577962600828999808714240 := by decide +kernel
private theorem receipt_0_10_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 128 128 = 1173115266359674876514403840 := by decide +kernel
private theorem receipt_0_10_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 256 128 = 861385405001516072784496128 := by decide +kernel
private theorem receipt_0_10_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 384 128 = 576204138160236212552557082 := by decide +kernel
private theorem receipt_0_10_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 512 128 = 316392544089376875673975224 := by decide +kernel
private theorem receipt_0_10_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 640 111 = 82778430890565901091481374 := by decide +kernel
private theorem receipt_0_10_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 128 256 = 2034500671361190949298899968 :=
  phaseBlock_append receipt_0_10_2383_1_part1 receipt_0_10_2383_1_part2 rfl rfl rfl
private theorem receipt_0_10_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 0 384 = 3547078633962019949107614208 :=
  phaseBlock_append receipt_0_10_2383_1_part0 receipt_0_10_2383_1_join0 rfl rfl rfl
private theorem receipt_0_10_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 512 239 = 399170974979942776765456598 :=
  phaseBlock_append receipt_0_10_2383_1_part4 receipt_0_10_2383_1_part5 rfl rfl rfl
private theorem receipt_0_10_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 384 367 = 975375113140178989318013680 :=
  phaseBlock_append receipt_0_10_2383_1_part3 receipt_0_10_2383_1_join2 rfl rfl rfl
private theorem receipt_0_10_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2383 20 1 0 1 1) 0 751 = 4522453747102198938425627888 :=
  phaseBlock_append receipt_0_10_2383_1_join1 receipt_0_10_2383_1_join3 rfl rfl rfl

private theorem receipt_0_10_2383_1 : fastPhase (bank 0 10).shape 179808 2383 20 1 0 1 1 = 4522453747102198938425627888 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2383_1_join4

private theorem receipt_0_10_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 0 128 = 1515319259832543230714270208 := by decide +kernel
private theorem receipt_0_10_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 128 128 = 1175638587309898971550265856 := by decide +kernel
private theorem receipt_0_10_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 256 128 = 863700492984884749337694720 := by decide +kernel
private theorem receipt_0_10_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 384 128 = 578320658777724267103405656 := by decide +kernel
private theorem receipt_0_10_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 512 128 = 318320085725412439453393197 := by decide +kernel
private theorem receipt_0_10_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 640 111 = 84304348294357839351962688 := by decide +kernel
private theorem receipt_0_10_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 128 256 = 2039339080294783720887960576 :=
  phaseBlock_append receipt_0_10_2384_0_part1 receipt_0_10_2384_0_part2 rfl rfl rfl
private theorem receipt_0_10_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 0 384 = 3554658340127326951602230784 :=
  phaseBlock_append receipt_0_10_2384_0_part0 receipt_0_10_2384_0_join0 rfl rfl rfl
private theorem receipt_0_10_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 512 239 = 402624434019770278805355885 :=
  phaseBlock_append receipt_0_10_2384_0_part4 receipt_0_10_2384_0_part5 rfl rfl rfl
private theorem receipt_0_10_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 384 367 = 980945092797494545908761541 :=
  phaseBlock_append receipt_0_10_2384_0_part3 receipt_0_10_2384_0_join2 rfl rfl rfl
private theorem receipt_0_10_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 0) 0 751 = 4535603432924821497510992325 :=
  phaseBlock_append receipt_0_10_2384_0_join1 receipt_0_10_2384_0_join3 rfl rfl rfl

private theorem receipt_0_10_2384_0 : fastPhase (bank 0 10).shape 179808 2384 20 1 0 1 0 = 4535603432924821497510992325 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2384_0_join4

private theorem receipt_0_10_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 0 128 = 1512591357452401675266343680 := by decide +kernel
private theorem receipt_0_10_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 128 128 = 1173124579081619256334443264 := by decide +kernel
private theorem receipt_0_10_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 256 128 = 861391409720168924987523840 := by decide +kernel
private theorem receipt_0_10_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 384 128 = 576207567765169783312820804 := by decide +kernel
private theorem receipt_0_10_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 512 128 = 316394087088751353080492899 := by decide +kernel
private theorem receipt_0_10_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 640 111 = 82778752547947192265915598 := by decide +kernel
private theorem receipt_0_10_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 128 256 = 2034515988801788181321967104 :=
  phaseBlock_append receipt_0_10_2384_1_part1 receipt_0_10_2384_1_part2 rfl rfl rfl
private theorem receipt_0_10_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 0 384 = 3547107346254189856588310784 :=
  phaseBlock_append receipt_0_10_2384_1_part0 receipt_0_10_2384_1_join0 rfl rfl rfl
private theorem receipt_0_10_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 512 239 = 399172839636698545346408497 :=
  phaseBlock_append receipt_0_10_2384_1_part4 receipt_0_10_2384_1_part5 rfl rfl rfl
private theorem receipt_0_10_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 384 367 = 975380407401868328659229301 :=
  phaseBlock_append receipt_0_10_2384_1_part3 receipt_0_10_2384_1_join2 rfl rfl rfl
private theorem receipt_0_10_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179808 2384 20 1 0 1 1) 0 751 = 4522487753656058185247540085 :=
  phaseBlock_append receipt_0_10_2384_1_join1 receipt_0_10_2384_1_join3 rfl rfl rfl

private theorem receipt_0_10_2384_1 : fastPhase (bank 0 10).shape 179808 2384 20 1 0 1 1 = 4522487753656058185247540085 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2384_1_join4

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2383_0 receipt_0_10_2383_1 receipt_0_10_2384_0 receipt_0_10_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 0 128 = 1351399791064650857091201600 := by decide +kernel
private theorem receipt_1_10_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 128 128 = 1047216347040688713426147904 := by decide +kernel
private theorem receipt_1_10_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 256 128 = 768438082005961466800749120 := by decide +kernel
private theorem receipt_1_10_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 384 128 = 513924344363232456993350212 := by decide +kernel
private theorem receipt_1_10_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 512 128 = 282544179152064477021998845 := by decide +kernel
private theorem receipt_1_10_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 640 111 = 74752684212311090987192712 := by decide +kernel
private theorem receipt_1_10_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 128 256 = 1815654429046650180226897024 :=
  phaseBlock_append receipt_1_10_2383_0_part1 receipt_1_10_2383_0_part2 rfl rfl rfl
private theorem receipt_1_10_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 0 384 = 3167054220111301037318098624 :=
  phaseBlock_append receipt_1_10_2383_0_part0 receipt_1_10_2383_0_join0 rfl rfl rfl
private theorem receipt_1_10_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 512 239 = 357296863364375568009191557 :=
  phaseBlock_append receipt_1_10_2383_0_part4 receipt_1_10_2383_0_part5 rfl rfl rfl
private theorem receipt_1_10_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 384 367 = 871221207727608025002541769 :=
  phaseBlock_append receipt_1_10_2383_0_part3 receipt_1_10_2383_0_join2 rfl rfl rfl
private theorem receipt_1_10_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 0) 0 751 = 4038275427838909062320640393 :=
  phaseBlock_append receipt_1_10_2383_0_join1 receipt_1_10_2383_0_join3 rfl rfl rfl

private theorem receipt_1_10_2383_0 : fastPhase (bank 1 10).shape 179808 2383 20 1 0 2 0 = 4038275427838909062320640393 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2383_0_join4

private theorem receipt_1_10_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 0 128 = 1348954418870919616742192896 := by decide +kernel
private theorem receipt_1_10_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 128 128 = 1044967227907373966104065792 := by decide +kernel
private theorem receipt_1_10_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 256 128 = 766376553093511591292139264 := by decide +kernel
private theorem receipt_1_10_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 384 128 = 512041813175941809001109150 := by decide +kernel
private theorem receipt_1_10_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 512 128 = 280832120131103390462331531 := by decide +kernel
private theorem receipt_1_10_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 640 111 = 73399473821731059081953822 := by decide +kernel
private theorem receipt_1_10_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 128 256 = 1811343781000885557396205056 :=
  phaseBlock_append receipt_1_10_2383_1_part1 receipt_1_10_2383_1_part2 rfl rfl rfl
private theorem receipt_1_10_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 0 384 = 3160298199871805174138397952 :=
  phaseBlock_append receipt_1_10_2383_1_part0 receipt_1_10_2383_1_join0 rfl rfl rfl
private theorem receipt_1_10_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 512 239 = 354231593952834449544285353 :=
  phaseBlock_append receipt_1_10_2383_1_part4 receipt_1_10_2383_1_part5 rfl rfl rfl
private theorem receipt_1_10_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 384 367 = 866273407128776258545394503 :=
  phaseBlock_append receipt_1_10_2383_1_part3 receipt_1_10_2383_1_join2 rfl rfl rfl
private theorem receipt_1_10_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2383 20 1 0 2 1) 0 751 = 4026571607000581432683792455 :=
  phaseBlock_append receipt_1_10_2383_1_join1 receipt_1_10_2383_1_join3 rfl rfl rfl

private theorem receipt_1_10_2383_1 : fastPhase (bank 1 10).shape 179808 2383 20 1 0 2 1 = 4026571607000581432683792455 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2383_1_join4

private theorem receipt_1_10_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 0 128 = 1351411754760342443897366304 := by decide +kernel
private theorem receipt_1_10_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 128 128 = 1047224657477233918244108064 := by decide +kernel
private theorem receipt_1_10_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 256 128 = 768443436789991193974064928 := by decide +kernel
private theorem receipt_1_10_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 384 128 = 513927401983356979102713126 := by decide +kernel
private theorem receipt_1_10_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 512 128 = 282545556339770516341541190 := by decide +kernel
private theorem receipt_1_10_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 640 111 = 74752974295593297417542535 := by decide +kernel
private theorem receipt_1_10_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 128 256 = 1815668094267225112218172992 :=
  phaseBlock_append receipt_1_10_2384_0_part1 receipt_1_10_2384_0_part2 rfl rfl rfl
private theorem receipt_1_10_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 0 384 = 3167079849027567556115539296 :=
  phaseBlock_append receipt_1_10_2384_0_part0 receipt_1_10_2384_0_join0 rfl rfl rfl
private theorem receipt_1_10_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 512 239 = 357298530635363813759083725 :=
  phaseBlock_append receipt_1_10_2384_0_part4 receipt_1_10_2384_0_part5 rfl rfl rfl
private theorem receipt_1_10_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 384 367 = 871225932618720792861796851 :=
  phaseBlock_append receipt_1_10_2384_0_part3 receipt_1_10_2384_0_join2 rfl rfl rfl
private theorem receipt_1_10_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 0) 0 751 = 4038305781646288348977336147 :=
  phaseBlock_append receipt_1_10_2384_0_join1 receipt_1_10_2384_0_join3 rfl rfl rfl

private theorem receipt_1_10_2384_0 : fastPhase (bank 1 10).shape 179808 2384 20 1 0 2 0 = 4038305781646288348977336147 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2384_0_join4

private theorem receipt_1_10_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 0 128 = 1348966364850555785303997216 := by decide +kernel
private theorem receipt_1_10_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 128 128 = 1044975523430106585995266848 := by decide +kernel
private theorem receipt_1_10_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 256 128 = 766381895581335124097162016 := by decide +kernel
private theorem receipt_1_10_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 384 128 = 512044860936059755769213054 := by decide +kernel
private theorem receipt_1_10_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 512 128 = 280833489738168858354624565 := by decide +kernel
private theorem receipt_1_10_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 640 111 = 73399759039064702418107544 := by decide +kernel
private theorem receipt_1_10_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 128 256 = 1811357419011441710092428864 :=
  phaseBlock_append receipt_1_10_2384_1_part1 receipt_1_10_2384_1_part2 rfl rfl rfl
private theorem receipt_1_10_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 0 384 = 3160323783861997495396426080 :=
  phaseBlock_append receipt_1_10_2384_1_part0 receipt_1_10_2384_1_join0 rfl rfl rfl
private theorem receipt_1_10_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 512 239 = 354233248777233560772732109 :=
  phaseBlock_append receipt_1_10_2384_1_part4 receipt_1_10_2384_1_part5 rfl rfl rfl
private theorem receipt_1_10_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 384 367 = 866278109713293316541945163 :=
  phaseBlock_append receipt_1_10_2384_1_part3 receipt_1_10_2384_1_join2 rfl rfl rfl
private theorem receipt_1_10_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179808 2384 20 1 0 2 1) 0 751 = 4026601893575290811938371243 :=
  phaseBlock_append receipt_1_10_2384_1_join1 receipt_1_10_2384_1_join3 rfl rfl rfl

private theorem receipt_1_10_2384_1 : fastPhase (bank 1 10).shape 179808 2384 20 1 0 2 1 = 4026601893575290811938371243 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2384_1_join4

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2383_0 receipt_1_10_2383_1 receipt_1_10_2384_0 receipt_1_10_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 0 128 = 677135131487072661337763200 := by decide +kernel
private theorem receipt_2_10_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 128 128 = 520056526079732336198544768 := by decide +kernel
private theorem receipt_2_10_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 256 128 = 378205377761644553831476608 := by decide +kernel
private theorem receipt_2_10_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 384 128 = 250677345949554998991340730 := by decide +kernel
private theorem receipt_2_10_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 512 128 = 136594453658816668773400635 := by decide +kernel
private theorem receipt_2_10_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 640 111 = 35856238302189110475026200 := by decide +kernel
private theorem receipt_2_10_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 128 256 = 898261903841376890030021376 :=
  phaseBlock_append receipt_2_10_2383_0_part1 receipt_2_10_2383_0_part2 rfl rfl rfl
private theorem receipt_2_10_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 0 384 = 1575397035328449551367784576 :=
  phaseBlock_append receipt_2_10_2383_0_part0 receipt_2_10_2383_0_join0 rfl rfl rfl
private theorem receipt_2_10_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 512 239 = 172450691961005779248426835 :=
  phaseBlock_append receipt_2_10_2383_0_part4 receipt_2_10_2383_0_part5 rfl rfl rfl
private theorem receipt_2_10_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 384 367 = 423128037910560778239767565 :=
  phaseBlock_append receipt_2_10_2383_0_part3 receipt_2_10_2383_0_join2 rfl rfl rfl
private theorem receipt_2_10_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 0) 0 751 = 1998525073239010329607552141 :=
  phaseBlock_append receipt_2_10_2383_0_join1 receipt_2_10_2383_0_join3 rfl rfl rfl

private theorem receipt_2_10_2383_0 : fastPhase (bank 2 10).shape 179808 2383 20 1 0 7 0 = 1998525073239010329607552141 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2383_0_join4

private theorem receipt_2_10_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 0 128 = 675862831151147605149660928 := by decide +kernel
private theorem receipt_2_10_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 128 128 = 518903306590978588887561984 := by decide +kernel
private theorem receipt_2_10_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 256 128 = 377164271568082633708386048 := by decide +kernel
private theorem receipt_2_10_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 384 128 = 249741585998487561165417092 := by decide +kernel
private theorem receipt_2_10_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 512 128 = 135757469471492954646952381 := by decide +kernel
private theorem receipt_2_10_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 640 111 = 35205445583843606162794392 := by decide +kernel
private theorem receipt_2_10_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 128 256 = 896067578159061222595948032 :=
  phaseBlock_append receipt_2_10_2383_1_part1 receipt_2_10_2383_1_part2 rfl rfl rfl
private theorem receipt_2_10_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 0 384 = 1571930409310208827745608960 :=
  phaseBlock_append receipt_2_10_2383_1_part0 receipt_2_10_2383_1_join0 rfl rfl rfl
private theorem receipt_2_10_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 512 239 = 170962915055336560809746773 :=
  phaseBlock_append receipt_2_10_2383_1_part4 receipt_2_10_2383_1_part5 rfl rfl rfl
private theorem receipt_2_10_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 384 367 = 420704501053824121975163865 :=
  phaseBlock_append receipt_2_10_2383_1_part3 receipt_2_10_2383_1_join2 rfl rfl rfl
private theorem receipt_2_10_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2383 20 1 0 7 1) 0 751 = 1992634910364032949720772825 :=
  phaseBlock_append receipt_2_10_2383_1_join1 receipt_2_10_2383_1_join3 rfl rfl rfl

private theorem receipt_2_10_2383_1 : fastPhase (bank 2 10).shape 179808 2383 20 1 0 7 1 = 1992634910364032949720772825 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2383_1_join4

private theorem receipt_2_10_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 0 128 = 677141126490406885380754656 := by decide +kernel
private theorem receipt_2_10_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 128 128 = 520060653479827694774213856 := by decide +kernel
private theorem receipt_2_10_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 256 128 = 378208013531087404414545120 := by decide +kernel
private theorem receipt_2_10_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 384 128 = 250678837566650166988950066 := by decide +kernel
private theorem receipt_2_10_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 512 128 = 136595119566243507009268971 := by decide +kernel
private theorem receipt_2_10_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 640 111 = 35856377461556435310475017 := by decide +kernel
private theorem receipt_2_10_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 128 256 = 898268667010915099188758976 :=
  phaseBlock_append receipt_2_10_2384_0_part1 receipt_2_10_2384_0_part2 rfl rfl rfl
private theorem receipt_2_10_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 0 384 = 1575409793501321984569513632 :=
  phaseBlock_append receipt_2_10_2384_0_part0 receipt_2_10_2384_0_join0 rfl rfl rfl
private theorem receipt_2_10_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 512 239 = 172451497027799942319743988 :=
  phaseBlock_append receipt_2_10_2384_0_part4 receipt_2_10_2384_0_part5 rfl rfl rfl
private theorem receipt_2_10_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 384 367 = 423130334594450109308694054 :=
  phaseBlock_append receipt_2_10_2384_0_part3 receipt_2_10_2384_0_join2 rfl rfl rfl
private theorem receipt_2_10_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 0) 0 751 = 1998540128095772093878207686 :=
  phaseBlock_append receipt_2_10_2384_0_join1 receipt_2_10_2384_0_join3 rfl rfl rfl

private theorem receipt_2_10_2384_0 : fastPhase (bank 2 10).shape 179808 2384 20 1 0 7 0 = 1998540128095772093878207686 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2384_0_join4

private theorem receipt_2_10_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 0 128 = 675868816860497979017211360 := by decide +kernel
private theorem receipt_2_10_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 128 128 = 518907426295923336215805408 := by decide +kernel
private theorem receipt_2_10_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 256 128 = 377166901100355812942761440 := by decide +kernel
private theorem receipt_2_10_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 384 128 = 249743072701175757474218934 := by decide +kernel
private theorem receipt_2_10_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 512 128 = 135758131668016718408170554 := by decide +kernel
private theorem receipt_2_10_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 640 111 = 35205582401969308606643886 := by decide +kernel
private theorem receipt_2_10_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 128 256 = 896074327396279149158566848 :=
  phaseBlock_append receipt_2_10_2384_1_part1 receipt_2_10_2384_1_part2 rfl rfl rfl
private theorem receipt_2_10_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 0 384 = 1571943144256777128175778208 :=
  phaseBlock_append receipt_2_10_2384_1_part0 receipt_2_10_2384_1_join0 rfl rfl rfl
private theorem receipt_2_10_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 512 239 = 170963714069986027014814440 :=
  phaseBlock_append receipt_2_10_2384_1_part4 receipt_2_10_2384_1_part5 rfl rfl rfl
private theorem receipt_2_10_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 384 367 = 420706786771161784489033374 :=
  phaseBlock_append receipt_2_10_2384_1_part3 receipt_2_10_2384_1_join2 rfl rfl rfl
private theorem receipt_2_10_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179808 2384 20 1 0 7 1) 0 751 = 1992649931027938912664811582 :=
  phaseBlock_append receipt_2_10_2384_1_join1 receipt_2_10_2384_1_join3 rfl rfl rfl

private theorem receipt_2_10_2384_1 : fastPhase (bank 2 10).shape 179808 2384 20 1 0 7 1 = 1992649931027938912664811582 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2384_1_join4

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2383_0 receipt_2_10_2383_1 receipt_2_10_2384_0 receipt_2_10_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 0 128 = 66879243960284298510445504 := by decide +kernel
private theorem receipt_3_10_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 128 128 = 46731405675264963375999936 := by decide +kernel
private theorem receipt_3_10_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 256 128 = 28725784561753578355600320 := by decide +kernel
private theorem receipt_3_10_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 384 128 = 12997569553455533119908800 := by decide +kernel
private theorem receipt_3_10_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 512 59 = 1356248411966123957958250 := by decide +kernel
private theorem receipt_3_10_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 0 256 = 113610649635549261886445440 :=
  phaseBlock_append receipt_3_10_2383_0_part0 receipt_3_10_2383_0_part1 rfl rfl rfl
private theorem receipt_3_10_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 384 187 = 14353817965421657077867050 :=
  phaseBlock_append receipt_3_10_2383_0_part3 receipt_3_10_2383_0_part4 rfl rfl rfl
private theorem receipt_3_10_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 256 315 = 43079602527175235433467370 :=
  phaseBlock_append receipt_3_10_2383_0_part2 receipt_3_10_2383_0_join1 rfl rfl rfl
private theorem receipt_3_10_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 0) 0 571 = 156690252162724497319912810 :=
  phaseBlock_append receipt_3_10_2383_0_join0 receipt_3_10_2383_0_join2 rfl rfl rfl

private theorem receipt_3_10_2383_0 : fastPhase (bank 3 10).shape 179808 2383 20 1 1 1 0 = 156690252162724497319912810 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2383_0_join3

private theorem receipt_3_10_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 0 128 = 66715880600011224328079808 := by decide +kernel
private theorem receipt_3_10_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 128 128 = 46583620034142187267377600 := by decide +kernel
private theorem receipt_3_10_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 256 128 = 28594726995761403524024768 := by decide +kernel
private theorem receipt_3_10_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 384 128 = 12884373127117714913675712 := by decide +kernel
private theorem receipt_3_10_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 512 59 = 1310394623791332561677314 := by decide +kernel
private theorem receipt_3_10_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 0 256 = 113299500634153411595457408 :=
  phaseBlock_append receipt_3_10_2383_1_part0 receipt_3_10_2383_1_part1 rfl rfl rfl
private theorem receipt_3_10_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 384 187 = 14194767750909047475353026 :=
  phaseBlock_append receipt_3_10_2383_1_part3 receipt_3_10_2383_1_part4 rfl rfl rfl
private theorem receipt_3_10_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 256 315 = 42789494746670450999377794 :=
  phaseBlock_append receipt_3_10_2383_1_part2 receipt_3_10_2383_1_join1 rfl rfl rfl
private theorem receipt_3_10_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2383 20 1 1 1 1) 0 571 = 156088995380823862594835202 :=
  phaseBlock_append receipt_3_10_2383_1_join0 receipt_3_10_2383_1_join2 rfl rfl rfl

private theorem receipt_3_10_2383_1 : fastPhase (bank 3 10).shape 179808 2383 20 1 1 1 1 = 156088995380823862594835202 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2383_1_join3

private theorem receipt_3_10_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 0 128 = 66879799749401779055665152 := by decide +kernel
private theorem receipt_3_10_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 128 128 = 46731704757062048124518400 := by decide +kernel
private theorem receipt_3_10_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 256 128 = 28725915966872242809987072 := by decide +kernel
private theorem receipt_3_10_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 384 128 = 12997606819635933606543360 := by decide +kernel
private theorem receipt_3_10_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 512 59 = 1356250545209488911816444 := by decide +kernel
private theorem receipt_3_10_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 0 256 = 113611504506463827180183552 :=
  phaseBlock_append receipt_3_10_2384_0_part0 receipt_3_10_2384_0_part1 rfl rfl rfl
private theorem receipt_3_10_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 384 187 = 14353857364845422518359804 :=
  phaseBlock_append receipt_3_10_2384_0_part3 receipt_3_10_2384_0_part4 rfl rfl rfl
private theorem receipt_3_10_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 256 315 = 43079773331717665328346876 :=
  phaseBlock_append receipt_3_10_2384_0_part2 receipt_3_10_2384_0_join1 rfl rfl rfl
private theorem receipt_3_10_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 0) 0 571 = 156691277838181492508530428 :=
  phaseBlock_append receipt_3_10_2384_0_join0 receipt_3_10_2384_0_join2 rfl rfl rfl

private theorem receipt_3_10_2384_0 : fastPhase (bank 3 10).shape 179808 2384 20 1 1 1 0 = 156691277838181492508530428 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2384_0_join3

private theorem receipt_3_10_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 0 128 = 66716434834316081612398656 := by decide +kernel
private theorem receipt_3_10_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 128 128 = 46583918053312163959955520 := by decide +kernel
private theorem receipt_3_10_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 256 128 = 28594857744704869566881856 := by decide +kernel
private theorem receipt_3_10_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 384 128 = 12884410059089471175974976 := by decide +kernel
private theorem receipt_3_10_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 512 59 = 1310396688353963297971686 := by decide +kernel
private theorem receipt_3_10_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 0 256 = 113300352887628245572354176 :=
  phaseBlock_append receipt_3_10_2384_1_part0 receipt_3_10_2384_1_part1 rfl rfl rfl
private theorem receipt_3_10_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 384 187 = 14194806747443434473946662 :=
  phaseBlock_append receipt_3_10_2384_1_part3 receipt_3_10_2384_1_part4 rfl rfl rfl
private theorem receipt_3_10_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 256 315 = 42789664492148304040828518 :=
  phaseBlock_append receipt_3_10_2384_1_part2 receipt_3_10_2384_1_join1 rfl rfl rfl
private theorem receipt_3_10_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179808 2384 20 1 1 1 1) 0 571 = 156090017379776549613182694 :=
  phaseBlock_append receipt_3_10_2384_1_join0 receipt_3_10_2384_1_join2 rfl rfl rfl

private theorem receipt_3_10_2384_1 : fastPhase (bank 3 10).shape 179808 2384 20 1 1 1 1 = 156090017379776549613182694 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2384_1_join3

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2726_570)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_10_2383_0 receipt_3_10_2383_1 receipt_3_10_2384_0 receipt_3_10_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group3_stage i)).shape
      (cutoff h rect (group3_stage i)), ¬ G∣Q :=
  (group3_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group3_avoids

end Lower6960.RescueSource
