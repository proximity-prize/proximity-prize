import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_2091_456_part0 :
    blockEstimate 2091 456 456 128 = 713999520 := rfl
private theorem moment_2091_456_part1 :
    blockEstimate 2091 456 584 128 = 4660499616 := rfl
private theorem moment_2091_456_part2 :
    blockEstimate 2091 456 712 128 = 11781039264 := rfl
private theorem moment_2091_456_part3 :
    blockEstimate 2091 456 840 128 = 21223686286 := rfl
private theorem moment_2091_456_part4 :
    blockEstimate 2091 456 968 128 = 30814903104 := rfl
private theorem moment_2091_456_part5 :
    blockEstimate 2091 456 1096 128 = 38594403136 := rfl
private theorem moment_2091_456_part6 :
    blockEstimate 2091 456 1224 128 = 44457106240 := rfl
private theorem moment_2091_456_part7 :
    blockEstimate 2091 456 1352 128 = 48403012416 := rfl
private theorem moment_2091_456_part8 :
    blockEstimate 2091 456 1480 128 = 50432121664 := rfl
private theorem moment_2091_456_part9 :
    blockEstimate 2091 456 1608 128 = 50544433984 := rfl
private theorem moment_2091_456_part10 :
    blockEstimate 2091 456 1736 128 = 48739949376 := rfl
private theorem moment_2091_456_part11 :
    blockEstimate 2091 456 1864 128 = 45018667840 := rfl
private theorem moment_2091_456_part12 :
    blockEstimate 2091 456 1992 128 = 39383175281 := rfl
private theorem moment_2091_456_part13 :
    blockEstimate 2091 456 2120 128 = 32263153930 := rfl
private theorem moment_2091_456_part14 :
    blockEstimate 2091 456 2248 128 = 24796295029 := rfl
private theorem moment_2091_456_part15 :
    blockEstimate 2091 456 2376 128 = 17602076717 := rfl
private theorem moment_2091_456_part16 :
    blockEstimate 2091 456 2504 128 = 11142425823 := rfl
private theorem moment_2091_456_part17 :
    blockEstimate 2091 456 2632 128 = 5851247200 := rfl
private theorem moment_2091_456_part18 :
    blockEstimate 2091 456 2760 128 = 2140420704 := rfl
private theorem moment_2091_456_part19 :
    blockEstimate 2091 456 2888 115 = 268468747 := rfl
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
    blockEstimate 2100 439 439 128 = 717219360 := rfl
private theorem moment_2100_439_part1 :
    blockEstimate 2100 439 567 128 = 4682741280 := rfl
private theorem moment_2100_439_part2 :
    blockEstimate 2100 439 695 128 = 11841177120 := rfl
private theorem moment_2100_439_part3 :
    blockEstimate 2100 439 823 128 = 21283064550 := rfl
private theorem moment_2100_439_part4 :
    blockEstimate 2100 439 951 128 = 30575072000 := rfl
private theorem moment_2100_439_part5 :
    blockEstimate 2100 439 1079 128 = 38068785920 := rfl
private theorem moment_2100_439_part6 :
    blockEstimate 2100 439 1207 128 = 43717006080 := rfl
private theorem moment_2100_439_part7 :
    blockEstimate 2100 439 1335 128 = 47519732480 := rfl
private theorem moment_2100_439_part8 :
    blockEstimate 2100 439 1463 128 = 49476965120 := rfl
private theorem moment_2100_439_part9 :
    blockEstimate 2100 439 1591 128 = 49588704000 := rfl
private theorem moment_2100_439_part10 :
    blockEstimate 2100 439 1719 128 = 47854949120 := rfl
private theorem moment_2100_439_part11 :
    blockEstimate 2100 439 1847 128 = 44275700480 := rfl
private theorem moment_2100_439_part12 :
    blockEstimate 2100 439 1975 128 = 38850961755 := rfl
private theorem moment_2100_439_part13 :
    blockEstimate 2100 439 2103 128 = 31839629831 := rfl
private theorem moment_2100_439_part14 :
    blockEstimate 2100 439 2231 128 = 24393218274 := rfl
private theorem moment_2100_439_part15 :
    blockEstimate 2100 439 2359 128 = 17228999980 := rfl
private theorem moment_2100_439_part16 :
    blockEstimate 2100 439 2487 128 = 10819779729 := rfl
private theorem moment_2100_439_part17 :
    blockEstimate 2100 439 2615 128 = 5596600704 := rfl
private theorem moment_2100_439_part18 :
    blockEstimate 2100 439 2743 128 = 1975910784 := rfl
private theorem moment_2100_439_part19 :
    blockEstimate 2100 439 2871 107 = 218225466 := rfl
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
    blockEstimate 2678 563 563 128 = 924004640 := rfl
private theorem moment_2678_563_part1 :
    blockEstimate 2678 563 691 128 = 6111150368 := rfl
private theorem moment_2678_563_part2 :
    blockEstimate 2678 563 819 128 = 15703363872 := rfl
private theorem moment_2678_563_part3 :
    blockEstimate 2678 563 947 128 = 28895338784 := rfl
private theorem moment_2678_563_part4 :
    blockEstimate 2678 563 1075 128 = 44725223347 := rfl
private theorem moment_2678_563_part5 :
    blockEstimate 2678 563 1203 128 = 60197172864 := rfl
private theorem moment_2678_563_part6 :
    blockEstimate 2678 563 1331 128 = 73351132800 := rfl
private theorem moment_2678_563_part7 :
    blockEstimate 2678 563 1459 128 = 84139505280 := rfl
private theorem moment_2678_563_part8 :
    blockEstimate 2678 563 1587 128 = 92562290304 := rfl
private theorem moment_2678_563_part9 :
    blockEstimate 2678 563 1715 128 = 98619487872 := rfl
private theorem moment_2678_563_part10 :
    blockEstimate 2678 563 1843 128 = 102311097984 := rfl
private theorem moment_2678_563_part11 :
    blockEstimate 2678 563 1971 128 = 103637120640 := rfl
private theorem moment_2678_563_part12 :
    blockEstimate 2678 563 2099 128 = 102597555840 := rfl
private theorem moment_2678_563_part13 :
    blockEstimate 2678 563 2227 128 = 99192403584 := rfl
private theorem moment_2678_563_part14 :
    blockEstimate 2678 563 2355 128 = 93421663872 := rfl
private theorem moment_2678_563_part15 :
    blockEstimate 2678 563 2483 128 = 85285336704 := rfl
private theorem moment_2678_563_part16 :
    blockEstimate 2678 563 2611 128 = 74814810745 := rfl
private theorem moment_2678_563_part17 :
    blockEstimate 2678 563 2739 128 = 62882490764 := rfl
private theorem moment_2678_563_part18 :
    blockEstimate 2678 563 2867 128 = 50739802930 := rfl
private theorem moment_2678_563_part19 :
    blockEstimate 2678 563 2995 128 = 38959239188 := rfl
private theorem moment_2678_563_part20 :
    blockEstimate 2678 563 3123 128 = 28030913412 := rfl
private theorem moment_2678_563_part21 :
    blockEstimate 2678 563 3251 128 = 18344851056 := rfl
private theorem moment_2678_563_part22 :
    blockEstimate 2678 563 3379 128 = 10401395312 := rfl
private theorem moment_2678_563_part23 :
    blockEstimate 2678 563 3507 128 = 4554763888 := rfl
private theorem moment_2678_563_part24 :
    blockEstimate 2678 563 3635 128 = 1056615024 := rfl
private theorem moment_2678_563_part25 :
    blockEstimate 2678 563 3763 41 = 16996463 := rfl
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
    blockEstimate 2678 584 584 128 = 924004640 := rfl
private theorem moment_2678_584_part1 :
    blockEstimate 2678 584 712 128 = 6111150368 := rfl
private theorem moment_2678_584_part2 :
    blockEstimate 2678 584 840 128 = 15703363872 := rfl
private theorem moment_2678_584_part3 :
    blockEstimate 2678 584 968 128 = 28895338784 := rfl
private theorem moment_2678_584_part4 :
    blockEstimate 2678 584 1096 128 = 44821712586 := rfl
private theorem moment_2678_584_part5 :
    blockEstimate 2678 584 1224 128 = 60886126080 := rfl
private theorem moment_2678_584_part6 :
    blockEstimate 2678 584 1352 128 = 74630499840 := rfl
private theorem moment_2678_584_part7 :
    blockEstimate 2678 584 1480 128 = 85921205760 := rfl
private theorem moment_2678_584_part8 :
    blockEstimate 2678 584 1608 128 = 94758243840 := rfl
private theorem moment_2678_584_part9 :
    blockEstimate 2678 584 1736 128 = 101141614080 := rfl
private theorem moment_2678_584_part10 :
    blockEstimate 2678 584 1864 128 = 105071316480 := rfl
private theorem moment_2678_584_part11 :
    blockEstimate 2678 584 1992 128 = 106547351040 := rfl
private theorem moment_2678_584_part12 :
    blockEstimate 2678 584 2120 128 = 105569717760 := rfl
private theorem moment_2678_584_part13 :
    blockEstimate 2678 584 2248 128 = 102138416640 := rfl
private theorem moment_2678_584_part14 :
    blockEstimate 2678 584 2376 128 = 96253447680 := rfl
private theorem moment_2678_584_part15 :
    blockEstimate 2678 584 2504 128 = 87914810880 := rfl
private theorem moment_2678_584_part16 :
    blockEstimate 2678 584 2632 128 = 77197419775 := rfl
private theorem moment_2678_584_part17 :
    blockEstimate 2678 584 2760 128 = 65154508826 := rfl
private theorem moment_2678_584_part18 :
    blockEstimate 2678 584 2888 128 = 52886238116 := rfl
private theorem moment_2678_584_part19 :
    blockEstimate 2678 584 3016 128 = 40935577062 := rfl
private theorem moment_2678_584_part20 :
    blockEstimate 2678 584 3144 128 = 29789439866 := rfl
private theorem moment_2678_584_part21 :
    blockEstimate 2678 584 3272 128 = 19830964336 := rfl
private theorem moment_2678_584_part22 :
    blockEstimate 2678 584 3400 128 = 11567529072 := rfl
private theorem moment_2678_584_part23 :
    blockEstimate 2678 584 3528 128 = 5359630448 := rfl
private theorem moment_2678_584_part24 :
    blockEstimate 2678 584 3656 128 = 1458926704 := rfl
private theorem moment_2678_584_part25 :
    blockEstimate 2678 584 3784 62 = 56510648 := rfl
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
    blockEstimate 2726 570 570 128 = 941177120 := rfl
private theorem moment_2726_570_part1 :
    blockEstimate 2726 570 698 128 = 6229772576 := rfl
private theorem moment_2726_570_part2 :
    blockEstimate 2726 570 826 128 = 16024099104 := rfl
private theorem moment_2726_570_part3 :
    blockEstimate 2726 570 954 128 = 29518850336 := rfl
private theorem moment_2726_570_part4 :
    blockEstimate 2726 570 1082 128 = 45788465784 := rfl
private theorem moment_2726_570_part5 :
    blockEstimate 2726 570 1210 128 = 61910907968 := rfl
private theorem moment_2726_570_part6 :
    blockEstimate 2726 570 1338 128 = 75709922368 := rfl
private theorem moment_2726_570_part7 :
    blockEstimate 2726 570 1466 128 = 87113989184 := rfl
private theorem moment_2726_570_part8 :
    blockEstimate 2726 570 1594 128 = 96123108416 := rfl
private theorem moment_2726_570_part9 :
    blockEstimate 2726 570 1722 128 = 102737280064 := rfl
private theorem moment_2726_570_part10 :
    blockEstimate 2726 570 1850 128 = 106956504128 := rfl
private theorem moment_2726_570_part11 :
    blockEstimate 2726 570 1978 128 = 108780780608 := rfl
private theorem moment_2726_570_part12 :
    blockEstimate 2726 570 2106 128 = 108210109504 := rfl
private theorem moment_2726_570_part13 :
    blockEstimate 2726 570 2234 128 = 105244490816 := rfl
private theorem moment_2726_570_part14 :
    blockEstimate 2726 570 2362 128 = 99883924544 := rfl
private theorem moment_2726_570_part15 :
    blockEstimate 2726 570 2490 128 = 92128410688 := rfl
private theorem moment_2726_570_part16 :
    blockEstimate 2726 570 2618 128 = 81979099023 := rfl
private theorem moment_2726_570_part17 :
    blockEstimate 2726 570 2746 128 = 69908824467 := rfl
private theorem moment_2726_570_part18 :
    blockEstimate 2726 570 2874 128 = 57337933609 := rfl
private theorem moment_2726_570_part19 :
    blockEstimate 2726 570 3002 128 = 44969478669 := rfl
private theorem moment_2726_570_part20 :
    blockEstimate 2726 570 3130 128 = 33309949796 := rfl
private theorem moment_2726_570_part21 :
    blockEstimate 2726 570 3258 128 = 22790468361 := rfl
private theorem moment_2726_570_part22 :
    blockEstimate 2726 570 3386 128 = 13842204672 := rfl
private theorem moment_2726_570_part23 :
    blockEstimate 2726 570 3514 128 = 6924756992 := rfl
private theorem moment_2726_570_part24 :
    blockEstimate 2726 570 3642 128 = 2297989120 := rfl
private theorem moment_2726_570_part25 :
    blockEstimate 2726 570 3770 96 = 207088896 := rfl
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
    blockEstimate 3438 750 750 128 = 1195902240 := rfl
private theorem moment_3438_750_part1 :
    blockEstimate 3438 750 878 128 = 7989335328 := rfl
private theorem moment_3438_750_part2 :
    blockEstimate 3438 750 1006 128 = 20781671712 := rfl
private theorem moment_3438_750_part3 :
    blockEstimate 3438 750 1134 128 = 38767605024 := rfl
private theorem moment_3438_750_part4 :
    blockEstimate 3438 750 1262 128 = 61141828896 := rfl
private theorem moment_3438_750_part5 :
    blockEstimate 3438 750 1390 128 = 87096444885 := rfl
private theorem moment_3438_750_part6 :
    blockEstimate 3438 750 1518 128 = 114498877888 := rfl
private theorem moment_3438_750_part7 :
    blockEstimate 3438 750 1646 128 = 139366037952 := rfl
private theorem moment_3438_750_part8 :
    blockEstimate 3438 750 1774 128 = 161083275712 := rfl
private theorem moment_3438_750_part9 :
    blockEstimate 3438 750 1902 128 = 179650591168 := rfl
private theorem moment_3438_750_part10 :
    blockEstimate 3438 750 2030 128 = 195067984320 := rfl
private theorem moment_3438_750_part11 :
    blockEstimate 3438 750 2158 128 = 207335455168 := rfl
private theorem moment_3438_750_part12 :
    blockEstimate 3438 750 2286 128 = 216453003712 := rfl
private theorem moment_3438_750_part13 :
    blockEstimate 3438 750 2414 128 = 222420629952 := rfl
private theorem moment_3438_750_part14 :
    blockEstimate 3438 750 2542 128 = 225238333888 := rfl
private theorem moment_3438_750_part15 :
    blockEstimate 3438 750 2670 128 = 224906115520 := rfl
private theorem moment_3438_750_part16 :
    blockEstimate 3438 750 2798 128 = 221423974848 := rfl
private theorem moment_3438_750_part17 :
    blockEstimate 3438 750 2926 128 = 214791911872 := rfl
private theorem moment_3438_750_part18 :
    blockEstimate 3438 750 3054 128 = 205009926592 := rfl
private theorem moment_3438_750_part19 :
    blockEstimate 3438 750 3182 128 = 192078019008 := rfl
private theorem moment_3438_750_part20 :
    blockEstimate 3438 750 3310 128 = 175996189120 := rfl
private theorem moment_3438_750_part21 :
    blockEstimate 3438 750 3438 128 = 157132247091 := rfl
private theorem moment_3438_750_part22 :
    blockEstimate 3438 750 3566 128 = 137136148062 := rfl
private theorem moment_3438_750_part23 :
    blockEstimate 3438 750 3694 128 = 116886978890 := rfl
private theorem moment_3438_750_part24 :
    blockEstimate 3438 750 3822 128 = 96919956452 := rfl
private theorem moment_3438_750_part25 :
    blockEstimate 3438 750 3950 128 = 77735984777 := rfl
private theorem moment_3438_750_part26 :
    blockEstimate 3438 750 4078 128 = 59798769904 := rfl
private theorem moment_3438_750_part27 :
    blockEstimate 3438 750 4206 128 = 43425779232 := rfl
private theorem moment_3438_750_part28 :
    blockEstimate 3438 750 4334 128 = 29202290208 := rfl
private theorem moment_3438_750_part29 :
    blockEstimate 3438 750 4462 128 = 17520614944 := rfl
private theorem moment_3438_750_part30 :
    blockEstimate 3438 750 4590 128 = 8632411680 := rfl
private theorem moment_3438_750_part31 :
    blockEstimate 3438 750 4718 128 = 2789338656 := rfl
private theorem moment_3438_750_part32 :
    blockEstimate 3438 750 4846 92 = 231246439 := rfl
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

private theorem receipt_0_8_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 0 128 = 533457038967798532811651520 := rfl
private theorem receipt_0_8_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 128 128 = 373589289509656646079199680 := rfl
private theorem receipt_0_8_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 256 128 = 230524885661836825000970193 := rfl
private theorem receipt_0_8_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 384 128 = 103334116826387530432644820 := rfl
private theorem receipt_0_8_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 512 52 = 9104122288216038622106507 := rfl
private theorem receipt_0_8_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 0 256 = 907046328477455178890851200 :=
  phaseBlock_append receipt_0_8_2339_0_part0 receipt_0_8_2339_0_part1 rfl rfl rfl
private theorem receipt_0_8_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 384 180 = 112438239114603569054751327 :=
  phaseBlock_append receipt_0_8_2339_0_part3 receipt_0_8_2339_0_part4 rfl rfl rfl
private theorem receipt_0_8_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 256 308 = 342963124776440394055721520 :=
  phaseBlock_append receipt_0_8_2339_0_part2 receipt_0_8_2339_0_join1 rfl rfl rfl
private theorem receipt_0_8_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 0) 0 564 = 1250009453253895572946572720 :=
  phaseBlock_append receipt_0_8_2339_0_join0 receipt_0_8_2339_0_join2 rfl rfl rfl

private theorem receipt_0_8_2339_0 : fastPhase (bank 0 8).shape 179827 2339 16 1 0 1 0 = 1250009453253895572946572720 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2339_0_join3

private theorem receipt_0_8_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 0 128 = 532156681657059228709174848 := rfl
private theorem receipt_0_8_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 128 128 = 372419352364937341283147328 := rfl
private theorem receipt_0_8_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 256 128 = 229478320814087245772556840 := rfl
private theorem receipt_0_8_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 384 128 = 102403906282250574323010798 := rfl
private theorem receipt_0_8_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 512 52 = 8757857541910216981638960 := rfl
private theorem receipt_0_8_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 0 256 = 904576034021996569992322176 :=
  phaseBlock_append receipt_0_8_2339_1_part0 receipt_0_8_2339_1_part1 rfl rfl rfl
private theorem receipt_0_8_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 384 180 = 111161763824160791304649758 :=
  phaseBlock_append receipt_0_8_2339_1_part3 receipt_0_8_2339_1_part4 rfl rfl rfl
private theorem receipt_0_8_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 256 308 = 340640084638248037077206598 :=
  phaseBlock_append receipt_0_8_2339_1_part2 receipt_0_8_2339_1_join1 rfl rfl rfl
private theorem receipt_0_8_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2339 16 1 0 1 1) 0 564 = 1245216118660244607069528774 :=
  phaseBlock_append receipt_0_8_2339_1_join0 receipt_0_8_2339_1_join2 rfl rfl rfl

private theorem receipt_0_8_2339_1 : fastPhase (bank 0 8).shape 179827 2339 16 1 0 1 1 = 1245216118660244607069528774 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2339_1_join3

private theorem receipt_0_8_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 0 128 = 533461662602736732626968480 := rfl
private theorem receipt_0_8_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 128 128 = 373592083006582184408887200 := rfl
private theorem receipt_0_8_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 256 128 = 230526317186508751676648189 := rfl
private theorem receipt_0_8_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 384 128 = 103334621019886329249772074 := rfl
private theorem receipt_0_8_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 512 52 = 9104156796734553272578915 := rfl
private theorem receipt_0_8_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 0 256 = 907053745609318917035855680 :=
  phaseBlock_append receipt_0_8_2340_0_part0 receipt_0_8_2340_0_part1 rfl rfl rfl
private theorem receipt_0_8_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 384 180 = 112438777816620882522350989 :=
  phaseBlock_append receipt_0_8_2340_0_part3 receipt_0_8_2340_0_part4 rfl rfl rfl
private theorem receipt_0_8_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 256 308 = 342965095003129634198999178 :=
  phaseBlock_append receipt_0_8_2340_0_part2 receipt_0_8_2340_0_join1 rfl rfl rfl
private theorem receipt_0_8_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 0) 0 564 = 1250018840612448551234854858 :=
  phaseBlock_append receipt_0_8_2340_0_join0 receipt_0_8_2340_0_join2 rfl rfl rfl

private theorem receipt_0_8_2340_0 : fastPhase (bank 0 8).shape 179827 2340 16 1 0 1 0 = 1250018840612448551234854858 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2340_0_join3

private theorem receipt_0_8_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 0 128 = 532161295994752582182604960 := rfl
private theorem receipt_0_8_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 128 128 = 372422138436799634400133280 := rfl
private theorem receipt_0_8_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 256 128 = 229479746634777735974253228 := rfl
private theorem receipt_0_8_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 384 128 = 102404406357705580264960700 := rfl
private theorem receipt_0_8_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 512 52 = 8757890796632278530955297 := rfl
private theorem receipt_0_8_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 0 256 = 904583434431552216582738240 :=
  phaseBlock_append receipt_0_8_2340_1_part0 receipt_0_8_2340_1_part1 rfl rfl rfl
private theorem receipt_0_8_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 384 180 = 111162297154337858795915997 :=
  phaseBlock_append receipt_0_8_2340_1_part3 receipt_0_8_2340_1_part4 rfl rfl rfl
private theorem receipt_0_8_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 256 308 = 340642043789115594770169225 :=
  phaseBlock_append receipt_0_8_2340_1_part2 receipt_0_8_2340_1_join1 rfl rfl rfl
private theorem receipt_0_8_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 8).shape 179827 2340 16 1 0 1 1) 0 564 = 1245225478220667811352907465 :=
  phaseBlock_append receipt_0_8_2340_1_join0 receipt_0_8_2340_1_join2 rfl rfl rfl

private theorem receipt_0_8_2340_1 : fastPhase (bank 0 8).shape 179827 2340 16 1 0 1 1 = 1245225478220667811352907465 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_0_8_2340_1_join3

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_8_2339_0 receipt_0_8_2339_1 receipt_0_8_2340_0 receipt_0_8_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_8_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 0 128 = 479914104747775510528215840 := rfl
private theorem receipt_1_8_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 128 128 = 335648720507375182633818912 := rfl
private theorem receipt_1_8_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 256 128 = 206841778138338311439062778 := rfl
private theorem receipt_1_8_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 384 128 = 92600196845892154805775312 := rfl
private theorem receipt_1_8_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 512 52 = 8150435828152142816250990 := rfl
private theorem receipt_1_8_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 0 256 = 815562825255150693162034752 :=
  phaseBlock_append receipt_1_8_2339_0_part0 receipt_1_8_2339_0_part1 rfl rfl rfl
private theorem receipt_1_8_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 384 180 = 100750632674044297622026302 :=
  phaseBlock_append receipt_1_8_2339_0_part3 receipt_1_8_2339_0_part4 rfl rfl rfl
private theorem receipt_1_8_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 256 308 = 307592410812382609061089080 :=
  phaseBlock_append receipt_1_8_2339_0_part2 receipt_1_8_2339_0_join1 rfl rfl rfl
private theorem receipt_1_8_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 0) 0 564 = 1123155236067533302223123832 :=
  phaseBlock_append receipt_1_8_2339_0_join0 receipt_1_8_2339_0_join2 rfl rfl rfl

private theorem receipt_1_8_2339_0 : fastPhase (bank 1 8).shape 179827 2339 16 1 0 2 0 = 1123155236067533302223123832 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2339_0_join3

private theorem receipt_1_8_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 0 128 = 478739320312132424558155104 := rfl
private theorem receipt_1_8_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 128 128 = 334594152278196487670138208 := rfl
private theorem receipt_1_8_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 256 128 = 205900635924873988136746470 := rfl
private theorem receipt_1_8_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 384 128 = 91765750739313659352966396 := rfl
private theorem receipt_1_8_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 512 52 = 7840388551341221148832158 := rfl
private theorem receipt_1_8_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 0 256 = 813333472590328912228293312 :=
  phaseBlock_append receipt_1_8_2339_1_part0 receipt_1_8_2339_1_part1 rfl rfl rfl
private theorem receipt_1_8_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 384 180 = 99606139290654880501798554 :=
  phaseBlock_append receipt_1_8_2339_1_part3 receipt_1_8_2339_1_part4 rfl rfl rfl
private theorem receipt_1_8_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 256 308 = 305506775215528868638545024 :=
  phaseBlock_append receipt_1_8_2339_1_part2 receipt_1_8_2339_1_join1 rfl rfl rfl
private theorem receipt_1_8_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2339 16 1 0 2 1) 0 564 = 1118840247805857780866838336 :=
  phaseBlock_append receipt_1_8_2339_1_join0 receipt_1_8_2339_1_join2 rfl rfl rfl

private theorem receipt_1_8_2339_1 : fastPhase (bank 1 8).shape 179827 2339 16 1 0 2 1 = 1118840247805857780866838336 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2339_1_join3

private theorem receipt_1_8_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 0 128 = 479918264370893824090361920 := rfl
private theorem receipt_1_8_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 128 128 = 335651230351156670767525952 := rfl
private theorem receipt_1_8_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 256 128 = 206843062624473653845839258 := rfl
private theorem receipt_1_8_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 384 128 = 92600648679304997447840844 := rfl
private theorem receipt_1_8_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 512 52 = 8150466721946464845565026 := rfl
private theorem receipt_1_8_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 0 256 = 815569494722050494857887872 :=
  phaseBlock_append receipt_1_8_2340_0_part0 receipt_1_8_2340_0_part1 rfl rfl rfl
private theorem receipt_1_8_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 384 180 = 100751115401251462293405870 :=
  phaseBlock_append receipt_1_8_2340_0_part3 receipt_1_8_2340_0_part4 rfl rfl rfl
private theorem receipt_1_8_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 256 308 = 307594178025725116139245128 :=
  phaseBlock_append receipt_1_8_2340_0_part2 receipt_1_8_2340_0_join1 rfl rfl rfl
private theorem receipt_1_8_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 0) 0 564 = 1123163672747775610997133000 :=
  phaseBlock_append receipt_1_8_2340_0_join0 receipt_1_8_2340_0_join2 rfl rfl rfl

private theorem receipt_1_8_2340_0 : fastPhase (bank 1 8).shape 179827 2340 16 1 0 2 0 = 1123163672747775610997133000 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2340_0_join3

private theorem receipt_1_8_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 0 128 = 478743471528161091942994752 := rfl
private theorem receipt_1_8_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 128 128 = 334596655425061721643103040 := rfl
private theorem receipt_1_8_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 256 128 = 205901915279864910219255912 := rfl
private theorem receipt_1_8_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 384 128 = 91766198878093486968570795 := rfl
private theorem receipt_1_8_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 512 52 = 7840418322458364190179813 := rfl
private theorem receipt_1_8_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 0 256 = 813340126953222813586097792 :=
  phaseBlock_append receipt_1_8_2340_1_part0 receipt_1_8_2340_1_part1 rfl rfl rfl
private theorem receipt_1_8_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 384 180 = 99606617200551851158750608 :=
  phaseBlock_append receipt_1_8_2340_1_part3 receipt_1_8_2340_1_part4 rfl rfl rfl
private theorem receipt_1_8_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 256 308 = 305508532480416761378006520 :=
  phaseBlock_append receipt_1_8_2340_1_part2 receipt_1_8_2340_1_join1 rfl rfl rfl
private theorem receipt_1_8_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 8).shape 179827 2340 16 1 0 2 1) 0 564 = 1118848659433639574964104312 :=
  phaseBlock_append receipt_1_8_2340_1_join0 receipt_1_8_2340_1_join2 rfl rfl rfl

private theorem receipt_1_8_2340_1 : fastPhase (bank 1 8).shape 179827 2340 16 1 0 2 1 = 1118848659433639574964104312 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_1_8_2340_1_join3

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_8_2339_0 receipt_1_8_2339_1 receipt_1_8_2340_0 receipt_1_8_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_8_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 0 128 = 255898891796815596012184896 := rfl
private theorem receipt_2_8_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 128 128 = 177272429602377085221668160 := rfl
private theorem receipt_2_8_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 256 128 = 108205054981204034544113826 := rfl
private theorem receipt_2_8_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 384 128 = 47993515266194807245622098 := rfl
private theorem receipt_2_8_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 512 52 = 4193967652020668699817098 := rfl
private theorem receipt_2_8_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 0 256 = 433171321399192681233853056 :=
  phaseBlock_append receipt_2_8_2339_0_part0 receipt_2_8_2339_0_part1 rfl rfl rfl
private theorem receipt_2_8_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 384 180 = 52187482918215475945439196 :=
  phaseBlock_append receipt_2_8_2339_0_part3 receipt_2_8_2339_0_part4 rfl rfl rfl
private theorem receipt_2_8_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 256 308 = 160392537899419510489553022 :=
  phaseBlock_append receipt_2_8_2339_0_part2 receipt_2_8_2339_0_join1 rfl rfl rfl
private theorem receipt_2_8_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 0) 0 564 = 593563859298612191723406078 :=
  phaseBlock_append receipt_2_8_2339_0_join0 receipt_2_8_2339_0_join2 rfl rfl rfl

private theorem receipt_2_8_2339_0 : fastPhase (bank 2 8).shape 179827 2339 16 1 0 7 0 = 593563859298612191723406078 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2339_0_join3

private theorem receipt_2_8_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 0 128 = 255253458115434891547256448 := rfl
private theorem receipt_2_8_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 128 128 = 176702257967242594163238528 := rfl
private theorem receipt_2_8_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 256 128 = 107704715639815976661537456 := rfl
private theorem receipt_2_8_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 384 128 = 47557756630742875260105936 := rfl
private theorem receipt_2_8_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 512 52 = 4034218727884989555031272 := rfl
private theorem receipt_2_8_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 0 256 = 431955716082677485710494976 :=
  phaseBlock_append receipt_2_8_2339_1_part0 receipt_2_8_2339_1_part1 rfl rfl rfl
private theorem receipt_2_8_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 384 180 = 51591975358627864815137208 :=
  phaseBlock_append receipt_2_8_2339_1_part3 receipt_2_8_2339_1_part4 rfl rfl rfl
private theorem receipt_2_8_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 256 308 = 159296690998443841476674664 :=
  phaseBlock_append receipt_2_8_2339_1_part2 receipt_2_8_2339_1_join1 rfl rfl rfl
private theorem receipt_2_8_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2339 16 1 0 7 1) 0 564 = 591252407081121327187169640 :=
  phaseBlock_append receipt_2_8_2339_1_join0 receipt_2_8_2339_1_join2 rfl rfl rfl

private theorem receipt_2_8_2339_1 : fastPhase (bank 2 8).shape 179827 2339 16 1 0 7 1 = 591252407081121327187169640 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2339_1_join3

private theorem receipt_2_8_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 0 128 = 255901110018330234749155456 := rfl
private theorem receipt_2_8_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 128 128 = 177273755348262014366636160 := rfl
private theorem receipt_2_8_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 256 128 = 108205727048273541740889602 := rfl
private theorem receipt_2_8_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 384 128 = 47993749496840141480143650 := rfl
private theorem receipt_2_8_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 512 52 = 4193983549621431824617831 := rfl
private theorem receipt_2_8_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 0 256 = 433174865366592249115791616 :=
  phaseBlock_append receipt_2_8_2340_0_part0 receipt_2_8_2340_0_part1 rfl rfl rfl
private theorem receipt_2_8_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 384 180 = 52187733046461573304761481 :=
  phaseBlock_append receipt_2_8_2340_0_part3 receipt_2_8_2340_0_part4 rfl rfl rfl
private theorem receipt_2_8_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 256 308 = 160393460094735115045651083 :=
  phaseBlock_append receipt_2_8_2340_0_part2 receipt_2_8_2340_0_join1 rfl rfl rfl
private theorem receipt_2_8_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 0) 0 564 = 593568325461327364161442699 :=
  phaseBlock_append receipt_2_8_2340_0_join0 receipt_2_8_2340_0_join2 rfl rfl rfl

private theorem receipt_2_8_2340_0 : fastPhase (bank 2 8).shape 179827 2340 16 1 0 7 0 = 593568325461327364161442699 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2340_0_join3

private theorem receipt_2_8_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 0 128 = 255255671688687271256495296 := rfl
private theorem receipt_2_8_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 128 128 = 176703580076854275972420800 := rfl
private theorem receipt_2_8_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 256 128 = 107705384972399247126126786 := rfl
private theorem receipt_2_8_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 384 128 = 47557988929956237424126220 := rfl
private theorem receipt_2_8_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 512 52 = 4034234046956524104593284 := rfl
private theorem receipt_2_8_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 0 256 = 431959251765541547228916096 :=
  phaseBlock_append receipt_2_8_2340_1_part0 receipt_2_8_2340_1_part1 rfl rfl rfl
private theorem receipt_2_8_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 384 180 = 51592222976912761528719504 :=
  phaseBlock_append receipt_2_8_2340_1_part3 receipt_2_8_2340_1_part4 rfl rfl rfl
private theorem receipt_2_8_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 256 308 = 159297607949312008654846290 :=
  phaseBlock_append receipt_2_8_2340_1_part2 receipt_2_8_2340_1_join1 rfl rfl rfl
private theorem receipt_2_8_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 8).shape 179827 2340 16 1 0 7 1) 0 564 = 591256859714853555883762386 :=
  phaseBlock_append receipt_2_8_2340_1_join0 receipt_2_8_2340_1_join2 rfl rfl rfl

private theorem receipt_2_8_2340_1 : fastPhase (bank 2 8).shape 179827 2340 16 1 0 7 1 = 591256859714853555883762386 :=
  phase_of_block (n := 564) (by decide +kernel) receipt_2_8_2340_1_join3

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_563)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_8_2339_0 receipt_2_8_2339_1 receipt_2_8_2340_0 receipt_2_8_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_8_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 0 128 = 45934573609227903066259968 := rfl
private theorem receipt_3_8_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 128 128 = 32303582470848087630963200 := rfl
private theorem receipt_3_8_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 256 128 = 20154692386942090074096128 := rfl
private theorem receipt_3_8_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 384 128 = 9579036979621954748981760 := rfl
private theorem receipt_3_8_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 512 73 = 1361662417321066799160950 := rfl
private theorem receipt_3_8_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 0 256 = 78238156080075990697223168 :=
  phaseBlock_append receipt_3_8_2339_0_part0 receipt_3_8_2339_0_part1 rfl rfl rfl
private theorem receipt_3_8_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 384 201 = 10940699396943021548142710 :=
  phaseBlock_append receipt_3_8_2339_0_part3 receipt_3_8_2339_0_part4 rfl rfl rfl
private theorem receipt_3_8_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 256 329 = 31095391783885111622238838 :=
  phaseBlock_append receipt_3_8_2339_0_part2 receipt_3_8_2339_0_join1 rfl rfl rfl
private theorem receipt_3_8_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 0) 0 585 = 109333547863961102319462006 :=
  phaseBlock_append receipt_3_8_2339_0_join0 receipt_3_8_2339_0_join2 rfl rfl rfl

private theorem receipt_3_8_2339_0 : fastPhase (bank 3 8).shape 179827 2339 16 1 1 1 0 = 109333547863961102319462006 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2339_0_join3

private theorem receipt_3_8_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 0 128 = 45823935284742031401787264 := rfl
private theorem receipt_3_8_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 128 128 = 32203741748051764915797888 := rfl
private theorem receipt_3_8_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 256 128 = 20066427017929316223836032 := rfl
private theorem receipt_3_8_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 384 128 = 9503110374208845440335744 := rfl
private theorem receipt_3_8_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 512 73 = 1324173625204106159520936 := rfl
private theorem receipt_3_8_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 0 256 = 78027677032793796317585152 :=
  phaseBlock_append receipt_3_8_2339_1_part0 receipt_3_8_2339_1_part1 rfl rfl rfl
private theorem receipt_3_8_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 384 201 = 10827283999412951599856680 :=
  phaseBlock_append receipt_3_8_2339_1_part3 receipt_3_8_2339_1_part4 rfl rfl rfl
private theorem receipt_3_8_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 256 329 = 30893711017342267823692712 :=
  phaseBlock_append receipt_3_8_2339_1_part2 receipt_3_8_2339_1_join1 rfl rfl rfl
private theorem receipt_3_8_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2339 16 1 1 1 1) 0 585 = 108921388050136064141277864 :=
  phaseBlock_append receipt_3_8_2339_1_join0 receipt_3_8_2339_1_join2 rfl rfl rfl

private theorem receipt_3_8_2339_1 : fastPhase (bank 3 8).shape 179827 2339 16 1 1 1 1 = 108921388050136064141277864 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2339_1_join3

private theorem receipt_3_8_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 0 128 = 45934956380102802537448224 := rfl
private theorem receipt_3_8_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 128 128 = 32303789156259863680193312 := rfl
private theorem receipt_3_8_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 256 128 = 20154784069386262168871712 := rfl
private theorem receipt_3_8_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 384 128 = 9579063907597360363025184 := rfl
private theorem receipt_3_8_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 512 73 = 1361664400126123044940930 := rfl
private theorem receipt_3_8_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 0 256 = 78238745536362666217641536 :=
  phaseBlock_append receipt_3_8_2340_0_part0 receipt_3_8_2340_0_part1 rfl rfl rfl
private theorem receipt_3_8_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 384 201 = 10940728307723483407966114 :=
  phaseBlock_append receipt_3_8_2340_0_part3 receipt_3_8_2340_0_part4 rfl rfl rfl
private theorem receipt_3_8_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 256 329 = 31095512377109745576837826 :=
  phaseBlock_append receipt_3_8_2340_0_part2 receipt_3_8_2340_0_join1 rfl rfl rfl
private theorem receipt_3_8_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 0) 0 585 = 109334257913472411794479362 :=
  phaseBlock_append receipt_3_8_2340_0_join0 receipt_3_8_2340_0_join2 rfl rfl rfl

private theorem receipt_3_8_2340_0 : fastPhase (bank 3 8).shape 179827 2340 16 1 1 1 0 = 109334257913472411794479362 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2340_0_join3

private theorem receipt_3_8_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 0 128 = 45824316996483077712917792 := rfl
private theorem receipt_3_8_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 128 128 = 32203947712864364187043104 := rfl
private theorem receipt_3_8_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 256 128 = 20066518258225707488007456 := rfl
private theorem receipt_3_8_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 384 128 = 9503137079446055176201504 := rfl
private theorem receipt_3_8_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 512 73 = 1324175556930542736783786 := rfl
private theorem receipt_3_8_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 0 256 = 78028264709347441899960896 :=
  phaseBlock_append receipt_3_8_2340_1_part0 receipt_3_8_2340_1_part1 rfl rfl rfl
private theorem receipt_3_8_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 384 201 = 10827312636376597912985290 :=
  phaseBlock_append receipt_3_8_2340_1_part3 receipt_3_8_2340_1_part4 rfl rfl rfl
private theorem receipt_3_8_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 256 329 = 30893830894602305400992746 :=
  phaseBlock_append receipt_3_8_2340_1_part2 receipt_3_8_2340_1_join1 rfl rfl rfl
private theorem receipt_3_8_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 8).shape 179827 2340 16 1 1 1 1) 0 585 = 108922095603949747300953642 :=
  phaseBlock_append receipt_3_8_2340_1_join0 receipt_3_8_2340_1_join2 rfl rfl rfl

private theorem receipt_3_8_2340_1 : fastPhase (bank 3 8).shape 179827 2340 16 1 1 1 1 = 108922095603949747300953642 :=
  phase_of_block (n := 585) (by decide +kernel) receipt_3_8_2340_1_join3

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2678_584)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_8_2339_0 receipt_3_8_2339_1 receipt_3_8_2340_0 receipt_3_8_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_9_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 0 128 = 138823068364924696603301072 := rfl
private theorem receipt_0_9_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 128 128 = 84764956930464645428937540 := rfl
private theorem receipt_0_9_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 256 128 = 38034901305968314697334014 := rfl
private theorem receipt_0_9_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 384 56 = 3701127952557238075753916 := rfl
private theorem receipt_0_9_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 0 256 = 223588025295389342032238612 :=
  phaseBlock_append receipt_0_9_2339_0_part0 receipt_0_9_2339_0_part1 rfl rfl rfl
private theorem receipt_0_9_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 256 184 = 41736029258525552773087930 :=
  phaseBlock_append receipt_0_9_2339_0_part2 receipt_0_9_2339_0_part3 rfl rfl rfl
private theorem receipt_0_9_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 0) 0 440 = 265324054553914894805326542 :=
  phaseBlock_append receipt_0_9_2339_0_join0 receipt_0_9_2339_0_join1 rfl rfl rfl

private theorem receipt_0_9_2339_0 : fastPhase (bank 0 9).shape 179827 2339 10 1 0 1 0 = 265324054553914894805326542 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2339_0_join2

private theorem receipt_0_9_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 0 128 = 138376376189563381521522702 := rfl
private theorem receipt_0_9_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 128 128 = 84375605619221343619630986 := rfl
private theorem receipt_0_9_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 256 128 = 37698860945102090463453870 := rfl
private theorem receipt_0_9_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 384 56 = 3569849859064412621256384 := rfl
private theorem receipt_0_9_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 0 256 = 222751981808784725141153688 :=
  phaseBlock_append receipt_0_9_2339_1_part0 receipt_0_9_2339_1_part1 rfl rfl rfl
private theorem receipt_0_9_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 256 184 = 41268710804166503084710254 :=
  phaseBlock_append receipt_0_9_2339_1_part2 receipt_0_9_2339_1_part3 rfl rfl rfl
private theorem receipt_0_9_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2339 10 1 0 1 1) 0 440 = 264020692612951228225863942 :=
  phaseBlock_append receipt_0_9_2339_1_join0 receipt_0_9_2339_1_join1 rfl rfl rfl

private theorem receipt_0_9_2339_1 : fastPhase (bank 0 9).shape 179827 2339 10 1 0 1 1 = 264020692612951228225863942 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2339_1_join2

private theorem receipt_0_9_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 0 128 = 138824266264238394582266242 := rfl
private theorem receipt_0_9_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 128 128 = 84765554616505273041352762 := rfl
private theorem receipt_0_9_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 256 128 = 38035106161019892468717214 := rfl
private theorem receipt_0_9_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 384 56 = 3701142752271792612926589 := rfl
private theorem receipt_0_9_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 0 256 = 223589820880743667623619004 :=
  phaseBlock_append receipt_0_9_2340_0_part0 receipt_0_9_2340_0_part1 rfl rfl rfl
private theorem receipt_0_9_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 256 184 = 41736248913291685081643803 :=
  phaseBlock_append receipt_0_9_2340_0_part2 receipt_0_9_2340_0_part3 rfl rfl rfl
private theorem receipt_0_9_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 0) 0 440 = 265326069794035352705262807 :=
  phaseBlock_append receipt_0_9_2340_0_join0 receipt_0_9_2340_0_join1 rfl rfl rfl

private theorem receipt_0_9_2340_0 : fastPhase (bank 0 9).shape 179827 2340 10 1 0 1 0 = 265326069794035352705262807 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2340_0_join2

private theorem receipt_0_9_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 0 128 = 138377570900875216747518091 := rfl
private theorem receipt_0_9_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 128 128 = 84376200950488493017531088 := rfl
private theorem receipt_0_9_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 256 128 = 37699064188635495760432491 := rfl
private theorem receipt_0_9_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 384 56 = 3569864164422546549181323 := rfl
private theorem receipt_0_9_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 0 256 = 222753771851363709765049179 :=
  phaseBlock_append receipt_0_9_2340_1_part0 receipt_0_9_2340_1_part1 rfl rfl rfl
private theorem receipt_0_9_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 256 184 = 41268928353058042309613814 :=
  phaseBlock_append receipt_0_9_2340_1_part2 receipt_0_9_2340_1_part3 rfl rfl rfl
private theorem receipt_0_9_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 9).shape 179827 2340 10 1 0 1 1) 0 440 = 264022700204421752074662993 :=
  phaseBlock_append receipt_0_9_2340_1_join0 receipt_0_9_2340_1_join1 rfl rfl rfl

private theorem receipt_0_9_2340_1 : fastPhase (bank 0 9).shape 179827 2340 10 1 0 1 1 = 264022700204421752074662993 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_0_9_2340_1_join2

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_9_2339_0 receipt_0_9_2339_1 receipt_0_9_2340_0 receipt_0_9_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_9_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 0 128 = 125064391298030634419381823 := rfl
private theorem receipt_1_9_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 128 128 = 76231729917786255384773349 := rfl
private theorem receipt_1_9_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 256 128 = 34148429220342813520986570 := rfl
private theorem receipt_1_9_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 384 56 = 3318593448777175888938423 := rfl
private theorem receipt_1_9_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 0 256 = 201296121215816889804155172 :=
  phaseBlock_append receipt_1_9_2339_0_part0 receipt_1_9_2339_0_part1 rfl rfl rfl
private theorem receipt_1_9_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 256 184 = 37467022669119989409924993 :=
  phaseBlock_append receipt_1_9_2339_0_part2 receipt_1_9_2339_0_part3 rfl rfl rfl
private theorem receipt_1_9_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 0) 0 440 = 238763143884936879214080165 :=
  phaseBlock_append receipt_1_9_2339_0_join0 receipt_1_9_2339_0_join1 rfl rfl rfl

private theorem receipt_1_9_2339_0 : fastPhase (bank 1 9).shape 179827 2339 10 1 0 2 0 = 238763143884936879214080165 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2339_0_join2

private theorem receipt_1_9_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 0 128 = 124660276432264678448935815 := rfl
private theorem receipt_1_9_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 128 128 = 75880553589069941779373919 := rfl
private theorem receipt_1_9_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 256 128 = 33846302978921853871634808 := rfl
private theorem receipt_1_9_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 384 56 = 3200854100238829787162031 := rfl
private theorem receipt_1_9_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 0 256 = 200540830021334620228309734 :=
  phaseBlock_append receipt_1_9_2339_1_part0 receipt_1_9_2339_1_part1 rfl rfl rfl
private theorem receipt_1_9_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 256 184 = 37047157079160683658796839 :=
  phaseBlock_append receipt_1_9_2339_1_part2 receipt_1_9_2339_1_part3 rfl rfl rfl
private theorem receipt_1_9_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2339 10 1 0 2 1) 0 440 = 237587987100495303887106573 :=
  phaseBlock_append receipt_1_9_2339_1_join0 receipt_1_9_2339_1_join1 rfl rfl rfl

private theorem receipt_1_9_2339_1 : fastPhase (bank 1 9).shape 179827 2339 10 1 0 2 1 = 237587987100495303887106573 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2339_1_join2

private theorem receipt_1_9_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 0 128 = 125065470501849469981337832 := rfl
private theorem receipt_1_9_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 128 128 = 76232267453476194221433025 := rfl
private theorem receipt_1_9_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 256 128 = 34148613151192045538018816 := rfl
private theorem receipt_1_9_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 384 56 = 3318606718972224043305378 := rfl
private theorem receipt_1_9_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 0 256 = 201297737955325664202770857 :=
  phaseBlock_append receipt_1_9_2340_0_part0 receipt_1_9_2340_0_part1 rfl rfl rfl
private theorem receipt_1_9_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 256 184 = 37467219870164269581324194 :=
  phaseBlock_append receipt_1_9_2340_0_part2 receipt_1_9_2340_0_part3 rfl rfl rfl
private theorem receipt_1_9_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 0) 0 440 = 238764957825489933784095051 :=
  phaseBlock_append receipt_1_9_2340_0_join0 receipt_1_9_2340_0_join1 rfl rfl rfl

private theorem receipt_1_9_2340_0 : fastPhase (bank 1 9).shape 179827 2340 10 1 0 2 0 = 238764957825489933784095051 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2340_0_join2

private theorem receipt_1_9_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 0 128 = 124661352749331689224492015 := rfl
private theorem receipt_1_9_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 128 128 = 75881088999754529039956098 := rfl
private theorem receipt_1_9_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 256 128 = 33846485460554126758965935 := rfl
private theorem receipt_1_9_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 384 56 = 3200866927044914755391526 := rfl
private theorem receipt_1_9_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 0 256 = 200542441749086218264448113 :=
  phaseBlock_append receipt_1_9_2340_1_part0 receipt_1_9_2340_1_part1 rfl rfl rfl
private theorem receipt_1_9_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 256 184 = 37047352387599041514357461 :=
  phaseBlock_append receipt_1_9_2340_1_part2 receipt_1_9_2340_1_part3 rfl rfl rfl
private theorem receipt_1_9_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 9).shape 179827 2340 10 1 0 2 1) 0 440 = 237589794136685259778805574 :=
  phaseBlock_append receipt_1_9_2340_1_join0 receipt_1_9_2340_1_join1 rfl rfl rfl

private theorem receipt_1_9_2340_1 : fastPhase (bank 1 9).shape 179827 2340 10 1 0 2 1 = 237589794136685259778805574 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_1_9_2340_1_join2

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_9_2339_0 receipt_1_9_2339_1 receipt_1_9_2340_0 receipt_1_9_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_9_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 0 128 = 67364572376296872840817642 := rfl
private theorem receipt_2_9_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 128 128 = 40552343105145198061587444 := rfl
private theorem receipt_2_9_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 256 128 = 17945336026016215640137868 := rfl
private theorem receipt_2_9_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 384 56 = 1727376020920199646511375 := rfl
private theorem receipt_2_9_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 0 256 = 107916915481442070902405086 :=
  phaseBlock_append receipt_2_9_2339_0_part0 receipt_2_9_2339_0_part1 rfl rfl rfl
private theorem receipt_2_9_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 256 184 = 19672712046936415286649243 :=
  phaseBlock_append receipt_2_9_2339_0_part2 receipt_2_9_2339_0_part3 rfl rfl rfl
private theorem receipt_2_9_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 0) 0 440 = 127589627528378486189054329 :=
  phaseBlock_append receipt_2_9_2339_0_join0 receipt_2_9_2339_0_join1 rfl rfl rfl

private theorem receipt_2_9_2339_0 : fastPhase (bank 2 9).shape 179827 2339 10 1 0 7 0 = 127589627528378486189054329 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2339_0_join2

private theorem receipt_2_9_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 0 128 = 67140354976550622961757013 := rfl
private theorem receipt_2_9_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 128 128 = 40361608234139944778880395 := rfl
private theorem receipt_2_9_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 256 128 = 17784948323230878742801148 := rfl
private theorem receipt_2_9_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 384 56 = 1665978037858142079609663 := rfl
private theorem receipt_2_9_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 0 256 = 107501963210690567740637408 :=
  phaseBlock_append receipt_2_9_2339_1_part0 receipt_2_9_2339_1_part1 rfl rfl rfl
private theorem receipt_2_9_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 256 184 = 19450926361089020822410811 :=
  phaseBlock_append receipt_2_9_2339_1_part2 receipt_2_9_2339_1_part3 rfl rfl rfl
private theorem receipt_2_9_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2339 10 1 0 7 1) 0 440 = 126952889571779588563048219 :=
  phaseBlock_append receipt_2_9_2339_1_join0 receipt_2_9_2339_1_join1 rfl rfl rfl

private theorem receipt_2_9_2339_1 : fastPhase (bank 2 9).shape 179827 2339 10 1 0 7 1 = 126952889571779588563048219 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2339_1_join2

private theorem receipt_2_9_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 0 128 = 67365153784454520771605265 := rfl
private theorem receipt_2_9_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 128 128 = 40552629123622699850545772 := rfl
private theorem receipt_2_9_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 256 128 = 17945432714983617593760025 := rfl
private theorem receipt_2_9_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 384 56 = 1727382928716149940318590 := rfl
private theorem receipt_2_9_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 0 256 = 107917782908077220622151037 :=
  phaseBlock_append receipt_2_9_2340_0_part0 receipt_2_9_2340_0_part1 rfl rfl rfl
private theorem receipt_2_9_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 256 184 = 19672815643699767534078615 :=
  phaseBlock_append receipt_2_9_2340_0_part2 receipt_2_9_2340_0_part3 rfl rfl rfl
private theorem receipt_2_9_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 0) 0 440 = 127590598551776988156229652 :=
  phaseBlock_append receipt_2_9_2340_0_join0 receipt_2_9_2340_0_join1 rfl rfl rfl

private theorem receipt_2_9_2340_0 : fastPhase (bank 2 9).shape 179827 2340 10 1 0 7 0 = 127590598551776988156229652 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2340_0_join2

private theorem receipt_2_9_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 0 128 = 67140934772947394430312738 := rfl
private theorem receipt_2_9_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 128 128 = 40361893094196107001987514 := rfl
private theorem receipt_2_9_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 256 128 = 17785044241571784431017979 := rfl
private theorem receipt_2_9_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 384 56 = 1665984714378782692011183 := rfl
private theorem receipt_2_9_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 0 256 = 107502827867143501432300252 :=
  phaseBlock_append receipt_2_9_2340_1_part0 receipt_2_9_2340_1_part1 rfl rfl rfl
private theorem receipt_2_9_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 256 184 = 19451028955950567123029162 :=
  phaseBlock_append receipt_2_9_2340_1_part2 receipt_2_9_2340_1_part3 rfl rfl rfl
private theorem receipt_2_9_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 9).shape 179827 2340 10 1 0 7 1) 0 440 = 126953856823094068555329414 :=
  phaseBlock_append receipt_2_9_2340_1_join0 receipt_2_9_2340_1_join1 rfl rfl rfl

private theorem receipt_2_9_2340_1 : fastPhase (bank 2 9).shape 179827 2340 10 1 0 7 1 = 126953856823094068555329414 :=
  phase_of_block (n := 440) (by decide +kernel) receipt_2_9_2340_1_join2

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2100_439)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_9_2339_0 receipt_2_9_2339_1 receipt_2_9_2340_0 receipt_2_9_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_9_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 0 128 = 12566070554930991433843872 := rfl
private theorem receipt_3_9_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 128 128 = 7730793172857724492469408 := rfl
private theorem receipt_3_9_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 256 128 = 3607928681024964610991264 := rfl
private theorem receipt_3_9_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 384 73 = 503312239984791355750506 := rfl
private theorem receipt_3_9_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 0 256 = 20296863727788715926313280 :=
  phaseBlock_append receipt_3_9_2339_0_part0 receipt_3_9_2339_0_part1 rfl rfl rfl
private theorem receipt_3_9_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 256 201 = 4111240921009755966741770 :=
  phaseBlock_append receipt_3_9_2339_0_part2 receipt_3_9_2339_0_part3 rfl rfl rfl
private theorem receipt_3_9_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 0) 0 457 = 24408104648798471893055050 :=
  phaseBlock_append receipt_3_9_2339_0_join0 receipt_3_9_2339_0_join1 rfl rfl rfl

private theorem receipt_3_9_2339_0 : fastPhase (bank 3 9).shape 179827 2339 10 1 1 1 0 = 24408104648798471893055050 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2339_0_join2

private theorem receipt_3_9_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 0 128 = 12526149839182406647728928 := rfl
private theorem receipt_3_9_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 128 128 = 7696035245502209579014944 := rfl
private theorem receipt_3_9_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 256 128 = 3578795210783237501414176 := rfl
private theorem receipt_3_9_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 384 73 = 489388929339240733938954 := rfl
private theorem receipt_3_9_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 0 256 = 20222185084684616226743872 :=
  phaseBlock_append receipt_3_9_2339_1_part0 receipt_3_9_2339_1_part1 rfl rfl rfl
private theorem receipt_3_9_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 256 201 = 4068184140122478235353130 :=
  phaseBlock_append receipt_3_9_2339_1_part2 receipt_3_9_2339_1_part3 rfl rfl rfl
private theorem receipt_3_9_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2339 10 1 1 1 1) 0 457 = 24290369224807094462097002 :=
  phaseBlock_append receipt_3_9_2339_1_join0 receipt_3_9_2339_1_join1 rfl rfl rfl

private theorem receipt_3_9_2339_1 : fastPhase (bank 3 9).shape 179827 2339 10 1 1 1 1 = 24290369224807094462097002 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2339_1_join2

private theorem receipt_3_9_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 0 128 = 12566172710587793669592864 := rfl
private theorem receipt_3_9_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 128 128 = 7730837188891098966943520 := rfl
private theorem receipt_3_9_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 256 128 = 3607941054033575034828576 := rfl
private theorem receipt_3_9_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 384 73 = 503313083877627775155774 := rfl
private theorem receipt_3_9_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 0 256 = 20297009899478892636536384 :=
  phaseBlock_append receipt_3_9_2340_0_part0 receipt_3_9_2340_0_part1 rfl rfl rfl
private theorem receipt_3_9_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 256 201 = 4111254137911202809984350 :=
  phaseBlock_append receipt_3_9_2340_0_part2 receipt_3_9_2340_0_part3 rfl rfl rfl
private theorem receipt_3_9_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 0) 0 457 = 24408264037390095446520734 :=
  phaseBlock_append receipt_3_9_2340_0_join0 receipt_3_9_2340_0_join1 rfl rfl rfl

private theorem receipt_3_9_2340_0 : fastPhase (bank 3 9).shape 179827 2340 10 1 1 1 0 = 24408264037390095446520734 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2340_0_join2

private theorem receipt_3_9_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 0 128 = 12526251624025587123988256 := rfl
private theorem receipt_3_9_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 128 128 = 7696079041583900188694304 := rfl
private theorem receipt_3_9_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 256 128 = 3578807478932245490370336 := rfl
private theorem receipt_3_9_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 384 73 = 489389751518172314620314 := rfl
private theorem receipt_3_9_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 0 256 = 20222330665609487312682560 :=
  phaseBlock_append receipt_3_9_2340_1_part0 receipt_3_9_2340_1_part1 rfl rfl rfl
private theorem receipt_3_9_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 256 201 = 4068197230450417804990650 :=
  phaseBlock_append receipt_3_9_2340_1_part2 receipt_3_9_2340_1_part3 rfl rfl rfl
private theorem receipt_3_9_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 9).shape 179827 2340 10 1 1 1 1) 0 457 = 24290527896059905117673210 :=
  phaseBlock_append receipt_3_9_2340_1_join0 receipt_3_9_2340_1_join1 rfl rfl rfl

private theorem receipt_3_9_2340_1 : fastPhase (bank 3 9).shape 179827 2340 10 1 1 1 1 = 24290527896059905117673210 :=
  phase_of_block (n := 457) (by decide +kernel) receipt_3_9_2340_1_join2

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2091_456)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_9_2339_0 receipt_3_9_2339_1 receipt_3_9_2340_0 receipt_3_9_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_10_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 0 128 = 1514139155147059726157877888 := rfl
private theorem receipt_0_10_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 128 128 = 1174778318896266908915978880 := rfl
private theorem receipt_0_10_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 256 128 = 863111275704256591480722048 := rfl
private theorem receipt_0_10_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 384 128 = 577956255340780815524940618 := rfl
private theorem receipt_0_10_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 512 128 = 318136863366850858200716784 := rfl
private theorem receipt_0_10_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 640 111 = 84260051028415879127841340 := rfl
private theorem receipt_0_10_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 128 256 = 2037889594600523500396700928 :=
  phaseBlock_append receipt_0_10_2339_0_part1 receipt_0_10_2339_0_part2 rfl rfl rfl
private theorem receipt_0_10_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 0 384 = 3552028749747583226554578816 :=
  phaseBlock_append receipt_0_10_2339_0_part0 receipt_0_10_2339_0_join0 rfl rfl rfl
private theorem receipt_0_10_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 512 239 = 402396914395266737328558124 :=
  phaseBlock_append receipt_0_10_2339_0_part4 receipt_0_10_2339_0_part5 rfl rfl rfl
private theorem receipt_0_10_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 384 367 = 980353169736047552853498742 :=
  phaseBlock_append receipt_0_10_2339_0_part3 receipt_0_10_2339_0_join2 rfl rfl rfl
private theorem receipt_0_10_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 0) 0 751 = 4532381919483630779408077558 :=
  phaseBlock_append receipt_0_10_2339_0_join1 receipt_0_10_2339_0_join3 rfl rfl rfl

private theorem receipt_0_10_2339_0 : fastPhase (bank 0 10).shape 179827 2339 20 1 0 1 0 = 4532381919483630779408077558 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2339_0_join4

private theorem receipt_0_10_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 0 128 = 1511413237308784302168661824 := rfl
private theorem receipt_0_10_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 128 128 = 1172266049315163141607358272 := rfl
private theorem receipt_0_10_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 256 128 = 860803699135058350330617664 := rfl
private theorem receipt_0_10_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 384 128 = 575844452902937151059741106 := rfl
private theorem receipt_0_10_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 512 128 = 316211948376651749749206099 := rfl
private theorem receipt_0_10_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 640 111 = 82735239879898062096893085 := rfl
private theorem receipt_0_10_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 128 256 = 2033069748450221491937975936 :=
  phaseBlock_append receipt_0_10_2339_1_part1 receipt_0_10_2339_1_part2 rfl rfl rfl
private theorem receipt_0_10_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 0 384 = 3544482985759005794106637760 :=
  phaseBlock_append receipt_0_10_2339_1_part0 receipt_0_10_2339_1_join0 rfl rfl rfl
private theorem receipt_0_10_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 512 239 = 398947188256549811846099184 :=
  phaseBlock_append receipt_0_10_2339_1_part4 receipt_0_10_2339_1_part5 rfl rfl rfl
private theorem receipt_0_10_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 384 367 = 974791641159486962905840290 :=
  phaseBlock_append receipt_0_10_2339_1_part3 receipt_0_10_2339_1_join2 rfl rfl rfl
private theorem receipt_0_10_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2339 20 1 0 1 1) 0 751 = 4519274626918492757012478050 :=
  phaseBlock_append receipt_0_10_2339_1_join1 receipt_0_10_2339_1_join3 rfl rfl rfl

private theorem receipt_0_10_2339_1 : fastPhase (bank 0 10).shape 179827 2339 20 1 0 1 1 = 4519274626918492757012478050 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2339_1_join4

private theorem receipt_0_10_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 0 128 = 1514152561449221797567840480 := rfl
private theorem receipt_0_10_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 128 128 = 1174787642505915418034245856 := rfl
private theorem receipt_0_10_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 256 128 = 863117290464366387485040864 := rfl
private theorem receipt_0_10_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 384 128 = 577959693478562584697414178 := rfl
private theorem receipt_0_10_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 512 128 = 318138413376831398404459916 := rfl
private theorem receipt_0_10_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 640 111 = 84260377824118666759031442 := rfl
private theorem receipt_0_10_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 128 256 = 2037904932970281805519286720 :=
  phaseBlock_append receipt_0_10_2340_0_part1 receipt_0_10_2340_0_part2 rfl rfl rfl
private theorem receipt_0_10_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 0 384 = 3552057494419503603087127200 :=
  phaseBlock_append receipt_0_10_2340_0_part0 receipt_0_10_2340_0_join0 rfl rfl rfl
private theorem receipt_0_10_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 512 239 = 402398791200950065163491358 :=
  phaseBlock_append receipt_0_10_2340_0_part4 receipt_0_10_2340_0_part5 rfl rfl rfl
private theorem receipt_0_10_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 384 367 = 980358484679512649860905536 :=
  phaseBlock_append receipt_0_10_2340_0_part3 receipt_0_10_2340_0_join2 rfl rfl rfl
private theorem receipt_0_10_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 0) 0 751 = 4532415979099016252948032736 :=
  phaseBlock_append receipt_0_10_2340_0_join1 receipt_0_10_2340_0_join3 rfl rfl rfl

private theorem receipt_0_10_2340_0 : fastPhase (bank 0 10).shape 179827 2340 20 1 0 1 0 = 4532415979099016252948032736 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2340_0_join4

private theorem receipt_0_10_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 0 128 = 1511426623883250065671498464 := rfl
private theorem receipt_0_10_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 128 128 = 1172275356279417642587699936 := rfl
private theorem receipt_0_10_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 256 128 = 860809700139258883728263904 := rfl
private theorem receipt_0_10_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 384 128 = 575847879985595021361768285 := rfl
private theorem receipt_0_10_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 512 128 = 316213489868587806850502596 := rfl
private theorem receipt_0_10_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 640 111 = 82735561195689852677419640 := rfl
private theorem receipt_0_10_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 128 256 = 2033085056418676526315963840 :=
  phaseBlock_append receipt_0_10_2340_1_part1 receipt_0_10_2340_1_part2 rfl rfl rfl
private theorem receipt_0_10_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 0 384 = 3544511680301926591987462304 :=
  phaseBlock_append receipt_0_10_2340_1_part0 receipt_0_10_2340_1_join0 rfl rfl rfl
private theorem receipt_0_10_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 512 239 = 398949051064277659527922236 :=
  phaseBlock_append receipt_0_10_2340_1_part4 receipt_0_10_2340_1_part5 rfl rfl rfl
private theorem receipt_0_10_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 384 367 = 974796931049872680889690521 :=
  phaseBlock_append receipt_0_10_2340_1_part3 receipt_0_10_2340_1_join2 rfl rfl rfl
private theorem receipt_0_10_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 10).shape 179827 2340 20 1 0 1 1) 0 751 = 4519308611351799272877152825 :=
  phaseBlock_append receipt_0_10_2340_1_join1 receipt_0_10_2340_1_join3 rfl rfl rfl

private theorem receipt_0_10_2340_1 : fastPhase (bank 0 10).shape 179827 2340 20 1 0 1 1 = 4519308611351799272877152825 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_0_10_2340_1_join4

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_10_2339_0 receipt_0_10_2339_1 receipt_0_10_2340_0 receipt_0_10_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_10_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 0 128 = 1350369844241310431351002368 := rfl
private theorem receipt_1_10_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 128 128 = 1046466151041317733905552640 := rfl
private theorem receipt_1_10_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 256 128 = 767924647752852864419812608 := rfl
private theorem receipt_1_10_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 384 128 = 513607029175641999276976959 := rfl
private theorem receipt_1_10_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 512 128 = 282384725240558484070978391 := rfl
private theorem receipt_1_10_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 640 111 = 74714148794148766878986768 := rfl
private theorem receipt_1_10_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 128 256 = 1814390798794170598325365248 :=
  phaseBlock_append receipt_1_10_2339_0_part1 receipt_1_10_2339_0_part2 rfl rfl rfl
private theorem receipt_1_10_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 0 384 = 3164760643035481029676367616 :=
  phaseBlock_append receipt_1_10_2339_0_part0 receipt_1_10_2339_0_join0 rfl rfl rfl
private theorem receipt_1_10_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 512 239 = 357098874034707250949965159 :=
  phaseBlock_append receipt_1_10_2339_0_part4 receipt_1_10_2339_0_part5 rfl rfl rfl
private theorem receipt_1_10_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 384 367 = 870705903210349250226942118 :=
  phaseBlock_append receipt_1_10_2339_0_part3 receipt_1_10_2339_0_join2 rfl rfl rfl
private theorem receipt_1_10_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 0) 0 751 = 4035466546245830279903309734 :=
  phaseBlock_append receipt_1_10_2339_0_join1 receipt_1_10_2339_0_join3 rfl rfl rfl

private theorem receipt_1_10_2339_0 : fastPhase (bank 1 10).shape 179827 2339 20 1 0 2 0 = 4035466546245830279903309734 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2339_0_join4

private theorem receipt_1_10_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 0 128 = 1347926211121381244992348224 := rfl
private theorem receipt_1_10_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 128 128 = 1044218553168052375109107776 := rfl
private theorem receipt_1_10_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 256 128 = 765864435167784603098685504 := rfl
private theorem receipt_1_10_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 384 128 = 511725622114539026418232325 := rfl
private theorem receipt_1_10_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 512 128 = 280673610280686005759459418 := rfl
private theorem receipt_1_10_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 640 111 = 73361621148886622666768003 := rfl
private theorem receipt_1_10_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 128 256 = 1810082988335836978207793280 :=
  phaseBlock_append receipt_1_10_2339_1_part1 receipt_1_10_2339_1_part2 rfl rfl rfl
private theorem receipt_1_10_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 0 384 = 3158009199457218223200141504 :=
  phaseBlock_append receipt_1_10_2339_1_part0 receipt_1_10_2339_1_join0 rfl rfl rfl
private theorem receipt_1_10_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 512 239 = 354035231429572628426227421 :=
  phaseBlock_append receipt_1_10_2339_1_part4 receipt_1_10_2339_1_part5 rfl rfl rfl
private theorem receipt_1_10_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 384 367 = 865760853544111654844459746 :=
  phaseBlock_append receipt_1_10_2339_1_part3 receipt_1_10_2339_1_join2 rfl rfl rfl
private theorem receipt_1_10_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2339 20 1 0 2 1) 0 751 = 4023770053001329878044601250 :=
  phaseBlock_append receipt_1_10_2339_1_join1 receipt_1_10_2339_1_join3 rfl rfl rfl

private theorem receipt_1_10_2339_1 : fastPhase (bank 1 10).shape 179827 2339 20 1 0 2 1 = 4023770053001329878044601250 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2339_1_join4

private theorem receipt_1_10_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 0 128 = 1350381800637748354693747392 := rfl
private theorem receipt_1_10_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 128 128 = 1046474456401808819456668352 := rfl
private theorem receipt_1_10_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 256 128 = 767929999262473432719069888 := rfl
private theorem receipt_1_10_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 384 128 = 513610084567600778460981507 := rfl
private theorem receipt_1_10_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 512 128 = 282386101091589680324516152 := rfl
private theorem receipt_1_10_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 640 111 = 74714438571361877777169902 := rfl
private theorem receipt_1_10_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 128 256 = 1814404455664282252175738240 :=
  phaseBlock_append receipt_1_10_2340_0_part1 receipt_1_10_2340_0_part2 rfl rfl rfl
private theorem receipt_1_10_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 0 384 = 3164786256302030606869485632 :=
  phaseBlock_append receipt_1_10_2340_0_part0 receipt_1_10_2340_0_join0 rfl rfl rfl
private theorem receipt_1_10_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 512 239 = 357100539662951558101686054 :=
  phaseBlock_append receipt_1_10_2340_0_part4 receipt_1_10_2340_0_part5 rfl rfl rfl
private theorem receipt_1_10_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 384 367 = 870710624230552336562667561 :=
  phaseBlock_append receipt_1_10_2340_0_part3 receipt_1_10_2340_0_join2 rfl rfl rfl
private theorem receipt_1_10_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 0) 0 751 = 4035496880532582943432153193 :=
  phaseBlock_append receipt_1_10_2340_0_join1 receipt_1_10_2340_0_join3 rfl rfl rfl

private theorem receipt_1_10_2340_0 : fastPhase (bank 1 10).shape 179827 2340 20 1 0 2 0 = 4035496880532582943432153193 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2340_0_join4

private theorem receipt_1_10_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 0 128 = 1347938149812508344468440768 := rfl
private theorem receipt_1_10_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 128 128 = 1044226843623795634089125568 := rfl
private theorem receipt_1_10_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 256 128 = 765869774388689261879871168 := rfl
private theorem receipt_1_10_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 384 128 = 511728667653891594744098014 := rfl
private theorem receipt_1_10_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 512 128 = 280674978558438490295919819 := rfl
private theorem receipt_1_10_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 640 111 = 73361906065051314710998388 := rfl
private theorem receipt_1_10_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 128 256 = 1810096618012484895968996736 :=
  phaseBlock_append receipt_1_10_2340_1_part1 receipt_1_10_2340_1_part2 rfl rfl rfl
private theorem receipt_1_10_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 0 384 = 3158034767824993240437437504 :=
  phaseBlock_append receipt_1_10_2340_1_part0 receipt_1_10_2340_1_join0 rfl rfl rfl
private theorem receipt_1_10_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 512 239 = 354036884623489805006918207 :=
  phaseBlock_append receipt_1_10_2340_1_part4 receipt_1_10_2340_1_part5 rfl rfl rfl
private theorem receipt_1_10_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 384 367 = 865765552277381399751016221 :=
  phaseBlock_append receipt_1_10_2340_1_part3 receipt_1_10_2340_1_join2 rfl rfl rfl
private theorem receipt_1_10_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 10).shape 179827 2340 20 1 0 2 1) 0 751 = 4023800320102374640188453725 :=
  phaseBlock_append receipt_1_10_2340_1_join1 receipt_1_10_2340_1_join3 rfl rfl rfl

private theorem receipt_1_10_2340_1 : fastPhase (bank 1 10).shape 179827 2340 20 1 0 2 1 = 4023800320102374640188453725 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_1_10_2340_1_join4

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_10_2339_0 receipt_1_10_2339_1 receipt_1_10_2340_0 receipt_1_10_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_10_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 0 128 = 676626163250732509361221248 := rfl
private theorem receipt_2_10_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 128 128 = 519688033656580400195235456 := rfl
private theorem receipt_2_10_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 256 128 = 377954608956076738001743488 := rfl
private theorem receipt_2_10_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 384 128 = 250523164006888385026872591 := rfl
private theorem receipt_2_10_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 512 128 = 136517318800717369671027249 := rfl
private theorem receipt_2_10_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 640 111 = 35837655788005876663724208 := rfl
private theorem receipt_2_10_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 128 256 = 897642642612657138196978944 :=
  phaseBlock_append receipt_2_10_2339_0_part1 receipt_2_10_2339_0_part2 rfl rfl rfl
private theorem receipt_2_10_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 0 384 = 1574268805863389647558200192 :=
  phaseBlock_append receipt_2_10_2339_0_part0 receipt_2_10_2339_0_join0 rfl rfl rfl
private theorem receipt_2_10_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 512 239 = 172354974588723246334751457 :=
  phaseBlock_append receipt_2_10_2339_0_part4 receipt_2_10_2339_0_part5 rfl rfl rfl
private theorem receipt_2_10_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 384 367 = 422878138595611631361624048 :=
  phaseBlock_append receipt_2_10_2339_0_part3 receipt_2_10_2339_0_join2 rfl rfl rfl
private theorem receipt_2_10_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 0) 0 751 = 1997146944459001278919824240 :=
  phaseBlock_append receipt_2_10_2339_0_join1 receipt_2_10_2339_0_join3 rfl rfl rfl

private theorem receipt_2_10_2339_0 : fastPhase (bank 2 10).shape 179827 2339 20 1 0 7 0 = 1997146944459001278919824240 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2339_0_join4

private theorem receipt_2_10_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 0 128 = 675354742764052422302724864 := rfl
private theorem receipt_2_10_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 128 128 = 518535575726195548609573632 := rfl
private theorem receipt_2_10_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 256 128 = 376914154992252140297024256 := rfl
private theorem receipt_2_10_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 384 128 = 249587955631074537500397969 := rfl
private theorem receipt_2_10_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 512 128 = 135680793706440463093877019 := rfl
private theorem receipt_2_10_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 640 111 = 35187192712701652781500860 := rfl
private theorem receipt_2_10_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 128 256 = 895449730718447688906597888 :=
  phaseBlock_append receipt_2_10_2339_1_part1 receipt_2_10_2339_1_part2 rfl rfl rfl
private theorem receipt_2_10_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 0 384 = 1570804473482500111209322752 :=
  phaseBlock_append receipt_2_10_2339_1_part0 receipt_2_10_2339_1_join0 rfl rfl rfl
private theorem receipt_2_10_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 512 239 = 170867986419142115875377879 :=
  phaseBlock_append receipt_2_10_2339_1_part4 receipt_2_10_2339_1_part5 rfl rfl rfl
private theorem receipt_2_10_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 384 367 = 420455942050216653375775848 :=
  phaseBlock_append receipt_2_10_2339_1_part3 receipt_2_10_2339_1_join2 rfl rfl rfl
private theorem receipt_2_10_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2339 20 1 0 7 1) 0 751 = 1991260415532716764585098600 :=
  phaseBlock_append receipt_2_10_2339_1_join1 receipt_2_10_2339_1_join3 rfl rfl rfl

private theorem receipt_2_10_2339_1 : fastPhase (bank 2 10).shape 179827 2339 20 1 0 7 1 = 1991260415532716764585098600 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2339_1_join4

private theorem receipt_2_10_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 0 128 = 676632154659610135886538464 := rfl
private theorem receipt_2_10_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 128 128 = 519692158568133230320367328 := rfl
private theorem receipt_2_10_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 256 128 = 377957243127405290809116384 := rfl
private theorem receipt_2_10_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 384 128 = 250524654541290019917298867 := rfl
private theorem receipt_2_10_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 512 128 = 136517984061639097707979644 := rfl
private theorem receipt_2_10_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 640 111 = 35837794800145639363702808 := rfl
private theorem receipt_2_10_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 128 256 = 897649401695538521129483712 :=
  phaseBlock_append receipt_2_10_2340_0_part1 receipt_2_10_2340_0_part2 rfl rfl rfl
private theorem receipt_2_10_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 0 384 = 1574281556355148657016022176 :=
  phaseBlock_append receipt_2_10_2340_0_part0 receipt_2_10_2340_0_join0 rfl rfl rfl
private theorem receipt_2_10_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 512 239 = 172355778861784737071682452 :=
  phaseBlock_append receipt_2_10_2340_0_part4 receipt_2_10_2340_0_part5 rfl rfl rfl
private theorem receipt_2_10_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 384 367 = 422880433403074756988981319 :=
  phaseBlock_append receipt_2_10_2340_0_part3 receipt_2_10_2340_0_join2 rfl rfl rfl
private theorem receipt_2_10_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 0) 0 751 = 1997161989758223414005003495 :=
  phaseBlock_append receipt_2_10_2340_0_join1 receipt_2_10_2340_0_join3 rfl rfl rfl

private theorem receipt_2_10_2340_0 : fastPhase (bank 2 10).shape 179827 2340 20 1 0 7 0 = 1997161989758223414005003495 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2340_0_join4

private theorem receipt_2_10_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 0 128 = 675360724884362160976228064 := rfl
private theorem receipt_2_10_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 128 128 = 518539692947128665754730208 := rfl
private theorem receipt_2_10_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 256 128 = 376916782930122730984181472 := rfl
private theorem receipt_2_10_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 384 128 = 249589441254709271918763841 := rfl
private theorem receipt_2_10_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 512 128 = 135681455260050142945976327 := rfl
private theorem receipt_2_10_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 640 111 = 35187329385962650092641928 := rfl
private theorem receipt_2_10_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 128 256 = 895456475877251396738911680 :=
  phaseBlock_append receipt_2_10_2340_1_part1 receipt_2_10_2340_1_part2 rfl rfl rfl
private theorem receipt_2_10_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 0 384 = 1570817200761613557715139744 :=
  phaseBlock_append receipt_2_10_2340_1_part0 receipt_2_10_2340_1_join0 rfl rfl rfl
private theorem receipt_2_10_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 512 239 = 170868784646012793038618255 :=
  phaseBlock_append receipt_2_10_2340_1_part4 receipt_2_10_2340_1_part5 rfl rfl rfl
private theorem receipt_2_10_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 384 367 = 420458225900722064957382096 :=
  phaseBlock_append receipt_2_10_2340_1_part3 receipt_2_10_2340_1_join2 rfl rfl rfl
private theorem receipt_2_10_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 10).shape 179827 2340 20 1 0 7 1) 0 751 = 1991275426662335622672521840 :=
  phaseBlock_append receipt_2_10_2340_1_join1 receipt_2_10_2340_1_join3 rfl rfl rfl

private theorem receipt_2_10_2340_1 : fastPhase (bank 2 10).shape 179827 2340 20 1 0 7 1 = 1991275426662335622672521840 :=
  phase_of_block (n := 751) (by decide +kernel) receipt_2_10_2340_1_join4

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3438_750)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_10_2339_0 receipt_2_10_2339_1 receipt_2_10_2340_0 receipt_2_10_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_10_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 0 128 = 67356802302272911495074816 := rfl
private theorem receipt_3_10_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 128 128 = 47069418994817819714319360 := rfl
private theorem receipt_3_10_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 256 128 = 28936113709797151162684416 := rfl
private theorem receipt_3_10_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 384 128 = 13093822798733336421381120 := rfl
private theorem receipt_3_10_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 512 59 = 1366378305062913135294372 := rfl
private theorem receipt_3_10_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 0 256 = 114426221297090731209394176 :=
  phaseBlock_append receipt_3_10_2339_0_part0 receipt_3_10_2339_0_part1 rfl rfl rfl
private theorem receipt_3_10_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 384 187 = 14460201103796249556675492 :=
  phaseBlock_append receipt_3_10_2339_0_part3 receipt_3_10_2339_0_part4 rfl rfl rfl
private theorem receipt_3_10_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 256 315 = 43396314813593400719359908 :=
  phaseBlock_append receipt_3_10_2339_0_part2 receipt_3_10_2339_0_join1 rfl rfl rfl
private theorem receipt_3_10_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 0) 0 571 = 157822536110684131928754084 :=
  phaseBlock_append receipt_3_10_2339_0_join0 receipt_3_10_2339_0_join2 rfl rfl rfl

private theorem receipt_3_10_2339_0 : fastPhase (bank 3 10).shape 179827 2339 20 1 1 1 0 = 157822536110684131928754084 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2339_0_join3

private theorem receipt_3_10_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 0 128 = 67192284747076406714423424 := rfl
private theorem receipt_3_10_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 128 128 = 46920572144445552898029696 := rfl
private theorem receipt_3_10_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 256 128 = 28804100650243774488549504 := rfl
private theorem receipt_3_10_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 384 128 = 12979789204547234166864000 := rfl
private theorem receipt_3_10_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 512 59 = 1320181929414124187183616 := rfl
private theorem receipt_3_10_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 0 256 = 114112856891521959612453120 :=
  phaseBlock_append receipt_3_10_2339_1_part0 receipt_3_10_2339_1_part1 rfl rfl rfl
private theorem receipt_3_10_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 384 187 = 14299971133961358354047616 :=
  phaseBlock_append receipt_3_10_2339_1_part3 receipt_3_10_2339_1_part4 rfl rfl rfl
private theorem receipt_3_10_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 256 315 = 43104071784205132842597120 :=
  phaseBlock_append receipt_3_10_2339_1_part2 receipt_3_10_2339_1_join1 rfl rfl rfl
private theorem receipt_3_10_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2339 20 1 1 1 1) 0 571 = 157216928675727092455050240 :=
  phaseBlock_append receipt_3_10_2339_1_join0 receipt_3_10_2339_1_join2 rfl rfl rfl

private theorem receipt_3_10_2339_1 : fastPhase (bank 3 10).shape 179827 2339 20 1 1 1 1 = 157216928675727092455050240 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2339_1_join3

private theorem receipt_3_10_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 0 128 = 67357362134443976808730848 := rfl
private theorem receipt_3_10_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 128 128 = 47069720255991987063447776 := rfl
private theorem receipt_3_10_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 256 128 = 28936246074075655078064352 := rfl
private theorem receipt_3_10_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 384 128 = 13093860337374941680894176 := rfl
private theorem receipt_3_10_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 512 59 = 1366380453924074209415451 := rfl
private theorem receipt_3_10_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 0 256 = 114427082390435963872178624 :=
  phaseBlock_append receipt_3_10_2340_0_part0 receipt_3_10_2340_0_part1 rfl rfl rfl
private theorem receipt_3_10_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 384 187 = 14460240791299015890309627 :=
  phaseBlock_append receipt_3_10_2340_0_part3 receipt_3_10_2340_0_part4 rfl rfl rfl
private theorem receipt_3_10_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 256 315 = 43396486865374670968373979 :=
  phaseBlock_append receipt_3_10_2340_0_part2 receipt_3_10_2340_0_join1 rfl rfl rfl
private theorem receipt_3_10_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 0) 0 571 = 157823569255810634840552603 :=
  phaseBlock_append receipt_3_10_2340_0_join0 receipt_3_10_2340_0_join2 rfl rfl rfl

private theorem receipt_3_10_2340_0 : fastPhase (bank 3 10).shape 179827 2340 20 1 1 1 0 = 157823569255810634840552603 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2340_0_join3

private theorem receipt_3_10_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 0 128 = 67192843013178638368599392 := rfl
private theorem receipt_3_10_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 128 128 = 46920872335278465615248736 := rfl
private theorem receipt_3_10_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 256 128 = 28804232353570145295273312 := rfl
private theorem receipt_3_10_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 384 128 = 12979826406540097406524768 := rfl
private theorem receipt_3_10_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 512 59 = 1320184009091879055414239 := rfl
private theorem receipt_3_10_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 0 256 = 114113715348457103983848128 :=
  phaseBlock_append receipt_3_10_2340_1_part0 receipt_3_10_2340_1_part1 rfl rfl rfl
private theorem receipt_3_10_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 384 187 = 14300010415631976461939007 :=
  phaseBlock_append receipt_3_10_2340_1_part3 receipt_3_10_2340_1_part4 rfl rfl rfl
private theorem receipt_3_10_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 256 315 = 43104242769202121757212319 :=
  phaseBlock_append receipt_3_10_2340_1_part2 receipt_3_10_2340_1_join1 rfl rfl rfl
private theorem receipt_3_10_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 10).shape 179827 2340 20 1 1 1 1) 0 571 = 157217958117659225741060447 :=
  phaseBlock_append receipt_3_10_2340_1_join0 receipt_3_10_2340_1_join2 rfl rfl rfl

private theorem receipt_3_10_2340_1 : fastPhase (bank 3 10).shape 179827 2340 20 1 1 1 1 = 157217958117659225741060447 :=
  phase_of_block (n := 571) (by decide +kernel) receipt_3_10_2340_1_join3

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2726_570)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_10_2339_0 receipt_3_10_2339_1 receipt_3_10_2340_0 receipt_3_10_2340_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 3) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group3_stage i)).shape
      (cutoff h rect (group3_stage i)), ¬ G∣Q :=
  (group3_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group3_avoids

end Lower6960.RescueSource
