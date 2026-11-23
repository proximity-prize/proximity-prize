import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_5949_1250_part0 :
    blockEstimate 5949 1250 1250 128 = 2094237600 := by decide +kernel
private theorem moment_5949_1250_part1 :
    blockEstimate 5949 1250 1378 128 = 14194759584 := by decide +kernel
private theorem moment_5949_1250_part2 :
    blockEstimate 5949 1250 1506 128 = 37560133536 := by decide +kernel
private theorem moment_5949_1250_part3 :
    blockEstimate 5949 1250 1634 128 = 71385053088 := by decide +kernel
private theorem moment_5949_1250_part4 :
    blockEstimate 5949 1250 1762 128 = 114864211872 := by decide +kernel
private theorem moment_5949_1250_part5 :
    blockEstimate 5949 1250 1890 128 = 167192303520 := by decide +kernel
private theorem moment_5949_1250_part6 :
    blockEstimate 5949 1250 2018 128 = 227564021664 := by decide +kernel
private theorem moment_5949_1250_part7 :
    blockEstimate 5949 1250 2146 128 = 295174059936 := by decide +kernel
private theorem moment_5949_1250_part8 :
    blockEstimate 5949 1250 2274 128 = 369217111968 := by decide +kernel
private theorem moment_5949_1250_part9 :
    blockEstimate 5949 1250 2402 128 = 448866848277 := by decide +kernel
private theorem moment_5949_1250_part10 :
    blockEstimate 5949 1250 2530 128 = 530390693376 := by decide +kernel
private theorem moment_5949_1250_part11 :
    blockEstimate 5949 1250 2658 128 = 607416104448 := by decide +kernel
private theorem moment_5949_1250_part12 :
    blockEstimate 5949 1250 2786 128 = 679194441216 := by decide +kernel
private theorem moment_5949_1250_part13 :
    blockEstimate 5949 1250 2914 128 = 745725703680 := by decide +kernel
private theorem moment_5949_1250_part14 :
    blockEstimate 5949 1250 3042 128 = 807009891840 := by decide +kernel
private theorem moment_5949_1250_part15 :
    blockEstimate 5949 1250 3170 128 = 863047005696 := by decide +kernel
private theorem moment_5949_1250_part16 :
    blockEstimate 5949 1250 3298 128 = 913837045248 := by decide +kernel
private theorem moment_5949_1250_part17 :
    blockEstimate 5949 1250 3426 128 = 959380010496 := by decide +kernel
private theorem moment_5949_1250_part18 :
    blockEstimate 5949 1250 3554 128 = 999675901440 := by decide +kernel
private theorem moment_5949_1250_part19 :
    blockEstimate 5949 1250 3682 128 = 1034724718080 := by decide +kernel
private theorem moment_5949_1250_part20 :
    blockEstimate 5949 1250 3810 128 = 1064526460416 := by decide +kernel
private theorem moment_5949_1250_part21 :
    blockEstimate 5949 1250 3938 128 = 1089081128448 := by decide +kernel
private theorem moment_5949_1250_part22 :
    blockEstimate 5949 1250 4066 128 = 1108388722176 := by decide +kernel
private theorem moment_5949_1250_part23 :
    blockEstimate 5949 1250 4194 128 = 1122449241600 := by decide +kernel
private theorem moment_5949_1250_part24 :
    blockEstimate 5949 1250 4322 128 = 1131262686720 := by decide +kernel
private theorem moment_5949_1250_part25 :
    blockEstimate 5949 1250 4450 128 = 1134829057536 := by decide +kernel
private theorem moment_5949_1250_part26 :
    blockEstimate 5949 1250 4578 128 = 1133148354048 := by decide +kernel
private theorem moment_5949_1250_part27 :
    blockEstimate 5949 1250 4706 128 = 1126220576256 := by decide +kernel
private theorem moment_5949_1250_part28 :
    blockEstimate 5949 1250 4834 128 = 1114045724160 := by decide +kernel
private theorem moment_5949_1250_part29 :
    blockEstimate 5949 1250 4962 128 = 1096623797760 := by decide +kernel
private theorem moment_5949_1250_part30 :
    blockEstimate 5949 1250 5090 128 = 1073954797056 := by decide +kernel
private theorem moment_5949_1250_part31 :
    blockEstimate 5949 1250 5218 128 = 1046038722048 := by decide +kernel
private theorem moment_5949_1250_part32 :
    blockEstimate 5949 1250 5346 128 = 1012875572736 := by decide +kernel
private theorem moment_5949_1250_part33 :
    blockEstimate 5949 1250 5474 128 = 974465349120 := by decide +kernel
private theorem moment_5949_1250_part34 :
    blockEstimate 5949 1250 5602 128 = 930808051200 := by decide +kernel
private theorem moment_5949_1250_part35 :
    blockEstimate 5949 1250 5730 128 = 881903678976 := by decide +kernel
private theorem moment_5949_1250_part36 :
    blockEstimate 5949 1250 5858 128 = 827767550913 := by decide +kernel
private theorem moment_5949_1250_part37 :
    blockEstimate 5949 1250 5986 128 = 769710699217 := by decide +kernel
private theorem moment_5949_1250_part38 :
    blockEstimate 5949 1250 6114 128 = 710286041995 := by decide +kernel
private theorem moment_5949_1250_part39 :
    blockEstimate 5949 1250 6242 128 = 650277555272 := by decide +kernel
private theorem moment_5949_1250_part40 :
    blockEstimate 5949 1250 6370 128 = 590241986434 := by decide +kernel
private theorem moment_5949_1250_part41 :
    blockEstimate 5949 1250 6498 128 = 530715481316 := by decide +kernel
private theorem moment_5949_1250_part42 :
    blockEstimate 5949 1250 6626 128 = 472213588042 := by decide +kernel
private theorem moment_5949_1250_part43 :
    blockEstimate 5949 1250 6754 128 = 415231254438 := by decide +kernel
private theorem moment_5949_1250_part44 :
    blockEstimate 5949 1250 6882 128 = 360242828388 := by decide +kernel
private theorem moment_5949_1250_part45 :
    blockEstimate 5949 1250 7010 128 = 307702059966 := by decide +kernel
private theorem moment_5949_1250_part46 :
    blockEstimate 5949 1250 7138 128 = 257941902511 := by decide +kernel
private theorem moment_5949_1250_part47 :
    blockEstimate 5949 1250 7266 128 = 211097989824 := by decide +kernel
private theorem moment_5949_1250_part48 :
    blockEstimate 5949 1250 7394 128 = 168191726272 := by decide +kernel
private theorem moment_5949_1250_part49 :
    blockEstimate 5949 1250 7522 128 = 129573548736 := by decide +kernel
private theorem moment_5949_1250_part50 :
    blockEstimate 5949 1250 7650 128 = 95495115456 := by decide +kernel
private theorem moment_5949_1250_part51 :
    blockEstimate 5949 1250 7778 128 = 66208084672 := by decide +kernel
private theorem moment_5949_1250_part52 :
    blockEstimate 5949 1250 7906 128 = 41964114624 := by decide +kernel
private theorem moment_5949_1250_part53 :
    blockEstimate 5949 1250 8034 128 = 23014863552 := by decide +kernel
private theorem moment_5949_1250_part54 :
    blockEstimate 5949 1250 8162 128 = 9611989696 := by decide +kernel
private theorem moment_5949_1250_part55 :
    blockEstimate 5949 1250 8290 128 = 2007151296 := by decide +kernel
private theorem moment_5949_1250_part56 :
    blockEstimate 5949 1250 8418 31 = 16950704 := by decide +kernel
private theorem moment_5949_1250_join0 :
    blockEstimate 5949 1250 1378 256 = 51754893120 :=
  block_append moment_5949_1250_part1 moment_5949_1250_part2 rfl rfl rfl
private theorem moment_5949_1250_join1 :
    blockEstimate 5949 1250 1250 384 = 53849130720 :=
  block_append moment_5949_1250_part0 moment_5949_1250_join0 rfl rfl rfl
private theorem moment_5949_1250_join2 :
    blockEstimate 5949 1250 1634 256 = 186249264960 :=
  block_append moment_5949_1250_part3 moment_5949_1250_part4 rfl rfl rfl
private theorem moment_5949_1250_join3 :
    blockEstimate 5949 1250 1890 256 = 394756325184 :=
  block_append moment_5949_1250_part5 moment_5949_1250_part6 rfl rfl rfl
private theorem moment_5949_1250_join4 :
    blockEstimate 5949 1250 1634 512 = 581005590144 :=
  block_append moment_5949_1250_join2 moment_5949_1250_join3 rfl rfl rfl
private theorem moment_5949_1250_join5 :
    blockEstimate 5949 1250 1250 896 = 634854720864 :=
  block_append moment_5949_1250_join1 moment_5949_1250_join4 rfl rfl rfl
private theorem moment_5949_1250_join6 :
    blockEstimate 5949 1250 2274 256 = 818083960245 :=
  block_append moment_5949_1250_part8 moment_5949_1250_part9 rfl rfl rfl
private theorem moment_5949_1250_join7 :
    blockEstimate 5949 1250 2146 384 = 1113258020181 :=
  block_append moment_5949_1250_part7 moment_5949_1250_join6 rfl rfl rfl
private theorem moment_5949_1250_join8 :
    blockEstimate 5949 1250 2530 256 = 1137806797824 :=
  block_append moment_5949_1250_part10 moment_5949_1250_part11 rfl rfl rfl
private theorem moment_5949_1250_join9 :
    blockEstimate 5949 1250 2786 256 = 1424920144896 :=
  block_append moment_5949_1250_part12 moment_5949_1250_part13 rfl rfl rfl
private theorem moment_5949_1250_join10 :
    blockEstimate 5949 1250 2530 512 = 2562726942720 :=
  block_append moment_5949_1250_join8 moment_5949_1250_join9 rfl rfl rfl
private theorem moment_5949_1250_join11 :
    blockEstimate 5949 1250 2146 896 = 3675984962901 :=
  block_append moment_5949_1250_join7 moment_5949_1250_join10 rfl rfl rfl
private theorem moment_5949_1250_join12 :
    blockEstimate 5949 1250 1250 1792 = 4310839683765 :=
  block_append moment_5949_1250_join5 moment_5949_1250_join11 rfl rfl rfl
private theorem moment_5949_1250_join13 :
    blockEstimate 5949 1250 3170 256 = 1776884050944 :=
  block_append moment_5949_1250_part15 moment_5949_1250_part16 rfl rfl rfl
private theorem moment_5949_1250_join14 :
    blockEstimate 5949 1250 3042 384 = 2583893942784 :=
  block_append moment_5949_1250_part14 moment_5949_1250_join13 rfl rfl rfl
private theorem moment_5949_1250_join15 :
    blockEstimate 5949 1250 3426 256 = 1959055911936 :=
  block_append moment_5949_1250_part17 moment_5949_1250_part18 rfl rfl rfl
private theorem moment_5949_1250_join16 :
    blockEstimate 5949 1250 3682 256 = 2099251178496 :=
  block_append moment_5949_1250_part19 moment_5949_1250_part20 rfl rfl rfl
private theorem moment_5949_1250_join17 :
    blockEstimate 5949 1250 3426 512 = 4058307090432 :=
  block_append moment_5949_1250_join15 moment_5949_1250_join16 rfl rfl rfl
private theorem moment_5949_1250_join18 :
    blockEstimate 5949 1250 3042 896 = 6642201033216 :=
  block_append moment_5949_1250_join14 moment_5949_1250_join17 rfl rfl rfl
private theorem moment_5949_1250_join19 :
    blockEstimate 5949 1250 4066 256 = 2230837963776 :=
  block_append moment_5949_1250_part22 moment_5949_1250_part23 rfl rfl rfl
private theorem moment_5949_1250_join20 :
    blockEstimate 5949 1250 3938 384 = 3319919092224 :=
  block_append moment_5949_1250_part21 moment_5949_1250_join19 rfl rfl rfl
private theorem moment_5949_1250_join21 :
    blockEstimate 5949 1250 4322 256 = 2266091744256 :=
  block_append moment_5949_1250_part24 moment_5949_1250_part25 rfl rfl rfl
private theorem moment_5949_1250_join22 :
    blockEstimate 5949 1250 4578 256 = 2259368930304 :=
  block_append moment_5949_1250_part26 moment_5949_1250_part27 rfl rfl rfl
private theorem moment_5949_1250_join23 :
    blockEstimate 5949 1250 4322 512 = 4525460674560 :=
  block_append moment_5949_1250_join21 moment_5949_1250_join22 rfl rfl rfl
private theorem moment_5949_1250_join24 :
    blockEstimate 5949 1250 3938 896 = 7845379766784 :=
  block_append moment_5949_1250_join20 moment_5949_1250_join23 rfl rfl rfl
private theorem moment_5949_1250_join25 :
    blockEstimate 5949 1250 3042 1792 = 14487580800000 :=
  block_append moment_5949_1250_join18 moment_5949_1250_join24 rfl rfl rfl
private theorem moment_5949_1250_join26 :
    blockEstimate 5949 1250 1250 3584 = 18798420483765 :=
  block_append moment_5949_1250_join12 moment_5949_1250_join25 rfl rfl rfl
private theorem moment_5949_1250_join27 :
    blockEstimate 5949 1250 4962 256 = 2170578594816 :=
  block_append moment_5949_1250_part29 moment_5949_1250_part30 rfl rfl rfl
private theorem moment_5949_1250_join28 :
    blockEstimate 5949 1250 4834 384 = 3284624318976 :=
  block_append moment_5949_1250_part28 moment_5949_1250_join27 rfl rfl rfl
private theorem moment_5949_1250_join29 :
    blockEstimate 5949 1250 5218 256 = 2058914294784 :=
  block_append moment_5949_1250_part31 moment_5949_1250_part32 rfl rfl rfl
private theorem moment_5949_1250_join30 :
    blockEstimate 5949 1250 5474 256 = 1905273400320 :=
  block_append moment_5949_1250_part33 moment_5949_1250_part34 rfl rfl rfl
private theorem moment_5949_1250_join31 :
    blockEstimate 5949 1250 5218 512 = 3964187695104 :=
  block_append moment_5949_1250_join29 moment_5949_1250_join30 rfl rfl rfl
private theorem moment_5949_1250_join32 :
    blockEstimate 5949 1250 4834 896 = 7248812014080 :=
  block_append moment_5949_1250_join28 moment_5949_1250_join31 rfl rfl rfl
private theorem moment_5949_1250_join33 :
    blockEstimate 5949 1250 5858 256 = 1597478250130 :=
  block_append moment_5949_1250_part36 moment_5949_1250_part37 rfl rfl rfl
private theorem moment_5949_1250_join34 :
    blockEstimate 5949 1250 5730 384 = 2479381929106 :=
  block_append moment_5949_1250_part35 moment_5949_1250_join33 rfl rfl rfl
private theorem moment_5949_1250_join35 :
    blockEstimate 5949 1250 6114 256 = 1360563597267 :=
  block_append moment_5949_1250_part38 moment_5949_1250_part39 rfl rfl rfl
private theorem moment_5949_1250_join36 :
    blockEstimate 5949 1250 6370 256 = 1120957467750 :=
  block_append moment_5949_1250_part40 moment_5949_1250_part41 rfl rfl rfl
private theorem moment_5949_1250_join37 :
    blockEstimate 5949 1250 6114 512 = 2481521065017 :=
  block_append moment_5949_1250_join35 moment_5949_1250_join36 rfl rfl rfl
private theorem moment_5949_1250_join38 :
    blockEstimate 5949 1250 5730 896 = 4960902994123 :=
  block_append moment_5949_1250_join34 moment_5949_1250_join37 rfl rfl rfl
private theorem moment_5949_1250_join39 :
    blockEstimate 5949 1250 4834 1792 = 12209715008203 :=
  block_append moment_5949_1250_join32 moment_5949_1250_join38 rfl rfl rfl
private theorem moment_5949_1250_join40 :
    blockEstimate 5949 1250 6754 256 = 775474082826 :=
  block_append moment_5949_1250_part43 moment_5949_1250_part44 rfl rfl rfl
private theorem moment_5949_1250_join41 :
    blockEstimate 5949 1250 6626 384 = 1247687670868 :=
  block_append moment_5949_1250_part42 moment_5949_1250_join40 rfl rfl rfl
private theorem moment_5949_1250_join42 :
    blockEstimate 5949 1250 7010 256 = 565643962477 :=
  block_append moment_5949_1250_part45 moment_5949_1250_part46 rfl rfl rfl
private theorem moment_5949_1250_join43 :
    blockEstimate 5949 1250 7266 256 = 379289716096 :=
  block_append moment_5949_1250_part47 moment_5949_1250_part48 rfl rfl rfl
private theorem moment_5949_1250_join44 :
    blockEstimate 5949 1250 7010 512 = 944933678573 :=
  block_append moment_5949_1250_join42 moment_5949_1250_join43 rfl rfl rfl
private theorem moment_5949_1250_join45 :
    blockEstimate 5949 1250 6626 896 = 2192621349441 :=
  block_append moment_5949_1250_join41 moment_5949_1250_join44 rfl rfl rfl
private theorem moment_5949_1250_join46 :
    blockEstimate 5949 1250 7522 256 = 225068664192 :=
  block_append moment_5949_1250_part49 moment_5949_1250_part50 rfl rfl rfl
private theorem moment_5949_1250_join47 :
    blockEstimate 5949 1250 7778 256 = 108172199296 :=
  block_append moment_5949_1250_part51 moment_5949_1250_part52 rfl rfl rfl
private theorem moment_5949_1250_join48 :
    blockEstimate 5949 1250 7522 512 = 333240863488 :=
  block_append moment_5949_1250_join46 moment_5949_1250_join47 rfl rfl rfl
private theorem moment_5949_1250_join49 :
    blockEstimate 5949 1250 8034 256 = 32626853248 :=
  block_append moment_5949_1250_part53 moment_5949_1250_part54 rfl rfl rfl
private theorem moment_5949_1250_join50 :
    blockEstimate 5949 1250 8290 159 = 2024102000 :=
  block_append moment_5949_1250_part55 moment_5949_1250_part56 rfl rfl rfl
private theorem moment_5949_1250_join51 :
    blockEstimate 5949 1250 8034 415 = 34650955248 :=
  block_append moment_5949_1250_join49 moment_5949_1250_join50 rfl rfl rfl
private theorem moment_5949_1250_join52 :
    blockEstimate 5949 1250 7522 927 = 367891818736 :=
  block_append moment_5949_1250_join48 moment_5949_1250_join51 rfl rfl rfl
private theorem moment_5949_1250_join53 :
    blockEstimate 5949 1250 6626 1823 = 2560513168177 :=
  block_append moment_5949_1250_join45 moment_5949_1250_join52 rfl rfl rfl
private theorem moment_5949_1250_join54 :
    blockEstimate 5949 1250 4834 3615 = 14770228176380 :=
  block_append moment_5949_1250_join39 moment_5949_1250_join53 rfl rfl rfl
private theorem moment_5949_1250_join55 :
    blockEstimate 5949 1250 1250 7199 = 33568648660145 :=
  block_append moment_5949_1250_join26 moment_5949_1250_join54 rfl rfl rfl

theorem moment_5949_1250 : momentEstimate 5949 1250 = 33568648660145 := moment_5949_1250_join55

private theorem moment_5949_1297_part0 :
    blockEstimate 5949 1297 1297 128 = 2094237600 := by decide +kernel
private theorem moment_5949_1297_part1 :
    blockEstimate 5949 1297 1425 128 = 14194759584 := by decide +kernel
private theorem moment_5949_1297_part2 :
    blockEstimate 5949 1297 1553 128 = 37560133536 := by decide +kernel
private theorem moment_5949_1297_part3 :
    blockEstimate 5949 1297 1681 128 = 71385053088 := by decide +kernel
private theorem moment_5949_1297_part4 :
    blockEstimate 5949 1297 1809 128 = 114864211872 := by decide +kernel
private theorem moment_5949_1297_part5 :
    blockEstimate 5949 1297 1937 128 = 167192303520 := by decide +kernel
private theorem moment_5949_1297_part6 :
    blockEstimate 5949 1297 2065 128 = 227564021664 := by decide +kernel
private theorem moment_5949_1297_part7 :
    blockEstimate 5949 1297 2193 128 = 295174059936 := by decide +kernel
private theorem moment_5949_1297_part8 :
    blockEstimate 5949 1297 2321 128 = 369217111968 := by decide +kernel
private theorem moment_5949_1297_part9 :
    blockEstimate 5949 1297 2449 128 = 448887871392 := by decide +kernel
private theorem moment_5949_1297_part10 :
    blockEstimate 5949 1297 2577 128 = 532339608380 := by decide +kernel
private theorem moment_5949_1297_part11 :
    blockEstimate 5949 1297 2705 128 = 612754814144 := by decide +kernel
private theorem moment_5949_1297_part12 :
    blockEstimate 5949 1297 2833 128 = 687729620160 := by decide +kernel
private theorem moment_5949_1297_part13 :
    blockEstimate 5949 1297 2961 128 = 757260219584 := by decide +kernel
private theorem moment_5949_1297_part14 :
    blockEstimate 5949 1297 3089 128 = 821346612416 := by decide +kernel
private theorem moment_5949_1297_part15 :
    blockEstimate 5949 1297 3217 128 = 879988798656 := by decide +kernel
private theorem moment_5949_1297_part16 :
    blockEstimate 5949 1297 3345 128 = 933186778304 := by decide +kernel
private theorem moment_5949_1297_part17 :
    blockEstimate 5949 1297 3473 128 = 980940551360 := by decide +kernel
private theorem moment_5949_1297_part18 :
    blockEstimate 5949 1297 3601 128 = 1023250117824 := by decide +kernel
private theorem moment_5949_1297_part19 :
    blockEstimate 5949 1297 3729 128 = 1060115477696 := by decide +kernel
private theorem moment_5949_1297_part20 :
    blockEstimate 5949 1297 3857 128 = 1091536630976 := by decide +kernel
private theorem moment_5949_1297_part21 :
    blockEstimate 5949 1297 3985 128 = 1117513577664 := by decide +kernel
private theorem moment_5949_1297_part22 :
    blockEstimate 5949 1297 4113 128 = 1138046317760 := by decide +kernel
private theorem moment_5949_1297_part23 :
    blockEstimate 5949 1297 4241 128 = 1153134851264 := by decide +kernel
private theorem moment_5949_1297_part24 :
    blockEstimate 5949 1297 4369 128 = 1162779178176 := by decide +kernel
private theorem moment_5949_1297_part25 :
    blockEstimate 5949 1297 4497 128 = 1166979298496 := by decide +kernel
private theorem moment_5949_1297_part26 :
    blockEstimate 5949 1297 4625 128 = 1165735212224 := by decide +kernel
private theorem moment_5949_1297_part27 :
    blockEstimate 5949 1297 4753 128 = 1159046919360 := by decide +kernel
private theorem moment_5949_1297_part28 :
    blockEstimate 5949 1297 4881 128 = 1146914419904 := by decide +kernel
private theorem moment_5949_1297_part29 :
    blockEstimate 5949 1297 5009 128 = 1129337713856 := by decide +kernel
private theorem moment_5949_1297_part30 :
    blockEstimate 5949 1297 5137 128 = 1106316801216 := by decide +kernel
private theorem moment_5949_1297_part31 :
    blockEstimate 5949 1297 5265 128 = 1077851681984 := by decide +kernel
private theorem moment_5949_1297_part32 :
    blockEstimate 5949 1297 5393 128 = 1043942356160 := by decide +kernel
private theorem moment_5949_1297_part33 :
    blockEstimate 5949 1297 5521 128 = 1004588823744 := by decide +kernel
private theorem moment_5949_1297_part34 :
    blockEstimate 5949 1297 5649 128 = 959791084736 := by decide +kernel
private theorem moment_5949_1297_part35 :
    blockEstimate 5949 1297 5777 128 = 909549139136 := by decide +kernel
private theorem moment_5949_1297_part36 :
    blockEstimate 5949 1297 5905 128 = 854036358193 := by decide +kernel
private theorem moment_5949_1297_part37 :
    blockEstimate 5949 1297 6033 128 = 795430602280 := by decide +kernel
private theorem moment_5949_1297_part38 :
    blockEstimate 5949 1297 6161 128 = 735560311444 := by decide +kernel
private theorem moment_5949_1297_part39 :
    blockEstimate 5949 1297 6289 128 = 675019149769 := by decide +kernel
private theorem moment_5949_1297_part40 :
    blockEstimate 5949 1297 6417 128 = 614358284506 := by decide +kernel
private theorem moment_5949_1297_part41 :
    blockEstimate 5949 1297 6545 128 = 554109028741 := by decide +kernel
private theorem moment_5949_1297_part42 :
    blockEstimate 5949 1297 6673 128 = 494782841619 := by decide +kernel
private theorem moment_5949_1297_part43 :
    blockEstimate 5949 1297 6801 128 = 436871329414 := by decide +kernel
private theorem moment_5949_1297_part44 :
    blockEstimate 5949 1297 6929 128 = 380846244653 := by decide +kernel
private theorem moment_5949_1297_part45 :
    blockEstimate 5949 1297 7057 128 = 327159486394 := by decide +kernel
private theorem moment_5949_1297_part46 :
    blockEstimate 5949 1297 7185 128 = 276134813703 := by decide +kernel
private theorem moment_5949_1297_part47 :
    blockEstimate 5949 1297 7313 128 = 227879129936 := by decide +kernel
private theorem moment_5949_1297_part48 :
    blockEstimate 5949 1297 7441 128 = 183461502800 := by decide +kernel
private theorem moment_5949_1297_part49 :
    blockEstimate 5949 1297 7569 128 = 143239555920 := by decide +kernel
private theorem moment_5949_1297_part50 :
    blockEstimate 5949 1297 7697 128 = 107464947536 := by decide +kernel
private theorem moment_5949_1297_part51 :
    blockEstimate 5949 1297 7825 128 = 76389335888 := by decide +kernel
private theorem moment_5949_1297_part52 :
    blockEstimate 5949 1297 7953 128 = 50264379216 := by decide +kernel
private theorem moment_5949_1297_part53 :
    blockEstimate 5949 1297 8081 128 = 29341735760 := by decide +kernel
private theorem moment_5949_1297_part54 :
    blockEstimate 5949 1297 8209 128 = 13873063760 := by decide +kernel
private theorem moment_5949_1297_part55 :
    blockEstimate 5949 1297 8337 128 = 4110021456 := by decide +kernel
private theorem moment_5949_1297_part56 :
    blockEstimate 5949 1297 8465 78 = 247522410 := by decide +kernel
private theorem moment_5949_1297_join0 :
    blockEstimate 5949 1297 1425 256 = 51754893120 :=
  block_append moment_5949_1297_part1 moment_5949_1297_part2 rfl rfl rfl
private theorem moment_5949_1297_join1 :
    blockEstimate 5949 1297 1297 384 = 53849130720 :=
  block_append moment_5949_1297_part0 moment_5949_1297_join0 rfl rfl rfl
private theorem moment_5949_1297_join2 :
    blockEstimate 5949 1297 1681 256 = 186249264960 :=
  block_append moment_5949_1297_part3 moment_5949_1297_part4 rfl rfl rfl
private theorem moment_5949_1297_join3 :
    blockEstimate 5949 1297 1937 256 = 394756325184 :=
  block_append moment_5949_1297_part5 moment_5949_1297_part6 rfl rfl rfl
private theorem moment_5949_1297_join4 :
    blockEstimate 5949 1297 1681 512 = 581005590144 :=
  block_append moment_5949_1297_join2 moment_5949_1297_join3 rfl rfl rfl
private theorem moment_5949_1297_join5 :
    blockEstimate 5949 1297 1297 896 = 634854720864 :=
  block_append moment_5949_1297_join1 moment_5949_1297_join4 rfl rfl rfl
private theorem moment_5949_1297_join6 :
    blockEstimate 5949 1297 2321 256 = 818104983360 :=
  block_append moment_5949_1297_part8 moment_5949_1297_part9 rfl rfl rfl
private theorem moment_5949_1297_join7 :
    blockEstimate 5949 1297 2193 384 = 1113279043296 :=
  block_append moment_5949_1297_part7 moment_5949_1297_join6 rfl rfl rfl
private theorem moment_5949_1297_join8 :
    blockEstimate 5949 1297 2577 256 = 1145094422524 :=
  block_append moment_5949_1297_part10 moment_5949_1297_part11 rfl rfl rfl
private theorem moment_5949_1297_join9 :
    blockEstimate 5949 1297 2833 256 = 1444989839744 :=
  block_append moment_5949_1297_part12 moment_5949_1297_part13 rfl rfl rfl
private theorem moment_5949_1297_join10 :
    blockEstimate 5949 1297 2577 512 = 2590084262268 :=
  block_append moment_5949_1297_join8 moment_5949_1297_join9 rfl rfl rfl
private theorem moment_5949_1297_join11 :
    blockEstimate 5949 1297 2193 896 = 3703363305564 :=
  block_append moment_5949_1297_join7 moment_5949_1297_join10 rfl rfl rfl
private theorem moment_5949_1297_join12 :
    blockEstimate 5949 1297 1297 1792 = 4338218026428 :=
  block_append moment_5949_1297_join5 moment_5949_1297_join11 rfl rfl rfl
private theorem moment_5949_1297_join13 :
    blockEstimate 5949 1297 3217 256 = 1813175576960 :=
  block_append moment_5949_1297_part15 moment_5949_1297_part16 rfl rfl rfl
private theorem moment_5949_1297_join14 :
    blockEstimate 5949 1297 3089 384 = 2634522189376 :=
  block_append moment_5949_1297_part14 moment_5949_1297_join13 rfl rfl rfl
private theorem moment_5949_1297_join15 :
    blockEstimate 5949 1297 3473 256 = 2004190669184 :=
  block_append moment_5949_1297_part17 moment_5949_1297_part18 rfl rfl rfl
private theorem moment_5949_1297_join16 :
    blockEstimate 5949 1297 3729 256 = 2151652108672 :=
  block_append moment_5949_1297_part19 moment_5949_1297_part20 rfl rfl rfl
private theorem moment_5949_1297_join17 :
    blockEstimate 5949 1297 3473 512 = 4155842777856 :=
  block_append moment_5949_1297_join15 moment_5949_1297_join16 rfl rfl rfl
private theorem moment_5949_1297_join18 :
    blockEstimate 5949 1297 3089 896 = 6790364967232 :=
  block_append moment_5949_1297_join14 moment_5949_1297_join17 rfl rfl rfl
private theorem moment_5949_1297_join19 :
    blockEstimate 5949 1297 4113 256 = 2291181169024 :=
  block_append moment_5949_1297_part22 moment_5949_1297_part23 rfl rfl rfl
private theorem moment_5949_1297_join20 :
    blockEstimate 5949 1297 3985 384 = 3408694746688 :=
  block_append moment_5949_1297_part21 moment_5949_1297_join19 rfl rfl rfl
private theorem moment_5949_1297_join21 :
    blockEstimate 5949 1297 4369 256 = 2329758476672 :=
  block_append moment_5949_1297_part24 moment_5949_1297_part25 rfl rfl rfl
private theorem moment_5949_1297_join22 :
    blockEstimate 5949 1297 4625 256 = 2324782131584 :=
  block_append moment_5949_1297_part26 moment_5949_1297_part27 rfl rfl rfl
private theorem moment_5949_1297_join23 :
    blockEstimate 5949 1297 4369 512 = 4654540608256 :=
  block_append moment_5949_1297_join21 moment_5949_1297_join22 rfl rfl rfl
private theorem moment_5949_1297_join24 :
    blockEstimate 5949 1297 3985 896 = 8063235354944 :=
  block_append moment_5949_1297_join20 moment_5949_1297_join23 rfl rfl rfl
private theorem moment_5949_1297_join25 :
    blockEstimate 5949 1297 3089 1792 = 14853600322176 :=
  block_append moment_5949_1297_join18 moment_5949_1297_join24 rfl rfl rfl
private theorem moment_5949_1297_join26 :
    blockEstimate 5949 1297 1297 3584 = 19191818348604 :=
  block_append moment_5949_1297_join12 moment_5949_1297_join25 rfl rfl rfl
private theorem moment_5949_1297_join27 :
    blockEstimate 5949 1297 5009 256 = 2235654515072 :=
  block_append moment_5949_1297_part29 moment_5949_1297_part30 rfl rfl rfl
private theorem moment_5949_1297_join28 :
    blockEstimate 5949 1297 4881 384 = 3382568934976 :=
  block_append moment_5949_1297_part28 moment_5949_1297_join27 rfl rfl rfl
private theorem moment_5949_1297_join29 :
    blockEstimate 5949 1297 5265 256 = 2121794038144 :=
  block_append moment_5949_1297_part31 moment_5949_1297_part32 rfl rfl rfl
private theorem moment_5949_1297_join30 :
    blockEstimate 5949 1297 5521 256 = 1964379908480 :=
  block_append moment_5949_1297_part33 moment_5949_1297_part34 rfl rfl rfl
private theorem moment_5949_1297_join31 :
    blockEstimate 5949 1297 5265 512 = 4086173946624 :=
  block_append moment_5949_1297_join29 moment_5949_1297_join30 rfl rfl rfl
private theorem moment_5949_1297_join32 :
    blockEstimate 5949 1297 4881 896 = 7468742881600 :=
  block_append moment_5949_1297_join28 moment_5949_1297_join31 rfl rfl rfl
private theorem moment_5949_1297_join33 :
    blockEstimate 5949 1297 5905 256 = 1649466960473 :=
  block_append moment_5949_1297_part36 moment_5949_1297_part37 rfl rfl rfl
private theorem moment_5949_1297_join34 :
    blockEstimate 5949 1297 5777 384 = 2559016099609 :=
  block_append moment_5949_1297_part35 moment_5949_1297_join33 rfl rfl rfl
private theorem moment_5949_1297_join35 :
    blockEstimate 5949 1297 6161 256 = 1410579461213 :=
  block_append moment_5949_1297_part38 moment_5949_1297_part39 rfl rfl rfl
private theorem moment_5949_1297_join36 :
    blockEstimate 5949 1297 6417 256 = 1168467313247 :=
  block_append moment_5949_1297_part40 moment_5949_1297_part41 rfl rfl rfl
private theorem moment_5949_1297_join37 :
    blockEstimate 5949 1297 6161 512 = 2579046774460 :=
  block_append moment_5949_1297_join35 moment_5949_1297_join36 rfl rfl rfl
private theorem moment_5949_1297_join38 :
    blockEstimate 5949 1297 5777 896 = 5138062874069 :=
  block_append moment_5949_1297_join34 moment_5949_1297_join37 rfl rfl rfl
private theorem moment_5949_1297_join39 :
    blockEstimate 5949 1297 4881 1792 = 12606805755669 :=
  block_append moment_5949_1297_join32 moment_5949_1297_join38 rfl rfl rfl
private theorem moment_5949_1297_join40 :
    blockEstimate 5949 1297 6801 256 = 817717574067 :=
  block_append moment_5949_1297_part43 moment_5949_1297_part44 rfl rfl rfl
private theorem moment_5949_1297_join41 :
    blockEstimate 5949 1297 6673 384 = 1312500415686 :=
  block_append moment_5949_1297_part42 moment_5949_1297_join40 rfl rfl rfl
private theorem moment_5949_1297_join42 :
    blockEstimate 5949 1297 7057 256 = 603294300097 :=
  block_append moment_5949_1297_part45 moment_5949_1297_part46 rfl rfl rfl
private theorem moment_5949_1297_join43 :
    blockEstimate 5949 1297 7313 256 = 411340632736 :=
  block_append moment_5949_1297_part47 moment_5949_1297_part48 rfl rfl rfl
private theorem moment_5949_1297_join44 :
    blockEstimate 5949 1297 7057 512 = 1014634932833 :=
  block_append moment_5949_1297_join42 moment_5949_1297_join43 rfl rfl rfl
private theorem moment_5949_1297_join45 :
    blockEstimate 5949 1297 6673 896 = 2327135348519 :=
  block_append moment_5949_1297_join41 moment_5949_1297_join44 rfl rfl rfl
private theorem moment_5949_1297_join46 :
    blockEstimate 5949 1297 7569 256 = 250704503456 :=
  block_append moment_5949_1297_part49 moment_5949_1297_part50 rfl rfl rfl
private theorem moment_5949_1297_join47 :
    blockEstimate 5949 1297 7825 256 = 126653715104 :=
  block_append moment_5949_1297_part51 moment_5949_1297_part52 rfl rfl rfl
private theorem moment_5949_1297_join48 :
    blockEstimate 5949 1297 7569 512 = 377358218560 :=
  block_append moment_5949_1297_join46 moment_5949_1297_join47 rfl rfl rfl
private theorem moment_5949_1297_join49 :
    blockEstimate 5949 1297 8081 256 = 43214799520 :=
  block_append moment_5949_1297_part53 moment_5949_1297_part54 rfl rfl rfl
private theorem moment_5949_1297_join50 :
    blockEstimate 5949 1297 8337 206 = 4357543866 :=
  block_append moment_5949_1297_part55 moment_5949_1297_part56 rfl rfl rfl
private theorem moment_5949_1297_join51 :
    blockEstimate 5949 1297 8081 462 = 47572343386 :=
  block_append moment_5949_1297_join49 moment_5949_1297_join50 rfl rfl rfl
private theorem moment_5949_1297_join52 :
    blockEstimate 5949 1297 7569 974 = 424930561946 :=
  block_append moment_5949_1297_join48 moment_5949_1297_join51 rfl rfl rfl
private theorem moment_5949_1297_join53 :
    blockEstimate 5949 1297 6673 1870 = 2752065910465 :=
  block_append moment_5949_1297_join45 moment_5949_1297_join52 rfl rfl rfl
private theorem moment_5949_1297_join54 :
    blockEstimate 5949 1297 4881 3662 = 15358871666134 :=
  block_append moment_5949_1297_join39 moment_5949_1297_join53 rfl rfl rfl
private theorem moment_5949_1297_join55 :
    blockEstimate 5949 1297 1297 7246 = 34550690014738 :=
  block_append moment_5949_1297_join26 moment_5949_1297_join54 rfl rfl rfl

theorem moment_5949_1297 : momentEstimate 5949 1297 = 34550690014738 := moment_5949_1297_join55

private theorem moment_9203_1934_part0 :
    blockEstimate 9203 1934 1934 128 = 3258388640 := by decide +kernel
private theorem moment_9203_1934_part1 :
    blockEstimate 9203 1934 2062 128 = 22236356768 := by decide +kernel
private theorem moment_9203_1934_part2 :
    blockEstimate 9203 1934 2190 128 = 59303309472 := by decide +kernel
private theorem moment_9203_1934_part3 :
    blockEstimate 9203 1934 2318 128 = 113653940384 := by decide +kernel
private theorem moment_9203_1934_part4 :
    blockEstimate 9203 1934 2446 128 = 184482943136 := by decide +kernel
private theorem moment_9203_1934_part5 :
    blockEstimate 9203 1934 2574 128 = 270985011360 := by decide +kernel
private theorem moment_9203_1934_part6 :
    blockEstimate 9203 1934 2702 128 = 372354838688 := by decide +kernel
private theorem moment_9203_1934_part7 :
    blockEstimate 9203 1934 2830 128 = 487787118752 := by decide +kernel
private theorem moment_9203_1934_part8 :
    blockEstimate 9203 1934 2958 128 = 616476545184 := by decide +kernel
private theorem moment_9203_1934_part9 :
    blockEstimate 9203 1934 3086 128 = 757617811616 := by decide +kernel
private theorem moment_9203_1934_part10 :
    blockEstimate 9203 1934 3214 128 = 910405611680 := by decide +kernel
private theorem moment_9203_1934_part11 :
    blockEstimate 9203 1934 3342 128 = 1074034639008 := by decide +kernel
private theorem moment_9203_1934_part12 :
    blockEstimate 9203 1934 3470 128 = 1247699587232 := by decide +kernel
private theorem moment_9203_1934_part13 :
    blockEstimate 9203 1934 3598 128 = 1430595149984 := by decide +kernel
private theorem moment_9203_1934_part14 :
    blockEstimate 9203 1934 3726 128 = 1621916020896 := by decide +kernel
private theorem moment_9203_1934_part15 :
    blockEstimate 9203 1934 3854 128 = 1819083128080 := by decide +kernel
private theorem moment_9203_1934_part16 :
    blockEstimate 9203 1934 3982 128 = 2011644080640 := by decide +kernel
private theorem moment_9203_1934_part17 :
    blockEstimate 9203 1934 4110 128 = 2196092367360 := by decide +kernel
private theorem moment_9203_1934_part18 :
    blockEstimate 9203 1934 4238 128 = 2372424675840 := by decide +kernel
private theorem moment_9203_1934_part19 :
    blockEstimate 9203 1934 4366 128 = 2540641006080 := by decide +kernel
private theorem moment_9203_1934_part20 :
    blockEstimate 9203 1934 4494 128 = 2700741358080 := by decide +kernel
private theorem moment_9203_1934_part21 :
    blockEstimate 9203 1934 4622 128 = 2852725731840 := by decide +kernel
private theorem moment_9203_1934_part22 :
    blockEstimate 9203 1934 4750 128 = 2996594127360 := by decide +kernel
private theorem moment_9203_1934_part23 :
    blockEstimate 9203 1934 4878 128 = 3132346544640 := by decide +kernel
private theorem moment_9203_1934_part24 :
    blockEstimate 9203 1934 5006 128 = 3259982983680 := by decide +kernel
private theorem moment_9203_1934_part25 :
    blockEstimate 9203 1934 5134 128 = 3379503444480 := by decide +kernel
private theorem moment_9203_1934_part26 :
    blockEstimate 9203 1934 5262 128 = 3490907927040 := by decide +kernel
private theorem moment_9203_1934_part27 :
    blockEstimate 9203 1934 5390 128 = 3594196431360 := by decide +kernel
private theorem moment_9203_1934_part28 :
    blockEstimate 9203 1934 5518 128 = 3689368957440 := by decide +kernel
private theorem moment_9203_1934_part29 :
    blockEstimate 9203 1934 5646 128 = 3776425505280 := by decide +kernel
private theorem moment_9203_1934_part30 :
    blockEstimate 9203 1934 5774 128 = 3855366074880 := by decide +kernel
private theorem moment_9203_1934_part31 :
    blockEstimate 9203 1934 5902 128 = 3926190666240 := by decide +kernel
private theorem moment_9203_1934_part32 :
    blockEstimate 9203 1934 6030 128 = 3988899279360 := by decide +kernel
private theorem moment_9203_1934_part33 :
    blockEstimate 9203 1934 6158 128 = 4043491914240 := by decide +kernel
private theorem moment_9203_1934_part34 :
    blockEstimate 9203 1934 6286 128 = 4089968570880 := by decide +kernel
private theorem moment_9203_1934_part35 :
    blockEstimate 9203 1934 6414 128 = 4128329249280 := by decide +kernel
private theorem moment_9203_1934_part36 :
    blockEstimate 9203 1934 6542 128 = 4158573949440 := by decide +kernel
private theorem moment_9203_1934_part37 :
    blockEstimate 9203 1934 6670 128 = 4180702671360 := by decide +kernel
private theorem moment_9203_1934_part38 :
    blockEstimate 9203 1934 6798 128 = 4194715415040 := by decide +kernel
private theorem moment_9203_1934_part39 :
    blockEstimate 9203 1934 6926 128 = 4200612180480 := by decide +kernel
private theorem moment_9203_1934_part40 :
    blockEstimate 9203 1934 7054 128 = 4198392967680 := by decide +kernel
private theorem moment_9203_1934_part41 :
    blockEstimate 9203 1934 7182 128 = 4188057776640 := by decide +kernel
private theorem moment_9203_1934_part42 :
    blockEstimate 9203 1934 7310 128 = 4169606607360 := by decide +kernel
private theorem moment_9203_1934_part43 :
    blockEstimate 9203 1934 7438 128 = 4143039459840 := by decide +kernel
private theorem moment_9203_1934_part44 :
    blockEstimate 9203 1934 7566 128 = 4108356334080 := by decide +kernel
private theorem moment_9203_1934_part45 :
    blockEstimate 9203 1934 7694 128 = 4065557230080 := by decide +kernel
private theorem moment_9203_1934_part46 :
    blockEstimate 9203 1934 7822 128 = 4014642147840 := by decide +kernel
private theorem moment_9203_1934_part47 :
    blockEstimate 9203 1934 7950 128 = 3955611087360 := by decide +kernel
private theorem moment_9203_1934_part48 :
    blockEstimate 9203 1934 8078 128 = 3888464048640 := by decide +kernel
private theorem moment_9203_1934_part49 :
    blockEstimate 9203 1934 8206 128 = 3813201031680 := by decide +kernel
private theorem moment_9203_1934_part50 :
    blockEstimate 9203 1934 8334 128 = 3729822036480 := by decide +kernel
private theorem moment_9203_1934_part51 :
    blockEstimate 9203 1934 8462 128 = 3638327063040 := by decide +kernel
private theorem moment_9203_1934_part52 :
    blockEstimate 9203 1934 8590 128 = 3538716111360 := by decide +kernel
private theorem moment_9203_1934_part53 :
    blockEstimate 9203 1934 8718 128 = 3430989181440 := by decide +kernel
private theorem moment_9203_1934_part54 :
    blockEstimate 9203 1934 8846 128 = 3315146273280 := by decide +kernel
private theorem moment_9203_1934_part55 :
    blockEstimate 9203 1934 8974 128 = 3191187386880 := by decide +kernel
private theorem moment_9203_1934_part56 :
    blockEstimate 9203 1934 9102 128 = 3059121798234 := by decide +kernel
private theorem moment_9203_1934_part57 :
    blockEstimate 9203 1934 9230 128 = 2920638266827 := by decide +kernel
private theorem moment_9203_1934_part58 :
    blockEstimate 9203 1934 9358 128 = 2779617520432 := by decide +kernel
private theorem moment_9203_1934_part59 :
    blockEstimate 9203 1934 9486 128 = 2637088908865 := by decide +kernel
private theorem moment_9203_1934_part60 :
    blockEstimate 9203 1934 9614 128 = 2493626915931 := by decide +kernel
private theorem moment_9203_1934_part61 :
    blockEstimate 9203 1934 9742 128 = 2349792706038 := by decide +kernel
private theorem moment_9203_1934_part62 :
    blockEstimate 9203 1934 9870 128 = 2206134127642 := by decide +kernel
private theorem moment_9203_1934_part63 :
    blockEstimate 9203 1934 9998 128 = 2063185710257 := by decide +kernel
private theorem moment_9203_1934_part64 :
    blockEstimate 9203 1934 10126 128 = 1921468665706 := by decide +kernel
private theorem moment_9203_1934_part65 :
    blockEstimate 9203 1934 10254 128 = 1781490889536 := by decide +kernel
private theorem moment_9203_1934_part66 :
    blockEstimate 9203 1934 10382 128 = 1643746957970 := by decide +kernel
private theorem moment_9203_1934_part67 :
    blockEstimate 9203 1934 10510 128 = 1508718129074 := by decide +kernel
private theorem moment_9203_1934_part68 :
    blockEstimate 9203 1934 10638 128 = 1376872345203 := by decide +kernel
private theorem moment_9203_1934_part69 :
    blockEstimate 9203 1934 10766 128 = 1248664229658 := by decide +kernel
private theorem moment_9203_1934_part70 :
    blockEstimate 9203 1934 10894 128 = 1124535088073 := by decide +kernel
private theorem moment_9203_1934_part71 :
    blockEstimate 9203 1934 11022 128 = 1004902387008 := by decide +kernel
private theorem moment_9203_1934_part72 :
    blockEstimate 9203 1934 11150 128 = 889211437200 := by decide +kernel
private theorem moment_9203_1934_part73 :
    blockEstimate 9203 1934 11278 128 = 778654456976 := by decide +kernel
private theorem moment_9203_1934_part74 :
    blockEstimate 9203 1934 11406 128 = 674346662032 := by decide +kernel
private theorem moment_9203_1934_part75 :
    blockEstimate 9203 1934 11534 128 = 576539710608 := by decide +kernel
private theorem moment_9203_1934_part76 :
    blockEstimate 9203 1934 11662 128 = 485485260944 := by decide +kernel
private theorem moment_9203_1934_part77 :
    blockEstimate 9203 1934 11790 128 = 401434971280 := by decide +kernel
private theorem moment_9203_1934_part78 :
    blockEstimate 9203 1934 11918 128 = 324640499856 := by decide +kernel
private theorem moment_9203_1934_part79 :
    blockEstimate 9203 1934 12046 128 = 255353504912 := by decide +kernel
private theorem moment_9203_1934_part80 :
    blockEstimate 9203 1934 12174 128 = 193825644688 := by decide +kernel
private theorem moment_9203_1934_part81 :
    blockEstimate 9203 1934 12302 128 = 140308577424 := by decide +kernel
private theorem moment_9203_1934_part82 :
    blockEstimate 9203 1934 12430 128 = 95053961360 := by decide +kernel
private theorem moment_9203_1934_part83 :
    blockEstimate 9203 1934 12558 128 = 58313454736 := by decide +kernel
private theorem moment_9203_1934_part84 :
    blockEstimate 9203 1934 12686 128 = 30338715792 := by decide +kernel
private theorem moment_9203_1934_part85 :
    blockEstimate 9203 1934 12814 128 = 11381402768 := by decide +kernel
private theorem moment_9203_1934_part86 :
    blockEstimate 9203 1934 12942 128 = 1693173904 := by decide +kernel
private theorem moment_9203_1934_part87 :
    blockEstimate 9203 1934 13070 1 = 9203 := by decide +kernel
private theorem moment_9203_1934_join0 :
    blockEstimate 9203 1934 1934 256 = 25494745408 :=
  block_append moment_9203_1934_part0 moment_9203_1934_part1 rfl rfl rfl
private theorem moment_9203_1934_join1 :
    blockEstimate 9203 1934 2318 256 = 298136883520 :=
  block_append moment_9203_1934_part3 moment_9203_1934_part4 rfl rfl rfl
private theorem moment_9203_1934_join2 :
    blockEstimate 9203 1934 2190 384 = 357440192992 :=
  block_append moment_9203_1934_part2 moment_9203_1934_join1 rfl rfl rfl
private theorem moment_9203_1934_join3 :
    blockEstimate 9203 1934 1934 640 = 382934938400 :=
  block_append moment_9203_1934_join0 moment_9203_1934_join2 rfl rfl rfl
private theorem moment_9203_1934_join4 :
    blockEstimate 9203 1934 2702 256 = 860141957440 :=
  block_append moment_9203_1934_part6 moment_9203_1934_part7 rfl rfl rfl
private theorem moment_9203_1934_join5 :
    blockEstimate 9203 1934 2574 384 = 1131126968800 :=
  block_append moment_9203_1934_part5 moment_9203_1934_join4 rfl rfl rfl
private theorem moment_9203_1934_join6 :
    blockEstimate 9203 1934 3086 256 = 1668023423296 :=
  block_append moment_9203_1934_part9 moment_9203_1934_part10 rfl rfl rfl
private theorem moment_9203_1934_join7 :
    blockEstimate 9203 1934 2958 384 = 2284499968480 :=
  block_append moment_9203_1934_part8 moment_9203_1934_join6 rfl rfl rfl
private theorem moment_9203_1934_join8 :
    blockEstimate 9203 1934 2574 768 = 3415626937280 :=
  block_append moment_9203_1934_join5 moment_9203_1934_join7 rfl rfl rfl
private theorem moment_9203_1934_join9 :
    blockEstimate 9203 1934 1934 1408 = 3798561875680 :=
  block_append moment_9203_1934_join3 moment_9203_1934_join8 rfl rfl rfl
private theorem moment_9203_1934_join10 :
    blockEstimate 9203 1934 3342 256 = 2321734226240 :=
  block_append moment_9203_1934_part11 moment_9203_1934_part12 rfl rfl rfl
private theorem moment_9203_1934_join11 :
    blockEstimate 9203 1934 3726 256 = 3440999148976 :=
  block_append moment_9203_1934_part14 moment_9203_1934_part15 rfl rfl rfl
private theorem moment_9203_1934_join12 :
    blockEstimate 9203 1934 3598 384 = 4871594298960 :=
  block_append moment_9203_1934_part13 moment_9203_1934_join11 rfl rfl rfl
private theorem moment_9203_1934_join13 :
    blockEstimate 9203 1934 3342 640 = 7193328525200 :=
  block_append moment_9203_1934_join10 moment_9203_1934_join12 rfl rfl rfl
private theorem moment_9203_1934_join14 :
    blockEstimate 9203 1934 4110 256 = 4568517043200 :=
  block_append moment_9203_1934_part17 moment_9203_1934_part18 rfl rfl rfl
private theorem moment_9203_1934_join15 :
    blockEstimate 9203 1934 3982 384 = 6580161123840 :=
  block_append moment_9203_1934_part16 moment_9203_1934_join14 rfl rfl rfl
private theorem moment_9203_1934_join16 :
    blockEstimate 9203 1934 4494 256 = 5553467089920 :=
  block_append moment_9203_1934_part20 moment_9203_1934_part21 rfl rfl rfl
private theorem moment_9203_1934_join17 :
    blockEstimate 9203 1934 4366 384 = 8094108096000 :=
  block_append moment_9203_1934_part19 moment_9203_1934_join16 rfl rfl rfl
private theorem moment_9203_1934_join18 :
    blockEstimate 9203 1934 3982 768 = 14674269219840 :=
  block_append moment_9203_1934_join15 moment_9203_1934_join17 rfl rfl rfl
private theorem moment_9203_1934_join19 :
    blockEstimate 9203 1934 3342 1408 = 21867597745040 :=
  block_append moment_9203_1934_join13 moment_9203_1934_join18 rfl rfl rfl
private theorem moment_9203_1934_join20 :
    blockEstimate 9203 1934 1934 2816 = 25666159620720 :=
  block_append moment_9203_1934_join9 moment_9203_1934_join19 rfl rfl rfl
private theorem moment_9203_1934_join21 :
    blockEstimate 9203 1934 4750 256 = 6128940672000 :=
  block_append moment_9203_1934_part22 moment_9203_1934_part23 rfl rfl rfl
private theorem moment_9203_1934_join22 :
    blockEstimate 9203 1934 5134 256 = 6870411371520 :=
  block_append moment_9203_1934_part25 moment_9203_1934_part26 rfl rfl rfl
private theorem moment_9203_1934_join23 :
    blockEstimate 9203 1934 5006 384 = 10130394355200 :=
  block_append moment_9203_1934_part24 moment_9203_1934_join22 rfl rfl rfl
private theorem moment_9203_1934_join24 :
    blockEstimate 9203 1934 4750 640 = 16259335027200 :=
  block_append moment_9203_1934_join21 moment_9203_1934_join23 rfl rfl rfl
private theorem moment_9203_1934_join25 :
    blockEstimate 9203 1934 5518 256 = 7465794462720 :=
  block_append moment_9203_1934_part28 moment_9203_1934_part29 rfl rfl rfl
private theorem moment_9203_1934_join26 :
    blockEstimate 9203 1934 5390 384 = 11059990894080 :=
  block_append moment_9203_1934_part27 moment_9203_1934_join25 rfl rfl rfl
private theorem moment_9203_1934_join27 :
    blockEstimate 9203 1934 5902 256 = 7915089945600 :=
  block_append moment_9203_1934_part31 moment_9203_1934_part32 rfl rfl rfl
private theorem moment_9203_1934_join28 :
    blockEstimate 9203 1934 5774 384 = 11770456020480 :=
  block_append moment_9203_1934_part30 moment_9203_1934_join27 rfl rfl rfl
private theorem moment_9203_1934_join29 :
    blockEstimate 9203 1934 5390 768 = 22830446914560 :=
  block_append moment_9203_1934_join26 moment_9203_1934_join28 rfl rfl rfl
private theorem moment_9203_1934_join30 :
    blockEstimate 9203 1934 4750 1408 = 39089781941760 :=
  block_append moment_9203_1934_join24 moment_9203_1934_join29 rfl rfl rfl
private theorem moment_9203_1934_join31 :
    blockEstimate 9203 1934 6158 256 = 8133460485120 :=
  block_append moment_9203_1934_part33 moment_9203_1934_part34 rfl rfl rfl
private theorem moment_9203_1934_join32 :
    blockEstimate 9203 1934 6542 256 = 8339276620800 :=
  block_append moment_9203_1934_part36 moment_9203_1934_part37 rfl rfl rfl
private theorem moment_9203_1934_join33 :
    blockEstimate 9203 1934 6414 384 = 12467605870080 :=
  block_append moment_9203_1934_part35 moment_9203_1934_join32 rfl rfl rfl
private theorem moment_9203_1934_join34 :
    blockEstimate 9203 1934 6158 640 = 20601066355200 :=
  block_append moment_9203_1934_join31 moment_9203_1934_join33 rfl rfl rfl
private theorem moment_9203_1934_join35 :
    blockEstimate 9203 1934 6926 256 = 8399005148160 :=
  block_append moment_9203_1934_part39 moment_9203_1934_part40 rfl rfl rfl
private theorem moment_9203_1934_join36 :
    blockEstimate 9203 1934 6798 384 = 12593720563200 :=
  block_append moment_9203_1934_part38 moment_9203_1934_join35 rfl rfl rfl
private theorem moment_9203_1934_join37 :
    blockEstimate 9203 1934 7310 256 = 8312646067200 :=
  block_append moment_9203_1934_part42 moment_9203_1934_part43 rfl rfl rfl
private theorem moment_9203_1934_join38 :
    blockEstimate 9203 1934 7182 384 = 12500703843840 :=
  block_append moment_9203_1934_part41 moment_9203_1934_join37 rfl rfl rfl
private theorem moment_9203_1934_join39 :
    blockEstimate 9203 1934 6798 768 = 25094424407040 :=
  block_append moment_9203_1934_join36 moment_9203_1934_join38 rfl rfl rfl
private theorem moment_9203_1934_join40 :
    blockEstimate 9203 1934 6158 1408 = 45695490762240 :=
  block_append moment_9203_1934_join34 moment_9203_1934_join39 rfl rfl rfl
private theorem moment_9203_1934_join41 :
    blockEstimate 9203 1934 4750 2816 = 84785272704000 :=
  block_append moment_9203_1934_join30 moment_9203_1934_join40 rfl rfl rfl
private theorem moment_9203_1934_join42 :
    blockEstimate 9203 1934 1934 5632 = 110451432324720 :=
  block_append moment_9203_1934_join20 moment_9203_1934_join41 rfl rfl rfl
private theorem moment_9203_1934_join43 :
    blockEstimate 9203 1934 7566 256 = 8173913564160 :=
  block_append moment_9203_1934_part44 moment_9203_1934_part45 rfl rfl rfl
private theorem moment_9203_1934_join44 :
    blockEstimate 9203 1934 7950 256 = 7844075136000 :=
  block_append moment_9203_1934_part47 moment_9203_1934_part48 rfl rfl rfl
private theorem moment_9203_1934_join45 :
    blockEstimate 9203 1934 7822 384 = 11858717283840 :=
  block_append moment_9203_1934_part46 moment_9203_1934_join44 rfl rfl rfl
private theorem moment_9203_1934_join46 :
    blockEstimate 9203 1934 7566 640 = 20032630848000 :=
  block_append moment_9203_1934_join43 moment_9203_1934_join45 rfl rfl rfl
private theorem moment_9203_1934_join47 :
    blockEstimate 9203 1934 8334 256 = 7368149099520 :=
  block_append moment_9203_1934_part50 moment_9203_1934_part51 rfl rfl rfl
private theorem moment_9203_1934_join48 :
    blockEstimate 9203 1934 8206 384 = 11181350131200 :=
  block_append moment_9203_1934_part49 moment_9203_1934_join47 rfl rfl rfl
private theorem moment_9203_1934_join49 :
    blockEstimate 9203 1934 8718 256 = 6746135454720 :=
  block_append moment_9203_1934_part53 moment_9203_1934_part54 rfl rfl rfl
private theorem moment_9203_1934_join50 :
    blockEstimate 9203 1934 8590 384 = 10284851566080 :=
  block_append moment_9203_1934_part52 moment_9203_1934_join49 rfl rfl rfl
private theorem moment_9203_1934_join51 :
    blockEstimate 9203 1934 8206 768 = 21466201697280 :=
  block_append moment_9203_1934_join48 moment_9203_1934_join50 rfl rfl rfl
private theorem moment_9203_1934_join52 :
    blockEstimate 9203 1934 7566 1408 = 41498832545280 :=
  block_append moment_9203_1934_join46 moment_9203_1934_join51 rfl rfl rfl
private theorem moment_9203_1934_join53 :
    blockEstimate 9203 1934 8974 256 = 6250309185114 :=
  block_append moment_9203_1934_part55 moment_9203_1934_part56 rfl rfl rfl
private theorem moment_9203_1934_join54 :
    blockEstimate 9203 1934 9358 256 = 5416706429297 :=
  block_append moment_9203_1934_part58 moment_9203_1934_part59 rfl rfl rfl
private theorem moment_9203_1934_join55 :
    blockEstimate 9203 1934 9230 384 = 8337344696124 :=
  block_append moment_9203_1934_part57 moment_9203_1934_join54 rfl rfl rfl
private theorem moment_9203_1934_join56 :
    blockEstimate 9203 1934 8974 640 = 14587653881238 :=
  block_append moment_9203_1934_join53 moment_9203_1934_join55 rfl rfl rfl
private theorem moment_9203_1934_join57 :
    blockEstimate 9203 1934 9742 256 = 4555926833680 :=
  block_append moment_9203_1934_part61 moment_9203_1934_part62 rfl rfl rfl
private theorem moment_9203_1934_join58 :
    blockEstimate 9203 1934 9614 384 = 7049553749611 :=
  block_append moment_9203_1934_part60 moment_9203_1934_join57 rfl rfl rfl
private theorem moment_9203_1934_join59 :
    blockEstimate 9203 1934 10126 256 = 3702959555242 :=
  block_append moment_9203_1934_part64 moment_9203_1934_part65 rfl rfl rfl
private theorem moment_9203_1934_join60 :
    blockEstimate 9203 1934 9998 384 = 5766145265499 :=
  block_append moment_9203_1934_part63 moment_9203_1934_join59 rfl rfl rfl
private theorem moment_9203_1934_join61 :
    blockEstimate 9203 1934 9614 768 = 12815699015110 :=
  block_append moment_9203_1934_join58 moment_9203_1934_join60 rfl rfl rfl
private theorem moment_9203_1934_join62 :
    blockEstimate 9203 1934 8974 1408 = 27403352896348 :=
  block_append moment_9203_1934_join56 moment_9203_1934_join61 rfl rfl rfl
private theorem moment_9203_1934_join63 :
    blockEstimate 9203 1934 7566 2816 = 68902185441628 :=
  block_append moment_9203_1934_join52 moment_9203_1934_join62 rfl rfl rfl
private theorem moment_9203_1934_join64 :
    blockEstimate 9203 1934 10382 256 = 3152465087044 :=
  block_append moment_9203_1934_part66 moment_9203_1934_part67 rfl rfl rfl
private theorem moment_9203_1934_join65 :
    blockEstimate 9203 1934 10766 256 = 2373199317731 :=
  block_append moment_9203_1934_part69 moment_9203_1934_part70 rfl rfl rfl
private theorem moment_9203_1934_join66 :
    blockEstimate 9203 1934 10638 384 = 3750071662934 :=
  block_append moment_9203_1934_part68 moment_9203_1934_join65 rfl rfl rfl
private theorem moment_9203_1934_join67 :
    blockEstimate 9203 1934 10382 640 = 6902536749978 :=
  block_append moment_9203_1934_join64 moment_9203_1934_join66 rfl rfl rfl
private theorem moment_9203_1934_join68 :
    blockEstimate 9203 1934 11150 256 = 1667865894176 :=
  block_append moment_9203_1934_part72 moment_9203_1934_part73 rfl rfl rfl
private theorem moment_9203_1934_join69 :
    blockEstimate 9203 1934 11022 384 = 2672768281184 :=
  block_append moment_9203_1934_part71 moment_9203_1934_join68 rfl rfl rfl
private theorem moment_9203_1934_join70 :
    blockEstimate 9203 1934 11534 256 = 1062024971552 :=
  block_append moment_9203_1934_part75 moment_9203_1934_part76 rfl rfl rfl
private theorem moment_9203_1934_join71 :
    blockEstimate 9203 1934 11406 384 = 1736371633584 :=
  block_append moment_9203_1934_part74 moment_9203_1934_join70 rfl rfl rfl
private theorem moment_9203_1934_join72 :
    blockEstimate 9203 1934 11022 768 = 4409139914768 :=
  block_append moment_9203_1934_join69 moment_9203_1934_join71 rfl rfl rfl
private theorem moment_9203_1934_join73 :
    blockEstimate 9203 1934 10382 1408 = 11311676664746 :=
  block_append moment_9203_1934_join67 moment_9203_1934_join72 rfl rfl rfl
private theorem moment_9203_1934_join74 :
    blockEstimate 9203 1934 11790 256 = 726075471136 :=
  block_append moment_9203_1934_part77 moment_9203_1934_part78 rfl rfl rfl
private theorem moment_9203_1934_join75 :
    blockEstimate 9203 1934 12174 256 = 334134222112 :=
  block_append moment_9203_1934_part80 moment_9203_1934_part81 rfl rfl rfl
private theorem moment_9203_1934_join76 :
    blockEstimate 9203 1934 12046 384 = 589487727024 :=
  block_append moment_9203_1934_part79 moment_9203_1934_join75 rfl rfl rfl
private theorem moment_9203_1934_join77 :
    blockEstimate 9203 1934 11790 640 = 1315563198160 :=
  block_append moment_9203_1934_join74 moment_9203_1934_join76 rfl rfl rfl
private theorem moment_9203_1934_join78 :
    blockEstimate 9203 1934 12558 256 = 88652170528 :=
  block_append moment_9203_1934_part83 moment_9203_1934_part84 rfl rfl rfl
private theorem moment_9203_1934_join79 :
    blockEstimate 9203 1934 12430 384 = 183706131888 :=
  block_append moment_9203_1934_part82 moment_9203_1934_join78 rfl rfl rfl
private theorem moment_9203_1934_join80 :
    blockEstimate 9203 1934 12942 129 = 1693183107 :=
  block_append moment_9203_1934_part86 moment_9203_1934_part87 rfl rfl rfl
private theorem moment_9203_1934_join81 :
    blockEstimate 9203 1934 12814 257 = 13074585875 :=
  block_append moment_9203_1934_part85 moment_9203_1934_join80 rfl rfl rfl
private theorem moment_9203_1934_join82 :
    blockEstimate 9203 1934 12430 641 = 196780717763 :=
  block_append moment_9203_1934_join79 moment_9203_1934_join81 rfl rfl rfl
private theorem moment_9203_1934_join83 :
    blockEstimate 9203 1934 11790 1281 = 1512343915923 :=
  block_append moment_9203_1934_join77 moment_9203_1934_join82 rfl rfl rfl
private theorem moment_9203_1934_join84 :
    blockEstimate 9203 1934 10382 2689 = 12824020580669 :=
  block_append moment_9203_1934_join73 moment_9203_1934_join83 rfl rfl rfl
private theorem moment_9203_1934_join85 :
    blockEstimate 9203 1934 7566 5505 = 81726206022297 :=
  block_append moment_9203_1934_join63 moment_9203_1934_join84 rfl rfl rfl
private theorem moment_9203_1934_join86 :
    blockEstimate 9203 1934 1934 11137 = 192177638347017 :=
  block_append moment_9203_1934_join42 moment_9203_1934_join85 rfl rfl rfl

theorem moment_9203_1934 : momentEstimate 9203 1934 = 192177638347017 := moment_9203_1934_join86

private theorem moment_9203_2007_part0 :
    blockEstimate 9203 2007 2007 128 = 3258388640 := by decide +kernel
private theorem moment_9203_2007_part1 :
    blockEstimate 9203 2007 2135 128 = 22236356768 := by decide +kernel
private theorem moment_9203_2007_part2 :
    blockEstimate 9203 2007 2263 128 = 59303309472 := by decide +kernel
private theorem moment_9203_2007_part3 :
    blockEstimate 9203 2007 2391 128 = 113653940384 := by decide +kernel
private theorem moment_9203_2007_part4 :
    blockEstimate 9203 2007 2519 128 = 184482943136 := by decide +kernel
private theorem moment_9203_2007_part5 :
    blockEstimate 9203 2007 2647 128 = 270985011360 := by decide +kernel
private theorem moment_9203_2007_part6 :
    blockEstimate 9203 2007 2775 128 = 372354838688 := by decide +kernel
private theorem moment_9203_2007_part7 :
    blockEstimate 9203 2007 2903 128 = 487787118752 := by decide +kernel
private theorem moment_9203_2007_part8 :
    blockEstimate 9203 2007 3031 128 = 616476545184 := by decide +kernel
private theorem moment_9203_2007_part9 :
    blockEstimate 9203 2007 3159 128 = 757617811616 := by decide +kernel
private theorem moment_9203_2007_part10 :
    blockEstimate 9203 2007 3287 128 = 910405611680 := by decide +kernel
private theorem moment_9203_2007_part11 :
    blockEstimate 9203 2007 3415 128 = 1074034639008 := by decide +kernel
private theorem moment_9203_2007_part12 :
    blockEstimate 9203 2007 3543 128 = 1247699587232 := by decide +kernel
private theorem moment_9203_2007_part13 :
    blockEstimate 9203 2007 3671 128 = 1430595149984 := by decide +kernel
private theorem moment_9203_2007_part14 :
    blockEstimate 9203 2007 3799 128 = 1621916020896 := by decide +kernel
private theorem moment_9203_2007_part15 :
    blockEstimate 9203 2007 3927 128 = 1820774630790 := by decide +kernel
private theorem moment_9203_2007_part16 :
    blockEstimate 9203 2007 4055 128 = 2021007534848 := by decide +kernel
private theorem moment_9203_2007_part17 :
    blockEstimate 9203 2007 4183 128 = 2213615151872 := by decide +kernel
private theorem moment_9203_2007_part18 :
    blockEstimate 9203 2007 4311 128 = 2397800606464 := by decide +kernel
private theorem moment_9203_2007_part19 :
    blockEstimate 9203 2007 4439 128 = 2573563898624 := by decide +kernel
private theorem moment_9203_2007_part20 :
    blockEstimate 9203 2007 4567 128 = 2740905028352 := by decide +kernel
private theorem moment_9203_2007_part21 :
    blockEstimate 9203 2007 4695 128 = 2899823995648 := by decide +kernel
private theorem moment_9203_2007_part22 :
    blockEstimate 9203 2007 4823 128 = 3050320800512 := by decide +kernel
private theorem moment_9203_2007_part23 :
    blockEstimate 9203 2007 4951 128 = 3192395442944 := by decide +kernel
private theorem moment_9203_2007_part24 :
    blockEstimate 9203 2007 5079 128 = 3326047922944 := by decide +kernel
private theorem moment_9203_2007_part25 :
    blockEstimate 9203 2007 5207 128 = 3451278240512 := by decide +kernel
private theorem moment_9203_2007_part26 :
    blockEstimate 9203 2007 5335 128 = 3568086395648 := by decide +kernel
private theorem moment_9203_2007_part27 :
    blockEstimate 9203 2007 5463 128 = 3676472388352 := by decide +kernel
private theorem moment_9203_2007_part28 :
    blockEstimate 9203 2007 5591 128 = 3776436218624 := by decide +kernel
private theorem moment_9203_2007_part29 :
    blockEstimate 9203 2007 5719 128 = 3867977886464 := by decide +kernel
private theorem moment_9203_2007_part30 :
    blockEstimate 9203 2007 5847 128 = 3951097391872 := by decide +kernel
private theorem moment_9203_2007_part31 :
    blockEstimate 9203 2007 5975 128 = 4025794734848 := by decide +kernel
private theorem moment_9203_2007_part32 :
    blockEstimate 9203 2007 6103 128 = 4092069915392 := by decide +kernel
private theorem moment_9203_2007_part33 :
    blockEstimate 9203 2007 6231 128 = 4149922933504 := by decide +kernel
private theorem moment_9203_2007_part34 :
    blockEstimate 9203 2007 6359 128 = 4199353789184 := by decide +kernel
private theorem moment_9203_2007_part35 :
    blockEstimate 9203 2007 6487 128 = 4240362482432 := by decide +kernel
private theorem moment_9203_2007_part36 :
    blockEstimate 9203 2007 6615 128 = 4272949013248 := by decide +kernel
private theorem moment_9203_2007_part37 :
    blockEstimate 9203 2007 6743 128 = 4297113381632 := by decide +kernel
private theorem moment_9203_2007_part38 :
    blockEstimate 9203 2007 6871 128 = 4312855587584 := by decide +kernel
private theorem moment_9203_2007_part39 :
    blockEstimate 9203 2007 6999 128 = 4320175631104 := by decide +kernel
private theorem moment_9203_2007_part40 :
    blockEstimate 9203 2007 7127 128 = 4319073512192 := by decide +kernel
private theorem moment_9203_2007_part41 :
    blockEstimate 9203 2007 7255 128 = 4309549230848 := by decide +kernel
private theorem moment_9203_2007_part42 :
    blockEstimate 9203 2007 7383 128 = 4291602787072 := by decide +kernel
private theorem moment_9203_2007_part43 :
    blockEstimate 9203 2007 7511 128 = 4265234180864 := by decide +kernel
private theorem moment_9203_2007_part44 :
    blockEstimate 9203 2007 7639 128 = 4230443412224 := by decide +kernel
private theorem moment_9203_2007_part45 :
    blockEstimate 9203 2007 7767 128 = 4187230481152 := by decide +kernel
private theorem moment_9203_2007_part46 :
    blockEstimate 9203 2007 7895 128 = 4135595387648 := by decide +kernel
private theorem moment_9203_2007_part47 :
    blockEstimate 9203 2007 8023 128 = 4075538131712 := by decide +kernel
private theorem moment_9203_2007_part48 :
    blockEstimate 9203 2007 8151 128 = 4007058713344 := by decide +kernel
private theorem moment_9203_2007_part49 :
    blockEstimate 9203 2007 8279 128 = 3930157132544 := by decide +kernel
private theorem moment_9203_2007_part50 :
    blockEstimate 9203 2007 8407 128 = 3844833389312 := by decide +kernel
private theorem moment_9203_2007_part51 :
    blockEstimate 9203 2007 8535 128 = 3751087483648 := by decide +kernel
private theorem moment_9203_2007_part52 :
    blockEstimate 9203 2007 8663 128 = 3648919415552 := by decide +kernel
private theorem moment_9203_2007_part53 :
    blockEstimate 9203 2007 8791 128 = 3538329185024 := by decide +kernel
private theorem moment_9203_2007_part54 :
    blockEstimate 9203 2007 8919 128 = 3419316792064 := by decide +kernel
private theorem moment_9203_2007_part55 :
    blockEstimate 9203 2007 9047 128 = 3291882236672 := by decide +kernel
private theorem moment_9203_2007_part56 :
    blockEstimate 9203 2007 9175 128 = 3156473853691 := by decide +kernel
private theorem moment_9203_2007_part57 :
    blockEstimate 9203 2007 9303 128 = 3016710173120 := by decide +kernel
private theorem moment_9203_2007_part58 :
    blockEstimate 9203 2007 9431 128 = 2874719964829 := by decide +kernel
private theorem moment_9203_2007_part59 :
    blockEstimate 9203 2007 9559 128 = 2731093206748 := by decide +kernel
private theorem moment_9203_2007_part60 :
    blockEstimate 9203 2007 9687 128 = 2586398134089 := by decide +kernel
private theorem moment_9203_2007_part61 :
    blockEstimate 9203 2007 9815 128 = 2441190151461 := by decide +kernel
private theorem moment_9203_2007_part62 :
    blockEstimate 9203 2007 9943 128 = 2296011826363 := by decide +kernel
private theorem moment_9203_2007_part63 :
    blockEstimate 9203 2007 10071 128 = 2151392895868 := by decide +kernel
private theorem moment_9203_2007_part64 :
    blockEstimate 9203 2007 10199 128 = 2007850261204 := by decide +kernel
private theorem moment_9203_2007_part65 :
    blockEstimate 9203 2007 10327 128 = 1865887990382 := by decide +kernel
private theorem moment_9203_2007_part66 :
    blockEstimate 9203 2007 10455 128 = 1725997319179 := by decide +kernel
private theorem moment_9203_2007_part67 :
    blockEstimate 9203 2007 10583 128 = 1588656648230 := by decide +kernel
private theorem moment_9203_2007_part68 :
    blockEstimate 9203 2007 10711 128 = 1454331545732 := by decide +kernel
private theorem moment_9203_2007_part69 :
    blockEstimate 9203 2007 10839 128 = 1323474745675 := by decide +kernel
private theorem moment_9203_2007_part70 :
    blockEstimate 9203 2007 10967 128 = 1196526148630 := by decide +kernel
private theorem moment_9203_2007_part71 :
    blockEstimate 9203 2007 11095 128 = 1073901487109 := by decide +kernel
private theorem moment_9203_2007_part72 :
    blockEstimate 9203 2007 11223 128 = 954965204496 := by decide +kernel
private theorem moment_9203_2007_part73 :
    blockEstimate 9203 2007 11351 128 = 840956924432 := by decide +kernel
private theorem moment_9203_2007_part74 :
    blockEstimate 9203 2007 11479 128 = 733054305808 := by decide +kernel
private theorem moment_9203_2007_part75 :
    blockEstimate 9203 2007 11607 128 = 631509006864 := by decide +kernel
private theorem moment_9203_2007_part76 :
    blockEstimate 9203 2007 11735 128 = 536572685840 := by decide +kernel
private theorem moment_9203_2007_part77 :
    blockEstimate 9203 2007 11863 128 = 448497000976 := by decide +kernel
private theorem moment_9203_2007_part78 :
    blockEstimate 9203 2007 11991 128 = 367533610512 := by decide +kernel
private theorem moment_9203_2007_part79 :
    blockEstimate 9203 2007 12119 128 = 293934172688 := by decide +kernel
private theorem moment_9203_2007_part80 :
    blockEstimate 9203 2007 12247 128 = 227950345744 := by decide +kernel
private theorem moment_9203_2007_part81 :
    blockEstimate 9203 2007 12375 128 = 169833787920 := by decide +kernel
private theorem moment_9203_2007_part82 :
    blockEstimate 9203 2007 12503 128 = 119836157456 := by decide +kernel
private theorem moment_9203_2007_part83 :
    blockEstimate 9203 2007 12631 128 = 78209112592 := by decide +kernel
private theorem moment_9203_2007_part84 :
    blockEstimate 9203 2007 12759 128 = 45204311568 := by decide +kernel
private theorem moment_9203_2007_part85 :
    blockEstimate 9203 2007 12887 128 = 21073412624 := by decide +kernel
private theorem moment_9203_2007_part86 :
    blockEstimate 9203 2007 13015 128 = 6068074000 := by decide +kernel
private theorem moment_9203_2007_part87 :
    blockEstimate 9203 2007 13143 74 = 328735283 := by decide +kernel
private theorem moment_9203_2007_join0 :
    blockEstimate 9203 2007 2007 256 = 25494745408 :=
  block_append moment_9203_2007_part0 moment_9203_2007_part1 rfl rfl rfl
private theorem moment_9203_2007_join1 :
    blockEstimate 9203 2007 2391 256 = 298136883520 :=
  block_append moment_9203_2007_part3 moment_9203_2007_part4 rfl rfl rfl
private theorem moment_9203_2007_join2 :
    blockEstimate 9203 2007 2263 384 = 357440192992 :=
  block_append moment_9203_2007_part2 moment_9203_2007_join1 rfl rfl rfl
private theorem moment_9203_2007_join3 :
    blockEstimate 9203 2007 2007 640 = 382934938400 :=
  block_append moment_9203_2007_join0 moment_9203_2007_join2 rfl rfl rfl
private theorem moment_9203_2007_join4 :
    blockEstimate 9203 2007 2775 256 = 860141957440 :=
  block_append moment_9203_2007_part6 moment_9203_2007_part7 rfl rfl rfl
private theorem moment_9203_2007_join5 :
    blockEstimate 9203 2007 2647 384 = 1131126968800 :=
  block_append moment_9203_2007_part5 moment_9203_2007_join4 rfl rfl rfl
private theorem moment_9203_2007_join6 :
    blockEstimate 9203 2007 3159 256 = 1668023423296 :=
  block_append moment_9203_2007_part9 moment_9203_2007_part10 rfl rfl rfl
private theorem moment_9203_2007_join7 :
    blockEstimate 9203 2007 3031 384 = 2284499968480 :=
  block_append moment_9203_2007_part8 moment_9203_2007_join6 rfl rfl rfl
private theorem moment_9203_2007_join8 :
    blockEstimate 9203 2007 2647 768 = 3415626937280 :=
  block_append moment_9203_2007_join5 moment_9203_2007_join7 rfl rfl rfl
private theorem moment_9203_2007_join9 :
    blockEstimate 9203 2007 2007 1408 = 3798561875680 :=
  block_append moment_9203_2007_join3 moment_9203_2007_join8 rfl rfl rfl
private theorem moment_9203_2007_join10 :
    blockEstimate 9203 2007 3415 256 = 2321734226240 :=
  block_append moment_9203_2007_part11 moment_9203_2007_part12 rfl rfl rfl
private theorem moment_9203_2007_join11 :
    blockEstimate 9203 2007 3799 256 = 3442690651686 :=
  block_append moment_9203_2007_part14 moment_9203_2007_part15 rfl rfl rfl
private theorem moment_9203_2007_join12 :
    blockEstimate 9203 2007 3671 384 = 4873285801670 :=
  block_append moment_9203_2007_part13 moment_9203_2007_join11 rfl rfl rfl
private theorem moment_9203_2007_join13 :
    blockEstimate 9203 2007 3415 640 = 7195020027910 :=
  block_append moment_9203_2007_join10 moment_9203_2007_join12 rfl rfl rfl
private theorem moment_9203_2007_join14 :
    blockEstimate 9203 2007 4183 256 = 4611415758336 :=
  block_append moment_9203_2007_part17 moment_9203_2007_part18 rfl rfl rfl
private theorem moment_9203_2007_join15 :
    blockEstimate 9203 2007 4055 384 = 6632423293184 :=
  block_append moment_9203_2007_part16 moment_9203_2007_join14 rfl rfl rfl
private theorem moment_9203_2007_join16 :
    blockEstimate 9203 2007 4567 256 = 5640729024000 :=
  block_append moment_9203_2007_part20 moment_9203_2007_part21 rfl rfl rfl
private theorem moment_9203_2007_join17 :
    blockEstimate 9203 2007 4439 384 = 8214292922624 :=
  block_append moment_9203_2007_part19 moment_9203_2007_join16 rfl rfl rfl
private theorem moment_9203_2007_join18 :
    blockEstimate 9203 2007 4055 768 = 14846716215808 :=
  block_append moment_9203_2007_join15 moment_9203_2007_join17 rfl rfl rfl
private theorem moment_9203_2007_join19 :
    blockEstimate 9203 2007 3415 1408 = 22041736243718 :=
  block_append moment_9203_2007_join13 moment_9203_2007_join18 rfl rfl rfl
private theorem moment_9203_2007_join20 :
    blockEstimate 9203 2007 2007 2816 = 25840298119398 :=
  block_append moment_9203_2007_join9 moment_9203_2007_join19 rfl rfl rfl
private theorem moment_9203_2007_join21 :
    blockEstimate 9203 2007 4823 256 = 6242716243456 :=
  block_append moment_9203_2007_part22 moment_9203_2007_part23 rfl rfl rfl
private theorem moment_9203_2007_join22 :
    blockEstimate 9203 2007 5207 256 = 7019364636160 :=
  block_append moment_9203_2007_part25 moment_9203_2007_part26 rfl rfl rfl
private theorem moment_9203_2007_join23 :
    blockEstimate 9203 2007 5079 384 = 10345412559104 :=
  block_append moment_9203_2007_part24 moment_9203_2007_join22 rfl rfl rfl
private theorem moment_9203_2007_join24 :
    blockEstimate 9203 2007 4823 640 = 16588128802560 :=
  block_append moment_9203_2007_join21 moment_9203_2007_join23 rfl rfl rfl
private theorem moment_9203_2007_join25 :
    blockEstimate 9203 2007 5591 256 = 7644414105088 :=
  block_append moment_9203_2007_part28 moment_9203_2007_part29 rfl rfl rfl
private theorem moment_9203_2007_join26 :
    blockEstimate 9203 2007 5463 384 = 11320886493440 :=
  block_append moment_9203_2007_part27 moment_9203_2007_join25 rfl rfl rfl
private theorem moment_9203_2007_join27 :
    blockEstimate 9203 2007 5975 256 = 8117864650240 :=
  block_append moment_9203_2007_part31 moment_9203_2007_part32 rfl rfl rfl
private theorem moment_9203_2007_join28 :
    blockEstimate 9203 2007 5847 384 = 12068962042112 :=
  block_append moment_9203_2007_part30 moment_9203_2007_join27 rfl rfl rfl
private theorem moment_9203_2007_join29 :
    blockEstimate 9203 2007 5463 768 = 23389848535552 :=
  block_append moment_9203_2007_join26 moment_9203_2007_join28 rfl rfl rfl
private theorem moment_9203_2007_join30 :
    blockEstimate 9203 2007 4823 1408 = 39977977338112 :=
  block_append moment_9203_2007_join24 moment_9203_2007_join29 rfl rfl rfl
private theorem moment_9203_2007_join31 :
    blockEstimate 9203 2007 6231 256 = 8349276722688 :=
  block_append moment_9203_2007_part33 moment_9203_2007_part34 rfl rfl rfl
private theorem moment_9203_2007_join32 :
    blockEstimate 9203 2007 6615 256 = 8570062394880 :=
  block_append moment_9203_2007_part36 moment_9203_2007_part37 rfl rfl rfl
private theorem moment_9203_2007_join33 :
    blockEstimate 9203 2007 6487 384 = 12810424877312 :=
  block_append moment_9203_2007_part35 moment_9203_2007_join32 rfl rfl rfl
private theorem moment_9203_2007_join34 :
    blockEstimate 9203 2007 6231 640 = 21159701600000 :=
  block_append moment_9203_2007_join31 moment_9203_2007_join33 rfl rfl rfl
private theorem moment_9203_2007_join35 :
    blockEstimate 9203 2007 6999 256 = 8639249143296 :=
  block_append moment_9203_2007_part39 moment_9203_2007_part40 rfl rfl rfl
private theorem moment_9203_2007_join36 :
    blockEstimate 9203 2007 6871 384 = 12952104730880 :=
  block_append moment_9203_2007_part38 moment_9203_2007_join35 rfl rfl rfl
private theorem moment_9203_2007_join37 :
    blockEstimate 9203 2007 7383 256 = 8556836967936 :=
  block_append moment_9203_2007_part42 moment_9203_2007_part43 rfl rfl rfl
private theorem moment_9203_2007_join38 :
    blockEstimate 9203 2007 7255 384 = 12866386198784 :=
  block_append moment_9203_2007_part41 moment_9203_2007_join37 rfl rfl rfl
private theorem moment_9203_2007_join39 :
    blockEstimate 9203 2007 6871 768 = 25818490929664 :=
  block_append moment_9203_2007_join36 moment_9203_2007_join38 rfl rfl rfl
private theorem moment_9203_2007_join40 :
    blockEstimate 9203 2007 6231 1408 = 46978192529664 :=
  block_append moment_9203_2007_join34 moment_9203_2007_join39 rfl rfl rfl
private theorem moment_9203_2007_join41 :
    blockEstimate 9203 2007 4823 2816 = 86956169867776 :=
  block_append moment_9203_2007_join30 moment_9203_2007_join40 rfl rfl rfl
private theorem moment_9203_2007_join42 :
    blockEstimate 9203 2007 2007 5632 = 112796467987174 :=
  block_append moment_9203_2007_join20 moment_9203_2007_join41 rfl rfl rfl
private theorem moment_9203_2007_join43 :
    blockEstimate 9203 2007 7639 256 = 8417673893376 :=
  block_append moment_9203_2007_part44 moment_9203_2007_part45 rfl rfl rfl
private theorem moment_9203_2007_join44 :
    blockEstimate 9203 2007 8023 256 = 8082596845056 :=
  block_append moment_9203_2007_part47 moment_9203_2007_part48 rfl rfl rfl
private theorem moment_9203_2007_join45 :
    blockEstimate 9203 2007 7895 384 = 12218192232704 :=
  block_append moment_9203_2007_part46 moment_9203_2007_join44 rfl rfl rfl
private theorem moment_9203_2007_join46 :
    blockEstimate 9203 2007 7639 640 = 20635866126080 :=
  block_append moment_9203_2007_join43 moment_9203_2007_join45 rfl rfl rfl
private theorem moment_9203_2007_join47 :
    blockEstimate 9203 2007 8407 256 = 7595920872960 :=
  block_append moment_9203_2007_part50 moment_9203_2007_part51 rfl rfl rfl
private theorem moment_9203_2007_join48 :
    blockEstimate 9203 2007 8279 384 = 11526078005504 :=
  block_append moment_9203_2007_part49 moment_9203_2007_join47 rfl rfl rfl
private theorem moment_9203_2007_join49 :
    blockEstimate 9203 2007 8791 256 = 6957645977088 :=
  block_append moment_9203_2007_part53 moment_9203_2007_part54 rfl rfl rfl
private theorem moment_9203_2007_join50 :
    blockEstimate 9203 2007 8663 384 = 10606565392640 :=
  block_append moment_9203_2007_part52 moment_9203_2007_join49 rfl rfl rfl
private theorem moment_9203_2007_join51 :
    blockEstimate 9203 2007 8279 768 = 22132643398144 :=
  block_append moment_9203_2007_join48 moment_9203_2007_join50 rfl rfl rfl
private theorem moment_9203_2007_join52 :
    blockEstimate 9203 2007 7639 1408 = 42768509524224 :=
  block_append moment_9203_2007_join46 moment_9203_2007_join51 rfl rfl rfl
private theorem moment_9203_2007_join53 :
    blockEstimate 9203 2007 9047 256 = 6448356090363 :=
  block_append moment_9203_2007_part55 moment_9203_2007_part56 rfl rfl rfl
private theorem moment_9203_2007_join54 :
    blockEstimate 9203 2007 9431 256 = 5605813171577 :=
  block_append moment_9203_2007_part58 moment_9203_2007_part59 rfl rfl rfl
private theorem moment_9203_2007_join55 :
    blockEstimate 9203 2007 9303 384 = 8622523344697 :=
  block_append moment_9203_2007_part57 moment_9203_2007_join54 rfl rfl rfl
private theorem moment_9203_2007_join56 :
    blockEstimate 9203 2007 9047 640 = 15070879435060 :=
  block_append moment_9203_2007_join53 moment_9203_2007_join55 rfl rfl rfl
private theorem moment_9203_2007_join57 :
    blockEstimate 9203 2007 9815 256 = 4737201977824 :=
  block_append moment_9203_2007_part61 moment_9203_2007_part62 rfl rfl rfl
private theorem moment_9203_2007_join58 :
    blockEstimate 9203 2007 9687 384 = 7323600111913 :=
  block_append moment_9203_2007_part60 moment_9203_2007_join57 rfl rfl rfl
private theorem moment_9203_2007_join59 :
    blockEstimate 9203 2007 10199 256 = 3873738251586 :=
  block_append moment_9203_2007_part64 moment_9203_2007_part65 rfl rfl rfl
private theorem moment_9203_2007_join60 :
    blockEstimate 9203 2007 10071 384 = 6025131147454 :=
  block_append moment_9203_2007_part63 moment_9203_2007_join59 rfl rfl rfl
private theorem moment_9203_2007_join61 :
    blockEstimate 9203 2007 9687 768 = 13348731259367 :=
  block_append moment_9203_2007_join58 moment_9203_2007_join60 rfl rfl rfl
private theorem moment_9203_2007_join62 :
    blockEstimate 9203 2007 9047 1408 = 28419610694427 :=
  block_append moment_9203_2007_join56 moment_9203_2007_join61 rfl rfl rfl
private theorem moment_9203_2007_join63 :
    blockEstimate 9203 2007 7639 2816 = 71188120218651 :=
  block_append moment_9203_2007_join52 moment_9203_2007_join62 rfl rfl rfl
private theorem moment_9203_2007_join64 :
    blockEstimate 9203 2007 10455 256 = 3314653967409 :=
  block_append moment_9203_2007_part66 moment_9203_2007_part67 rfl rfl rfl
private theorem moment_9203_2007_join65 :
    blockEstimate 9203 2007 10839 256 = 2520000894305 :=
  block_append moment_9203_2007_part69 moment_9203_2007_part70 rfl rfl rfl
private theorem moment_9203_2007_join66 :
    blockEstimate 9203 2007 10711 384 = 3974332440037 :=
  block_append moment_9203_2007_part68 moment_9203_2007_join65 rfl rfl rfl
private theorem moment_9203_2007_join67 :
    blockEstimate 9203 2007 10455 640 = 7288986407446 :=
  block_append moment_9203_2007_join64 moment_9203_2007_join66 rfl rfl rfl
private theorem moment_9203_2007_join68 :
    blockEstimate 9203 2007 11223 256 = 1795922128928 :=
  block_append moment_9203_2007_part72 moment_9203_2007_part73 rfl rfl rfl
private theorem moment_9203_2007_join69 :
    blockEstimate 9203 2007 11095 384 = 2869823616037 :=
  block_append moment_9203_2007_part71 moment_9203_2007_join68 rfl rfl rfl
private theorem moment_9203_2007_join70 :
    blockEstimate 9203 2007 11607 256 = 1168081692704 :=
  block_append moment_9203_2007_part75 moment_9203_2007_part76 rfl rfl rfl
private theorem moment_9203_2007_join71 :
    blockEstimate 9203 2007 11479 384 = 1901135998512 :=
  block_append moment_9203_2007_part74 moment_9203_2007_join70 rfl rfl rfl
private theorem moment_9203_2007_join72 :
    blockEstimate 9203 2007 11095 768 = 4770959614549 :=
  block_append moment_9203_2007_join69 moment_9203_2007_join71 rfl rfl rfl
private theorem moment_9203_2007_join73 :
    blockEstimate 9203 2007 10455 1408 = 12059946021995 :=
  block_append moment_9203_2007_join67 moment_9203_2007_join72 rfl rfl rfl
private theorem moment_9203_2007_join74 :
    blockEstimate 9203 2007 11863 256 = 816030611488 :=
  block_append moment_9203_2007_part77 moment_9203_2007_part78 rfl rfl rfl
private theorem moment_9203_2007_join75 :
    blockEstimate 9203 2007 12247 256 = 397784133664 :=
  block_append moment_9203_2007_part80 moment_9203_2007_part81 rfl rfl rfl
private theorem moment_9203_2007_join76 :
    blockEstimate 9203 2007 12119 384 = 691718306352 :=
  block_append moment_9203_2007_part79 moment_9203_2007_join75 rfl rfl rfl
private theorem moment_9203_2007_join77 :
    blockEstimate 9203 2007 11863 640 = 1507748917840 :=
  block_append moment_9203_2007_join74 moment_9203_2007_join76 rfl rfl rfl
private theorem moment_9203_2007_join78 :
    blockEstimate 9203 2007 12631 256 = 123413424160 :=
  block_append moment_9203_2007_part83 moment_9203_2007_part84 rfl rfl rfl
private theorem moment_9203_2007_join79 :
    blockEstimate 9203 2007 12503 384 = 243249581616 :=
  block_append moment_9203_2007_part82 moment_9203_2007_join78 rfl rfl rfl
private theorem moment_9203_2007_join80 :
    blockEstimate 9203 2007 13015 202 = 6396809283 :=
  block_append moment_9203_2007_part86 moment_9203_2007_part87 rfl rfl rfl
private theorem moment_9203_2007_join81 :
    blockEstimate 9203 2007 12887 330 = 27470221907 :=
  block_append moment_9203_2007_part85 moment_9203_2007_join80 rfl rfl rfl
private theorem moment_9203_2007_join82 :
    blockEstimate 9203 2007 12503 714 = 270719803523 :=
  block_append moment_9203_2007_join79 moment_9203_2007_join81 rfl rfl rfl
private theorem moment_9203_2007_join83 :
    blockEstimate 9203 2007 11863 1354 = 1778468721363 :=
  block_append moment_9203_2007_join77 moment_9203_2007_join82 rfl rfl rfl
private theorem moment_9203_2007_join84 :
    blockEstimate 9203 2007 10455 2762 = 13838414743358 :=
  block_append moment_9203_2007_join73 moment_9203_2007_join83 rfl rfl rfl
private theorem moment_9203_2007_join85 :
    blockEstimate 9203 2007 7639 5578 = 85026534962009 :=
  block_append moment_9203_2007_join63 moment_9203_2007_join84 rfl rfl rfl
private theorem moment_9203_2007_join86 :
    blockEstimate 9203 2007 2007 11210 = 197823002949183 :=
  block_append moment_9203_2007_join42 moment_9203_2007_join85 rfl rfl rfl

theorem moment_9203_2007 : momentEstimate 9203 2007 = 197823002949183 := moment_9203_2007_join86

private theorem receipt_0_13_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 0 128 = 21563985072628579927393483200 := by decide +kernel
private theorem receipt_0_13_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 128 128 = 18720667898534456938888436160 := by decide +kernel
private theorem receipt_0_13_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 256 128 = 16010638009381444968835807680 := by decide +kernel
private theorem receipt_0_13_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 384 128 = 13430675138186218890234878400 := by decide +kernel
private theorem receipt_0_13_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 512 128 = 10977566900393470776208013760 := by decide +kernel
private theorem receipt_0_13_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 640 128 = 8648108787597082778888149440 := by decide +kernel
private theorem receipt_0_13_2339_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 768 128 = 6439104862707844204113120342 := by decide +kernel
private theorem receipt_0_13_2339_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 896 128 = 4347370406420599644957892608 := by decide +kernel
private theorem receipt_0_13_2339_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 1024 128 = 2369718964630508532240826482 := by decide +kernel
private theorem receipt_0_13_2339_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 1152 99 = 546940996810341822414650070 := by decide +kernel
private theorem receipt_0_13_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 0 256 = 40284652971163036866281919360 :=
  phaseBlock_append receipt_0_13_2339_0_part0 receipt_0_13_2339_0_part1 rfl rfl rfl
private theorem receipt_0_13_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 384 256 = 24408242038579689666442892160 :=
  phaseBlock_append receipt_0_13_2339_0_part3 receipt_0_13_2339_0_part4 rfl rfl rfl
private theorem receipt_0_13_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 256 384 = 40418880047961134635278699840 :=
  phaseBlock_append receipt_0_13_2339_0_part2 receipt_0_13_2339_0_join1 rfl rfl rfl
private theorem receipt_0_13_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 0 640 = 80703533019124171501560619200 :=
  phaseBlock_append receipt_0_13_2339_0_join0 receipt_0_13_2339_0_join2 rfl rfl rfl
private theorem receipt_0_13_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 640 256 = 15087213650304926983001269782 :=
  phaseBlock_append receipt_0_13_2339_0_part5 receipt_0_13_2339_0_part6 rfl rfl rfl
private theorem receipt_0_13_2339_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 1024 227 = 2916659961440850354655476552 :=
  phaseBlock_append receipt_0_13_2339_0_part8 receipt_0_13_2339_0_part9 rfl rfl rfl
private theorem receipt_0_13_2339_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 896 355 = 7264030367861449999613369160 :=
  phaseBlock_append receipt_0_13_2339_0_part7 receipt_0_13_2339_0_join5 rfl rfl rfl
private theorem receipt_0_13_2339_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 640 611 = 22351244018166376982614638942 :=
  phaseBlock_append receipt_0_13_2339_0_join4 receipt_0_13_2339_0_join6 rfl rfl rfl
private theorem receipt_0_13_2339_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 0) 0 1251 = 103054777037290548484175258142 :=
  phaseBlock_append receipt_0_13_2339_0_join3 receipt_0_13_2339_0_join7 rfl rfl rfl

private theorem receipt_0_13_2339_0 : fastPhase (bank 0 13).shape 179827 2339 44 1 0 1 0 = 103054777037290548484175258142 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2339_0_join8

private theorem receipt_0_13_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 0 128 = 21541538353967797782924409728 := by decide +kernel
private theorem receipt_0_13_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 128 128 = 18699240223016769818252376960 := by decide +kernel
private theorem receipt_0_13_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 256 128 = 15990204992793764845242039168 := by decide +kernel
private theorem receipt_0_13_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 384 128 = 13411212456417043360553040768 := by decide +kernel
private theorem receipt_0_13_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 512 128 = 10959050289384794133220932480 := by decide +kernel
private theorem receipt_0_13_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 640 128 = 8630514043296307083544656768 := by decide +kernel
private theorem receipt_0_13_2339_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 768 128 = 6422407839162005790209642643 := by decide +kernel
private theorem receipt_0_13_2339_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 896 128 = 4331547000735355650337632084 := by decide +kernel
private theorem receipt_0_13_2339_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 1024 128 = 2354745125091854343813740718 := by decide +kernel
private theorem receipt_0_13_2339_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 1152 99 = 535927104885295928491914840 := by decide +kernel
private theorem receipt_0_13_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 0 256 = 40240778576984567601176786688 :=
  phaseBlock_append receipt_0_13_2339_1_part0 receipt_0_13_2339_1_part1 rfl rfl rfl
private theorem receipt_0_13_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 384 256 = 24370262745801837493773973248 :=
  phaseBlock_append receipt_0_13_2339_1_part3 receipt_0_13_2339_1_part4 rfl rfl rfl
private theorem receipt_0_13_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 256 384 = 40360467738595602339016012416 :=
  phaseBlock_append receipt_0_13_2339_1_part2 receipt_0_13_2339_1_join1 rfl rfl rfl
private theorem receipt_0_13_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 0 640 = 80601246315580169940192799104 :=
  phaseBlock_append receipt_0_13_2339_1_join0 receipt_0_13_2339_1_join2 rfl rfl rfl
private theorem receipt_0_13_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 640 256 = 15052921882458312873754299411 :=
  phaseBlock_append receipt_0_13_2339_1_part5 receipt_0_13_2339_1_part6 rfl rfl rfl
private theorem receipt_0_13_2339_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 1024 227 = 2890672229977150272305655558 :=
  phaseBlock_append receipt_0_13_2339_1_part8 receipt_0_13_2339_1_part9 rfl rfl rfl
private theorem receipt_0_13_2339_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 896 355 = 7222219230712505922643287642 :=
  phaseBlock_append receipt_0_13_2339_1_part7 receipt_0_13_2339_1_join5 rfl rfl rfl
private theorem receipt_0_13_2339_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 640 611 = 22275141113170818796397587053 :=
  phaseBlock_append receipt_0_13_2339_1_join4 receipt_0_13_2339_1_join6 rfl rfl rfl
private theorem receipt_0_13_2339_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2339 44 1 0 1 1) 0 1251 = 102876387428750988736590386157 :=
  phaseBlock_append receipt_0_13_2339_1_join3 receipt_0_13_2339_1_join7 rfl rfl rfl

private theorem receipt_0_13_2339_1 : fastPhase (bank 0 13).shape 179827 2339 44 1 0 1 1 = 102876387428750988736590386157 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2339_1_join8

private theorem receipt_0_13_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 0 128 = 21564177171168869678085095808 := by decide +kernel
private theorem receipt_0_13_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 128 128 = 18720824932694028250268410240 := by decide +kernel
private theorem receipt_0_13_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 256 128 = 16010763719951134827434901888 := by decide +kernel
private theorem receipt_0_13_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 384 128 = 13430773154861062855276323200 := by decide +kernel
private theorem receipt_0_13_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 512 128 = 10977640742047696781949026688 := by decide +kernel
private theorem receipt_0_13_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 640 128 = 8648161862558885034635895168 := by decide +kernel
private theorem receipt_0_13_2340_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 768 128 = 6439140449198581068263410774 := by decide +kernel
private theorem receipt_0_13_2340_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 896 128 = 4347391668507492241320146879 := by decide +kernel
private theorem receipt_0_13_2340_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 1024 128 = 2369729027934448114292955514 := by decide +kernel
private theorem receipt_0_13_2340_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 1152 99 = 546943011716170677632480355 := by decide +kernel
private theorem receipt_0_13_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 0 256 = 40285002103862897928353506048 :=
  phaseBlock_append receipt_0_13_2340_0_part0 receipt_0_13_2340_0_part1 rfl rfl rfl
private theorem receipt_0_13_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 384 256 = 24408413896908759637225349888 :=
  phaseBlock_append receipt_0_13_2340_0_part3 receipt_0_13_2340_0_part4 rfl rfl rfl
private theorem receipt_0_13_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 256 384 = 40419177616859894464660251776 :=
  phaseBlock_append receipt_0_13_2340_0_part2 receipt_0_13_2340_0_join1 rfl rfl rfl
private theorem receipt_0_13_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 0 640 = 80704179720722792393013757824 :=
  phaseBlock_append receipt_0_13_2340_0_join0 receipt_0_13_2340_0_join2 rfl rfl rfl
private theorem receipt_0_13_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 640 256 = 15087302311757466102899305942 :=
  phaseBlock_append receipt_0_13_2340_0_part5 receipt_0_13_2340_0_part6 rfl rfl rfl
private theorem receipt_0_13_2340_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 1024 227 = 2916672039650618791925435869 :=
  phaseBlock_append receipt_0_13_2340_0_part8 receipt_0_13_2340_0_part9 rfl rfl rfl
private theorem receipt_0_13_2340_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 896 355 = 7264063708158111033245582748 :=
  phaseBlock_append receipt_0_13_2340_0_part7 receipt_0_13_2340_0_join5 rfl rfl rfl
private theorem receipt_0_13_2340_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 640 611 = 22351366019915577136144888690 :=
  phaseBlock_append receipt_0_13_2340_0_join4 receipt_0_13_2340_0_join6 rfl rfl rfl
private theorem receipt_0_13_2340_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 0) 0 1251 = 103055545740638369529158646514 :=
  phaseBlock_append receipt_0_13_2340_0_join3 receipt_0_13_2340_0_join7 rfl rfl rfl

private theorem receipt_0_13_2340_0 : fastPhase (bank 0 13).shape 179827 2340 44 1 0 1 0 = 103055545740638369529158646514 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2340_0_join8

private theorem receipt_0_13_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 0 128 = 21541730288445478837261135488 := by decide +kernel
private theorem receipt_0_13_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 128 128 = 18699397107906773059493023360 := by decide +kernel
private theorem receipt_0_13_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 256 128 = 15990330568361956178911833728 := by decide +kernel
private theorem receipt_0_13_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 384 128 = 13411310351834993403063078528 := by decide +kernel
private theorem receipt_0_13_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 512 128 = 10959124023004770708539633280 := by decide +kernel
private theorem receipt_0_13_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 640 128 = 8630567022926047817543667328 := by decide +kernel
private theorem receipt_0_13_2340_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 768 128 = 6422443342555270211518176492 := by decide +kernel
private theorem receipt_0_13_2340_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 896 128 = 4331568191563993243868252960 := by decide +kernel
private theorem receipt_0_13_2340_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 1024 128 = 2354755128440575691435411145 := by decide +kernel
private theorem receipt_0_13_2340_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 1152 99 = 535929080830425824217801942 := by decide +kernel
private theorem receipt_0_13_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 0 256 = 40241127396352251896754158848 :=
  phaseBlock_append receipt_0_13_2340_1_part0 receipt_0_13_2340_1_part1 rfl rfl rfl
private theorem receipt_0_13_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 384 256 = 24370434374839764111602711808 :=
  phaseBlock_append receipt_0_13_2340_1_part3 receipt_0_13_2340_1_part4 rfl rfl rfl
private theorem receipt_0_13_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 256 384 = 40360764943201720290514545536 :=
  phaseBlock_append receipt_0_13_2340_1_part2 receipt_0_13_2340_1_join1 rfl rfl rfl
private theorem receipt_0_13_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 0 640 = 80601892339553972187268704384 :=
  phaseBlock_append receipt_0_13_2340_1_join0 receipt_0_13_2340_1_join2 rfl rfl rfl
private theorem receipt_0_13_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 640 256 = 15053010365481318029061843820 :=
  phaseBlock_append receipt_0_13_2340_1_part5 receipt_0_13_2340_1_part6 rfl rfl rfl
private theorem receipt_0_13_2340_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 1024 227 = 2890684209271001515653213087 :=
  phaseBlock_append receipt_0_13_2340_1_part8 receipt_0_13_2340_1_part9 rfl rfl rfl
private theorem receipt_0_13_2340_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 896 355 = 7222252400834994759521466047 :=
  phaseBlock_append receipt_0_13_2340_1_part7 receipt_0_13_2340_1_join5 rfl rfl rfl
private theorem receipt_0_13_2340_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 640 611 = 22275262766316312788583309867 :=
  phaseBlock_append receipt_0_13_2340_1_join4 receipt_0_13_2340_1_join6 rfl rfl rfl
private theorem receipt_0_13_2340_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179827 2340 44 1 0 1 1) 0 1251 = 102877155105870284975852014251 :=
  phaseBlock_append receipt_0_13_2340_1_join3 receipt_0_13_2340_1_join7 rfl rfl rfl

private theorem receipt_0_13_2340_1 : fastPhase (bank 0 13).shape 179827 2340 44 1 0 1 1 = 102877155105870284975852014251 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2340_1_join8

theorem receipt_0_13 : Checked (bank 0 13) 44 0 1 := by
  refine checked_from_values (bank 0 13) 44 0 1
    (P3_7_1.checked (bank 0 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_13_2339_0 receipt_0_13_2339_1 receipt_0_13_2340_0 receipt_0_13_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_13_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 0 128 = 19411017083763549805379668800 := by decide +kernel
private theorem receipt_1_13_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 128 128 = 16839452809440054536849746752 := by decide +kernel
private theorem receipt_1_13_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 256 128 = 14391379285067004998116150080 := by decide +kernel
private theorem receipt_1_13_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 384 128 = 12063646198973001375832648512 := by decide +kernel
private theorem receipt_1_13_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 512 128 = 9853118524048166206996859712 := by decide +kernel
private theorem receipt_1_13_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 640 128 = 7756676492628835894500191040 := by decide +kernel
private theorem receipt_1_13_2339_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 768 128 = 5771216199917562331006114335 := by decide +kernel
private theorem receipt_1_13_2339_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 896 128 = 3893651952741782559456433432 := by decide +kernel
private theorem receipt_1_13_2339_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 1024 128 = 2120904647554306412707490135 := by decide +kernel
private theorem receipt_1_13_2339_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 1152 99 = 489220099458474179821008210 := by decide +kernel
private theorem receipt_1_13_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 0 256 = 36250469893203604342229415552 :=
  phaseBlock_append receipt_1_13_2339_0_part0 receipt_1_13_2339_0_part1 rfl rfl rfl
private theorem receipt_1_13_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 384 256 = 21916764723021167582829508224 :=
  phaseBlock_append receipt_1_13_2339_0_part3 receipt_1_13_2339_0_part4 rfl rfl rfl
private theorem receipt_1_13_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 256 384 = 36308144008088172580945658304 :=
  phaseBlock_append receipt_1_13_2339_0_part2 receipt_1_13_2339_0_join1 rfl rfl rfl
private theorem receipt_1_13_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 0 640 = 72558613901291776923175073856 :=
  phaseBlock_append receipt_1_13_2339_0_join0 receipt_1_13_2339_0_join2 rfl rfl rfl
private theorem receipt_1_13_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 640 256 = 13527892692546398225506305375 :=
  phaseBlock_append receipt_1_13_2339_0_part5 receipt_1_13_2339_0_part6 rfl rfl rfl
private theorem receipt_1_13_2339_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 1024 227 = 2610124747012780592528498345 :=
  phaseBlock_append receipt_1_13_2339_0_part8 receipt_1_13_2339_0_part9 rfl rfl rfl
private theorem receipt_1_13_2339_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 896 355 = 6503776699754563151984931777 :=
  phaseBlock_append receipt_1_13_2339_0_part7 receipt_1_13_2339_0_join5 rfl rfl rfl
private theorem receipt_1_13_2339_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 640 611 = 20031669392300961377491237152 :=
  phaseBlock_append receipt_1_13_2339_0_join4 receipt_1_13_2339_0_join6 rfl rfl rfl
private theorem receipt_1_13_2339_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 0) 0 1251 = 92590283293592738300666311008 :=
  phaseBlock_append receipt_1_13_2339_0_join3 receipt_1_13_2339_0_join7 rfl rfl rfl

private theorem receipt_1_13_2339_0 : fastPhase (bank 1 13).shape 179827 2339 44 1 0 2 0 = 92590283293592738300666311008 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2339_0_join8

private theorem receipt_1_13_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 0 128 = 19390702455240694410879870848 := by decide +kernel
private theorem receipt_1_13_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 128 128 = 16820083741398706975177467776 := by decide +kernel
private theorem receipt_1_13_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 256 128 = 14372931874735336082686748544 := by decide +kernel
private theorem receipt_1_13_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 384 128 = 12046096660189294167516768128 := by decide +kernel
private theorem receipt_1_13_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 512 128 = 9836443187068460303131715456 := by decide +kernel
private theorem receipt_1_13_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 640 128 = 7740851803934571717900855168 := by decide +kernel
private theorem receipt_1_13_2339_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 768 128 = 5756218720355093768856312614 := by decide +kernel
private theorem receipt_1_13_2339_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 896 128 = 3879458343890426351061862314 := by decide +kernel
private theorem receipt_1_13_2339_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 1024 128 = 2107491678936282355403016699 := by decide +kernel
private theorem receipt_1_13_2339_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 1152 99 = 479366726794488668054153460 := by decide +kernel
private theorem receipt_1_13_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 0 256 = 36210786196639401386057338624 :=
  phaseBlock_append receipt_1_13_2339_1_part0 receipt_1_13_2339_1_part1 rfl rfl rfl
private theorem receipt_1_13_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 384 256 = 21882539847257754470648483584 :=
  phaseBlock_append receipt_1_13_2339_1_part3 receipt_1_13_2339_1_part4 rfl rfl rfl
private theorem receipt_1_13_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 256 384 = 36255471721993090553335232128 :=
  phaseBlock_append receipt_1_13_2339_1_part2 receipt_1_13_2339_1_join1 rfl rfl rfl
private theorem receipt_1_13_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 0 640 = 72466257918632491939392570752 :=
  phaseBlock_append receipt_1_13_2339_1_join0 receipt_1_13_2339_1_join2 rfl rfl rfl
private theorem receipt_1_13_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 640 256 = 13497070524289665486757167782 :=
  phaseBlock_append receipt_1_13_2339_1_part5 receipt_1_13_2339_1_part6 rfl rfl rfl
private theorem receipt_1_13_2339_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 1024 227 = 2586858405730771023457170159 :=
  phaseBlock_append receipt_1_13_2339_1_part8 receipt_1_13_2339_1_part9 rfl rfl rfl
private theorem receipt_1_13_2339_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 896 355 = 6466316749621197374519032473 :=
  phaseBlock_append receipt_1_13_2339_1_part7 receipt_1_13_2339_1_join5 rfl rfl rfl
private theorem receipt_1_13_2339_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 640 611 = 19963387273910862861276200255 :=
  phaseBlock_append receipt_1_13_2339_1_join4 receipt_1_13_2339_1_join6 rfl rfl rfl
private theorem receipt_1_13_2339_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2339 44 1 0 2 1) 0 1251 = 92429645192543354800668771007 :=
  phaseBlock_append receipt_1_13_2339_1_join3 receipt_1_13_2339_1_join7 rfl rfl rfl

private theorem receipt_1_13_2339_1 : fastPhase (bank 1 13).shape 179827 2339 44 1 0 2 1 = 92429645192543354800668771007 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2339_1_join8

private theorem receipt_1_13_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 0 128 = 19411190003606287800521533728 := by decide +kernel
private theorem receipt_1_13_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 128 128 = 16839594063979534875417213216 := by decide +kernel
private theorem receipt_1_13_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 256 128 = 14391492282190516939987732768 := by decide +kernel
private theorem receipt_1_13_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 384 128 = 12063734239519004760626567456 := by decide +kernel
private theorem receipt_1_13_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 512 128 = 9853184802337315438112434464 := by decide +kernel
private theorem receipt_1_13_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 640 128 = 7756724096994124313857014048 := by decide +kernel
private theorem receipt_1_13_2340_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 768 128 = 5771248095459117057980792239 := by decide +kernel
private theorem receipt_1_13_2340_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 896 128 = 3893670995936997076232152947 := by decide +kernel
private theorem receipt_1_13_2340_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 1024 128 = 2120913654319477352067293884 := by decide +kernel
private theorem receipt_1_13_2340_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 1152 99 = 489221901731366760009830373 := by decide +kernel
private theorem receipt_1_13_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 0 256 = 36250784067585822675938746944 :=
  phaseBlock_append receipt_1_13_2340_0_part0 receipt_1_13_2340_0_part1 rfl rfl rfl
private theorem receipt_1_13_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 384 256 = 21916919041856320198739001920 :=
  phaseBlock_append receipt_1_13_2340_0_part3 receipt_1_13_2340_0_part4 rfl rfl rfl
private theorem receipt_1_13_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 256 384 = 36308411324046837138726734688 :=
  phaseBlock_append receipt_1_13_2340_0_part2 receipt_1_13_2340_0_join1 rfl rfl rfl
private theorem receipt_1_13_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 0 640 = 72559195391632659814665481632 :=
  phaseBlock_append receipt_1_13_2340_0_join0 receipt_1_13_2340_0_join2 rfl rfl rfl
private theorem receipt_1_13_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 640 256 = 13527972192453241371837806287 :=
  phaseBlock_append receipt_1_13_2340_0_part5 receipt_1_13_2340_0_part6 rfl rfl rfl
private theorem receipt_1_13_2340_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 1024 227 = 2610135556050844112077124257 :=
  phaseBlock_append receipt_1_13_2340_0_part8 receipt_1_13_2340_0_part9 rfl rfl rfl
private theorem receipt_1_13_2340_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 896 355 = 6503806551987841188309277204 :=
  phaseBlock_append receipt_1_13_2340_0_part7 receipt_1_13_2340_0_join5 rfl rfl rfl
private theorem receipt_1_13_2340_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 640 611 = 20031778744441082560147083491 :=
  phaseBlock_append receipt_1_13_2340_0_join4 receipt_1_13_2340_0_join6 rfl rfl rfl
private theorem receipt_1_13_2340_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 0) 0 1251 = 92590974136073742374812565123 :=
  phaseBlock_append receipt_1_13_2340_0_join3 receipt_1_13_2340_0_join7 rfl rfl rfl

private theorem receipt_1_13_2340_0 : fastPhase (bank 1 13).shape 179827 2340 44 1 0 2 0 = 92590974136073742374812565123 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2340_0_join8

private theorem receipt_1_13_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 0 128 = 19390875226429123951662271008 := by decide +kernel
private theorem receipt_1_13_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 128 128 = 16820224860874001002302462496 := by decide +kernel
private theorem receipt_1_13_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 256 128 = 14373044749874896003625953824 := by decide +kernel
private theorem receipt_1_13_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 384 128 = 12046184591324605070241593888 := by decide +kernel
private theorem receipt_1_13_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 512 128 = 9836509368016109717474527776 := by decide +kernel
private theorem receipt_1_13_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 640 128 = 7740899322526388767613917728 := by decide +kernel
private theorem receipt_1_13_2340_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 768 128 = 5756250541239058585261143709 := by decide +kernel
private theorem receipt_1_13_2340_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 896 128 = 3879477323157957717115923995 := by decide +kernel
private theorem receipt_1_13_2340_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 1024 128 = 2107500631992623507609904271 := by decide +kernel
private theorem receipt_1_13_2340_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 1152 99 = 479368494211320542925749185 := by decide +kernel
private theorem receipt_1_13_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 0 256 = 36211100087303124953964733504 :=
  phaseBlock_append receipt_1_13_2340_1_part0 receipt_1_13_2340_1_part1 rfl rfl rfl
private theorem receipt_1_13_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 384 256 = 21882693959340714787716121664 :=
  phaseBlock_append receipt_1_13_2340_1_part3 receipt_1_13_2340_1_part4 rfl rfl rfl
private theorem receipt_1_13_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 256 384 = 36255738709215610791342075488 :=
  phaseBlock_append receipt_1_13_2340_1_part2 receipt_1_13_2340_1_join1 rfl rfl rfl
private theorem receipt_1_13_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 0 640 = 72466838796518735745306808992 :=
  phaseBlock_append receipt_1_13_2340_1_join0 receipt_1_13_2340_1_join2 rfl rfl rfl
private theorem receipt_1_13_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 640 256 = 13497149863765447352875061437 :=
  phaseBlock_append receipt_1_13_2340_1_part5 receipt_1_13_2340_1_part6 rfl rfl rfl
private theorem receipt_1_13_2340_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 1024 227 = 2586869126203944050535653456 :=
  phaseBlock_append receipt_1_13_2340_1_part8 receipt_1_13_2340_1_part9 rfl rfl rfl
private theorem receipt_1_13_2340_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 896 355 = 6466346449361901767651577451 :=
  phaseBlock_append receipt_1_13_2340_1_part7 receipt_1_13_2340_1_join5 rfl rfl rfl
private theorem receipt_1_13_2340_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 640 611 = 19963496313127349120526638888 :=
  phaseBlock_append receipt_1_13_2340_1_join4 receipt_1_13_2340_1_join6 rfl rfl rfl
private theorem receipt_1_13_2340_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179827 2340 44 1 0 2 1) 0 1251 = 92430335109646084865833447880 :=
  phaseBlock_append receipt_1_13_2340_1_join3 receipt_1_13_2340_1_join7 rfl rfl rfl

private theorem receipt_1_13_2340_1 : fastPhase (bank 1 13).shape 179827 2340 44 1 0 2 1 = 92430335109646084865833447880 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2340_1_join8

theorem receipt_1_13 : Checked (bank 1 13) 44 0 2 := by
  refine checked_from_values (bank 1 13) 44 0 2
    (P3_7_1.checked (bank 1 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_13_2339_0 receipt_1_13_2339_1 receipt_1_13_2340_0 receipt_1_13_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_13_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 0 128 = 10404461521802658364234334400 := by decide +kernel
private theorem receipt_2_13_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 128 128 = 8979399536054924029655802048 := by decide +kernel
private theorem receipt_2_13_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 256 128 = 7634163681202243020856344768 := by decide +kernel
private theorem receipt_2_13_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 384 128 = 6366039979151987839372566720 := by decide +kernel
private theorem receipt_2_13_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 512 128 = 5172359651540927556202561728 := by decide +kernel
private theorem receipt_2_13_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 640 128 = 4050498812072698877292699840 := by decide +kernel
private theorem receipt_2_13_2339_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 768 128 = 2997878484762608924735886570 := by decide +kernel
private theorem receipt_2_13_2339_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 896 128 = 2011965515274879410798886436 := by decide +kernel
private theorem receipt_2_13_2339_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 1024 128 = 1090266264271516687705122302 := by decide +kernel
private theorem receipt_2_13_2339_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 1152 99 = 250377020872220887320135930 := by decide +kernel
private theorem receipt_2_13_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 0 256 = 19383861057857582393890136448 :=
  phaseBlock_append receipt_2_13_2339_0_part0 receipt_2_13_2339_0_part1 rfl rfl rfl
private theorem receipt_2_13_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 384 256 = 11538399630692915395575128448 :=
  phaseBlock_append receipt_2_13_2339_0_part3 receipt_2_13_2339_0_part4 rfl rfl rfl
private theorem receipt_2_13_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 256 384 = 19172563311895158416431473216 :=
  phaseBlock_append receipt_2_13_2339_0_part2 receipt_2_13_2339_0_join1 rfl rfl rfl
private theorem receipt_2_13_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 0 640 = 38556424369752740810321609664 :=
  phaseBlock_append receipt_2_13_2339_0_join0 receipt_2_13_2339_0_join2 rfl rfl rfl
private theorem receipt_2_13_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 640 256 = 7048377296835307802028586410 :=
  phaseBlock_append receipt_2_13_2339_0_part5 receipt_2_13_2339_0_part6 rfl rfl rfl
private theorem receipt_2_13_2339_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 1024 227 = 1340643285143737575025258232 :=
  phaseBlock_append receipt_2_13_2339_0_part8 receipt_2_13_2339_0_part9 rfl rfl rfl
private theorem receipt_2_13_2339_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 896 355 = 3352608800418616985824144668 :=
  phaseBlock_append receipt_2_13_2339_0_part7 receipt_2_13_2339_0_join5 rfl rfl rfl
private theorem receipt_2_13_2339_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 640 611 = 10400986097253924787852731078 :=
  phaseBlock_append receipt_2_13_2339_0_join4 receipt_2_13_2339_0_join6 rfl rfl rfl
private theorem receipt_2_13_2339_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 0) 0 1251 = 48957410467006665598174340742 :=
  phaseBlock_append receipt_2_13_2339_0_join3 receipt_2_13_2339_0_join7 rfl rfl rfl

private theorem receipt_2_13_2339_0 : fastPhase (bank 2 13).shape 179827 2339 44 1 0 7 0 = 48957410467006665598174340742 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2339_0_join8

private theorem receipt_2_13_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 0 128 = 10393152448308840587953687040 := by decide +kernel
private theorem receipt_2_13_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 128 128 = 8968707237260599353620318720 := by decide +kernel
private theorem receipt_2_13_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 256 128 = 7624067361014495929074240000 := by decide +kernel
private theorem receipt_2_13_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 384 128 = 6356519187564773431629662720 := by decide +kernel
private theorem receipt_2_13_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 512 128 = 5163394282278714088450542080 := by decide +kernel
private theorem receipt_2_13_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 640 128 = 4042069100234110302037363200 := by decide +kernel
private theorem receipt_2_13_2339_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 768 128 = 2989965003585646686472982990 := by decide +kernel
private theorem receipt_2_13_2339_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 896 128 = 2004549166792734549562324626 := by decide +kernel
private theorem receipt_2_13_2339_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 1024 128 = 1083328281104274146805620964 := by decide +kernel
private theorem receipt_2_13_2339_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 1152 99 = 245327297598380722392392160 := by decide +kernel
private theorem receipt_2_13_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 0 256 = 19361859685569439941574005760 :=
  phaseBlock_append receipt_2_13_2339_1_part0 receipt_2_13_2339_1_part1 rfl rfl rfl
private theorem receipt_2_13_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 384 256 = 11519913469843487520080204800 :=
  phaseBlock_append receipt_2_13_2339_1_part3 receipt_2_13_2339_1_part4 rfl rfl rfl
private theorem receipt_2_13_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 256 384 = 19143980830857983449154444800 :=
  phaseBlock_append receipt_2_13_2339_1_part2 receipt_2_13_2339_1_join1 rfl rfl rfl
private theorem receipt_2_13_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 0 640 = 38505840516427423390728450560 :=
  phaseBlock_append receipt_2_13_2339_1_join0 receipt_2_13_2339_1_join2 rfl rfl rfl
private theorem receipt_2_13_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 640 256 = 7032034103819756988510346190 :=
  phaseBlock_append receipt_2_13_2339_1_part5 receipt_2_13_2339_1_part6 rfl rfl rfl
private theorem receipt_2_13_2339_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 1024 227 = 1328655578702654869198013124 :=
  phaseBlock_append receipt_2_13_2339_1_part8 receipt_2_13_2339_1_part9 rfl rfl rfl
private theorem receipt_2_13_2339_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 896 355 = 3333204745495389418760337750 :=
  phaseBlock_append receipt_2_13_2339_1_part7 receipt_2_13_2339_1_join5 rfl rfl rfl
private theorem receipt_2_13_2339_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 640 611 = 10365238849315146407270683940 :=
  phaseBlock_append receipt_2_13_2339_1_join4 receipt_2_13_2339_1_join6 rfl rfl rfl
private theorem receipt_2_13_2339_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2339 44 1 0 7 1) 0 1251 = 48871079365742569797999134500 :=
  phaseBlock_append receipt_2_13_2339_1_join3 receipt_2_13_2339_1_join7 rfl rfl rfl

private theorem receipt_2_13_2339_1 : fastPhase (bank 2 13).shape 179827 2339 44 1 0 7 1 = 48871079365742569797999134500 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2339_1_join8

private theorem receipt_2_13_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 0 128 = 10404554210530499150824277280 := by decide +kernel
private theorem receipt_2_13_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 128 128 = 8979474860091446069992338720 := by decide +kernel
private theorem receipt_2_13_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 256 128 = 7634223624351056802809931040 := by decide +kernel
private theorem receipt_2_13_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 384 128 = 6366086440105352155374359840 := by decide +kernel
private theorem receipt_2_13_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 512 128 = 5172394445410284704314279200 := by decide +kernel
private theorem receipt_2_13_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 640 128 = 4050523671908434648324273440 := by decide +kernel
private theorem receipt_2_13_2340_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 768 128 = 2997895053843287987137663240 := by decide +kernel
private theorem receipt_2_13_2340_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 896 128 = 2011975356032607729205546149 := by decide +kernel
private theorem receipt_2_13_2340_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 1024 128 = 1090270894573998432895880590 := by decide +kernel
private theorem receipt_2_13_2340_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 1152 99 = 250377943285129665268834209 := by decide +kernel
private theorem receipt_2_13_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 0 256 = 19384029070621945220816616000 :=
  phaseBlock_append receipt_2_13_2340_0_part0 receipt_2_13_2340_0_part1 rfl rfl rfl
private theorem receipt_2_13_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 384 256 = 11538480885515636859688639040 :=
  phaseBlock_append receipt_2_13_2340_0_part3 receipt_2_13_2340_0_part4 rfl rfl rfl
private theorem receipt_2_13_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 256 384 = 19172704509866693662498570080 :=
  phaseBlock_append receipt_2_13_2340_0_part2 receipt_2_13_2340_0_join1 rfl rfl rfl
private theorem receipt_2_13_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 0 640 = 38556733580488638883315186080 :=
  phaseBlock_append receipt_2_13_2340_0_join0 receipt_2_13_2340_0_join2 rfl rfl rfl
private theorem receipt_2_13_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 640 256 = 7048418725751722635461936680 :=
  phaseBlock_append receipt_2_13_2340_0_part5 receipt_2_13_2340_0_part6 rfl rfl rfl
private theorem receipt_2_13_2340_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 1024 227 = 1340648837859128098164714799 :=
  phaseBlock_append receipt_2_13_2340_0_part8 receipt_2_13_2340_0_part9 rfl rfl rfl
private theorem receipt_2_13_2340_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 896 355 = 3352624193891735827370260948 :=
  phaseBlock_append receipt_2_13_2340_0_part7 receipt_2_13_2340_0_join5 rfl rfl rfl
private theorem receipt_2_13_2340_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 640 611 = 10401042919643458462832197628 :=
  phaseBlock_append receipt_2_13_2340_0_join4 receipt_2_13_2340_0_join6 rfl rfl rfl
private theorem receipt_2_13_2340_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 0) 0 1251 = 48957776500132097346147383708 :=
  phaseBlock_append receipt_2_13_2340_0_join3 receipt_2_13_2340_0_join7 rfl rfl rfl

private theorem receipt_2_13_2340_0 : fastPhase (bank 2 13).shape 179827 2340 44 1 0 7 0 = 48957776500132097346147383708 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2340_0_join8

private theorem receipt_2_13_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 0 128 = 10393245053609909986206049440 := by decide +kernel
private theorem receipt_2_13_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 128 128 = 8968782486219735025986524320 := by decide +kernel
private theorem receipt_2_13_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 256 128 = 7624127237013597452147901600 := by decide +kernel
private theorem receipt_2_13_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 384 128 = 6356565588882869826951132320 := by decide +kernel
private theorem receipt_2_13_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 512 128 = 5163429023622435045743928480 := by decide +kernel
private theorem receipt_2_13_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 640 128 = 4042093914257382188495344800 := by decide +kernel
private theorem receipt_2_13_2340_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 768 128 = 2989981533203167075728896470 := by decide +kernel
private theorem receipt_2_13_2340_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 896 128 = 2004558974113417483100141624 := by decide +kernel
private theorem receipt_2_13_2340_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 1024 128 = 1083332883612738445037190295 := by decide +kernel
private theorem receipt_2_13_2340_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 1152 99 = 245328202145754552552036037 := by decide +kernel
private theorem receipt_2_13_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 0 256 = 19362027539829645012192573760 :=
  phaseBlock_append receipt_2_13_2340_1_part0 receipt_2_13_2340_1_part1 rfl rfl rfl
private theorem receipt_2_13_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 384 256 = 11519994612505304872695060800 :=
  phaseBlock_append receipt_2_13_2340_1_part3 receipt_2_13_2340_1_part4 rfl rfl rfl
private theorem receipt_2_13_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 256 384 = 19144121849518902324842962400 :=
  phaseBlock_append receipt_2_13_2340_1_part2 receipt_2_13_2340_1_join1 rfl rfl rfl
private theorem receipt_2_13_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 0 640 = 38506149389348547337035536160 :=
  phaseBlock_append receipt_2_13_2340_1_join0 receipt_2_13_2340_1_join2 rfl rfl rfl
private theorem receipt_2_13_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 640 256 = 7032075447460549264224241270 :=
  phaseBlock_append receipt_2_13_2340_1_part5 receipt_2_13_2340_1_part6 rfl rfl rfl
private theorem receipt_2_13_2340_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 1024 227 = 1328661085758492997589226332 :=
  phaseBlock_append receipt_2_13_2340_1_part8 receipt_2_13_2340_1_part9 rfl rfl rfl
private theorem receipt_2_13_2340_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 896 355 = 3333220059871910480689367956 :=
  phaseBlock_append receipt_2_13_2340_1_part7 receipt_2_13_2340_1_join5 rfl rfl rfl
private theorem receipt_2_13_2340_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 640 611 = 10365295507332459744913609226 :=
  phaseBlock_append receipt_2_13_2340_1_join4 receipt_2_13_2340_1_join6 rfl rfl rfl
private theorem receipt_2_13_2340_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179827 2340 44 1 0 7 1) 0 1251 = 48871444896681007081949145386 :=
  phaseBlock_append receipt_2_13_2340_1_join3 receipt_2_13_2340_1_join7 rfl rfl rfl

private theorem receipt_2_13_2340_1 : fastPhase (bank 2 13).shape 179827 2340 44 1 0 7 1 = 48871444896681007081949145386 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2340_1_join8

theorem receipt_2_13 : Checked (bank 2 13) 44 0 7 := by
  refine checked_from_values (bank 2 13) 44 0 7
    (P3_7_1.checked (bank 2 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_13_2339_0 receipt_2_13_2339_1 receipt_2_13_2340_0 receipt_2_13_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_13_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 0 128 = 2384320877103731529953824896 := by decide +kernel
private theorem receipt_3_13_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 128 128 = 2073522329243576649909072000 := by decide +kernel
private theorem receipt_3_13_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 256 128 = 1776442056178347294978347136 := by decide +kernel
private theorem receipt_3_13_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 384 128 = 1493481821838471579301261440 := by decide +kernel
private theorem receipt_3_13_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 512 128 = 1225039733575929731725938816 := by decide +kernel
private theorem receipt_3_13_2339_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 640 128 = 971510251636194925378367616 := by decide +kernel
private theorem receipt_3_13_2339_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 768 128 = 733284198630174107231752320 := by decide +kernel
private theorem receipt_3_13_2339_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 896 128 = 510748769006148827675865216 := by decide +kernel
private theorem receipt_3_13_2339_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 1024 128 = 304287538521716070086398080 := by decide +kernel
private theorem receipt_3_13_2339_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 1152 128 = 114280473715729080394313856 := by decide +kernel
private theorem receipt_3_13_2339_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 1280 18 = 1790635442968616572092294 := by decide +kernel
private theorem receipt_3_13_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 0 256 = 4457843206347308179862896896 :=
  phaseBlock_append receipt_3_13_2339_0_part0 receipt_3_13_2339_0_part1 rfl rfl rfl
private theorem receipt_3_13_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 384 256 = 2718521555414401311027200256 :=
  phaseBlock_append receipt_3_13_2339_0_part3 receipt_3_13_2339_0_part4 rfl rfl rfl
private theorem receipt_3_13_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 256 384 = 4494963611592748606005547392 :=
  phaseBlock_append receipt_3_13_2339_0_part2 receipt_3_13_2339_0_join1 rfl rfl rfl
private theorem receipt_3_13_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 0 640 = 8952806817940056785868444288 :=
  phaseBlock_append receipt_3_13_2339_0_join0 receipt_3_13_2339_0_join2 rfl rfl rfl
private theorem receipt_3_13_2339_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 768 256 = 1244032967636322934907617536 :=
  phaseBlock_append receipt_3_13_2339_0_part6 receipt_3_13_2339_0_part7 rfl rfl rfl
private theorem receipt_3_13_2339_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 640 384 = 2215543219272517860285985152 :=
  phaseBlock_append receipt_3_13_2339_0_part5 receipt_3_13_2339_0_join4 rfl rfl rfl
private theorem receipt_3_13_2339_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 1152 146 = 116071109158697696966406150 :=
  phaseBlock_append receipt_3_13_2339_0_part9 receipt_3_13_2339_0_part10 rfl rfl rfl
private theorem receipt_3_13_2339_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 1024 274 = 420358647680413767052804230 :=
  phaseBlock_append receipt_3_13_2339_0_part8 receipt_3_13_2339_0_join6 rfl rfl rfl
private theorem receipt_3_13_2339_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 640 658 = 2635901866952931627338789382 :=
  phaseBlock_append receipt_3_13_2339_0_join5 receipt_3_13_2339_0_join7 rfl rfl rfl
private theorem receipt_3_13_2339_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 0) 0 1298 = 11588708684892988413207233670 :=
  phaseBlock_append receipt_3_13_2339_0_join3 receipt_3_13_2339_0_join8 rfl rfl rfl

private theorem receipt_3_13_2339_0 : fastPhase (bank 3 13).shape 179827 2339 44 1 1 1 0 = 11588708684892988413207233670 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2339_0_join9

private theorem receipt_3_13_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 0 128 = 2381872628065702226072116800 := by decide +kernel
private theorem receipt_3_13_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 128 128 = 2071175256858595936699506240 := by decide +kernel
private theorem receipt_3_13_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 256 128 = 1774199574705637404876709440 := by decide +kernel
private theorem receipt_3_13_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 384 128 = 1491347315453484636338249280 := by decide +kernel
private theorem receipt_3_13_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 512 128 = 1223016556447240516667711040 := by decide +kernel
private theorem receipt_3_13_2339_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 640 128 = 969601728002393640867094080 := by decide +kernel
private theorem receipt_3_13_2339_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 768 128 = 731493622876759142926163520 := by decide +kernel
private theorem receipt_3_13_2339_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 896 128 = 509079405742419525391801920 := by decide +kernel
private theorem receipt_3_13_2339_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 1024 128 = 302742622657665488937360960 := by decide +kernel
private theorem receipt_3_13_2339_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 1152 128 = 112863210538936761932013120 := by decide +kernel
private theorem receipt_3_13_2339_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 1280 18 = 1601752677431564225435040 := by decide +kernel
private theorem receipt_3_13_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 0 256 = 4453047884924298162771623040 :=
  phaseBlock_append receipt_3_13_2339_1_part0 receipt_3_13_2339_1_part1 rfl rfl rfl
private theorem receipt_3_13_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 384 256 = 2714363871900725153005960320 :=
  phaseBlock_append receipt_3_13_2339_1_part3 receipt_3_13_2339_1_part4 rfl rfl rfl
private theorem receipt_3_13_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 256 384 = 4488563446606362557882669760 :=
  phaseBlock_append receipt_3_13_2339_1_part2 receipt_3_13_2339_1_join1 rfl rfl rfl
private theorem receipt_3_13_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 0 640 = 8941611331530660720654292800 :=
  phaseBlock_append receipt_3_13_2339_1_join0 receipt_3_13_2339_1_join2 rfl rfl rfl
private theorem receipt_3_13_2339_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 768 256 = 1240573028619178668317965440 :=
  phaseBlock_append receipt_3_13_2339_1_part6 receipt_3_13_2339_1_part7 rfl rfl rfl
private theorem receipt_3_13_2339_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 640 384 = 2210174756621572309185059520 :=
  phaseBlock_append receipt_3_13_2339_1_part5 receipt_3_13_2339_1_join4 rfl rfl rfl
private theorem receipt_3_13_2339_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 1152 146 = 114464963216368326157448160 :=
  phaseBlock_append receipt_3_13_2339_1_part9 receipt_3_13_2339_1_part10 rfl rfl rfl
private theorem receipt_3_13_2339_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 1024 274 = 417207585874033815094809120 :=
  phaseBlock_append receipt_3_13_2339_1_part8 receipt_3_13_2339_1_join6 rfl rfl rfl
private theorem receipt_3_13_2339_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 640 658 = 2627382342495606124279868640 :=
  phaseBlock_append receipt_3_13_2339_1_join5 receipt_3_13_2339_1_join7 rfl rfl rfl
private theorem receipt_3_13_2339_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2339 44 1 1 1 1) 0 1298 = 11568993674026266844934161440 :=
  phaseBlock_append receipt_3_13_2339_1_join3 receipt_3_13_2339_1_join8 rfl rfl rfl

private theorem receipt_3_13_2339_1 : fastPhase (bank 3 13).shape 179827 2339 44 1 1 1 1 = 11568993674026266844934161440 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2339_1_join9

private theorem receipt_3_13_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 0 128 = 2384341820766547703992186752 := by decide +kernel
private theorem receipt_3_13_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 128 128 = 2073538689103871574249248640 := by decide +kernel
private theorem receipt_3_13_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 256 128 = 1776454512345176547371366272 := by decide +kernel
private theorem receipt_3_13_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 384 128 = 1493491006047903284036654976 := by decide +kernel
private theorem receipt_3_13_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 512 128 = 1225046229552234679111972736 := by decide +kernel
private theorem receipt_3_13_2340_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 640 128 = 971514595452157081920051072 := by decide +kernel
private theorem receipt_3_13_2340_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 768 128 = 733286879066521516506625920 := by decide +kernel
private theorem receipt_3_13_2340_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 896 128 = 510750227910104901907568512 := by decide +kernel
private theorem receipt_3_13_2340_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 1024 128 = 304288171164671272416016256 := by decide +kernel
private theorem receipt_3_13_2340_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 1152 128 = 114280629150032997849503616 := by decide +kernel
private theorem receipt_3_13_2340_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 1280 18 = 1790636940180766332725838 := by decide +kernel
private theorem receipt_3_13_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 0 256 = 4457880509870419278241435392 :=
  phaseBlock_append receipt_3_13_2340_0_part0 receipt_3_13_2340_0_part1 rfl rfl rfl
private theorem receipt_3_13_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 384 256 = 2718537235600137963148627712 :=
  phaseBlock_append receipt_3_13_2340_0_part3 receipt_3_13_2340_0_part4 rfl rfl rfl
private theorem receipt_3_13_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 256 384 = 4494991747945314510519993984 :=
  phaseBlock_append receipt_3_13_2340_0_part2 receipt_3_13_2340_0_join1 rfl rfl rfl
private theorem receipt_3_13_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 0 640 = 8952872257815733788761429376 :=
  phaseBlock_append receipt_3_13_2340_0_join0 receipt_3_13_2340_0_join2 rfl rfl rfl
private theorem receipt_3_13_2340_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 768 256 = 1244037106976626418414194432 :=
  phaseBlock_append receipt_3_13_2340_0_part6 receipt_3_13_2340_0_part7 rfl rfl rfl
private theorem receipt_3_13_2340_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 640 384 = 2215551702428783500334245504 :=
  phaseBlock_append receipt_3_13_2340_0_part5 receipt_3_13_2340_0_join4 rfl rfl rfl
private theorem receipt_3_13_2340_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 1152 146 = 116071266090213764182229454 :=
  phaseBlock_append receipt_3_13_2340_0_part9 receipt_3_13_2340_0_part10 rfl rfl rfl
private theorem receipt_3_13_2340_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 1024 274 = 420359437254885036598245710 :=
  phaseBlock_append receipt_3_13_2340_0_part8 receipt_3_13_2340_0_join6 rfl rfl rfl
private theorem receipt_3_13_2340_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 640 658 = 2635911139683668536932491214 :=
  phaseBlock_append receipt_3_13_2340_0_join5 receipt_3_13_2340_0_join7 rfl rfl rfl
private theorem receipt_3_13_2340_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 0) 0 1298 = 11588783397499402325693920590 :=
  phaseBlock_append receipt_3_13_2340_0_join3 receipt_3_13_2340_0_join8 rfl rfl rfl

private theorem receipt_3_13_2340_0 : fastPhase (bank 3 13).shape 179827 2340 44 1 1 1 0 = 11588783397499402325693920590 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2340_0_join9

private theorem receipt_3_13_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 0 128 = 2381893546834039402088370432 := by decide +kernel
private theorem receipt_3_13_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 128 128 = 2071191595431857821470863616 := by decide +kernel
private theorem receipt_3_13_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 256 128 = 1774212012925270276977807616 := by decide +kernel
private theorem receipt_3_13_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 384 128 = 1491356484790139761563529472 := by decide +kernel
private theorem receipt_3_13_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 512 128 = 1223023040361958632514556160 := by decide +kernel
private theorem receipt_3_13_2340_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 640 128 = 969606062306909831716745472 := by decide +kernel
private theorem receipt_3_13_2340_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 768 128 = 731496296092928105922416896 := by decide +kernel
private theorem receipt_3_13_2340_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 896 128 = 509080859460761227017482496 := by decide +kernel
private theorem receipt_3_13_2340_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 1024 128 = 302743251895031212288577792 := by decide +kernel
private theorem receipt_3_13_2340_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 1152 128 = 112863364095295544690192640 := by decide +kernel
private theorem receipt_3_13_2340_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 1280 18 = 1601754018729060022933098 := by decide +kernel
private theorem receipt_3_13_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 0 256 = 4453085142265897223559234048 :=
  phaseBlock_append receipt_3_13_2340_1_part0 receipt_3_13_2340_1_part1 rfl rfl rfl
private theorem receipt_3_13_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 384 256 = 2714379525152098394078085632 :=
  phaseBlock_append receipt_3_13_2340_1_part3 receipt_3_13_2340_1_part4 rfl rfl rfl
private theorem receipt_3_13_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 256 384 = 4488591538077368671055893248 :=
  phaseBlock_append receipt_3_13_2340_1_part2 receipt_3_13_2340_1_join1 rfl rfl rfl
private theorem receipt_3_13_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 0 640 = 8941676680343265894615127296 :=
  phaseBlock_append receipt_3_13_2340_1_join0 receipt_3_13_2340_1_join2 rfl rfl rfl
private theorem receipt_3_13_2340_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 768 256 = 1240577155553689332939899392 :=
  phaseBlock_append receipt_3_13_2340_1_part6 receipt_3_13_2340_1_part7 rfl rfl rfl
private theorem receipt_3_13_2340_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 640 384 = 2210183217860599164656644864 :=
  phaseBlock_append receipt_3_13_2340_1_part5 receipt_3_13_2340_1_join4 rfl rfl rfl
private theorem receipt_3_13_2340_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 1152 146 = 114465118114024604713125738 :=
  phaseBlock_append receipt_3_13_2340_1_part9 receipt_3_13_2340_1_part10 rfl rfl rfl
private theorem receipt_3_13_2340_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 1024 274 = 417208370009055817001703530 :=
  phaseBlock_append receipt_3_13_2340_1_part8 receipt_3_13_2340_1_join6 rfl rfl rfl
private theorem receipt_3_13_2340_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 640 658 = 2627391587869654981658348394 :=
  phaseBlock_append receipt_3_13_2340_1_join5 receipt_3_13_2340_1_join7 rfl rfl rfl
private theorem receipt_3_13_2340_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179827 2340 44 1 1 1 1) 0 1298 = 11569068268212920876273475690 :=
  phaseBlock_append receipt_3_13_2340_1_join3 receipt_3_13_2340_1_join8 rfl rfl rfl

private theorem receipt_3_13_2340_1 : fastPhase (bank 3 13).shape 179827 2340 44 1 1 1 1 = 11569068268212920876273475690 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2340_1_join9

theorem receipt_3_13 : Checked (bank 3 13) 44 1 1 := by
  refine checked_from_values (bank 3 13) 44 1 1
    (P3_7_1.checked (bank 3 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1297)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_13_2339_0 receipt_3_13_2339_1 receipt_3_13_2340_0 receipt_3_13_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_14_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 0 128 = 188173045036608620968378906560 := by decide +kernel
private theorem receipt_0_14_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 128 128 = 172239186108789644542726641600 := by decide +kernel
private theorem receipt_0_14_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 256 128 = 156786517564625822414277965760 := by decide +kernel
private theorem receipt_0_14_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 384 128 = 141807598726593450803098015680 := by decide +kernel
private theorem receipt_0_14_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 512 128 = 127295000892537152037728794560 := by decide +kernel
private theorem receipt_0_14_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 640 128 = 113241307329391047434076657600 := by decide +kernel
private theorem receipt_0_14_2339_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 768 128 = 99639113266899930174299797440 := by decide +kernel
private theorem receipt_0_14_2339_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 896 128 = 86481025891340438185695729600 := by decide +kernel
private theorem receipt_0_14_2339_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1024 128 = 73759664339242227019588777920 := by decide +kernel
private theorem receipt_0_14_2339_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1152 128 = 61467659724690105914829283881 := by decide +kernel
private theorem receipt_0_14_2339_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1280 128 = 49597665012628162539132915211 := by decide +kernel
private theorem receipt_0_14_2339_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1408 128 = 38142347265979790835558533088 := by decide +kernel
private theorem receipt_0_14_2339_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1536 128 = 27094353120820770561550942602 := by decide +kernel
private theorem receipt_0_14_2339_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1664 128 = 16446337078964397402119429133 := by decide +kernel
private theorem receipt_0_14_2339_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1792 128 = 6190965564821952656784148860 := by decide +kernel
private theorem receipt_0_14_2339_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1920 15 = 72060459585999257990755632 := by decide +kernel
private theorem receipt_0_14_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 0 256 = 360412231145398265511105548160 :=
  phaseBlock_append receipt_0_14_2339_0_part0 receipt_0_14_2339_0_part1 rfl rfl rfl
private theorem receipt_0_14_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 256 256 = 298594116291219273217375981440 :=
  phaseBlock_append receipt_0_14_2339_0_part2 receipt_0_14_2339_0_part3 rfl rfl rfl
private theorem receipt_0_14_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 0 512 = 659006347436617538728481529600 :=
  phaseBlock_append receipt_0_14_2339_0_join0 receipt_0_14_2339_0_join1 rfl rfl rfl
private theorem receipt_0_14_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 512 256 = 240536308221928199471805452160 :=
  phaseBlock_append receipt_0_14_2339_0_part4 receipt_0_14_2339_0_part5 rfl rfl rfl
private theorem receipt_0_14_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 768 256 = 186120139158240368359995527040 :=
  phaseBlock_append receipt_0_14_2339_0_part6 receipt_0_14_2339_0_part7 rfl rfl rfl
private theorem receipt_0_14_2339_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 512 512 = 426656447380168567831800979200 :=
  phaseBlock_append receipt_0_14_2339_0_join3 receipt_0_14_2339_0_join4 rfl rfl rfl
private theorem receipt_0_14_2339_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 0 1024 = 1085662794816786106560282508800 :=
  phaseBlock_append receipt_0_14_2339_0_join2 receipt_0_14_2339_0_join5 rfl rfl rfl
private theorem receipt_0_14_2339_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1024 256 = 135227324063932332934418061801 :=
  phaseBlock_append receipt_0_14_2339_0_part8 receipt_0_14_2339_0_part9 rfl rfl rfl
private theorem receipt_0_14_2339_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1280 256 = 87740012278607953374691448299 :=
  phaseBlock_append receipt_0_14_2339_0_part10 receipt_0_14_2339_0_part11 rfl rfl rfl
private theorem receipt_0_14_2339_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1024 512 = 222967336342540286309109510100 :=
  phaseBlock_append receipt_0_14_2339_0_join7 receipt_0_14_2339_0_join8 rfl rfl rfl
private theorem receipt_0_14_2339_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1536 256 = 43540690199785167963670371735 :=
  phaseBlock_append receipt_0_14_2339_0_part12 receipt_0_14_2339_0_part13 rfl rfl rfl
private theorem receipt_0_14_2339_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1792 143 = 6263026024407951914774904492 :=
  phaseBlock_append receipt_0_14_2339_0_part14 receipt_0_14_2339_0_part15 rfl rfl rfl
private theorem receipt_0_14_2339_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1536 399 = 49803716224193119878445276227 :=
  phaseBlock_append receipt_0_14_2339_0_join10 receipt_0_14_2339_0_join11 rfl rfl rfl
private theorem receipt_0_14_2339_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 1024 911 = 272771052566733406187554786327 :=
  phaseBlock_append receipt_0_14_2339_0_join9 receipt_0_14_2339_0_join12 rfl rfl rfl
private theorem receipt_0_14_2339_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 0) 0 1935 = 1358433847383519512747837295127 :=
  phaseBlock_append receipt_0_14_2339_0_join6 receipt_0_14_2339_0_join13 rfl rfl rfl

private theorem receipt_0_14_2339_0 : fastPhase (bank 0 14).shape 179827 2339 73 1 0 1 0 = 1358433847383519512747837295127 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2339_0_join14

private theorem receipt_0_14_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 0 128 = 188048318842103461816522049088 := by decide +kernel
private theorem receipt_0_14_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 128 128 = 172118123203161645128503993920 := by decide +kernel
private theorem receipt_0_14_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 256 128 = 156669061628229346557991929408 := by decide +kernel
private theorem receipt_0_14_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 384 128 = 141693693531080325818949264960 := by decide +kernel
private theorem receipt_0_14_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 512 128 = 127184590300808579806069098048 := by decide +kernel
private theorem receipt_0_14_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 640 128 = 113134335295549515473661699648 := by decide +kernel
private theorem receipt_0_14_2339_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 768 128 = 99535523836201122714541999680 := by decide +kernel
private theorem receipt_0_14_2339_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 896 128 = 86380763200145147238917072448 := by decide +kernel
private theorem receipt_0_14_2339_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1024 128 = 73662672614968263453273622080 := by decide +kernel
private theorem receipt_0_14_2339_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1152 128 = 61373883285712510715925361008 := by decide +kernel
private theorem receipt_0_14_2339_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1280 128 = 49507048250604421140948581911 := by decide +kernel
private theorem receipt_0_14_2339_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1408 128 = 38054834623225081021043455092 := by decide +kernel
private theorem receipt_0_14_2339_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1536 128 = 27009889125267288219191210418 := by decide +kernel
private theorem receipt_0_14_2339_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1664 128 = 16364866349476222412191823295 := by decide +kernel
private theorem receipt_0_14_2339_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1792 128 = 6112432811230835051344041138 := by decide +kernel
private theorem receipt_0_14_2339_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1920 15 = 63047172060730152102531129 := by decide +kernel
private theorem receipt_0_14_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 0 256 = 360166442045265106945026043008 :=
  phaseBlock_append receipt_0_14_2339_1_part0 receipt_0_14_2339_1_part1 rfl rfl rfl
private theorem receipt_0_14_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 256 256 = 298362755159309672376941194368 :=
  phaseBlock_append receipt_0_14_2339_1_part2 receipt_0_14_2339_1_part3 rfl rfl rfl
private theorem receipt_0_14_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 0 512 = 658529197204574779321967237376 :=
  phaseBlock_append receipt_0_14_2339_1_join0 receipt_0_14_2339_1_join1 rfl rfl rfl
private theorem receipt_0_14_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 512 256 = 240318925596358095279730797696 :=
  phaseBlock_append receipt_0_14_2339_1_part4 receipt_0_14_2339_1_part5 rfl rfl rfl
private theorem receipt_0_14_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 768 256 = 185916287036346269953459072128 :=
  phaseBlock_append receipt_0_14_2339_1_part6 receipt_0_14_2339_1_part7 rfl rfl rfl
private theorem receipt_0_14_2339_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 512 512 = 426235212632704365233189869824 :=
  phaseBlock_append receipt_0_14_2339_1_join3 receipt_0_14_2339_1_join4 rfl rfl rfl
private theorem receipt_0_14_2339_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 0 1024 = 1084764409837279144555157107200 :=
  phaseBlock_append receipt_0_14_2339_1_join2 receipt_0_14_2339_1_join5 rfl rfl rfl
private theorem receipt_0_14_2339_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1024 256 = 135036555900680774169198983088 :=
  phaseBlock_append receipt_0_14_2339_1_part8 receipt_0_14_2339_1_part9 rfl rfl rfl
private theorem receipt_0_14_2339_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1280 256 = 87561882873829502161992037003 :=
  phaseBlock_append receipt_0_14_2339_1_part10 receipt_0_14_2339_1_part11 rfl rfl rfl
private theorem receipt_0_14_2339_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1024 512 = 222598438774510276331191020091 :=
  phaseBlock_append receipt_0_14_2339_1_join7 receipt_0_14_2339_1_join8 rfl rfl rfl
private theorem receipt_0_14_2339_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1536 256 = 43374755474743510631383033713 :=
  phaseBlock_append receipt_0_14_2339_1_part12 receipt_0_14_2339_1_part13 rfl rfl rfl
private theorem receipt_0_14_2339_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1792 143 = 6175479983291565203446572267 :=
  phaseBlock_append receipt_0_14_2339_1_part14 receipt_0_14_2339_1_part15 rfl rfl rfl
private theorem receipt_0_14_2339_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1536 399 = 49550235458035075834829605980 :=
  phaseBlock_append receipt_0_14_2339_1_join10 receipt_0_14_2339_1_join11 rfl rfl rfl
private theorem receipt_0_14_2339_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 1024 911 = 272148674232545352166020626071 :=
  phaseBlock_append receipt_0_14_2339_1_join9 receipt_0_14_2339_1_join12 rfl rfl rfl
private theorem receipt_0_14_2339_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2339 73 1 0 1 1) 0 1935 = 1356913084069824496721177733271 :=
  phaseBlock_append receipt_0_14_2339_1_join6 receipt_0_14_2339_1_join13 rfl rfl rfl

private theorem receipt_0_14_2339_1 : fastPhase (bank 0 14).shape 179827 2339 73 1 0 1 1 = 1356913084069824496721177733271 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2339_1_join14

private theorem receipt_0_14_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 0 128 = 188174734100960288993097259200 := by decide +kernel
private theorem receipt_0_14_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 128 128 = 172240674813785065533753432256 := by decide +kernel
private theorem receipt_0_14_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 256 128 = 156787819445702079363528628416 := by decide +kernel
private theorem receipt_0_14_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 384 128 = 141808727062563850501822650560 := by decide +kernel
private theorem receipt_0_14_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 512 128 = 127295968706008976994702956736 := by decide +kernel
private theorem receipt_0_14_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 640 128 = 113242127387183087891466590400 := by decide +kernel
private theorem receipt_0_14_2340_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 768 128 = 99639798080459796221202110656 := by decide +kernel
private theorem receipt_0_14_2340_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 896 128 = 86481587717161651969351522496 := by decide +kernel
private theorem receipt_0_14_2340_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1024 128 = 73760115179281095054272207040 := by decide +kernel
private theorem receipt_0_14_2340_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1152 128 = 61468011318822868460505269388 := by decide +kernel
private theorem receipt_0_14_2340_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1280 128 = 49597928606524180363917232954 := by decide +kernel
private theorem receipt_0_14_2340_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1408 128 = 38142534121180311700554677550 := by decide +kernel
private theorem receipt_0_14_2340_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1536 128 = 27094474409317303551105195317 := by decide +kernel
private theorem receipt_0_14_2340_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1664 128 = 16446403693217543916708760575 := by decide +kernel
private theorem receipt_0_14_2340_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1792 128 = 6190988123928261552158190819 := by decide +kernel
private theorem receipt_0_14_2340_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1920 15 = 72060700287505875664463256 := by decide +kernel
private theorem receipt_0_14_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 0 256 = 360415408914745354526850691456 :=
  phaseBlock_append receipt_0_14_2340_0_part0 receipt_0_14_2340_0_part1 rfl rfl rfl
private theorem receipt_0_14_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 256 256 = 298596546508265929865351278976 :=
  phaseBlock_append receipt_0_14_2340_0_part2 receipt_0_14_2340_0_part3 rfl rfl rfl
private theorem receipt_0_14_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 0 512 = 659011955423011284392201970432 :=
  phaseBlock_append receipt_0_14_2340_0_join0 receipt_0_14_2340_0_join1 rfl rfl rfl
private theorem receipt_0_14_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 512 256 = 240538096093192064886169547136 :=
  phaseBlock_append receipt_0_14_2340_0_part4 receipt_0_14_2340_0_part5 rfl rfl rfl
private theorem receipt_0_14_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 768 256 = 186121385797621448190553633152 :=
  phaseBlock_append receipt_0_14_2340_0_part6 receipt_0_14_2340_0_part7 rfl rfl rfl
private theorem receipt_0_14_2340_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 512 512 = 426659481890813513076723180288 :=
  phaseBlock_append receipt_0_14_2340_0_join3 receipt_0_14_2340_0_join4 rfl rfl rfl
private theorem receipt_0_14_2340_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 0 1024 = 1085671437313824797468925150720 :=
  phaseBlock_append receipt_0_14_2340_0_join2 receipt_0_14_2340_0_join5 rfl rfl rfl
private theorem receipt_0_14_2340_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1024 256 = 135228126498103963514777476428 :=
  phaseBlock_append receipt_0_14_2340_0_part8 receipt_0_14_2340_0_part9 rfl rfl rfl
private theorem receipt_0_14_2340_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1280 256 = 87740462727704492064471910504 :=
  phaseBlock_append receipt_0_14_2340_0_part10 receipt_0_14_2340_0_part11 rfl rfl rfl
private theorem receipt_0_14_2340_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1024 512 = 222968589225808455579249386932 :=
  phaseBlock_append receipt_0_14_2340_0_join7 receipt_0_14_2340_0_join8 rfl rfl rfl
private theorem receipt_0_14_2340_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1536 256 = 43540878102534847467813955892 :=
  phaseBlock_append receipt_0_14_2340_0_part12 receipt_0_14_2340_0_part13 rfl rfl rfl
private theorem receipt_0_14_2340_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1792 143 = 6263048824215767427822654075 :=
  phaseBlock_append receipt_0_14_2340_0_part14 receipt_0_14_2340_0_part15 rfl rfl rfl
private theorem receipt_0_14_2340_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1536 399 = 49803926926750614895636609967 :=
  phaseBlock_append receipt_0_14_2340_0_join10 receipt_0_14_2340_0_join11 rfl rfl rfl
private theorem receipt_0_14_2340_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 1024 911 = 272772516152559070474885996899 :=
  phaseBlock_append receipt_0_14_2340_0_join9 receipt_0_14_2340_0_join12 rfl rfl rfl
private theorem receipt_0_14_2340_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 0) 0 1935 = 1358443953466383867943811147619 :=
  phaseBlock_append receipt_0_14_2340_0_join6 receipt_0_14_2340_0_join13 rfl rfl rfl

private theorem receipt_0_14_2340_0 : fastPhase (bank 0 14).shape 179827 2340 73 1 0 1 0 = 1358443953466383867943811147619 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2340_0_join14

private theorem receipt_0_14_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 0 128 = 188050006989701242153623745536 := by decide +kernel
private theorem receipt_0_14_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 128 128 = 172119611044754164755506099200 := by decide +kernel
private theorem receipt_0_14_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 256 128 = 156670362698041157504614593536 := by decide +kernel
private theorem receipt_0_14_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 384 128 = 141694821106714491781048857600 := by decide +kernel
private theorem receipt_0_14_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 512 128 = 127185557403664426758158939136 := by decide +kernel
private theorem receipt_0_14_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 640 128 = 113135154691240162379107234816 := by decide +kernel
private theorem receipt_0_14_2340_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 768 128 = 99536208034970792333430420480 := by decide +kernel
private theorem receipt_0_14_2340_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 896 128 = 86381324457286257033601381376 := by decide +kernel
private theorem receipt_0_14_2340_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1024 128 = 73663122931238296591591142400 := by decide +kernel
private theorem receipt_0_14_2340_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1152 128 = 61374234399803296689941029773 := by decide +kernel
private theorem receipt_0_14_2340_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1280 128 = 49507311407426707567624613539 := by decide +kernel
private theorem receipt_0_14_2340_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1408 128 = 38055021083314839167596344830 := by decide +kernel
private theorem receipt_0_14_2340_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1536 128 = 27010010059361787255105928641 := by decide +kernel
private theorem receipt_0_14_2340_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1664 128 = 16364932648792773044229202434 := by decide +kernel
private theorem receipt_0_14_2340_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1792 128 = 6112455093633807793412039044 := by decide +kernel
private theorem receipt_0_14_2340_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1920 15 = 63047382779829472870008311 := by decide +kernel
private theorem receipt_0_14_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 0 256 = 360169618034455406909129844736 :=
  phaseBlock_append receipt_0_14_2340_1_part0 receipt_0_14_2340_1_part1 rfl rfl rfl
private theorem receipt_0_14_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 256 256 = 298365183804755649285663451136 :=
  phaseBlock_append receipt_0_14_2340_1_part2 receipt_0_14_2340_1_part3 rfl rfl rfl
private theorem receipt_0_14_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 0 512 = 658534801839211056194793295872 :=
  phaseBlock_append receipt_0_14_2340_1_join0 receipt_0_14_2340_1_join1 rfl rfl rfl
private theorem receipt_0_14_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 512 256 = 240320712094904589137266173952 :=
  phaseBlock_append receipt_0_14_2340_1_part4 receipt_0_14_2340_1_part5 rfl rfl rfl
private theorem receipt_0_14_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 768 256 = 185917532492257049367031801856 :=
  phaseBlock_append receipt_0_14_2340_1_part6 receipt_0_14_2340_1_part7 rfl rfl rfl
private theorem receipt_0_14_2340_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 512 512 = 426238244587161638504297975808 :=
  phaseBlock_append receipt_0_14_2340_1_join3 receipt_0_14_2340_1_join4 rfl rfl rfl
private theorem receipt_0_14_2340_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 0 1024 = 1084773046426372694699091271680 :=
  phaseBlock_append receipt_0_14_2340_1_join2 receipt_0_14_2340_1_join5 rfl rfl rfl
private theorem receipt_0_14_2340_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1024 256 = 135037357331041593281532172173 :=
  phaseBlock_append receipt_0_14_2340_1_part8 receipt_0_14_2340_1_part9 rfl rfl rfl
private theorem receipt_0_14_2340_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1280 256 = 87562332490741546735220958369 :=
  phaseBlock_append receipt_0_14_2340_1_part10 receipt_0_14_2340_1_part11 rfl rfl rfl
private theorem receipt_0_14_2340_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1024 512 = 222599689821783140016753130542 :=
  phaseBlock_append receipt_0_14_2340_1_join7 receipt_0_14_2340_1_join8 rfl rfl rfl
private theorem receipt_0_14_2340_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1536 256 = 43374942708154560299335131075 :=
  phaseBlock_append receipt_0_14_2340_1_part12 receipt_0_14_2340_1_part13 rfl rfl rfl
private theorem receipt_0_14_2340_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1792 143 = 6175502476413637266282047355 :=
  phaseBlock_append receipt_0_14_2340_1_part14 receipt_0_14_2340_1_part15 rfl rfl rfl
private theorem receipt_0_14_2340_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1536 399 = 49550445184568197565617178430 :=
  phaseBlock_append receipt_0_14_2340_1_join10 receipt_0_14_2340_1_join11 rfl rfl rfl
private theorem receipt_0_14_2340_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 1024 911 = 272150135006351337582370308972 :=
  phaseBlock_append receipt_0_14_2340_1_join9 receipt_0_14_2340_1_join12 rfl rfl rfl
private theorem receipt_0_14_2340_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179827 2340 73 1 0 1 1) 0 1935 = 1356923181432724032281461580652 :=
  phaseBlock_append receipt_0_14_2340_1_join6 receipt_0_14_2340_1_join13 rfl rfl rfl

private theorem receipt_0_14_2340_1 : fastPhase (bank 0 14).shape 179827 2340 73 1 0 1 1 = 1356923181432724032281461580652 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2340_1_join14

theorem receipt_0_14 : Checked (bank 0 14) 73 0 1 := by
  refine checked_from_values (bank 0 14) 73 0 1
    (P3_7_1.checked (bank 0 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_14_2339_0 receipt_0_14_2339_1 receipt_0_14_2340_0 receipt_0_14_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_14_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 0 128 = 169408035475042285480537989504 := by decide +kernel
private theorem receipt_1_14_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 128 128 = 154989573507030031797622235520 := by decide +kernel
private theorem receipt_1_14_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 256 128 = 141017507478179493669457305984 := by decide +kernel
private theorem receipt_1_14_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 384 128 = 127484535147885220704811278720 := by decide +kernel
private theorem receipt_1_14_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 512 128 = 114383377523769394605922099584 := by decide +kernel
private theorem receipt_1_14_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 640 128 = 101706778836566520684047524224 := by decide +kernel
private theorem receipt_1_14_2339_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 768 128 = 89447506515008119375015059840 := by decide +kernel
private theorem receipt_1_14_2339_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 896 128 = 77598351160707417754771906944 := by decide +kernel
private theorem receipt_1_14_2339_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1024 128 = 66152126523044041054934901120 := by decide +kernel
private theorem receipt_1_14_2339_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1152 128 = 55101669504144800382980137749 := by decide +kernel
private theorem receipt_1_14_2339_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1280 128 = 44439848984985497788263764560 := by decide +kernel
private theorem receipt_1_14_2339_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1408 128 = 34159558844206401154959166554 := by decide +kernel
private theorem receipt_1_14_2339_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1536 128 = 24253687026763549511859074274 := by decide +kernel
private theorem receipt_1_14_2339_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1664 128 = 14715140907533957270172178425 := by decide +kernel
private theorem receipt_1_14_2339_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1792 128 = 5536850909046005142624958134 := by decide +kernel
private theorem receipt_1_14_2339_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1920 15 = 64425955753916501193398382 := by decide +kernel
private theorem receipt_1_14_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 0 256 = 324397608982072317278160225024 :=
  phaseBlock_append receipt_1_14_2339_0_part0 receipt_1_14_2339_0_part1 rfl rfl rfl
private theorem receipt_1_14_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 256 256 = 268502042626064714374268584704 :=
  phaseBlock_append receipt_1_14_2339_0_part2 receipt_1_14_2339_0_part3 rfl rfl rfl
private theorem receipt_1_14_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 0 512 = 592899651608137031652428809728 :=
  phaseBlock_append receipt_1_14_2339_0_join0 receipt_1_14_2339_0_join1 rfl rfl rfl
private theorem receipt_1_14_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 512 256 = 216090156360335915289969623808 :=
  phaseBlock_append receipt_1_14_2339_0_part4 receipt_1_14_2339_0_part5 rfl rfl rfl
private theorem receipt_1_14_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 768 256 = 167045857675715537129786966784 :=
  phaseBlock_append receipt_1_14_2339_0_part6 receipt_1_14_2339_0_part7 rfl rfl rfl
private theorem receipt_1_14_2339_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 512 512 = 383136014036051452419756590592 :=
  phaseBlock_append receipt_1_14_2339_0_join3 receipt_1_14_2339_0_join4 rfl rfl rfl
private theorem receipt_1_14_2339_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 0 1024 = 976035665644188484072185400320 :=
  phaseBlock_append receipt_1_14_2339_0_join2 receipt_1_14_2339_0_join5 rfl rfl rfl
private theorem receipt_1_14_2339_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1024 256 = 121253796027188841437915038869 :=
  phaseBlock_append receipt_1_14_2339_0_part8 receipt_1_14_2339_0_part9 rfl rfl rfl
private theorem receipt_1_14_2339_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1280 256 = 78599407829191898943222931114 :=
  phaseBlock_append receipt_1_14_2339_0_part10 receipt_1_14_2339_0_part11 rfl rfl rfl
private theorem receipt_1_14_2339_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1024 512 = 199853203856380740381137969983 :=
  phaseBlock_append receipt_1_14_2339_0_join7 receipt_1_14_2339_0_join8 rfl rfl rfl
private theorem receipt_1_14_2339_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1536 256 = 38968827934297506782031252699 :=
  phaseBlock_append receipt_1_14_2339_0_part12 receipt_1_14_2339_0_part13 rfl rfl rfl
private theorem receipt_1_14_2339_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1792 143 = 5601276864799921643818356516 :=
  phaseBlock_append receipt_1_14_2339_0_part14 receipt_1_14_2339_0_part15 rfl rfl rfl
private theorem receipt_1_14_2339_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1536 399 = 44570104799097428425849609215 :=
  phaseBlock_append receipt_1_14_2339_0_join10 receipt_1_14_2339_0_join11 rfl rfl rfl
private theorem receipt_1_14_2339_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 1024 911 = 244423308655478168806987579198 :=
  phaseBlock_append receipt_1_14_2339_0_join9 receipt_1_14_2339_0_join12 rfl rfl rfl
private theorem receipt_1_14_2339_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 0) 0 1935 = 1220458974299666652879172979518 :=
  phaseBlock_append receipt_1_14_2339_0_join6 receipt_1_14_2339_0_join13 rfl rfl rfl

private theorem receipt_1_14_2339_0 : fastPhase (bank 1 14).shape 179827 2339 73 1 0 2 0 = 1220458974299666652879172979518 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2339_0_join14

private theorem receipt_1_14_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 0 128 = 169295119836206739351988762176 := by decide +kernel
private theorem receipt_1_14_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 128 128 = 154880060624113947508148573760 := by decide +kernel
private theorem receipt_1_14_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 256 128 = 140911341989147163139888297536 := by decide +kernel
private theorem receipt_1_14_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 384 128 = 127381661868020639360084923968 := by decide +kernel
private theorem receipt_1_14_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 512 128 = 114283741445483905664096597568 := by decide +kernel
private theorem receipt_1_14_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 640 128 = 101610325129206459445312558656 := by decide +kernel
private theorem receipt_1_14_2339_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 768 128 = 89354180524662457510703085120 := by decide +kernel
private theorem receipt_1_14_2339_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 896 128 = 77508098410015407596369434176 := by decide +kernel
private theorem receipt_1_14_2339_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1024 128 = 66064892711002859883093784128 := by decide +kernel
private theorem receipt_1_14_2339_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1152 128 = 55017400505870747944269879858 := by decide +kernel
private theorem receipt_1_14_2339_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1280 128 = 44358490835696671958124693400 := by decide +kernel
private theorem receipt_1_14_2339_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1408 128 = 34081057718832039485466498462 := by decide +kernel
private theorem receipt_1_14_2339_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1536 128 = 24177989271265463243087179836 := by decide +kernel
private theorem receipt_1_14_2339_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1664 128 = 14642193043535807314356286833 := by decide +kernel
private theorem receipt_1_14_2339_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1792 128 = 5466599633715818770932143808 := by decide +kernel
private theorem receipt_1_14_2339_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1920 15 = 56367447553934428472962953 := by decide +kernel
private theorem receipt_1_14_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 0 256 = 324175180460320686860137335936 :=
  phaseBlock_append receipt_1_14_2339_1_part0 receipt_1_14_2339_1_part1 rfl rfl rfl
private theorem receipt_1_14_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 256 256 = 268293003857167802499973221504 :=
  phaseBlock_append receipt_1_14_2339_1_part2 receipt_1_14_2339_1_part3 rfl rfl rfl
private theorem receipt_1_14_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 0 512 = 592468184317488489360110557440 :=
  phaseBlock_append receipt_1_14_2339_1_join0 receipt_1_14_2339_1_join1 rfl rfl rfl
private theorem receipt_1_14_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 512 256 = 215894066574690365109409156224 :=
  phaseBlock_append receipt_1_14_2339_1_part4 receipt_1_14_2339_1_part5 rfl rfl rfl
private theorem receipt_1_14_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 768 256 = 166862278934677865107072519296 :=
  phaseBlock_append receipt_1_14_2339_1_part6 receipt_1_14_2339_1_part7 rfl rfl rfl
private theorem receipt_1_14_2339_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 512 512 = 382756345509368230216481675520 :=
  phaseBlock_append receipt_1_14_2339_1_join3 receipt_1_14_2339_1_join4 rfl rfl rfl
private theorem receipt_1_14_2339_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 0 1024 = 975224529826856719576592232960 :=
  phaseBlock_append receipt_1_14_2339_1_join2 receipt_1_14_2339_1_join5 rfl rfl rfl
private theorem receipt_1_14_2339_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1024 256 = 121082293216873607827363663986 :=
  phaseBlock_append receipt_1_14_2339_1_part8 receipt_1_14_2339_1_part9 rfl rfl rfl
private theorem receipt_1_14_2339_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1280 256 = 78439548554528711443591191862 :=
  phaseBlock_append receipt_1_14_2339_1_part10 receipt_1_14_2339_1_part11 rfl rfl rfl
private theorem receipt_1_14_2339_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1024 512 = 199521841771402319270954855848 :=
  phaseBlock_append receipt_1_14_2339_1_join7 receipt_1_14_2339_1_join8 rfl rfl rfl
private theorem receipt_1_14_2339_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1536 256 = 38820182314801270557443466669 :=
  phaseBlock_append receipt_1_14_2339_1_part12 receipt_1_14_2339_1_part13 rfl rfl rfl
private theorem receipt_1_14_2339_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1792 143 = 5522967081269753199405106761 :=
  phaseBlock_append receipt_1_14_2339_1_part14 receipt_1_14_2339_1_part15 rfl rfl rfl
private theorem receipt_1_14_2339_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1536 399 = 44343149396071023756848573430 :=
  phaseBlock_append receipt_1_14_2339_1_join10 receipt_1_14_2339_1_join11 rfl rfl rfl
private theorem receipt_1_14_2339_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 1024 911 = 243864991167473343027803429278 :=
  phaseBlock_append receipt_1_14_2339_1_join9 receipt_1_14_2339_1_join12 rfl rfl rfl
private theorem receipt_1_14_2339_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2339 73 1 0 2 1) 0 1935 = 1219089520994330062604395662238 :=
  phaseBlock_append receipt_1_14_2339_1_join6 receipt_1_14_2339_1_join13 rfl rfl rfl

private theorem receipt_1_14_2339_1 : fastPhase (bank 1 14).shape 179827 2339 73 1 0 2 1 = 1219089520994330062604395662238 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2339_1_join14

private theorem receipt_1_14_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 0 128 = 169409556104571933927339200352 := by decide +kernel
private theorem receipt_1_14_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 128 128 = 154990913121508724069487558496 := by decide +kernel
private theorem receipt_1_14_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 256 128 = 141018678422771458368944631648 := by decide +kernel
private theorem receipt_1_14_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 384 128 = 127485549519744397024694476640 := by decide +kernel
private theorem receipt_1_14_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 512 128 = 114384247172847013449309933408 := by decide +kernel
private theorem receipt_1_14_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 640 128 = 101707515366417806175200345952 := by decide +kernel
private theorem receipt_1_14_2340_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 768 128 = 89448121283598110760859283296 := by decide +kernel
private theorem receipt_1_14_2340_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 896 128 = 77598855281215911697112260448 := by decide +kernel
private theorem receipt_1_14_2340_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1024 128 = 66152530864669654313364459360 := by decide +kernel
private theorem receipt_1_14_2340_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1152 128 = 55101984685774607497729830006 := by decide +kernel
private theorem receipt_1_14_2340_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1280 128 = 44440085167657936672715589451 := by decide +kernel
private theorem receipt_1_14_2340_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1408 128 = 34159726188730858211516203734 := by decide +kernel
private theorem receipt_1_14_2340_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1536 128 = 24253795599363834616254458150 := by decide +kernel
private theorem receipt_1_14_2340_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1664 128 = 14715200509998446673011929431 := by decide +kernel
private theorem receipt_1_14_2340_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1792 128 = 5536871084717434429703982948 := by decide +kernel
private theorem receipt_1_14_2340_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1920 15 = 64426170954118212187839921 := by decide +kernel
private theorem receipt_1_14_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 0 256 = 324400469226080657996826758848 :=
  phaseBlock_append receipt_1_14_2340_0_part0 receipt_1_14_2340_0_part1 rfl rfl rfl
private theorem receipt_1_14_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 256 256 = 268504227942515855393639108288 :=
  phaseBlock_append receipt_1_14_2340_0_part2 receipt_1_14_2340_0_part3 rfl rfl rfl
private theorem receipt_1_14_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 0 512 = 592904697168596513390465867136 :=
  phaseBlock_append receipt_1_14_2340_0_join0 receipt_1_14_2340_0_join1 rfl rfl rfl
private theorem receipt_1_14_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 512 256 = 216091762539264819624510279360 :=
  phaseBlock_append receipt_1_14_2340_0_part4 receipt_1_14_2340_0_part5 rfl rfl rfl
private theorem receipt_1_14_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 768 256 = 167046976564814022457971543744 :=
  phaseBlock_append receipt_1_14_2340_0_part6 receipt_1_14_2340_0_part7 rfl rfl rfl
private theorem receipt_1_14_2340_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 512 512 = 383138739104078842082481823104 :=
  phaseBlock_append receipt_1_14_2340_0_join3 receipt_1_14_2340_0_join4 rfl rfl rfl
private theorem receipt_1_14_2340_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 0 1024 = 976043436272675355472947690240 :=
  phaseBlock_append receipt_1_14_2340_0_join2 receipt_1_14_2340_0_join5 rfl rfl rfl
private theorem receipt_1_14_2340_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1024 256 = 121254515550444261811094289366 :=
  phaseBlock_append receipt_1_14_2340_0_part8 receipt_1_14_2340_0_part9 rfl rfl rfl
private theorem receipt_1_14_2340_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1280 256 = 78599811356388794884231793185 :=
  phaseBlock_append receipt_1_14_2340_0_part10 receipt_1_14_2340_0_part11 rfl rfl rfl
private theorem receipt_1_14_2340_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1024 512 = 199854326906833056695326082551 :=
  phaseBlock_append receipt_1_14_2340_0_join7 receipt_1_14_2340_0_join8 rfl rfl rfl
private theorem receipt_1_14_2340_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1536 256 = 38968996109362281289266387581 :=
  phaseBlock_append receipt_1_14_2340_0_part12 receipt_1_14_2340_0_part13 rfl rfl rfl
private theorem receipt_1_14_2340_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1792 143 = 5601297255671552641891822869 :=
  phaseBlock_append receipt_1_14_2340_0_part14 receipt_1_14_2340_0_part15 rfl rfl rfl
private theorem receipt_1_14_2340_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1536 399 = 44570293365033833931158210450 :=
  phaseBlock_append receipt_1_14_2340_0_join10 receipt_1_14_2340_0_join11 rfl rfl rfl
private theorem receipt_1_14_2340_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 1024 911 = 244424620271866890626484293001 :=
  phaseBlock_append receipt_1_14_2340_0_join9 receipt_1_14_2340_0_join12 rfl rfl rfl
private theorem receipt_1_14_2340_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 0) 0 1935 = 1220468056544542246099431983241 :=
  phaseBlock_append receipt_1_14_2340_0_join6 receipt_1_14_2340_0_join13 rfl rfl rfl

private theorem receipt_1_14_2340_0 : fastPhase (bank 1 14).shape 179827 2340 73 1 0 2 0 = 1220468056544542246099431983241 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2340_0_join14

private theorem receipt_1_14_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 0 128 = 169296639634769448475671142368 := by decide +kernel
private theorem receipt_1_14_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 128 128 = 154881399456692814935640133600 := by decide +kernel
private theorem receipt_1_14_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 256 128 = 140912512199725383167443763168 := by decide +kernel
private theorem receipt_1_14_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 384 128 = 127382675552575546477421440992 := by decide +kernel
private theorem receipt_1_14_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 512 128 = 114284610452794550451832414176 := by decide +kernel
private theorem receipt_1_14_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 640 128 = 101611061061660304863103487968 := by decide +kernel
private theorem receipt_1_14_2340_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 768 128 = 89354794739061195576076746720 := by decide +kernel
private theorem receipt_1_14_2340_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 896 128 = 77508602018379896454257274848 := by decide +kernel
private theorem receipt_1_14_2340_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1024 128 = 66065296581377181266060877792 := by decide +kernel
private theorem receipt_1_14_2340_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1152 128 = 55017715256002739758640135544 := by decide +kernel
private theorem receipt_1_14_2340_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1280 128 = 44358726625870172079925196851 := by decide +kernel
private theorem receipt_1_14_2340_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1408 128 = 34081224708881860921020765584 := by decide +kernel
private theorem receipt_1_14_2340_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1536 128 = 24178097526219520808986360464 := by decide +kernel
private theorem receipt_1_14_2340_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1664 128 = 14642252363998895750487881865 := by decide +kernel
private theorem receipt_1_14_2340_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1792 128 = 5466619561859509458661554556 := by decide +kernel
private theorem receipt_1_14_2340_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1920 15 = 56367635947766222639053301 := by decide +kernel
private theorem receipt_1_14_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 0 256 = 324178039091462263411311275968 :=
  phaseBlock_append receipt_1_14_2340_1_part0 receipt_1_14_2340_1_part1 rfl rfl rfl
private theorem receipt_1_14_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 256 256 = 268295187752300929644865204160 :=
  phaseBlock_append receipt_1_14_2340_1_part2 receipt_1_14_2340_1_part3 rfl rfl rfl
private theorem receipt_1_14_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 0 512 = 592473226843763193056176480128 :=
  phaseBlock_append receipt_1_14_2340_1_join0 receipt_1_14_2340_1_join1 rfl rfl rfl
private theorem receipt_1_14_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 512 256 = 215895671514454855314935902144 :=
  phaseBlock_append receipt_1_14_2340_1_part4 receipt_1_14_2340_1_part5 rfl rfl rfl
private theorem receipt_1_14_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 768 256 = 166863396757441092030334021568 :=
  phaseBlock_append receipt_1_14_2340_1_part6 receipt_1_14_2340_1_part7 rfl rfl rfl
private theorem receipt_1_14_2340_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 512 512 = 382759068271895947345269923712 :=
  phaseBlock_append receipt_1_14_2340_1_join3 receipt_1_14_2340_1_join4 rfl rfl rfl
private theorem receipt_1_14_2340_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 0 1024 = 975232295115659140401446403840 :=
  phaseBlock_append receipt_1_14_2340_1_join2 receipt_1_14_2340_1_join5 rfl rfl rfl
private theorem receipt_1_14_2340_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1024 256 = 121083011837379921024701013336 :=
  phaseBlock_append receipt_1_14_2340_1_part8 receipt_1_14_2340_1_part9 rfl rfl rfl
private theorem receipt_1_14_2340_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1280 256 = 78439951334752033000945962435 :=
  phaseBlock_append receipt_1_14_2340_1_part10 receipt_1_14_2340_1_part11 rfl rfl rfl
private theorem receipt_1_14_2340_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1024 512 = 199522963172131954025646975771 :=
  phaseBlock_append receipt_1_14_2340_1_join7 receipt_1_14_2340_1_join8 rfl rfl rfl
private theorem receipt_1_14_2340_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1536 256 = 38820349890218416559474242329 :=
  phaseBlock_append receipt_1_14_2340_1_part12 receipt_1_14_2340_1_part13 rfl rfl rfl
private theorem receipt_1_14_2340_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1792 143 = 5522987197807275681300607857 :=
  phaseBlock_append receipt_1_14_2340_1_part14 receipt_1_14_2340_1_part15 rfl rfl rfl
private theorem receipt_1_14_2340_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1536 399 = 44343337088025692240774850186 :=
  phaseBlock_append receipt_1_14_2340_1_join10 receipt_1_14_2340_1_join11 rfl rfl rfl
private theorem receipt_1_14_2340_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 1024 911 = 243866300260157646266421825957 :=
  phaseBlock_append receipt_1_14_2340_1_join9 receipt_1_14_2340_1_join12 rfl rfl rfl
private theorem receipt_1_14_2340_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179827 2340 73 1 0 2 1) 0 1935 = 1219098595375816786667868229797 :=
  phaseBlock_append receipt_1_14_2340_1_join6 receipt_1_14_2340_1_join13 rfl rfl rfl

private theorem receipt_1_14_2340_1 : fastPhase (bank 1 14).shape 179827 2340 73 1 0 2 1 = 1219098595375816786667868229797 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2340_1_join14

theorem receipt_1_14 : Checked (bank 1 14) 73 0 2 := by
  refine checked_from_values (bank 1 14) 73 0 2
    (P3_7_1.checked (bank 1 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_14_2339_0 receipt_1_14_2339_1 receipt_1_14_2340_0 receipt_1_14_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_14_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 0 128 = 90900577546896803066449507008 := by decide +kernel
private theorem receipt_2_14_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 128 128 = 82880498002256339967162045120 := by decide +kernel
private theorem receipt_2_14_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 256 128 = 75151275442951405890303914688 := by decide +kernel
private theorem receipt_2_14_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 384 128 = 67706522492627410266719064768 := by decide +kernel
private theorem receipt_2_14_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 512 128 = 60539921018346266891038929600 := by decide +kernel
private theorem receipt_2_14_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 640 128 = 53645221822923864987169215168 := by decide +kernel
private theorem receipt_2_14_2339_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 768 128 = 47016244337267540273776685760 := by decide +kernel
private theorem receipt_2_14_2339_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 896 128 = 40646876312713546029775950528 := by decide +kernel
private theorem receipt_2_14_2339_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1024 128 = 34531073513364524159816250048 := by decide +kernel
private theorem receipt_2_14_2339_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1152 128 = 28662859424055754926411431817 := by decide +kernel
private theorem receipt_2_14_2339_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1280 128 = 23036329527269896243043675476 := by decide +kernel
private theorem receipt_2_14_2339_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1408 128 = 17645647332495447247734933888 := by decide +kernel
private theorem receipt_2_14_2339_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1536 128 = 12485028133752451629991009665 := by decide +kernel
private theorem receipt_2_14_2339_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1664 128 = 7548751986647372537289149376 := by decide +kernel
private theorem receipt_2_14_2339_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1792 128 = 2831165296809753402441042468 := by decide +kernel
private theorem receipt_2_14_2339_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1920 15 = 32864249436056744652892518 := by decide +kernel
private theorem receipt_2_14_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 0 256 = 173781075549153143033611552128 :=
  phaseBlock_append receipt_2_14_2339_0_part0 receipt_2_14_2339_0_part1 rfl rfl rfl
private theorem receipt_2_14_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 256 256 = 142857797935578816157022979456 :=
  phaseBlock_append receipt_2_14_2339_0_part2 receipt_2_14_2339_0_part3 rfl rfl rfl
private theorem receipt_2_14_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 0 512 = 316638873484731959190634531584 :=
  phaseBlock_append receipt_2_14_2339_0_join0 receipt_2_14_2339_0_join1 rfl rfl rfl
private theorem receipt_2_14_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 512 256 = 114185142841270131878208144768 :=
  phaseBlock_append receipt_2_14_2339_0_part4 receipt_2_14_2339_0_part5 rfl rfl rfl
private theorem receipt_2_14_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 768 256 = 87663120649981086303552636288 :=
  phaseBlock_append receipt_2_14_2339_0_part6 receipt_2_14_2339_0_part7 rfl rfl rfl
private theorem receipt_2_14_2339_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 512 512 = 201848263491251218181760781056 :=
  phaseBlock_append receipt_2_14_2339_0_join3 receipt_2_14_2339_0_join4 rfl rfl rfl
private theorem receipt_2_14_2339_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 0 1024 = 518487136975983177372395312640 :=
  phaseBlock_append receipt_2_14_2339_0_join2 receipt_2_14_2339_0_join5 rfl rfl rfl
private theorem receipt_2_14_2339_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1024 256 = 63193932937420279086227681865 :=
  phaseBlock_append receipt_2_14_2339_0_part8 receipt_2_14_2339_0_part9 rfl rfl rfl
private theorem receipt_2_14_2339_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1280 256 = 40681976859765343490778609364 :=
  phaseBlock_append receipt_2_14_2339_0_part10 receipt_2_14_2339_0_part11 rfl rfl rfl
private theorem receipt_2_14_2339_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1024 512 = 103875909797185622577006291229 :=
  phaseBlock_append receipt_2_14_2339_0_join7 receipt_2_14_2339_0_join8 rfl rfl rfl
private theorem receipt_2_14_2339_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1536 256 = 20033780120399824167280159041 :=
  phaseBlock_append receipt_2_14_2339_0_part12 receipt_2_14_2339_0_part13 rfl rfl rfl
private theorem receipt_2_14_2339_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1792 143 = 2864029546245810147093934986 :=
  phaseBlock_append receipt_2_14_2339_0_part14 receipt_2_14_2339_0_part15 rfl rfl rfl
private theorem receipt_2_14_2339_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1536 399 = 22897809666645634314374094027 :=
  phaseBlock_append receipt_2_14_2339_0_join10 receipt_2_14_2339_0_join11 rfl rfl rfl
private theorem receipt_2_14_2339_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 1024 911 = 126773719463831256891380385256 :=
  phaseBlock_append receipt_2_14_2339_0_join9 receipt_2_14_2339_0_join12 rfl rfl rfl
private theorem receipt_2_14_2339_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 0) 0 1935 = 645260856439814434263775697896 :=
  phaseBlock_append receipt_2_14_2339_0_join6 receipt_2_14_2339_0_join13 rfl rfl rfl

private theorem receipt_2_14_2339_0 : fastPhase (bank 2 14).shape 179827 2339 73 1 0 7 0 = 645260856439814434263775697896 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2339_0_join14

private theorem receipt_2_14_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 0 128 = 90837569613103235535970720320 := by decide +kernel
private theorem receipt_2_14_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 128 128 = 82819724156721542193385077312 := by decide +kernel
private theorem receipt_2_14_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 256 128 = 75092686877638454378544863808 := by decide +kernel
private theorem receipt_2_14_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 384 128 = 67650070929086198362460830272 := by decide +kernel
private theorem receipt_2_14_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 512 128 = 60485558705357147320319466048 := by decide +kernel
private theorem receipt_2_14_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 640 128 = 53592901534141292396969785920 := by decide +kernel
private theorem receipt_2_14_2339_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 768 128 = 46965919368863713772410116672 := by decide +kernel
private theorem receipt_2_14_2339_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 896 128 = 40598500481022051727274883648 := by decide +kernel
private theorem receipt_2_14_2339_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1024 128 = 34484601152523977708321397312 := by decide +kernel
private theorem receipt_2_14_2339_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1152 128 = 28618245383628898067165003403 := by decide +kernel
private theorem receipt_2_14_2339_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1280 128 = 22993529161565044676269908103 := by decide +kernel
private theorem receipt_2_14_2339_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1408 128 = 17604616487856743210450995584 := by decide +kernel
private theorem receipt_2_14_2339_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1536 128 = 12445723163096318804660883888 := by decide +kernel
private theorem receipt_2_14_2339_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1664 128 = 7511129749664281836212613237 := by decide +kernel
private theorem receipt_2_14_2339_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1792 128 = 2795183157641918611302585048 := by decide +kernel
private theorem receipt_2_14_2339_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1920 15 = 28753002079780979088386160 := by decide +kernel
private theorem receipt_2_14_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 0 256 = 173657293769824777729355797632 :=
  phaseBlock_append receipt_2_14_2339_1_part0 receipt_2_14_2339_1_part1 rfl rfl rfl
private theorem receipt_2_14_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 256 256 = 142742757806724652741005694080 :=
  phaseBlock_append receipt_2_14_2339_1_part2 receipt_2_14_2339_1_part3 rfl rfl rfl
private theorem receipt_2_14_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 0 512 = 316400051576549430470361491712 :=
  phaseBlock_append receipt_2_14_2339_1_join0 receipt_2_14_2339_1_join1 rfl rfl rfl
private theorem receipt_2_14_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 512 256 = 114078460239498439717289251968 :=
  phaseBlock_append receipt_2_14_2339_1_part4 receipt_2_14_2339_1_part5 rfl rfl rfl
private theorem receipt_2_14_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 768 256 = 87564419849885765499685000320 :=
  phaseBlock_append receipt_2_14_2339_1_part6 receipt_2_14_2339_1_part7 rfl rfl rfl
private theorem receipt_2_14_2339_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 512 512 = 201642880089384205216974252288 :=
  phaseBlock_append receipt_2_14_2339_1_join3 receipt_2_14_2339_1_join4 rfl rfl rfl
private theorem receipt_2_14_2339_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 0 1024 = 518042931665933635687335744000 :=
  phaseBlock_append receipt_2_14_2339_1_join2 receipt_2_14_2339_1_join5 rfl rfl rfl
private theorem receipt_2_14_2339_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1024 256 = 63102846536152875775486400715 :=
  phaseBlock_append receipt_2_14_2339_1_part8 receipt_2_14_2339_1_part9 rfl rfl rfl
private theorem receipt_2_14_2339_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1280 256 = 40598145649421787886720903687 :=
  phaseBlock_append receipt_2_14_2339_1_part10 receipt_2_14_2339_1_part11 rfl rfl rfl
private theorem receipt_2_14_2339_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1024 512 = 103700992185574663662207304402 :=
  phaseBlock_append receipt_2_14_2339_1_join7 receipt_2_14_2339_1_join8 rfl rfl rfl
private theorem receipt_2_14_2339_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1536 256 = 19956852912760600640873497125 :=
  phaseBlock_append receipt_2_14_2339_1_part12 receipt_2_14_2339_1_part13 rfl rfl rfl
private theorem receipt_2_14_2339_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1792 143 = 2823936159721699590390971208 :=
  phaseBlock_append receipt_2_14_2339_1_part14 receipt_2_14_2339_1_part15 rfl rfl rfl
private theorem receipt_2_14_2339_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1536 399 = 22780789072482300231264468333 :=
  phaseBlock_append receipt_2_14_2339_1_join10 receipt_2_14_2339_1_join11 rfl rfl rfl
private theorem receipt_2_14_2339_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 1024 911 = 126481781258056963893471772735 :=
  phaseBlock_append receipt_2_14_2339_1_join9 receipt_2_14_2339_1_join12 rfl rfl rfl
private theorem receipt_2_14_2339_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2339 73 1 0 7 1) 0 1935 = 644524712923990599580807516735 :=
  phaseBlock_append receipt_2_14_2339_1_join6 receipt_2_14_2339_1_join13 rfl rfl rfl

private theorem receipt_2_14_2339_1 : fastPhase (bank 2 14).shape 179827 2339 73 1 0 7 1 = 644524712923990599580807516735 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2339_1_join14

private theorem receipt_2_14_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 0 128 = 90901393491337640866382878176 := by decide +kernel
private theorem receipt_2_14_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 128 128 = 82881214367516189991722730976 := by decide +kernel
private theorem receipt_2_14_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 256 128 = 75151899471983613150623266272 := by decide +kernel
private theorem receipt_2_14_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 384 128 = 67707061228224851787886110176 := by decide +kernel
private theorem receipt_2_14_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 512 128 = 60540381305485140413776844256 := by decide +kernel
private theorem receipt_2_14_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 640 128 = 53645610311096702455559587296 := by decide +kernel
private theorem receipt_2_14_2340_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 768 128 = 47016567482805446109031577056 := by decide +kernel
private theorem receipt_2_14_2340_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 896 128 = 40647140381097660190057752032 := by decide +kernel
private theorem receipt_2_14_2340_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1024 128 = 34531284581526709986105333216 := by decide +kernel
private theorem receipt_2_14_2340_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1152 128 = 28663023378963937465126369074 := by decide +kernel
private theorem receipt_2_14_2340_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1280 128 = 23036451960289715214618252442 := by decide +kernel
private theorem receipt_2_14_2340_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1408 128 = 17645733779055666325122904887 := by decide +kernel
private theorem receipt_2_14_2340_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1536 128 = 12485084025037560444251337716 := by decide +kernel
private theorem receipt_2_14_2340_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1664 128 = 7548782563187729648840450982 := by decide +kernel
private theorem receipt_2_14_2340_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1792 128 = 2831175613554623089312173528 := by decide +kernel
private theorem receipt_2_14_2340_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1920 15 = 32864359211624710236766548 := by decide +kernel
private theorem receipt_2_14_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 0 256 = 173782607858853830858105609152 :=
  phaseBlock_append receipt_2_14_2340_0_part0 receipt_2_14_2340_0_part1 rfl rfl rfl
private theorem receipt_2_14_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 256 256 = 142858960700208464938509376448 :=
  phaseBlock_append receipt_2_14_2340_0_part2 receipt_2_14_2340_0_part3 rfl rfl rfl
private theorem receipt_2_14_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 0 512 = 316641568559062295796614985600 :=
  phaseBlock_append receipt_2_14_2340_0_join0 receipt_2_14_2340_0_join1 rfl rfl rfl
private theorem receipt_2_14_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 512 256 = 114185991616581842869336431552 :=
  phaseBlock_append receipt_2_14_2340_0_part4 receipt_2_14_2340_0_part5 rfl rfl rfl
private theorem receipt_2_14_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 768 256 = 87663707863903106299089329088 :=
  phaseBlock_append receipt_2_14_2340_0_part6 receipt_2_14_2340_0_part7 rfl rfl rfl
private theorem receipt_2_14_2340_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 512 512 = 201849699480484949168425760640 :=
  phaseBlock_append receipt_2_14_2340_0_join3 receipt_2_14_2340_0_join4 rfl rfl rfl
private theorem receipt_2_14_2340_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 0 1024 = 518491268039547244965040746240 :=
  phaseBlock_append receipt_2_14_2340_0_join2 receipt_2_14_2340_0_join5 rfl rfl rfl
private theorem receipt_2_14_2340_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1024 256 = 63194307960490647451231702290 :=
  phaseBlock_append receipt_2_14_2340_0_part8 receipt_2_14_2340_0_part9 rfl rfl rfl
private theorem receipt_2_14_2340_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1280 256 = 40682185739345381539741157329 :=
  phaseBlock_append receipt_2_14_2340_0_part10 receipt_2_14_2340_0_part11 rfl rfl rfl
private theorem receipt_2_14_2340_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1024 512 = 103876493699836028990972859619 :=
  phaseBlock_append receipt_2_14_2340_0_join7 receipt_2_14_2340_0_join8 rfl rfl rfl
private theorem receipt_2_14_2340_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1536 256 = 20033866588225290093091788698 :=
  phaseBlock_append receipt_2_14_2340_0_part12 receipt_2_14_2340_0_part13 rfl rfl rfl
private theorem receipt_2_14_2340_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1792 143 = 2864039972766247799548940076 :=
  phaseBlock_append receipt_2_14_2340_0_part14 receipt_2_14_2340_0_part15 rfl rfl rfl
private theorem receipt_2_14_2340_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1536 399 = 22897906560991537892640728774 :=
  phaseBlock_append receipt_2_14_2340_0_join10 receipt_2_14_2340_0_join11 rfl rfl rfl
private theorem receipt_2_14_2340_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 1024 911 = 126774400260827566883613588393 :=
  phaseBlock_append receipt_2_14_2340_0_join9 receipt_2_14_2340_0_join12 rfl rfl rfl
private theorem receipt_2_14_2340_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 0) 0 1935 = 645265668300374811848654334633 :=
  phaseBlock_append receipt_2_14_2340_0_join6 receipt_2_14_2340_0_join13 rfl rfl rfl

private theorem receipt_2_14_2340_0 : fastPhase (bank 2 14).shape 179827 2340 73 1 0 7 0 = 645265668300374811848654334633 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2340_0_join14

private theorem receipt_2_14_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 0 128 = 90838385089936268500016823072 := by decide +kernel
private theorem receipt_2_14_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 128 128 = 82820440084735207185838402336 := by decide +kernel
private theorem receipt_2_14_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 256 128 = 75093310498795745720437365536 := by decide +kernel
private theorem receipt_2_14_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 384 128 = 67650609285202620997192862496 := by decide +kernel
private theorem receipt_2_14_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 512 128 = 60486018640444441537503410976 := by decide +kernel
private theorem receipt_2_14_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 640 128 = 53593289696740383342321478432 := by decide +kernel
private theorem receipt_2_14_2340_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 768 128 = 46966242214366885743688063776 := by decide +kernel
private theorem receipt_2_14_2340_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 896 128 = 40598764273984347256267279136 := by decide +kernel
private theorem receipt_2_14_2340_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1024 128 = 34484811968963821428880931616 := by decide +kernel
private theorem receipt_2_14_2340_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1152 128 = 28618409109619132749698708574 := by decide +kernel
private theorem receipt_2_14_2340_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1280 128 = 22993651387788781992137297617 := by decide +kernel
private theorem receipt_2_14_2340_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1408 128 = 17604702748951402282087392758 := by decide +kernel
private theorem receipt_2_14_2340_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1536 128 = 12445778889348213797042308674 := by decide +kernel
private theorem receipt_2_14_2340_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1664 128 = 7511160180722687816096959245 := by decide +kernel
private theorem receipt_2_14_2340_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1792 128 = 2795193347591952097854134014 := by decide +kernel
private theorem receipt_2_14_2340_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1920 15 = 28753098179397403596603632 := by decide +kernel
private theorem receipt_2_14_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 0 256 = 173658825174671475685855225408 :=
  phaseBlock_append receipt_2_14_2340_1_part0 receipt_2_14_2340_1_part1 rfl rfl rfl
private theorem receipt_2_14_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 256 256 = 142743919783998366717630228032 :=
  phaseBlock_append receipt_2_14_2340_1_part2 receipt_2_14_2340_1_part3 rfl rfl rfl
private theorem receipt_2_14_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 0 512 = 316402744958669842403485453440 :=
  phaseBlock_append receipt_2_14_2340_1_join0 receipt_2_14_2340_1_join1 rfl rfl rfl
private theorem receipt_2_14_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 512 256 = 114079308337184824879824889408 :=
  phaseBlock_append receipt_2_14_2340_1_part4 receipt_2_14_2340_1_part5 rfl rfl rfl
private theorem receipt_2_14_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 768 256 = 87565006488351232999955342912 :=
  phaseBlock_append receipt_2_14_2340_1_part6 receipt_2_14_2340_1_part7 rfl rfl rfl
private theorem receipt_2_14_2340_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 512 512 = 201644314825536057879780232320 :=
  phaseBlock_append receipt_2_14_2340_1_join3 receipt_2_14_2340_1_join4 rfl rfl rfl
private theorem receipt_2_14_2340_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 0 1024 = 518047059784205900283265685760 :=
  phaseBlock_append receipt_2_14_2340_1_join2 receipt_2_14_2340_1_join5 rfl rfl rfl
private theorem receipt_2_14_2340_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1024 256 = 63103221078582954178579640190 :=
  phaseBlock_append receipt_2_14_2340_1_part8 receipt_2_14_2340_1_part9 rfl rfl rfl
private theorem receipt_2_14_2340_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1280 256 = 40598354136740184274224690375 :=
  phaseBlock_append receipt_2_14_2340_1_part10 receipt_2_14_2340_1_part11 rfl rfl rfl
private theorem receipt_2_14_2340_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1024 512 = 103701575215323138452804330565 :=
  phaseBlock_append receipt_2_14_2340_1_join7 receipt_2_14_2340_1_join8 rfl rfl rfl
private theorem receipt_2_14_2340_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1536 256 = 19956939070070901613139267919 :=
  phaseBlock_append receipt_2_14_2340_1_part12 receipt_2_14_2340_1_part13 rfl rfl rfl
private theorem receipt_2_14_2340_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1792 143 = 2823946445771349501450737646 :=
  phaseBlock_append receipt_2_14_2340_1_part14 receipt_2_14_2340_1_part15 rfl rfl rfl
private theorem receipt_2_14_2340_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1536 399 = 22780885515842251114590005565 :=
  phaseBlock_append receipt_2_14_2340_1_join10 receipt_2_14_2340_1_join11 rfl rfl rfl
private theorem receipt_2_14_2340_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 1024 911 = 126482460731165389567394336130 :=
  phaseBlock_append receipt_2_14_2340_1_join9 receipt_2_14_2340_1_join12 rfl rfl rfl
private theorem receipt_2_14_2340_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179827 2340 73 1 0 7 1) 0 1935 = 644529520515371289850660021890 :=
  phaseBlock_append receipt_2_14_2340_1_join6 receipt_2_14_2340_1_join13 rfl rfl rfl

private theorem receipt_2_14_2340_1 : fastPhase (bank 2 14).shape 179827 2340 73 1 0 7 1 = 644529520515371289850660021890 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2340_1_join14

theorem receipt_2_14 : Checked (bank 2 14) 73 0 7 := by
  refine checked_from_values (bank 2 14) 73 0 7
    (P3_7_1.checked (bank 2 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_14_2339_0 receipt_2_14_2339_1 receipt_2_14_2340_0 receipt_2_14_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_14_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 0 128 = 21330424901831439610917101376 := by decide +kernel
private theorem receipt_3_14_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 128 128 = 19546953317054718672366477120 := by decide +kernel
private theorem receipt_3_14_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 256 128 = 17812851194365842261727321920 := by decide +kernel
private theorem receipt_3_14_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 384 128 = 16129072156085524759857733440 := by decide +kernel
private theorem receipt_3_14_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 512 128 = 14496564194140908175543443264 := by decide +kernel
private theorem receipt_3_14_2339_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 640 128 = 12916269679537502975067168576 := by decide +kernel
private theorem receipt_3_14_2339_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 768 128 = 11389125371831128911777963840 := by decide +kernel
private theorem receipt_3_14_2339_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 896 128 = 9916062428599855855660572480 := by decide +kernel
private theorem receipt_3_14_2339_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1024 128 = 8498006414915944622904778560 := by decide +kernel
private theorem receipt_3_14_2339_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1152 128 = 7135877312817787805474758464 := by decide +kernel
private theorem receipt_3_14_2339_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1280 128 = 5830589530781850600678432576 := by decide +kernel
private theorem receipt_3_14_2339_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1408 128 = 4583051913194611640736816960 := by decide +kernel
private theorem receipt_3_14_2339_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1536 128 = 3394167749824503822353375040 := by decide +kernel
private theorem receipt_3_14_2339_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1664 128 = 2264834785293855136283369280 := by decide +kernel
private theorem receipt_3_14_2339_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1792 128 = 1195945228550829496903212864 := by decide +kernel
private theorem receipt_3_14_2339_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1920 88 = 234007447668878381820852156 := by decide +kernel
private theorem receipt_3_14_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 0 256 = 40877378218886158283283578496 :=
  phaseBlock_append receipt_3_14_2339_0_part0 receipt_3_14_2339_0_part1 rfl rfl rfl
private theorem receipt_3_14_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 256 256 = 33941923350451367021585055360 :=
  phaseBlock_append receipt_3_14_2339_0_part2 receipt_3_14_2339_0_part3 rfl rfl rfl
private theorem receipt_3_14_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 0 512 = 74819301569337525304868633856 :=
  phaseBlock_append receipt_3_14_2339_0_join0 receipt_3_14_2339_0_join1 rfl rfl rfl
private theorem receipt_3_14_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 512 256 = 27412833873678411150610611840 :=
  phaseBlock_append receipt_3_14_2339_0_part4 receipt_3_14_2339_0_part5 rfl rfl rfl
private theorem receipt_3_14_2339_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 768 256 = 21305187800430984767438536320 :=
  phaseBlock_append receipt_3_14_2339_0_part6 receipt_3_14_2339_0_part7 rfl rfl rfl
private theorem receipt_3_14_2339_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 512 512 = 48718021674109395918049148160 :=
  phaseBlock_append receipt_3_14_2339_0_join3 receipt_3_14_2339_0_join4 rfl rfl rfl
private theorem receipt_3_14_2339_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 0 1024 = 123537323243446921222917782016 :=
  phaseBlock_append receipt_3_14_2339_0_join2 receipt_3_14_2339_0_join5 rfl rfl rfl
private theorem receipt_3_14_2339_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1024 256 = 15633883727733732428379537024 :=
  phaseBlock_append receipt_3_14_2339_0_part8 receipt_3_14_2339_0_part9 rfl rfl rfl
private theorem receipt_3_14_2339_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1280 256 = 10413641443976462241415249536 :=
  phaseBlock_append receipt_3_14_2339_0_part10 receipt_3_14_2339_0_part11 rfl rfl rfl
private theorem receipt_3_14_2339_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1024 512 = 26047525171710194669794786560 :=
  phaseBlock_append receipt_3_14_2339_0_join7 receipt_3_14_2339_0_join8 rfl rfl rfl
private theorem receipt_3_14_2339_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1536 256 = 5659002535118358958636744320 :=
  phaseBlock_append receipt_3_14_2339_0_part12 receipt_3_14_2339_0_part13 rfl rfl rfl
private theorem receipt_3_14_2339_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1792 216 = 1429952676219707878724065020 :=
  phaseBlock_append receipt_3_14_2339_0_part14 receipt_3_14_2339_0_part15 rfl rfl rfl
private theorem receipt_3_14_2339_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1536 472 = 7088955211338066837360809340 :=
  phaseBlock_append receipt_3_14_2339_0_join10 receipt_3_14_2339_0_join11 rfl rfl rfl
private theorem receipt_3_14_2339_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 1024 984 = 33136480383048261507155595900 :=
  phaseBlock_append receipt_3_14_2339_0_join9 receipt_3_14_2339_0_join12 rfl rfl rfl
private theorem receipt_3_14_2339_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 0) 0 2008 = 156673803626495182730073377916 :=
  phaseBlock_append receipt_3_14_2339_0_join6 receipt_3_14_2339_0_join13 rfl rfl rfl

private theorem receipt_3_14_2339_0 : fastPhase (bank 3 14).shape 179827 2339 73 1 1 1 0 = 156673803626495182730073377916 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2339_0_join14

private theorem receipt_3_14_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 0 128 = 21316488017795095225480850880 := by decide +kernel
private theorem receipt_3_14_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 128 128 = 19533381894610069765940489664 := by decide +kernel
private theorem receipt_3_14_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 256 128 = 17799653324685069971554577856 := by decide +kernel
private theorem receipt_3_14_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 384 128 = 16116255884038843435997834688 := by decide +kernel
private theorem receipt_3_14_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 512 128 = 14484137518373458146013162944 := by decide +kernel
private theorem receipt_3_14_2339_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 640 128 = 12904240552546243310981000640 := by decide +kernel
private theorem receipt_3_14_2339_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 768 128 = 11377501700041730192488672704 := by decide +kernel
private theorem receipt_3_14_2339_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 896 128 = 9904852072443592933899742656 := by decide +kernel
private theorem receipt_3_14_2339_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1024 128 = 8487217188906589389923364288 := by decide +kernel
private theorem receipt_3_14_2339_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1152 128 = 7125516985628501956183633344 := by decide +kernel
private theorem receipt_3_14_2339_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1280 128 = 5820665825322078398788939200 := by decide +kernel
private theorem receipt_3_14_2339_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1408 128 = 4573572506686972683901316544 := by decide +kernel
private theorem receipt_3_14_2339_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1536 128 = 3385140273881685807305797056 := by decide +kernel
private theorem receipt_3_14_2339_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1664 128 = 2256266825995506623979761088 := by decide +kernel
private theorem receipt_3_14_2339_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1792 128 = 1187844326520452677662289344 := by decide +kernel
private theorem receipt_3_14_2339_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1920 88 = 228712903995828157818764148 := by decide +kernel
private theorem receipt_3_14_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 0 256 = 40849869912405164991421340544 :=
  phaseBlock_append receipt_3_14_2339_1_part0 receipt_3_14_2339_1_part1 rfl rfl rfl
private theorem receipt_3_14_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 256 256 = 33915909208723913407552412544 :=
  phaseBlock_append receipt_3_14_2339_1_part2 receipt_3_14_2339_1_part3 rfl rfl rfl
private theorem receipt_3_14_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 0 512 = 74765779121129078398973753088 :=
  phaseBlock_append receipt_3_14_2339_1_join0 receipt_3_14_2339_1_join1 rfl rfl rfl
private theorem receipt_3_14_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 512 256 = 27388378070919701456994163584 :=
  phaseBlock_append receipt_3_14_2339_1_part4 receipt_3_14_2339_1_part5 rfl rfl rfl
private theorem receipt_3_14_2339_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 768 256 = 21282353772485323126388415360 :=
  phaseBlock_append receipt_3_14_2339_1_part6 receipt_3_14_2339_1_part7 rfl rfl rfl
private theorem receipt_3_14_2339_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 512 512 = 48670731843405024583382578944 :=
  phaseBlock_append receipt_3_14_2339_1_join3 receipt_3_14_2339_1_join4 rfl rfl rfl
private theorem receipt_3_14_2339_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 0 1024 = 123436510964534102982356332032 :=
  phaseBlock_append receipt_3_14_2339_1_join2 receipt_3_14_2339_1_join5 rfl rfl rfl
private theorem receipt_3_14_2339_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1024 256 = 15612734174535091346106997632 :=
  phaseBlock_append receipt_3_14_2339_1_part8 receipt_3_14_2339_1_part9 rfl rfl rfl
private theorem receipt_3_14_2339_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1280 256 = 10394238332009051082690255744 :=
  phaseBlock_append receipt_3_14_2339_1_part10 receipt_3_14_2339_1_part11 rfl rfl rfl
private theorem receipt_3_14_2339_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1024 512 = 26006972506544142428797253376 :=
  phaseBlock_append receipt_3_14_2339_1_join7 receipt_3_14_2339_1_join8 rfl rfl rfl
private theorem receipt_3_14_2339_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1536 256 = 5641407099877192431285558144 :=
  phaseBlock_append receipt_3_14_2339_1_part12 receipt_3_14_2339_1_part13 rfl rfl rfl
private theorem receipt_3_14_2339_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1792 216 = 1416557230516280835481053492 :=
  phaseBlock_append receipt_3_14_2339_1_part14 receipt_3_14_2339_1_part15 rfl rfl rfl
private theorem receipt_3_14_2339_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1536 472 = 7057964330393473266766611636 :=
  phaseBlock_append receipt_3_14_2339_1_join10 receipt_3_14_2339_1_join11 rfl rfl rfl
private theorem receipt_3_14_2339_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 1024 984 = 33064936836937615695563865012 :=
  phaseBlock_append receipt_3_14_2339_1_join9 receipt_3_14_2339_1_join12 rfl rfl rfl
private theorem receipt_3_14_2339_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2339 73 1 1 1 1) 0 2008 = 156501447801471718677920197044 :=
  phaseBlock_append receipt_3_14_2339_1_join6 receipt_3_14_2339_1_join13 rfl rfl rfl

private theorem receipt_3_14_2339_1 : fastPhase (bank 3 14).shape 179827 2339 73 1 1 1 1 = 156501447801471718677920197044 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2339_1_join14

private theorem receipt_3_14_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 0 128 = 21330615121303536646084893984 := by decide +kernel
private theorem receipt_3_14_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 128 128 = 19547116260677202129587186976 := by decide +kernel
private theorem receipt_3_14_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 256 128 = 17812989439633496396608126240 := by decide +kernel
private theorem receipt_3_14_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 384 128 = 16129188165599072026777341216 := by decide +kernel
private theorem receipt_3_14_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 512 128 = 14496660316163320054986988832 := by decide +kernel
private theorem receipt_3_14_2340_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 640 128 = 12916348148549431191658884384 := by decide +kernel
private theorem receipt_3_14_2340_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 768 128 = 11389188309085457043011632416 := by decide +kernel
private theorem receipt_3_14_2340_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 896 128 = 9916111842675371331327757600 := by decide +kernel
private theorem receipt_3_14_2340_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1024 128 = 8498044202270131115220835616 := by decide +kernel
private theorem receipt_3_14_2340_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1152 128 = 7135905258338738009902624032 := by decide +kernel
private theorem receipt_3_14_2340_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1280 128 = 5830609308339299407450193184 := by decide +kernel
private theorem receipt_3_14_2340_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1408 128 = 4583065086190089697073057056 := by decide +kernel
private theorem receipt_3_14_2340_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1536 128 = 3394175771740611485380304160 := by decide +kernel
private theorem receipt_3_14_2340_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1664 128 = 2264839000242656816647728416 := by decide +kernel
private theorem receipt_3_14_2340_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1792 128 = 1195946871821368393084960032 := by decide +kernel
private theorem receipt_3_14_2340_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1920 88 = 234007675678387778476557006 := by decide +kernel
private theorem receipt_3_14_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 0 256 = 40877731381980738775672080960 :=
  phaseBlock_append receipt_3_14_2340_0_part0 receipt_3_14_2340_0_part1 rfl rfl rfl
private theorem receipt_3_14_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 256 256 = 33942177605232568423385467456 :=
  phaseBlock_append receipt_3_14_2340_0_part2 receipt_3_14_2340_0_part3 rfl rfl rfl
private theorem receipt_3_14_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 0 512 = 74819908987213307199057548416 :=
  phaseBlock_append receipt_3_14_2340_0_join0 receipt_3_14_2340_0_join1 rfl rfl rfl
private theorem receipt_3_14_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 512 256 = 27413008464712751246645873216 :=
  phaseBlock_append receipt_3_14_2340_0_part4 receipt_3_14_2340_0_part5 rfl rfl rfl
private theorem receipt_3_14_2340_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 768 256 = 21305300151760828374339390016 :=
  phaseBlock_append receipt_3_14_2340_0_part6 receipt_3_14_2340_0_part7 rfl rfl rfl
private theorem receipt_3_14_2340_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 512 512 = 48718308616473579620985263232 :=
  phaseBlock_append receipt_3_14_2340_0_join3 receipt_3_14_2340_0_join4 rfl rfl rfl
private theorem receipt_3_14_2340_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 0 1024 = 123538217603686886820042811648 :=
  phaseBlock_append receipt_3_14_2340_0_join2 receipt_3_14_2340_0_join5 rfl rfl rfl
private theorem receipt_3_14_2340_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1024 256 = 15633949460608869125123459648 :=
  phaseBlock_append receipt_3_14_2340_0_part8 receipt_3_14_2340_0_part9 rfl rfl rfl
private theorem receipt_3_14_2340_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1280 256 = 10413674394529389104523250240 :=
  phaseBlock_append receipt_3_14_2340_0_part10 receipt_3_14_2340_0_part11 rfl rfl rfl
private theorem receipt_3_14_2340_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1024 512 = 26047623855138258229646709888 :=
  phaseBlock_append receipt_3_14_2340_0_join7 receipt_3_14_2340_0_join8 rfl rfl rfl
private theorem receipt_3_14_2340_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1536 256 = 5659014771983268302028032576 :=
  phaseBlock_append receipt_3_14_2340_0_part12 receipt_3_14_2340_0_part13 rfl rfl rfl
private theorem receipt_3_14_2340_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1792 216 = 1429954547499756171561517038 :=
  phaseBlock_append receipt_3_14_2340_0_part14 receipt_3_14_2340_0_part15 rfl rfl rfl
private theorem receipt_3_14_2340_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1536 472 = 7088969319483024473589549614 :=
  phaseBlock_append receipt_3_14_2340_0_join10 receipt_3_14_2340_0_join11 rfl rfl rfl
private theorem receipt_3_14_2340_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 1024 984 = 33136593174621282703236259502 :=
  phaseBlock_append receipt_3_14_2340_0_join9 receipt_3_14_2340_0_join12 rfl rfl rfl
private theorem receipt_3_14_2340_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 0) 0 2008 = 156674810778308169523279071150 :=
  phaseBlock_append receipt_3_14_2340_0_join6 receipt_3_14_2340_0_join13 rfl rfl rfl

private theorem receipt_3_14_2340_0 : fastPhase (bank 3 14).shape 179827 2340 73 1 1 1 0 = 156674810778308169523279071150 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2340_0_join14

private theorem receipt_3_14_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 0 128 = 21316678093137976820957375520 := by decide +kernel
private theorem receipt_3_14_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 128 128 = 19533544707620977677961575456 := by decide +kernel
private theorem receipt_3_14_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 256 128 = 17799791452223728013241912352 := by decide +kernel
private theorem receipt_3_14_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 384 128 = 16116371788074289369050012704 := by decide +kernel
private theorem receipt_3_14_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 512 128 = 14484233546540348873043487776 := by decide +kernel
private theorem receipt_3_14_2340_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 640 128 = 12904318938700280458553064480 := by decide +kernel
private theorem receipt_3_14_2340_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 768 128 = 11377564564814206084849716256 := by decide +kernel
private theorem receipt_3_14_2340_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 896 128 = 9904901423795056957411793952 := by decide +kernel
private theorem receipt_3_14_2340_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1024 128 = 8487254922679634748192156704 := by decide +kernel
private theorem receipt_3_14_2340_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1152 128 = 7125544886099672815885302816 := by decide +kernel
private theorem receipt_3_14_2340_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1280 128 = 5820685565752897426194500640 := by decide +kernel
private theorem receipt_3_14_2340_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1408 128 = 4573585649874088972098919456 := by decide +kernel
private theorem receipt_3_14_2340_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1536 128 = 3385148272706143194120760352 := by decide +kernel
private theorem receipt_3_14_2340_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1664 128 = 2256271023971132400592387104 := by decide +kernel
private theorem receipt_3_14_2340_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1792 128 = 1187845958341366687923457056 := by decide +kernel
private theorem receipt_3_14_2340_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1920 88 = 228713127030242612801501502 := by decide +kernel
private theorem receipt_3_14_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 0 256 = 40850222800758954498918950976 :=
  phaseBlock_append receipt_3_14_2340_1_part0 receipt_3_14_2340_1_part1 rfl rfl rfl
private theorem receipt_3_14_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 256 256 = 33916163240298017382291925056 :=
  phaseBlock_append receipt_3_14_2340_1_part2 receipt_3_14_2340_1_part3 rfl rfl rfl
private theorem receipt_3_14_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 0 512 = 74766386041056971881210876032 :=
  phaseBlock_append receipt_3_14_2340_1_join0 receipt_3_14_2340_1_join1 rfl rfl rfl
private theorem receipt_3_14_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 512 256 = 27388552485240629331596552256 :=
  phaseBlock_append receipt_3_14_2340_1_part4 receipt_3_14_2340_1_part5 rfl rfl rfl
private theorem receipt_3_14_2340_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 768 256 = 21282465988609263042261510208 :=
  phaseBlock_append receipt_3_14_2340_1_part6 receipt_3_14_2340_1_part7 rfl rfl rfl
private theorem receipt_3_14_2340_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 512 512 = 48671018473849892373858062464 :=
  phaseBlock_append receipt_3_14_2340_1_join3 receipt_3_14_2340_1_join4 rfl rfl rfl
private theorem receipt_3_14_2340_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 0 1024 = 123437404514906864255068938496 :=
  phaseBlock_append receipt_3_14_2340_1_join2 receipt_3_14_2340_1_join5 rfl rfl rfl
private theorem receipt_3_14_2340_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1024 256 = 15612799808779307564077459520 :=
  phaseBlock_append receipt_3_14_2340_1_part8 receipt_3_14_2340_1_part9 rfl rfl rfl
private theorem receipt_3_14_2340_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1280 256 = 10394271215626986398293420096 :=
  phaseBlock_append receipt_3_14_2340_1_part10 receipt_3_14_2340_1_part11 rfl rfl rfl
private theorem receipt_3_14_2340_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1024 512 = 26007071024406293962370879616 :=
  phaseBlock_append receipt_3_14_2340_1_join7 receipt_3_14_2340_1_join8 rfl rfl rfl
private theorem receipt_3_14_2340_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1536 256 = 5641419296677275594713147456 :=
  phaseBlock_append receipt_3_14_2340_1_part12 receipt_3_14_2340_1_part13 rfl rfl rfl
private theorem receipt_3_14_2340_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1792 216 = 1416559085371609300724958558 :=
  phaseBlock_append receipt_3_14_2340_1_part14 receipt_3_14_2340_1_part15 rfl rfl rfl
private theorem receipt_3_14_2340_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1536 472 = 7057978382048884895438106014 :=
  phaseBlock_append receipt_3_14_2340_1_join10 receipt_3_14_2340_1_join11 rfl rfl rfl
private theorem receipt_3_14_2340_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 1024 984 = 33065049406455178857808985630 :=
  phaseBlock_append receipt_3_14_2340_1_join9 receipt_3_14_2340_1_join12 rfl rfl rfl
private theorem receipt_3_14_2340_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179827 2340 73 1 1 1 1) 0 2008 = 156502453921362043112877924126 :=
  phaseBlock_append receipt_3_14_2340_1_join6 receipt_3_14_2340_1_join13 rfl rfl rfl

private theorem receipt_3_14_2340_1 : fastPhase (bank 3 14).shape 179827 2340 73 1 1 1 1 = 156502453921362043112877924126 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2340_1_join14

theorem receipt_3_14 : Checked (bank 3 14) 73 1 1 := by
  refine checked_from_values (bank 3 14) 73 1 1
    (P3_7_1.checked (bank 3 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_14_2339_0 receipt_3_14_2339_1 receipt_3_14_2340_0 receipt_3_14_2340_1 (by decide +kernel) (by decide +kernel)

def group5_stage (i : Fin 2) : Fin 17 :=
  ⟨13+i.val, by have := i.isLt; omega⟩

theorem group5_checked (rect : Fin 4) (i : Fin 2) :
    Checked (bank rect (group5_stage i)) (reserve (group5_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_13
    · exact receipt_1_13
    · exact receipt_2_13
    · exact receipt_3_13
  · fin_cases rect
    · exact receipt_0_14
    · exact receipt_1_14
    · exact receipt_2_14
    · exact receipt_3_14

theorem group5_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group5_stage i)).shape
      (cutoff h rect (group5_stage i)), ¬ G∣Q :=
  (group5_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group5_avoids

end Lower6960.RescueSource
