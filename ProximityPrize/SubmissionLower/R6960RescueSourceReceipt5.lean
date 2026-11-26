import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

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

private theorem receipt_0_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 0 128 = 21492977201547188888012112480 := by decide +kernel
private theorem receipt_0_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 128 128 = 18658777832640935923781104224 := by decide +kernel
private theorem receipt_0_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 256 128 = 15957491851217647710496629344 := by decide +kernel
private theorem receipt_0_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 384 128 = 13385907185669639030399947360 := by decide +kernel
private theorem receipt_0_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 512 128 = 10940819639310752769006862944 := by decide +kernel
private theorem receipt_0_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 640 128 = 8619032884093134747484107360 := by decide +kernel
private theorem receipt_0_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 768 128 = 6417358960496063987841826409 := by decide +kernel
private theorem receipt_0_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 896 128 = 4332621250562907083956067817 := by decide +kernel
private theorem receipt_0_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 1024 128 = 2361642219077322032939007634 := by decide +kernel
private theorem receipt_0_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 1152 99 = 545069393615548047810979461 := by decide +kernel
private theorem receipt_0_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 0 256 = 40151755034188124811793216704 :=
  phaseBlock_append receipt_0_13_2359_0_part0 receipt_0_13_2359_0_part1 rfl rfl rfl
private theorem receipt_0_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 384 256 = 24326726824980391799406810304 :=
  phaseBlock_append receipt_0_13_2359_0_part3 receipt_0_13_2359_0_part4 rfl rfl rfl
private theorem receipt_0_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 256 384 = 40284218676198039509903439648 :=
  phaseBlock_append receipt_0_13_2359_0_part2 receipt_0_13_2359_0_join1 rfl rfl rfl
private theorem receipt_0_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 0 640 = 80435973710386164321696656352 :=
  phaseBlock_append receipt_0_13_2359_0_join0 receipt_0_13_2359_0_join2 rfl rfl rfl
private theorem receipt_0_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 640 256 = 15036391844589198735325933769 :=
  phaseBlock_append receipt_0_13_2359_0_part5 receipt_0_13_2359_0_part6 rfl rfl rfl
private theorem receipt_0_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 1024 227 = 2906711612692870080749987095 :=
  phaseBlock_append receipt_0_13_2359_0_part8 receipt_0_13_2359_0_part9 rfl rfl rfl
private theorem receipt_0_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 896 355 = 7239332863255777164706054912 :=
  phaseBlock_append receipt_0_13_2359_0_part7 receipt_0_13_2359_0_join5 rfl rfl rfl
private theorem receipt_0_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 640 611 = 22275724707844975900031988681 :=
  phaseBlock_append receipt_0_13_2359_0_join4 receipt_0_13_2359_0_join6 rfl rfl rfl
private theorem receipt_0_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 0) 0 1251 = 102711698418231140221728645033 :=
  phaseBlock_append receipt_0_13_2359_0_join3 receipt_0_13_2359_0_join7 rfl rfl rfl

private theorem receipt_0_13_2359_0 : fastPhase (bank 0 13).shape 179818 2359 44 1 0 1 0 = 102711698418231140221728645033 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2359_0_join8

private theorem receipt_0_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 0 128 = 21470604691305115296956225248 := by decide +kernel
private theorem receipt_0_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 128 128 = 18637421232926801666851325664 := by decide +kernel
private theorem receipt_0_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 256 128 = 15937126846102674501817497312 := by decide +kernel
private theorem receipt_0_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 384 128 = 13366509519257659970203363040 := by decide +kernel
private theorem receipt_0_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 512 128 = 10922365115690097302483752672 := by decide +kernel
private theorem receipt_0_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 640 128 = 8601497367288513623636084448 := by decide +kernel
private theorem receipt_0_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 768 128 = 6400718373070666584824731173 := by decide +kernel
private theorem receipt_0_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 896 128 = 4316851558840720841276678607 := by decide +kernel
private theorem receipt_0_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 1024 128 = 2346719438905511335324388889 := by decide +kernel
private theorem receipt_0_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 1152 99 = 534093215097607388652767377 := by decide +kernel
private theorem receipt_0_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 0 256 = 40108025924231916963807550912 :=
  phaseBlock_append receipt_0_13_2359_1_part0 receipt_0_13_2359_1_part1 rfl rfl rfl
private theorem receipt_0_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 384 256 = 24288874634947757272687115712 :=
  phaseBlock_append receipt_0_13_2359_1_part3 receipt_0_13_2359_1_part4 rfl rfl rfl
private theorem receipt_0_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 256 384 = 40226001481050431774504613024 :=
  phaseBlock_append receipt_0_13_2359_1_part2 receipt_0_13_2359_1_join1 rfl rfl rfl
private theorem receipt_0_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 0 640 = 80334027405282348738312163936 :=
  phaseBlock_append receipt_0_13_2359_1_join0 receipt_0_13_2359_1_join2 rfl rfl rfl
private theorem receipt_0_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 640 256 = 15002215740359180208460815621 :=
  phaseBlock_append receipt_0_13_2359_1_part5 receipt_0_13_2359_1_part6 rfl rfl rfl
private theorem receipt_0_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 1024 227 = 2880812654003118723977156266 :=
  phaseBlock_append receipt_0_13_2359_1_part8 receipt_0_13_2359_1_part9 rfl rfl rfl
private theorem receipt_0_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 896 355 = 7197664212843839565253834873 :=
  phaseBlock_append receipt_0_13_2359_1_part7 receipt_0_13_2359_1_join5 rfl rfl rfl
private theorem receipt_0_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 640 611 = 22199879953203019773714650494 :=
  phaseBlock_append receipt_0_13_2359_1_join4 receipt_0_13_2359_1_join6 rfl rfl rfl
private theorem receipt_0_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2359 44 1 0 1 1) 0 1251 = 102533907358485368512026814430 :=
  phaseBlock_append receipt_0_13_2359_1_join3 receipt_0_13_2359_1_join7 rfl rfl rfl

private theorem receipt_0_13_2359_1 : fastPhase (bank 0 13).shape 179818 2359 44 1 0 1 1 = 102533907358485368512026814430 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2359_1_join8

private theorem receipt_0_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 0 128 = 21493168654760370441579645120 := by decide +kernel
private theorem receipt_0_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 128 128 = 18658934339095971671405414592 := by decide +kernel
private theorem receipt_0_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 256 128 = 15957617139206959264475498688 := by decide +kernel
private theorem receipt_0_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 384 128 = 13386004872751233357729810624 := by decide +kernel
private theorem receipt_0_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 512 128 = 10940893232582761070788331712 := by decide +kernel
private theorem receipt_0_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 640 128 = 8619085780468131436001937600 := by decide +kernel
private theorem receipt_0_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 768 128 = 6417394430915807794455468603 := by decide +kernel
private theorem receipt_0_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 896 128 = 4332642444937221066953708331 := by decide +kernel
private theorem receipt_0_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 1024 128 = 2361652250170165615882529312 := by decide +kernel
private theorem receipt_0_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 1152 99 = 545071401984256214085771354 := by decide +kernel
private theorem receipt_0_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 0 256 = 40152102993856342112985059712 :=
  phaseBlock_append receipt_0_13_2360_0_part0 receipt_0_13_2360_0_part1 rfl rfl rfl
private theorem receipt_0_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 384 256 = 24326898105333994428518142336 :=
  phaseBlock_append receipt_0_13_2360_0_part3 receipt_0_13_2360_0_part4 rfl rfl rfl
private theorem receipt_0_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 256 384 = 40284515244540953692993641024 :=
  phaseBlock_append receipt_0_13_2360_0_part2 receipt_0_13_2360_0_join1 rfl rfl rfl
private theorem receipt_0_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 0 640 = 80436618238397295805978700736 :=
  phaseBlock_append receipt_0_13_2360_0_join0 receipt_0_13_2360_0_join2 rfl rfl rfl
private theorem receipt_0_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 640 256 = 15036480211383939230457406203 :=
  phaseBlock_append receipt_0_13_2360_0_part5 receipt_0_13_2360_0_part6 rfl rfl rfl
private theorem receipt_0_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 1024 227 = 2906723652154421829968300666 :=
  phaseBlock_append receipt_0_13_2360_0_part8 receipt_0_13_2360_0_part9 rfl rfl rfl
private theorem receipt_0_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 896 355 = 7239366097091642896922008997 :=
  phaseBlock_append receipt_0_13_2360_0_part7 receipt_0_13_2360_0_join5 rfl rfl rfl
private theorem receipt_0_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 640 611 = 22275846308475582127379415200 :=
  phaseBlock_append receipt_0_13_2360_0_join4 receipt_0_13_2360_0_join6 rfl rfl rfl
private theorem receipt_0_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 0) 0 1251 = 102712464546872877933358115936 :=
  phaseBlock_append receipt_0_13_2360_0_join3 receipt_0_13_2360_0_join7 rfl rfl rfl

private theorem receipt_0_13_2360_0 : fastPhase (bank 0 13).shape 179818 2360 44 1 0 1 0 = 102712464546872877933358115936 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2360_0_join8

private theorem receipt_0_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 0 128 = 21470795981005198151207531648 := by decide +kernel
private theorem receipt_0_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 128 128 = 18637577590612544853873939584 := by decide +kernel
private theorem receipt_0_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 256 128 = 15937251999543229543053128832 := by decide +kernel
private theorem receipt_0_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 384 128 = 13366607085489267392125965440 := by decide +kernel
private theorem receipt_0_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 512 128 = 10922438601290624210334987392 := by decide +kernel
private theorem receipt_0_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 640 128 = 8601550168651771372835230848 := by decide +kernel
private theorem receipt_0_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 768 128 = 6400753760663159341343174310 := by decide +kernel
private theorem receipt_0_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 896 128 = 4316872682183475260760316451 := by decide +kernel
private theorem receipt_0_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 1024 128 = 2346729410234481188429031516 := by decide +kernel
private theorem receipt_0_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 1152 99 = 534095184631722422643868602 := by decide +kernel
private theorem receipt_0_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 0 256 = 40108373571617743005081471232 :=
  phaseBlock_append receipt_0_13_2360_1_part0 receipt_0_13_2360_1_part1 rfl rfl rfl
private theorem receipt_0_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 384 256 = 24289045686779891602460952832 :=
  phaseBlock_append receipt_0_13_2360_1_part3 receipt_0_13_2360_1_part4 rfl rfl rfl
private theorem receipt_0_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 256 384 = 40226297686323121145514081664 :=
  phaseBlock_append receipt_0_13_2360_1_part2 receipt_0_13_2360_1_join1 rfl rfl rfl
private theorem receipt_0_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 0 640 = 80334671257940864150595552896 :=
  phaseBlock_append receipt_0_13_2360_1_join0 receipt_0_13_2360_1_join2 rfl rfl rfl
private theorem receipt_0_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 640 256 = 15002303929314930714178405158 :=
  phaseBlock_append receipt_0_13_2360_1_part5 receipt_0_13_2360_1_part6 rfl rfl rfl
private theorem receipt_0_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 1024 227 = 2880824594866203611072900118 :=
  phaseBlock_append receipt_0_13_2360_1_part8 receipt_0_13_2360_1_part9 rfl rfl rfl
private theorem receipt_0_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 896 355 = 7197697277049678871833216569 :=
  phaseBlock_append receipt_0_13_2360_1_part7 receipt_0_13_2360_1_join5 rfl rfl rfl
private theorem receipt_0_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 640 611 = 22200001206364609586011621727 :=
  phaseBlock_append receipt_0_13_2360_1_join4 receipt_0_13_2360_1_join6 rfl rfl rfl
private theorem receipt_0_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179818 2360 44 1 0 1 1) 0 1251 = 102534672464305473736607174623 :=
  phaseBlock_append receipt_0_13_2360_1_join3 receipt_0_13_2360_1_join7 rfl rfl rfl

private theorem receipt_0_13_2360_1 : fastPhase (bank 0 13).shape 179818 2360 44 1 0 1 1 = 102534672464305473736607174623 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2360_1_join8

theorem receipt_0_13 : Checked (bank 0 13) 44 0 1 := by
  refine checked_from_values (bank 0 13) 44 0 1
    (P3_7_1.checked (bank 0 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_13_2359_0 receipt_0_13_2359_1 receipt_0_13_2360_0 receipt_0_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 0 128 = 19347107416565934253388382816 := by decide +kernel
private theorem receipt_1_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 128 128 = 16783769202907655253728834144 := by decide +kernel
private theorem receipt_1_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 256 128 = 14343579786628847339675820640 := by decide +kernel
private theorem receipt_1_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 384 128 = 12023396518529095109095002720 := by decide +kernel
private theorem receipt_1_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 512 128 = 9820092019896554095471133280 := by decide +kernel
private theorem receipt_1_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 640 128 = 7730554157375050097413583456 := by decide +kernel
private theorem receipt_1_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 768 128 = 5751686471379349290209269899 := by decide +kernel
private theorem receipt_1_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 896 128 = 3880410817777386541303195333 := by decide +kernel
private theorem receipt_1_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 1024 128 = 2113656366677851348522279578 := by decide +kernel
private theorem receipt_1_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 1152 99 = 487541002734731424656883669 := by decide +kernel
private theorem receipt_1_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 0 256 = 36130876619473589507117216960 :=
  phaseBlock_append receipt_1_13_2359_0_part0 receipt_1_13_2359_0_part1 rfl rfl rfl
private theorem receipt_1_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 384 256 = 21843488538425649204566136000 :=
  phaseBlock_append receipt_1_13_2359_0_part3 receipt_1_13_2359_0_part4 rfl rfl rfl
private theorem receipt_1_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 256 384 = 36187068325054496544241956640 :=
  phaseBlock_append receipt_1_13_2359_0_part2 receipt_1_13_2359_0_join1 rfl rfl rfl
private theorem receipt_1_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 0 640 = 72317944944528086051359173600 :=
  phaseBlock_append receipt_1_13_2359_0_join0 receipt_1_13_2359_0_join2 rfl rfl rfl
private theorem receipt_1_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 640 256 = 13482240628754399387622853355 :=
  phaseBlock_append receipt_1_13_2359_0_part5 receipt_1_13_2359_0_part6 rfl rfl rfl
private theorem receipt_1_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 1024 227 = 2601197369412582773179163247 :=
  phaseBlock_append receipt_1_13_2359_0_part8 receipt_1_13_2359_0_part9 rfl rfl rfl
private theorem receipt_1_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 896 355 = 6481608187189969314482358580 :=
  phaseBlock_append receipt_1_13_2359_0_part7 receipt_1_13_2359_0_join5 rfl rfl rfl
private theorem receipt_1_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 640 611 = 19963848815944368702105211935 :=
  phaseBlock_append receipt_1_13_2359_0_join4 receipt_1_13_2359_0_join6 rfl rfl rfl
private theorem receipt_1_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 0) 0 1251 = 92281793760472454753464385535 :=
  phaseBlock_append receipt_1_13_2359_0_join3 receipt_1_13_2359_0_join7 rfl rfl rfl

private theorem receipt_1_13_2359_0 : fastPhase (bank 1 13).shape 179818 2359 44 1 0 2 0 = 92281793760472454753464385535 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2359_0_join8

private theorem receipt_1_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 0 128 = 19326859754352160209345971232 := by decide +kernel
private theorem receipt_1_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 128 128 = 16764464236972434324809602080 := by decide +kernel
private theorem receipt_1_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 256 128 = 14325193678226666501710586912 := by decide +kernel
private theorem receipt_1_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 384 128 = 12005905545394670261055583264 := by decide +kernel
private theorem receipt_1_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 512 128 = 9803472576052369894876988448 := by decide +kernel
private theorem receipt_1_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 640 128 = 7714782752938899795738465312 := by decide +kernel
private theorem receipt_1_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 768 128 = 5736739731159855153559559129 := by decide +kernel
private theorem receipt_1_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 896 128 = 3866265467876166632418318483 := by decide +kernel
private theorem receipt_1_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 1024 128 = 2100289239581552537259014925 := by decide +kernel
private theorem receipt_1_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 1152 99 = 477721467509070040119109083 := by decide +kernel
private theorem receipt_1_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 0 256 = 36091323991324594534155573312 :=
  phaseBlock_append receipt_1_13_2359_1_part0 receipt_1_13_2359_1_part1 rfl rfl rfl
private theorem receipt_1_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 384 256 = 21809378121447040155932571712 :=
  phaseBlock_append receipt_1_13_2359_1_part3 receipt_1_13_2359_1_part4 rfl rfl rfl
private theorem receipt_1_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 256 384 = 36134571799673706657643158624 :=
  phaseBlock_append receipt_1_13_2359_1_part2 receipt_1_13_2359_1_join1 rfl rfl rfl
private theorem receipt_1_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 0 640 = 72225895790998301191798731936 :=
  phaseBlock_append receipt_1_13_2359_1_join0 receipt_1_13_2359_1_join2 rfl rfl rfl
private theorem receipt_1_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 640 256 = 13451522484098754949298024441 :=
  phaseBlock_append receipt_1_13_2359_1_part5 receipt_1_13_2359_1_part6 rfl rfl rfl
private theorem receipt_1_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 1024 227 = 2578010707090622577378124008 :=
  phaseBlock_append receipt_1_13_2359_1_part8 receipt_1_13_2359_1_part9 rfl rfl rfl
private theorem receipt_1_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 896 355 = 6444276174966789209796442491 :=
  phaseBlock_append receipt_1_13_2359_1_part7 receipt_1_13_2359_1_join5 rfl rfl rfl
private theorem receipt_1_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 640 611 = 19895798659065544159094466932 :=
  phaseBlock_append receipt_1_13_2359_1_join4 receipt_1_13_2359_1_join6 rfl rfl rfl
private theorem receipt_1_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2359 44 1 0 2 1) 0 1251 = 92121694450063845350893198868 :=
  phaseBlock_append receipt_1_13_2359_1_join3 receipt_1_13_2359_1_join7 rfl rfl rfl

private theorem receipt_1_13_2359_1 : fastPhase (bank 1 13).shape 179818 2359 44 1 0 2 1 = 92121694450063845350893198868 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2359_1_join8

private theorem receipt_1_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 0 128 = 19347279755588101095484677504 := by decide +kernel
private theorem receipt_1_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 128 128 = 16783909982662635926542818688 := by decide +kernel
private theorem receipt_1_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 256 128 = 14343692403686763461750054272 := by decide +kernel
private theorem receipt_1_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 384 128 = 12023484262748257347988725120 := by decide +kernel
private theorem receipt_1_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 512 128 = 9820158074953623035173854592 := by decide +kernel
private theorem receipt_1_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 640 128 = 7730601601294317496456453504 := by decide +kernel
private theorem receipt_1_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 768 128 = 5751718262670782645824173117 := by decide +kernel
private theorem receipt_1_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 896 128 = 3880429800173688245157143881 := by decide +kernel
private theorem receipt_1_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 1024 128 = 2113665344530705780689501463 := by decide +kernel
private theorem receipt_1_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 1152 99 = 487542799141903113311547576 := by decide +kernel
private theorem receipt_1_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 0 256 = 36131189738250737022027496192 :=
  phaseBlock_append receipt_1_13_2360_0_part0 receipt_1_13_2360_0_part1 rfl rfl rfl
private theorem receipt_1_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 384 256 = 21843642337701880383162579712 :=
  phaseBlock_append receipt_1_13_2360_0_part3 receipt_1_13_2360_0_part4 rfl rfl rfl
private theorem receipt_1_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 256 384 = 36187334741388643844912633984 :=
  phaseBlock_append receipt_1_13_2360_0_part2 receipt_1_13_2360_0_join1 rfl rfl rfl
private theorem receipt_1_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 0 640 = 72318524479639380866940130176 :=
  phaseBlock_append receipt_1_13_2360_0_join0 receipt_1_13_2360_0_join2 rfl rfl rfl
private theorem receipt_1_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 640 256 = 13482319863965100142280626621 :=
  phaseBlock_append receipt_1_13_2360_0_part5 receipt_1_13_2360_0_part6 rfl rfl rfl
private theorem receipt_1_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 1024 227 = 2601208143672608894001049039 :=
  phaseBlock_append receipt_1_13_2360_0_part8 receipt_1_13_2360_0_part9 rfl rfl rfl
private theorem receipt_1_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 896 355 = 6481637943846297139158192920 :=
  phaseBlock_append receipt_1_13_2360_0_part7 receipt_1_13_2360_0_join5 rfl rfl rfl
private theorem receipt_1_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 640 611 = 19963957807811397281438819541 :=
  phaseBlock_append receipt_1_13_2360_0_join4 receipt_1_13_2360_0_join6 rfl rfl rfl
private theorem receipt_1_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 0) 0 1251 = 92282482287450778148378949717 :=
  phaseBlock_append receipt_1_13_2360_0_join3 receipt_1_13_2360_0_join7 rfl rfl rfl

private theorem receipt_1_13_2360_0 : fastPhase (bank 1 13).shape 179818 2360 44 1 0 2 0 = 92282482287450778148378949717 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2360_0_join8

private theorem receipt_1_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 0 128 = 19327031945216232596745576192 := by decide +kernel
private theorem receipt_1_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 128 128 = 16764604882114670380752756480 := by decide +kernel
private theorem receipt_1_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 256 128 = 14325306173708893027659439872 := by decide +kernel
private theorem receipt_1_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 384 128 = 12005993180569811488079994624 := by decide +kernel
private theorem receipt_1_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 512 128 = 9803538534094603128387886848 := by decide +kernel
private theorem receipt_1_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 640 128 = 7714830111372931450918985472 := by decide +kernel
private theorem receipt_1_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 768 128 = 5736771448036684223847580218 := by decide +kernel
private theorem receipt_1_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 896 128 = 3866284386548493973022300418 := by decide +kernel
private theorem receipt_1_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 1024 128 = 2100298163897400686097283500 := by decide +kernel
private theorem receipt_1_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 1152 99 = 477723229173346536682584126 := by decide +kernel
private theorem receipt_1_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 0 256 = 36091636827330902977498332672 :=
  phaseBlock_append receipt_1_13_2360_1_part0 receipt_1_13_2360_1_part1 rfl rfl rfl
private theorem receipt_1_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 384 256 = 21809531714664414616467881472 :=
  phaseBlock_append receipt_1_13_2360_1_part3 receipt_1_13_2360_1_part4 rfl rfl rfl
private theorem receipt_1_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 256 384 = 36134837888373307644127321344 :=
  phaseBlock_append receipt_1_13_2360_1_part2 receipt_1_13_2360_1_join1 rfl rfl rfl
private theorem receipt_1_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 0 640 = 72226474715704210621625654016 :=
  phaseBlock_append receipt_1_13_2360_1_join0 receipt_1_13_2360_1_join2 rfl rfl rfl
private theorem receipt_1_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 640 256 = 13451601559409615674766565690 :=
  phaseBlock_append receipt_1_13_2360_1_part5 receipt_1_13_2360_1_part6 rfl rfl rfl
private theorem receipt_1_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 1024 227 = 2578021393070747222779867626 :=
  phaseBlock_append receipt_1_13_2360_1_part8 receipt_1_13_2360_1_part9 rfl rfl rfl
private theorem receipt_1_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 896 355 = 6444305779619241195802168044 :=
  phaseBlock_append receipt_1_13_2360_1_part7 receipt_1_13_2360_1_join5 rfl rfl rfl
private theorem receipt_1_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 640 611 = 19895907339028856870568733734 :=
  phaseBlock_append receipt_1_13_2360_1_join4 receipt_1_13_2360_1_join6 rfl rfl rfl
private theorem receipt_1_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179818 2360 44 1 0 2 1) 0 1251 = 92122382054733067492194387750 :=
  phaseBlock_append receipt_1_13_2360_1_join3 receipt_1_13_2360_1_join7 rfl rfl rfl

private theorem receipt_1_13_2360_1 : fastPhase (bank 1 13).shape 179818 2360 44 1 0 2 1 = 92122382054733067492194387750 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2360_1_join8

theorem receipt_1_13 : Checked (bank 1 13) 44 0 2 := by
  refine checked_from_values (bank 1 13) 44 0 2
    (P3_7_1.checked (bank 1 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_13_2359_0 receipt_1_13_2359_1 receipt_1_13_2360_0 receipt_1_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 0 128 = 10370188400260706875757363040 := by decide +kernel
private theorem receipt_2_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 128 128 = 8949614010588341211569467232 := by decide +kernel
private theorem receipt_2_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 256 128 = 7608661380924932816714555232 := by decide +kernel
private theorem receipt_2_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 384 128 = 6344621743052323062506884960 := by decide +kernel
private theorem receipt_2_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 512 128 = 5154831495478289832190000992 := by decide +kernel
private theorem receipt_2_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 640 128 = 4036671895558514307379425120 := by decide +kernel
private theorem receipt_2_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 768 128 = 2987568986751510661291055477 := by decide +kernel
private theorem receipt_2_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 896 128 = 2004994662815334069695339365 := by decide +kernel
private theorem receipt_2_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 1024 128 = 1086460679649692194079900184 := by decide +kernel
private theorem receipt_2_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 1152 99 = 249497486311792076197897413 := by decide +kernel
private theorem receipt_2_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 0 256 = 19319802410849048087326830272 :=
  phaseBlock_append receipt_2_13_2359_0_part0 receipt_2_13_2359_0_part1 rfl rfl rfl
private theorem receipt_2_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 384 256 = 11499453238530612894696885952 :=
  phaseBlock_append receipt_2_13_2359_0_part3 receipt_2_13_2359_0_part4 rfl rfl rfl
private theorem receipt_2_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 256 384 = 19108114619455545711411441184 :=
  phaseBlock_append receipt_2_13_2359_0_part2 receipt_2_13_2359_0_join1 rfl rfl rfl
private theorem receipt_2_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 0 640 = 38427917030304593798738271456 :=
  phaseBlock_append receipt_2_13_2359_0_join0 receipt_2_13_2359_0_join2 rfl rfl rfl
private theorem receipt_2_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 640 256 = 7024240882310024968670480597 :=
  phaseBlock_append receipt_2_13_2359_0_part5 receipt_2_13_2359_0_part6 rfl rfl rfl
private theorem receipt_2_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 1024 227 = 1335958165961484270277797597 :=
  phaseBlock_append receipt_2_13_2359_0_part8 receipt_2_13_2359_0_part9 rfl rfl rfl
private theorem receipt_2_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 896 355 = 3340952828776818339973136962 :=
  phaseBlock_append receipt_2_13_2359_0_part7 receipt_2_13_2359_0_join5 rfl rfl rfl
private theorem receipt_2_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 640 611 = 10365193711086843308643617559 :=
  phaseBlock_append receipt_2_13_2359_0_join4 receipt_2_13_2359_0_join6 rfl rfl rfl
private theorem receipt_2_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 0) 0 1251 = 48793110741391437107381889015 :=
  phaseBlock_append receipt_2_13_2359_0_join3 receipt_2_13_2359_0_join7 rfl rfl rfl

private theorem receipt_2_13_2359_0 : fastPhase (bank 2 13).shape 179818 2359 44 1 0 7 0 = 48793110741391437107381889015 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2359_0_join8

private theorem receipt_2_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 0 128 = 10358915917760986107433298784 := by decide +kernel
private theorem receipt_2_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 128 128 = 8938956594159180495556008800 := by decide +kernel
private theorem receipt_2_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 256 128 = 7598598278679882539906960224 := by decide +kernel
private theorem receipt_2_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 384 128 = 6335132548876675560562539360 := by decide +kernel
private theorem receipt_2_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 512 128 = 5145896146671442373259848544 := by decide +kernel
private theorem receipt_2_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 640 128 = 4028270670476332075839396704 := by decide +kernel
private theorem receipt_2_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 768 128 = 2979682501810607514178008159 := by decide +kernel
private theorem receipt_2_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 896 128 = 1997603863262366245065511771 := by decide +kernel
private theorem receipt_2_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 1024 128 = 1079546840239548340812765591 := by decide +kernel
private theorem receipt_2_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 1152 99 = 244465499535894260966190417 := by decide +kernel
private theorem receipt_2_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 0 256 = 19297872511920166602989307584 :=
  phaseBlock_append receipt_2_13_2359_1_part0 receipt_2_13_2359_1_part1 rfl rfl rfl
private theorem receipt_2_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 384 256 = 11481028695548117933822387904 :=
  phaseBlock_append receipt_2_13_2359_1_part3 receipt_2_13_2359_1_part4 rfl rfl rfl
private theorem receipt_2_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 256 384 = 19079626974228000473729348128 :=
  phaseBlock_append receipt_2_13_2359_1_part2 receipt_2_13_2359_1_join1 rfl rfl rfl
private theorem receipt_2_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 0 640 = 38377499486148167076718655712 :=
  phaseBlock_append receipt_2_13_2359_1_join0 receipt_2_13_2359_1_join2 rfl rfl rfl
private theorem receipt_2_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 640 256 = 7007953172286939590017404863 :=
  phaseBlock_append receipt_2_13_2359_1_part5 receipt_2_13_2359_1_part6 rfl rfl rfl
private theorem receipt_2_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 1024 227 = 1324012339775442601778956008 :=
  phaseBlock_append receipt_2_13_2359_1_part8 receipt_2_13_2359_1_part9 rfl rfl rfl
private theorem receipt_2_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 896 355 = 3321616203037808846844467779 :=
  phaseBlock_append receipt_2_13_2359_1_part7 receipt_2_13_2359_1_join5 rfl rfl rfl
private theorem receipt_2_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 640 611 = 10329569375324748436861872642 :=
  phaseBlock_append receipt_2_13_2359_1_join4 receipt_2_13_2359_1_join6 rfl rfl rfl
private theorem receipt_2_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2359 44 1 0 7 1) 0 1251 = 48707068861472915513580528354 :=
  phaseBlock_append receipt_2_13_2359_1_join3 receipt_2_13_2359_1_join7 rfl rfl rfl

private theorem receipt_2_13_2359_1 : fastPhase (bank 2 13).shape 179818 2359 44 1 0 7 1 = 48707068861472915513580528354 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2359_1_join8

private theorem receipt_2_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 0 128 = 10370280777508048038763253760 := by decide +kernel
private theorem receipt_2_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 128 128 = 8949689080668560384198897664 := by decide +kernel
private theorem receipt_2_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 256 128 = 7608721121309881499823673344 := by decide +kernel
private theorem receipt_2_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 384 128 = 6344668046328580604990730240 := by decide +kernel
private theorem receipt_2_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 512 128 = 5154866170875485864901464064 := by decide +kernel
private theorem receipt_2_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 640 128 = 4036696670466875963096002560 := by decide +kernel
private theorem receipt_2_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 768 128 = 2987585500765957705993213683 := by decide +kernel
private theorem receipt_2_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 896 128 = 2005004471525929989696550689 := by decide +kernel
private theorem receipt_2_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 1024 128 = 1086465294751039425751994136 := by decide +kernel
private theorem receipt_2_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 1152 99 = 249498405648199871979088608 := by decide +kernel
private theorem receipt_2_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 0 256 = 19319969858176608422962151424 :=
  phaseBlock_append receipt_2_13_2360_0_part0 receipt_2_13_2360_0_part1 rfl rfl rfl
private theorem receipt_2_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 384 256 = 11499534217204066469892194304 :=
  phaseBlock_append receipt_2_13_2360_0_part3 receipt_2_13_2360_0_part4 rfl rfl rfl
private theorem receipt_2_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 256 384 = 19108255338513947969715867648 :=
  phaseBlock_append receipt_2_13_2360_0_part2 receipt_2_13_2360_0_join1 rfl rfl rfl
private theorem receipt_2_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 0 640 = 38428225196690556392678019072 :=
  phaseBlock_append receipt_2_13_2360_0_join0 receipt_2_13_2360_0_join2 rfl rfl rfl
private theorem receipt_2_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 640 256 = 7024282171232833669089216243 :=
  phaseBlock_append receipt_2_13_2360_0_part5 receipt_2_13_2360_0_part6 rfl rfl rfl
private theorem receipt_2_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 1024 227 = 1335963700399239297731082744 :=
  phaseBlock_append receipt_2_13_2360_0_part8 receipt_2_13_2360_0_part9 rfl rfl rfl
private theorem receipt_2_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 896 355 = 3340968171925169287427633433 :=
  phaseBlock_append receipt_2_13_2360_0_part7 receipt_2_13_2360_0_join5 rfl rfl rfl
private theorem receipt_2_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 640 611 = 10365250343158002956516849676 :=
  phaseBlock_append receipt_2_13_2360_0_join4 receipt_2_13_2360_0_join6 rfl rfl rfl
private theorem receipt_2_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 0) 0 1251 = 48793475539848559349194868748 :=
  phaseBlock_append receipt_2_13_2360_0_join3 receipt_2_13_2360_0_join7 rfl rfl rfl

private theorem receipt_2_13_2360_0 : fastPhase (bank 2 13).shape 179818 2360 44 1 0 7 0 = 48793475539848559349194868748 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2360_0_join8

private theorem receipt_2_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 0 128 = 10359008211853961603268945984 := by decide +kernel
private theorem receipt_2_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 128 128 = 8939031589408637174713051200 := by decide +kernel
private theorem receipt_2_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 256 128 = 7598657952137054737619855424 := by decide +kernel
private theorem receipt_2_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 384 128 = 6335178792715994499420317760 := by decide +kernel
private theorem receipt_2_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 512 128 = 5145930769718794619292231744 := by decide +kernel
private theorem receipt_2_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 640 128 = 4028295399726542780650711104 := by decide +kernel
private theorem receipt_2_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 768 128 = 2979698976491343547429601904 := by decide +kernel
private theorem receipt_2_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 896 128 = 1997613638643910691049970809 := by decide +kernel
private theorem receipt_2_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 1024 128 = 1079551427637507628582986372 := by decide +kernel
private theorem receipt_2_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 1152 99 = 244466401066165705737055860 := by decide +kernel
private theorem receipt_2_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 0 256 = 19298039801262598777981997184 :=
  phaseBlock_append receipt_2_13_2360_1_part0 receipt_2_13_2360_1_part1 rfl rfl rfl
private theorem receipt_2_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 384 256 = 11481109562434789118712549504 :=
  phaseBlock_append receipt_2_13_2360_1_part3 receipt_2_13_2360_1_part4 rfl rfl rfl
private theorem receipt_2_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 256 384 = 19079767514571843856332404928 :=
  phaseBlock_append receipt_2_13_2360_1_part2 receipt_2_13_2360_1_join1 rfl rfl rfl
private theorem receipt_2_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 0 640 = 38377807315834442634314402112 :=
  phaseBlock_append receipt_2_13_2360_1_join0 receipt_2_13_2360_1_join2 rfl rfl rfl
private theorem receipt_2_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 640 256 = 7007994376217886328080313008 :=
  phaseBlock_append receipt_2_13_2360_1_part5 receipt_2_13_2360_1_part6 rfl rfl rfl
private theorem receipt_2_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 1024 227 = 1324017828703673334320042232 :=
  phaseBlock_append receipt_2_13_2360_1_part8 receipt_2_13_2360_1_part9 rfl rfl rfl
private theorem receipt_2_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 896 355 = 3321631467347584025370013041 :=
  phaseBlock_append receipt_2_13_2360_1_part7 receipt_2_13_2360_1_join5 rfl rfl rfl
private theorem receipt_2_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 640 611 = 10329625843565470353450326049 :=
  phaseBlock_append receipt_2_13_2360_1_join4 receipt_2_13_2360_1_join6 rfl rfl rfl
private theorem receipt_2_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179818 2360 44 1 0 7 1) 0 1251 = 48707433159399912987764728161 :=
  phaseBlock_append receipt_2_13_2360_1_join3 receipt_2_13_2360_1_join7 rfl rfl rfl

private theorem receipt_2_13_2360_1 : fastPhase (bank 2 13).shape 179818 2360 44 1 0 7 1 = 48707433159399912987764728161 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2360_1_join8

theorem receipt_2_13 : Checked (bank 2 13) 44 0 7 := by
  refine checked_from_values (bank 2 13) 44 0 7
    (P3_7_1.checked (bank 2 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_13_2359_0 receipt_2_13_2359_1 receipt_2_13_2360_0 receipt_2_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 0 128 = 2388729501364004751759068384 := by decide +kernel
private theorem receipt_3_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 128 128 = 2077324944143721532855786720 := by decide +kernel
private theorem receipt_3_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 256 128 = 1779673556709537959399910624 := by decide +kernel
private theorem receipt_3_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 384 128 = 1496176934880251356496936160 := by decide +kernel
private theorem receipt_3_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 512 128 = 1227233021698527775326244064 := by decide +kernel
private theorem receipt_3_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 640 128 = 973236116885250636666035424 := by decide +kernel
private theorem receipt_3_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 768 128 = 734576886293869374418267360 := by decide +kernel
private theorem receipt_3_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 896 128 = 511642371364748079133588704 := by decide +kernel
private theorem receipt_3_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 1024 128 = 304815998579514141536275680 := by decide +kernel
private theorem receipt_3_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 1152 128 = 114477588915406896049167584 := by decide +kernel
private theorem receipt_3_13_2359_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 1280 18 = 1793708541504986703000831 := by decide +kernel
private theorem receipt_3_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 0 256 = 4466054445507726284614855104 :=
  phaseBlock_append receipt_3_13_2359_0_part0 receipt_3_13_2359_0_part1 rfl rfl rfl
private theorem receipt_3_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 384 256 = 2723409956578779131823180224 :=
  phaseBlock_append receipt_3_13_2359_0_part3 receipt_3_13_2359_0_part4 rfl rfl rfl
private theorem receipt_3_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 256 384 = 4503083513288317091223090848 :=
  phaseBlock_append receipt_3_13_2359_0_part2 receipt_3_13_2359_0_join1 rfl rfl rfl
private theorem receipt_3_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 0 640 = 8969137958796043375837945952 :=
  phaseBlock_append receipt_3_13_2359_0_join0 receipt_3_13_2359_0_join2 rfl rfl rfl
private theorem receipt_3_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 768 256 = 1246219257658617453551856064 :=
  phaseBlock_append receipt_3_13_2359_0_part6 receipt_3_13_2359_0_part7 rfl rfl rfl
private theorem receipt_3_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 640 384 = 2219455374543868090217891488 :=
  phaseBlock_append receipt_3_13_2359_0_part5 receipt_3_13_2359_0_join4 rfl rfl rfl
private theorem receipt_3_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 1152 146 = 116271297456911882752168415 :=
  phaseBlock_append receipt_3_13_2359_0_part9 receipt_3_13_2359_0_part10 rfl rfl rfl
private theorem receipt_3_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 1024 274 = 421087296036426024288444095 :=
  phaseBlock_append receipt_3_13_2359_0_part8 receipt_3_13_2359_0_join6 rfl rfl rfl
private theorem receipt_3_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 640 658 = 2640542670580294114506335583 :=
  phaseBlock_append receipt_3_13_2359_0_join5 receipt_3_13_2359_0_join7 rfl rfl rfl
private theorem receipt_3_13_2359_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 0) 0 1298 = 11609680629376337490344281535 :=
  phaseBlock_append receipt_3_13_2359_0_join3 receipt_3_13_2359_0_join8 rfl rfl rfl

private theorem receipt_3_13_2359_0 : fastPhase (bank 3 13).shape 179818 2359 44 1 1 1 0 = 11609680629376337490344281535 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2359_0_join9

private theorem receipt_3_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 0 128 = 2386276713303041943480429408 := by decide +kernel
private theorem receipt_3_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 128 128 = 2074973560205640320174709600 := by decide +kernel
private theorem receipt_3_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 256 128 = 1777426992514797587008047968 := by decide +kernel
private theorem receipt_3_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 384 128 = 1494038575981348611436100448 := by decide +kernel
private theorem receipt_3_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 512 128 = 1225206223656777052187110240 := by decide +kernel
private theorem receipt_3_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 640 128 = 971324205347564002786843488 := by decide +kernel
private theorem receipt_3_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 768 128 = 732783157069536635083524960 := by decide +kernel
private theorem receipt_3_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 896 128 = 509970090502216842772773728 := by decide +kernel
private theorem receipt_3_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 1024 128 = 303268402443169884922538848 := by decide +kernel
private theorem receipt_3_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 1152 128 = 113057884262353029498035040 := by decide +kernel
private theorem receipt_3_13_2359_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 1280 18 = 1604501679627994823956812 := by decide +kernel
private theorem receipt_3_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 0 256 = 4461250273508682263655139008 :=
  phaseBlock_append receipt_3_13_2359_1_part0 receipt_3_13_2359_1_part1 rfl rfl rfl
private theorem receipt_3_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 384 256 = 2719244799638125663623210688 :=
  phaseBlock_append receipt_3_13_2359_1_part3 receipt_3_13_2359_1_part4 rfl rfl rfl
private theorem receipt_3_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 256 384 = 4496671792152923250631258656 :=
  phaseBlock_append receipt_3_13_2359_1_part2 receipt_3_13_2359_1_join1 rfl rfl rfl
private theorem receipt_3_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 0 640 = 8957922065661605514286397664 :=
  phaseBlock_append receipt_3_13_2359_1_join0 receipt_3_13_2359_1_join2 rfl rfl rfl
private theorem receipt_3_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 768 256 = 1242753247571753477856298688 :=
  phaseBlock_append receipt_3_13_2359_1_part6 receipt_3_13_2359_1_part7 rfl rfl rfl
private theorem receipt_3_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 640 384 = 2214077452919317480643142176 :=
  phaseBlock_append receipt_3_13_2359_1_part5 receipt_3_13_2359_1_join4 rfl rfl rfl
private theorem receipt_3_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 1152 146 = 114662385941981024321991852 :=
  phaseBlock_append receipt_3_13_2359_1_part9 receipt_3_13_2359_1_part10 rfl rfl rfl
private theorem receipt_3_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 1024 274 = 417930788385150909244530700 :=
  phaseBlock_append receipt_3_13_2359_1_part8 receipt_3_13_2359_1_join6 rfl rfl rfl
private theorem receipt_3_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 640 658 = 2632008241304468389887672876 :=
  phaseBlock_append receipt_3_13_2359_1_join5 receipt_3_13_2359_1_join7 rfl rfl rfl
private theorem receipt_3_13_2359_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2359 44 1 1 1 1) 0 1298 = 11589930306966073904174070540 :=
  phaseBlock_append receipt_3_13_2359_1_join3 receipt_3_13_2359_1_join8 rfl rfl rfl

private theorem receipt_3_13_2359_1 : fastPhase (bank 3 13).shape 179818 2359 44 1 1 1 1 = 11589930306966073904174070540 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2359_1_join9

private theorem receipt_3_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 0 128 = 2388750482386761583437106720 := by decide +kernel
private theorem receipt_3_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 128 128 = 2077341333216175669614591520 := by decide +kernel
private theorem receipt_3_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 256 128 = 1779686035140164720271175200 := by decide +kernel
private theorem receipt_3_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 384 128 = 1496186135521572866064817696 := by decide +kernel
private theorem receipt_3_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 512 128 = 1227239529308619192800579104 := by decide +kernel
private theorem receipt_3_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 640 128 = 973240468488366775653334560 := by decide +kernel
private theorem receipt_3_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 768 128 = 734579571540191713390489120 := by decide +kernel
private theorem receipt_3_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 896 128 = 511643832889252162594692640 := by decide +kernel
private theorem receipt_3_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 1024 128 = 304816632359957371886554656 := by decide +kernel
private theorem receipt_3_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 1152 128 = 114477744629436716147359264 := by decide +kernel
private theorem receipt_3_13_2360_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 1280 18 = 1793710041413516908296405 := by decide +kernel
private theorem receipt_3_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 0 256 = 4466091815602937253051698240 :=
  phaseBlock_append receipt_3_13_2360_0_part0 receipt_3_13_2360_0_part1 rfl rfl rfl
private theorem receipt_3_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 384 256 = 2723425664830192058865396800 :=
  phaseBlock_append receipt_3_13_2360_0_part3 receipt_3_13_2360_0_part4 rfl rfl rfl
private theorem receipt_3_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 256 384 = 4503111699970356779136572000 :=
  phaseBlock_append receipt_3_13_2360_0_part2 receipt_3_13_2360_0_join1 rfl rfl rfl
private theorem receipt_3_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 0 640 = 8969203515573294032188270240 :=
  phaseBlock_append receipt_3_13_2360_0_join0 receipt_3_13_2360_0_join2 rfl rfl rfl
private theorem receipt_3_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 768 256 = 1246223404429443875985181760 :=
  phaseBlock_append receipt_3_13_2360_0_part6 receipt_3_13_2360_0_part7 rfl rfl rfl
private theorem receipt_3_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 640 384 = 2219463872917810651638516320 :=
  phaseBlock_append receipt_3_13_2360_0_part5 receipt_3_13_2360_0_join4 rfl rfl rfl
private theorem receipt_3_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 1152 146 = 116271454670850233055655669 :=
  phaseBlock_append receipt_3_13_2360_0_part9 receipt_3_13_2360_0_part10 rfl rfl rfl
private theorem receipt_3_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 1024 274 = 421088087030807604942210325 :=
  phaseBlock_append receipt_3_13_2360_0_part8 receipt_3_13_2360_0_join6 rfl rfl rfl
private theorem receipt_3_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 640 658 = 2640551959948618256580726645 :=
  phaseBlock_append receipt_3_13_2360_0_join5 receipt_3_13_2360_0_join7 rfl rfl rfl
private theorem receipt_3_13_2360_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 0) 0 1298 = 11609755475521912288768996885 :=
  phaseBlock_append receipt_3_13_2360_0_join3 receipt_3_13_2360_0_join8 rfl rfl rfl

private theorem receipt_3_13_2360_0 : fastPhase (bank 3 13).shape 179818 2360 44 1 1 1 0 = 11609755475521912288768996885 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2360_0_join9

private theorem receipt_3_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 0 128 = 2386297669387201350039547680 := by decide +kernel
private theorem receipt_3_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 128 128 = 2074989927953277494049586976 := by decide +kernel
private theorem receipt_3_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 256 128 = 1777439452966322139506003744 := by decide +kernel
private theorem receipt_3_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 384 128 = 1494047761723411314043019040 := by decide +kernel
private theorem receipt_3_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 512 128 = 1225212719183770430643564320 := by decide +kernel
private theorem receipt_3_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 640 128 = 971328547422243321861996320 := by decide +kernel
private theorem receipt_3_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 768 128 = 732785835082761274046811936 := by decide +kernel
private theorem receipt_3_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 896 128 = 509971546831812061563363104 := by decide +kernel
private theorem receipt_3_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 1024 128 = 303269032811908981016571680 := by decide +kernel
private theorem receipt_3_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 1152 128 = 113058038095059885473644320 := by decide +kernel
private theorem receipt_3_13_2360_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 1280 18 = 1604503023341091943504260 := by decide +kernel
private theorem receipt_3_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 0 256 = 4461287597340478844089134656 :=
  phaseBlock_append receipt_3_13_2360_1_part0 receipt_3_13_2360_1_part1 rfl rfl rfl
private theorem receipt_3_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 384 256 = 2719260480907181744686583360 :=
  phaseBlock_append receipt_3_13_2360_1_part3 receipt_3_13_2360_1_part4 rfl rfl rfl
private theorem receipt_3_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 256 384 = 4496699933873503884192587104 :=
  phaseBlock_append receipt_3_13_2360_1_part2 receipt_3_13_2360_1_join1 rfl rfl rfl
private theorem receipt_3_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 0 640 = 8957987531213982728281721760 :=
  phaseBlock_append receipt_3_13_2360_1_join0 receipt_3_13_2360_1_join2 rfl rfl rfl
private theorem receipt_3_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 768 256 = 1242757381914573335610175040 :=
  phaseBlock_append receipt_3_13_2360_1_part6 receipt_3_13_2360_1_part7 rfl rfl rfl
private theorem receipt_3_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 640 384 = 2214085929336816657472171360 :=
  phaseBlock_append receipt_3_13_2360_1_part5 receipt_3_13_2360_1_join4 rfl rfl rfl
private theorem receipt_3_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 1152 146 = 114662541118400977417148580 :=
  phaseBlock_append receipt_3_13_2360_1_part9 receipt_3_13_2360_1_part10 rfl rfl rfl
private theorem receipt_3_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 1024 274 = 417931573930309958433720260 :=
  phaseBlock_append receipt_3_13_2360_1_part8 receipt_3_13_2360_1_join6 rfl rfl rfl
private theorem receipt_3_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 640 658 = 2632017503267126615905891620 :=
  phaseBlock_append receipt_3_13_2360_1_join5 receipt_3_13_2360_1_join7 rfl rfl rfl
private theorem receipt_3_13_2360_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179818 2360 44 1 1 1 1) 0 1298 = 11590005034481109344187613380 :=
  phaseBlock_append receipt_3_13_2360_1_join3 receipt_3_13_2360_1_join8 rfl rfl rfl

private theorem receipt_3_13_2360_1 : fastPhase (bank 3 13).shape 179818 2360 44 1 1 1 1 = 11590005034481109344187613380 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2360_1_join9

theorem receipt_3_13 : Checked (bank 3 13) 44 1 1 := by
  refine checked_from_values (bank 3 13) 44 1 1
    (P3_7_1.checked (bank 3 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1297)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_13_2359_0 receipt_3_13_2359_1 receipt_3_13_2360_0 receipt_3_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 0 128 = 188046750371445458019926050848 := by decide +kernel
private theorem receipt_0_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 128 128 = 172122232215881481632092444704 := by decide +kernel
private theorem receipt_0_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 256 128 = 156678800382563119498779371552 := by decide +kernel
private theorem receipt_0_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 384 128 = 141709014374113107831609325600 := by decide +kernel
private theorem receipt_0_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 512 128 = 127205445672525906447557969952 := by decide +kernel
private theorem receipt_0_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 640 128 = 113160677732884473601330518048 := by decide +kernel
private theorem receipt_0_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 768 128 = 99567305977077040817738115104 := by decide +kernel
private theorem receipt_0_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 896 128 = 86417937787513887724074219552 := by decide +kernel
private theorem receipt_0_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1024 128 = 73705192500844116882490984480 := by decide +kernel
private theorem receipt_0_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1152 128 = 61421701401672428622375639072 := by decide +kernel
private theorem receipt_0_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1280 128 = 49560115150940743168219642177 := by decide +kernel
private theorem receipt_0_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1408 128 = 38113103769695586968142533409 := by decide +kernel
private theorem receipt_0_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1536 128 = 27073315904550890293495281863 := by decide +kernel
private theorem receipt_0_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1664 128 = 16433405839689445807990096537 := by decide +kernel
private theorem receipt_0_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1792 128 = 6186039844288818705479299267 := by decide +kernel
private theorem receipt_0_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1920 15 = 72002622137542673345227716 := by decide +kernel
private theorem receipt_0_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 0 256 = 360168982587326939652018495552 :=
  phaseBlock_append receipt_0_14_2359_0_part0 receipt_0_14_2359_0_part1 rfl rfl rfl
private theorem receipt_0_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 256 256 = 298387814756676227330388697152 :=
  phaseBlock_append receipt_0_14_2359_0_part2 receipt_0_14_2359_0_part3 rfl rfl rfl
private theorem receipt_0_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 0 512 = 658556797344003166982407192704 :=
  phaseBlock_append receipt_0_14_2359_0_join0 receipt_0_14_2359_0_join1 rfl rfl rfl
private theorem receipt_0_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 512 256 = 240366123405410380048888488000 :=
  phaseBlock_append receipt_0_14_2359_0_part4 receipt_0_14_2359_0_part5 rfl rfl rfl
private theorem receipt_0_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 768 256 = 185985243764590928541812334656 :=
  phaseBlock_append receipt_0_14_2359_0_part6 receipt_0_14_2359_0_part7 rfl rfl rfl
private theorem receipt_0_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 512 512 = 426351367170001308590700822656 :=
  phaseBlock_append receipt_0_14_2359_0_join3 receipt_0_14_2359_0_join4 rfl rfl rfl
private theorem receipt_0_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 0 1024 = 1084908164514004475573108015360 :=
  phaseBlock_append receipt_0_14_2359_0_join2 receipt_0_14_2359_0_join5 rfl rfl rfl
private theorem receipt_0_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1024 256 = 135126893902516545504866623552 :=
  phaseBlock_append receipt_0_14_2359_0_part8 receipt_0_14_2359_0_part9 rfl rfl rfl
private theorem receipt_0_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1280 256 = 87673218920636330136362175586 :=
  phaseBlock_append receipt_0_14_2359_0_part10 receipt_0_14_2359_0_part11 rfl rfl rfl
private theorem receipt_0_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1024 512 = 222800112823152875641228799138 :=
  phaseBlock_append receipt_0_14_2359_0_join7 receipt_0_14_2359_0_join8 rfl rfl rfl
private theorem receipt_0_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1536 256 = 43506721744240336101485378400 :=
  phaseBlock_append receipt_0_14_2359_0_part12 receipt_0_14_2359_0_part13 rfl rfl rfl
private theorem receipt_0_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1792 143 = 6258042466426361378824526983 :=
  phaseBlock_append receipt_0_14_2359_0_part14 receipt_0_14_2359_0_part15 rfl rfl rfl
private theorem receipt_0_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1536 399 = 49764764210666697480309905383 :=
  phaseBlock_append receipt_0_14_2359_0_join10 receipt_0_14_2359_0_join11 rfl rfl rfl
private theorem receipt_0_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 1024 911 = 272564877033819573121538704521 :=
  phaseBlock_append receipt_0_14_2359_0_join9 receipt_0_14_2359_0_join12 rfl rfl rfl
private theorem receipt_0_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 0) 0 1935 = 1357473041547824048694646719881 :=
  phaseBlock_append receipt_0_14_2359_0_join6 receipt_0_14_2359_0_join13 rfl rfl rfl

private theorem receipt_0_14_2359_0 : fastPhase (bank 0 14).shape 179818 2359 73 1 0 1 0 = 1357473041547824048694646719881 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2359_0_join14

private theorem receipt_0_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 0 128 = 187922110365034860046236250080 := by decide +kernel
private theorem receipt_0_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 128 128 = 172001253709762564805998968800 := by decide +kernel
private theorem receipt_0_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 256 128 = 156561427073015626125740675040 := by decide +kernel
private theorem receipt_0_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 384 128 = 141595190048726843527973412832 := by decide +kernel
private theorem receipt_0_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 512 128 = 127095114210152625099414056928 := by decide +kernel
private theorem receipt_0_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 640 128 = 113053783103589762323360694240 := by decide +kernel
private theorem receipt_0_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 768 128 = 99463792242092204912069005280 := by decide +kernel
private theorem receipt_0_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 896 128 = 86317749099187835639128645600 := by decide +kernel
private theorem receipt_0_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1024 128 = 73608273102595245171839627232 := by decide +kernel
private theorem receipt_0_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1152 128 = 61327995627940506903588700128 := by decide +kernel
private theorem receipt_0_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1280 128 = 49469567413857511761029604476 := by decide +kernel
private theorem receipt_0_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1408 128 = 38025658529485167595179295944 := by decide +kernel
private theorem receipt_0_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1536 128 = 26988917704094781720252045112 := by decide +kernel
private theorem receipt_0_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1664 128 = 16351999312902872402078150001 := by decide +kernel
private theorem receipt_0_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1792 128 = 6107569716011356565292776811 := by decide +kernel
private theorem receipt_0_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1920 15 = 62996570935108556812686375 := by decide +kernel
private theorem receipt_0_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 0 256 = 359923364074797424852235218880 :=
  phaseBlock_append receipt_0_14_2359_1_part0 receipt_0_14_2359_1_part1 rfl rfl rfl
private theorem receipt_0_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 256 256 = 298156617121742469653714087872 :=
  phaseBlock_append receipt_0_14_2359_1_part2 receipt_0_14_2359_1_part3 rfl rfl rfl
private theorem receipt_0_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 0 512 = 658079981196539894505949306752 :=
  phaseBlock_append receipt_0_14_2359_1_join0 receipt_0_14_2359_1_join1 rfl rfl rfl
private theorem receipt_0_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 512 256 = 240148897313742387422774751168 :=
  phaseBlock_append receipt_0_14_2359_1_part4 receipt_0_14_2359_1_part5 rfl rfl rfl
private theorem receipt_0_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 768 256 = 185781541341280040551197650880 :=
  phaseBlock_append receipt_0_14_2359_1_part6 receipt_0_14_2359_1_part7 rfl rfl rfl
private theorem receipt_0_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 512 512 = 425930438655022427973972402048 :=
  phaseBlock_append receipt_0_14_2359_1_join3 receipt_0_14_2359_1_join4 rfl rfl rfl
private theorem receipt_0_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 0 1024 = 1084010419851562322479921708800 :=
  phaseBlock_append receipt_0_14_2359_1_join2 receipt_0_14_2359_1_join5 rfl rfl rfl
private theorem receipt_0_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1024 256 = 134936268730535752075428327360 :=
  phaseBlock_append receipt_0_14_2359_1_part8 receipt_0_14_2359_1_part9 rfl rfl rfl
private theorem receipt_0_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1280 256 = 87495225943342679356208900420 :=
  phaseBlock_append receipt_0_14_2359_1_part10 receipt_0_14_2359_1_part11 rfl rfl rfl
private theorem receipt_0_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1024 512 = 222431494673878431431637227780 :=
  phaseBlock_append receipt_0_14_2359_1_join7 receipt_0_14_2359_1_join8 rfl rfl rfl
private theorem receipt_0_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1536 256 = 43340917016997654122330195113 :=
  phaseBlock_append receipt_0_14_2359_1_part12 receipt_0_14_2359_1_part13 rfl rfl rfl
private theorem receipt_0_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1792 143 = 6170566286946465122105463186 :=
  phaseBlock_append receipt_0_14_2359_1_part14 receipt_0_14_2359_1_part15 rfl rfl rfl
private theorem receipt_0_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1536 399 = 49511483303944119244435658299 :=
  phaseBlock_append receipt_0_14_2359_1_join10 receipt_0_14_2359_1_join11 rfl rfl rfl
private theorem receipt_0_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 1024 911 = 271942977977822550676072886079 :=
  phaseBlock_append receipt_0_14_2359_1_join9 receipt_0_14_2359_1_join12 rfl rfl rfl
private theorem receipt_0_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2359 73 1 0 1 1) 0 1935 = 1355953397829384873155994594879 :=
  phaseBlock_append receipt_0_14_2359_1_join6 receipt_0_14_2359_1_join13 rfl rfl rfl

private theorem receipt_0_14_2359_1 : fastPhase (bank 0 14).shape 179818 2359 73 1 0 1 1 = 1355953397829384873155994594879 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2359_1_join14

private theorem receipt_0_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 0 128 = 188048438186846201370202008576 := by decide +kernel
private theorem receipt_0_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 128 128 = 172123719819842791445912128512 := by decide +kernel
private theorem receipt_0_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 256 128 = 156680101300572590566879669248 := by decide +kernel
private theorem receipt_0_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 384 128 = 141710141875218041664381373440 := by decide +kernel
private theorem receipt_0_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 512 128 = 127206412769750911323194354688 := by decide +kernel
private theorem receipt_0_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 640 128 = 113161497183648844711646923776 := by decide +kernel
private theorem receipt_0_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 768 128 = 99567990283611920511669414912 := by decide +kernel
private theorem receipt_0_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 896 128 = 86418499197279205848845011968 := by decide +kernel
private theorem receipt_0_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1024 128 = 73705643006945311222460574720 := by decide +kernel
private theorem receipt_0_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1152 128 = 61422052743276945435557465088 := by decide +kernel
private theorem receipt_0_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1280 128 = 49560378591846346848179646923 := by decide +kernel
private theorem receipt_0_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1408 128 = 38113290519862009528942418170 := by decide +kernel
private theorem receipt_0_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1536 128 = 27073437123327769222205217503 := by decide +kernel
private theorem receipt_0_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1664 128 = 16433472414363018324281805646 := by decide +kernel
private theorem receipt_0_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1792 128 = 6186062390687245585647284351 := by decide +kernel
private theorem receipt_0_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1920 15 = 72002862674276253140881296 := by decide +kernel
private theorem receipt_0_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 0 256 = 360172158006688992816114137088 :=
  phaseBlock_append receipt_0_14_2360_0_part0 receipt_0_14_2360_0_part1 rfl rfl rfl
private theorem receipt_0_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 256 256 = 298390243175790632231261042688 :=
  phaseBlock_append receipt_0_14_2360_0_part2 receipt_0_14_2360_0_part3 rfl rfl rfl
private theorem receipt_0_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 0 512 = 658562401182479625047375179776 :=
  phaseBlock_append receipt_0_14_2360_0_join0 receipt_0_14_2360_0_join1 rfl rfl rfl
private theorem receipt_0_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 512 256 = 240367909953399756034841278464 :=
  phaseBlock_append receipt_0_14_2360_0_part4 receipt_0_14_2360_0_part5 rfl rfl rfl
private theorem receipt_0_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 768 256 = 185986489480891126360514426880 :=
  phaseBlock_append receipt_0_14_2360_0_part6 receipt_0_14_2360_0_part7 rfl rfl rfl
private theorem receipt_0_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 512 512 = 426354399434290882395355705344 :=
  phaseBlock_append receipt_0_14_2360_0_join3 receipt_0_14_2360_0_join4 rfl rfl rfl
private theorem receipt_0_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 0 1024 = 1084916800616770507442730885120 :=
  phaseBlock_append receipt_0_14_2360_0_join2 receipt_0_14_2360_0_join5 rfl rfl rfl
private theorem receipt_0_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1024 256 = 135127695750222256658018039808 :=
  phaseBlock_append receipt_0_14_2360_0_part8 receipt_0_14_2360_0_part9 rfl rfl rfl
private theorem receipt_0_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1280 256 = 87673669111708356377122065093 :=
  phaseBlock_append receipt_0_14_2360_0_part10 receipt_0_14_2360_0_part11 rfl rfl rfl
private theorem receipt_0_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1024 512 = 222801364861930613035140104901 :=
  phaseBlock_append receipt_0_14_2360_0_join7 receipt_0_14_2360_0_join8 rfl rfl rfl
private theorem receipt_0_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1536 256 = 43506909537690787546487023149 :=
  phaseBlock_append receipt_0_14_2360_0_part12 receipt_0_14_2360_0_part13 rfl rfl rfl
private theorem receipt_0_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1792 143 = 6258065253361521838788165647 :=
  phaseBlock_append receipt_0_14_2360_0_part14 receipt_0_14_2360_0_part15 rfl rfl rfl
private theorem receipt_0_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1536 399 = 49764974791052309385275188796 :=
  phaseBlock_append receipt_0_14_2360_0_join10 receipt_0_14_2360_0_join11 rfl rfl rfl
private theorem receipt_0_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 1024 911 = 272566339652982922420415293697 :=
  phaseBlock_append receipt_0_14_2360_0_join9 receipt_0_14_2360_0_join12 rfl rfl rfl
private theorem receipt_0_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 0) 0 1935 = 1357483140269753429863146178817 :=
  phaseBlock_append receipt_0_14_2360_0_join6 receipt_0_14_2360_0_join13 rfl rfl rfl

private theorem receipt_0_14_2360_0 : fastPhase (bank 0 14).shape 179818 2360 73 1 0 1 0 = 1357483140269753429863146178817 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2360_0_join14

private theorem receipt_0_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 0 128 = 187923797264357506830440948928 := by decide +kernel
private theorem receipt_0_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 128 128 = 172002740450957698529349362880 := by decide +kernel
private theorem receipt_0_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 256 128 = 156562727180359174200605500608 := by decide +kernel
private theorem receipt_0_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 384 128 = 141596316790056727122637907136 := by decide +kernel
private theorem receipt_0_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 512 128 = 127096080597286357880557102272 := by decide +kernel
private theorem receipt_0_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 640 128 = 113054601892741829296206406848 := by decide +kernel
private theorem receipt_0_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 768 128 = 99464475934291221358212768960 := by decide +kernel
private theorem receipt_0_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 896 128 = 86318309940693486152037590208 := by decide +kernel
private theorem receipt_0_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1024 128 = 73608723085315002790027551936 := by decide +kernel
private theorem receipt_0_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1152 128 = 61328346489846132341465441472 := by decide +kernel
private theorem receipt_0_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1280 128 = 49469830417941591865590779593 := by decide +kernel
private theorem receipt_0_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1408 128 = 38025844884761866504962616274 := by decide +kernel
private theorem receipt_0_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1536 128 = 26989038568671633070544832838 := by decide +kernel
private theorem receipt_0_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1664 128 = 16352065572826733949168582068 := by decide +kernel
private theorem receipt_0_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1792 128 = 6107591985864214791289291860 := by decide +kernel
private theorem receipt_0_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1920 15 = 62996781507095486618112006 := by decide +kernel
private theorem receipt_0_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 0 256 = 359926537715315205359790311808 :=
  phaseBlock_append receipt_0_14_2360_1_part0 receipt_0_14_2360_1_part1 rfl rfl rfl
private theorem receipt_0_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 256 256 = 298159043970415901323243407744 :=
  phaseBlock_append receipt_0_14_2360_1_part2 receipt_0_14_2360_1_part3 rfl rfl rfl
private theorem receipt_0_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 0 512 = 658085581685731106683033719552 :=
  phaseBlock_append receipt_0_14_2360_1_join0 receipt_0_14_2360_1_join1 rfl rfl rfl
private theorem receipt_0_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 512 256 = 240150682490028187176763509120 :=
  phaseBlock_append receipt_0_14_2360_1_part4 receipt_0_14_2360_1_part5 rfl rfl rfl
private theorem receipt_0_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 768 256 = 185782785874984707510250359168 :=
  phaseBlock_append receipt_0_14_2360_1_part6 receipt_0_14_2360_1_part7 rfl rfl rfl
private theorem receipt_0_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 512 512 = 425933468365012894687013868288 :=
  phaseBlock_append receipt_0_14_2360_1_join3 receipt_0_14_2360_1_join4 rfl rfl rfl
private theorem receipt_0_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 0 1024 = 1084019050050744001370047587840 :=
  phaseBlock_append receipt_0_14_2360_1_join2 receipt_0_14_2360_1_join5 rfl rfl rfl
private theorem receipt_0_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1024 256 = 134937069575161135131492993408 :=
  phaseBlock_append receipt_0_14_2360_1_part8 receipt_0_14_2360_1_part9 rfl rfl rfl
private theorem receipt_0_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1280 256 = 87495675302703458370553395867 :=
  phaseBlock_append receipt_0_14_2360_1_part10 receipt_0_14_2360_1_part11 rfl rfl rfl
private theorem receipt_0_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1024 512 = 222432744877864593502046389275 :=
  phaseBlock_append receipt_0_14_2360_1_join7 receipt_0_14_2360_1_join8 rfl rfl rfl
private theorem receipt_0_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1536 256 = 43341104141498367019713414906 :=
  phaseBlock_append receipt_0_14_2360_1_part12 receipt_0_14_2360_1_part13 rfl rfl rfl
private theorem receipt_0_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1792 143 = 6170588767371310277907403866 :=
  phaseBlock_append receipt_0_14_2360_1_part14 receipt_0_14_2360_1_part15 rfl rfl rfl
private theorem receipt_0_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1536 399 = 49511692908869677297620818772 :=
  phaseBlock_append receipt_0_14_2360_1_join10 receipt_0_14_2360_1_join11 rfl rfl rfl
private theorem receipt_0_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 1024 911 = 271944437786734270799667208047 :=
  phaseBlock_append receipt_0_14_2360_1_join9 receipt_0_14_2360_1_join12 rfl rfl rfl
private theorem receipt_0_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179818 2360 73 1 0 1 1) 0 1935 = 1355963487837478272169714795887 :=
  phaseBlock_append receipt_0_14_2360_1_join6 receipt_0_14_2360_1_join13 rfl rfl rfl

private theorem receipt_0_14_2360_1 : fastPhase (bank 0 14).shape 179818 2360 73 1 0 1 1 = 1355963487837478272169714795887 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2360_1_join14

theorem receipt_0_14 : Checked (bank 0 14) 73 0 1 := by
  refine checked_from_values (bank 0 14) 73 0 1
    (P3_7_1.checked (bank 0 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_14_2359_0 receipt_0_14_2359_1 receipt_0_14_2360_0 receipt_0_14_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 0 128 = 169294150884966903086545787808 := by decide +kernel
private theorem receipt_1_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 128 128 = 154884136572719216629019454368 := by decide +kernel
private theorem receipt_1_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 256 128 = 140920421031555347891976010656 := by decide +kernel
private theorem receipt_1_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 384 128 = 127395702099403428870982060960 := by decide +kernel
private theorem receipt_1_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 512 128 = 114302700870274959082748746656 := by decide +kernel
private theorem receipt_1_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 640 128 = 101634161669131904894637271968 := by decide +kernel
private theorem receipt_1_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 768 128 = 89382852026753798854164429728 := by decide +kernel
private theorem receipt_1_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 896 128 = 77541562654604839018508127136 := by decide +kernel
private theorem receipt_1_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1024 128 = 66103107419700988284012911520 := by decide +kernel
private theorem receipt_1_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1152 128 = 55060323319477073715695496096 := by decide +kernel
private theorem receipt_1_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1280 128 = 44406077117369879387567188286 := by decide +kernel
private theorem receipt_1_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1408 128 = 34133265295131748426963223667 := by decide +kernel
private theorem receipt_1_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1536 128 = 24234777552661394681499941041 := by decide +kernel
private theorem receipt_1_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1664 128 = 14703521027108751562982757243 := by decide +kernel
private theorem receipt_1_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1792 128 = 5532425963980114495283847261 := by decide +kernel
private theorem receipt_1_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1920 15 = 64374009379587238275486708 := by decide +kernel
private theorem receipt_1_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 0 256 = 324178287457686119715565242176 :=
  phaseBlock_append receipt_1_14_2359_0_part0 receipt_1_14_2359_0_part1 rfl rfl rfl
private theorem receipt_1_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 256 256 = 268316123130958776762958071616 :=
  phaseBlock_append receipt_1_14_2359_0_part2 receipt_1_14_2359_0_part3 rfl rfl rfl
private theorem receipt_1_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 0 512 = 592494410588644896478523313792 :=
  phaseBlock_append receipt_1_14_2359_0_join0 receipt_1_14_2359_0_join1 rfl rfl rfl
private theorem receipt_1_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 512 256 = 215936862539406863977386018624 :=
  phaseBlock_append receipt_1_14_2359_0_part4 receipt_1_14_2359_0_part5 rfl rfl rfl
private theorem receipt_1_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 768 256 = 166924414681358637872672556864 :=
  phaseBlock_append receipt_1_14_2359_0_part6 receipt_1_14_2359_0_part7 rfl rfl rfl
private theorem receipt_1_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 512 512 = 382861277220765501850058575488 :=
  phaseBlock_append receipt_1_14_2359_0_join3 receipt_1_14_2359_0_join4 rfl rfl rfl
private theorem receipt_1_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 0 1024 = 975355687809410398328581889280 :=
  phaseBlock_append receipt_1_14_2359_0_join2 receipt_1_14_2359_0_join5 rfl rfl rfl
private theorem receipt_1_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1024 256 = 121163430739178061999708407616 :=
  phaseBlock_append receipt_1_14_2359_0_part8 receipt_1_14_2359_0_part9 rfl rfl rfl
private theorem receipt_1_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1280 256 = 78539342412501627814530411953 :=
  phaseBlock_append receipt_1_14_2359_0_part10 receipt_1_14_2359_0_part11 rfl rfl rfl
private theorem receipt_1_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1024 512 = 199702773151679689814238819569 :=
  phaseBlock_append receipt_1_14_2359_0_join7 receipt_1_14_2359_0_join8 rfl rfl rfl
private theorem receipt_1_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1536 256 = 38938298579770146244482698284 :=
  phaseBlock_append receipt_1_14_2359_0_part12 receipt_1_14_2359_0_part13 rfl rfl rfl
private theorem receipt_1_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1792 143 = 5596799973359701733559333969 :=
  phaseBlock_append receipt_1_14_2359_0_part14 receipt_1_14_2359_0_part15 rfl rfl rfl
private theorem receipt_1_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1536 399 = 44535098553129847978042032253 :=
  phaseBlock_append receipt_1_14_2359_0_join10 receipt_1_14_2359_0_join11 rfl rfl rfl
private theorem receipt_1_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 1024 911 = 244237871704809537792280851822 :=
  phaseBlock_append receipt_1_14_2359_0_join9 receipt_1_14_2359_0_join12 rfl rfl rfl
private theorem receipt_1_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 0) 0 1935 = 1219593559514219936120862741102 :=
  phaseBlock_append receipt_1_14_2359_0_join6 receipt_1_14_2359_0_join13 rfl rfl rfl

private theorem receipt_1_14_2359_0 : fastPhase (bank 1 14).shape 179818 2359 73 1 0 2 0 = 1219593559514219936120862741102 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2359_0_join14

private theorem receipt_1_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 0 128 = 169181313150702725633851918368 := by decide +kernel
private theorem receipt_1_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 128 128 = 154774699952099067057004689440 := by decide +kernel
private theorem receipt_1_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 256 128 = 140814330177067741566523959328 := by decide +kernel
private theorem receipt_1_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 384 128 = 127292901840881960872910755872 := by decide +kernel
private theorem receipt_1_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 512 128 = 114203136214705844043217291296 := by decide +kernel
private theorem receipt_1_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 640 128 = 101537777800461516830552487968 := by decide +kernel
private theorem receipt_1_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 768 128 = 89289594305696211003587504160 := by decide +kernel
private theorem receipt_1_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 896 128 = 77451376618449363676061259808 := by decide +kernel
private theorem receipt_1_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1024 128 = 66015938782119716636285962272 := by decide +kernel
private theorem receipt_1_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1152 128 = 54976117970332415676652632096 := by decide +kernel
private theorem receipt_1_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1280 128 = 44324781110598624307749753593 := by decide +kernel
private theorem receipt_1_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1408 128 = 34054824822083561000920760240 := by decide +kernel
private theorem receipt_1_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1536 128 = 24159138973073993939288289330 := by decide +kernel
private theorem receipt_1_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1664 128 = 14630630876489048948721329073 := by decide +kernel
private theorem receipt_1_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1792 128 = 5462230953356481353915175599 := by decide +kernel
private theorem receipt_1_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1920 15 = 56322000494077115279016829 := by decide +kernel
private theorem receipt_1_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 0 256 = 323956013102801792690856607808 :=
  phaseBlock_append receipt_1_14_2359_1_part0 receipt_1_14_2359_1_part1 rfl rfl rfl
private theorem receipt_1_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 256 256 = 268107232017949702439434715200 :=
  phaseBlock_append receipt_1_14_2359_1_part2 receipt_1_14_2359_1_part3 rfl rfl rfl
private theorem receipt_1_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 0 512 = 592063245120751495130291323008 :=
  phaseBlock_append receipt_1_14_2359_1_join0 receipt_1_14_2359_1_join1 rfl rfl rfl
private theorem receipt_1_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 512 256 = 215740914015167360873769779264 :=
  phaseBlock_append receipt_1_14_2359_1_part4 receipt_1_14_2359_1_part5 rfl rfl rfl
private theorem receipt_1_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 768 256 = 166740970924145574679648763968 :=
  phaseBlock_append receipt_1_14_2359_1_part6 receipt_1_14_2359_1_part7 rfl rfl rfl
private theorem receipt_1_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 512 512 = 382481884939312935553418543232 :=
  phaseBlock_append receipt_1_14_2359_1_join3 receipt_1_14_2359_1_join4 rfl rfl rfl
private theorem receipt_1_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 0 1024 = 974545130060064430683709866240 :=
  phaseBlock_append receipt_1_14_2359_1_join2 receipt_1_14_2359_1_join5 rfl rfl rfl
private theorem receipt_1_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1024 256 = 120992056752452132312938594368 :=
  phaseBlock_append receipt_1_14_2359_1_part8 receipt_1_14_2359_1_part9 rfl rfl rfl
private theorem receipt_1_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1280 256 = 78379605932682185308670513833 :=
  phaseBlock_append receipt_1_14_2359_1_part10 receipt_1_14_2359_1_part11 rfl rfl rfl
private theorem receipt_1_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1024 512 = 199371662685134317621609108201 :=
  phaseBlock_append receipt_1_14_2359_1_join7 receipt_1_14_2359_1_join8 rfl rfl rfl
private theorem receipt_1_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1536 256 = 38789769849563042888009618403 :=
  phaseBlock_append receipt_1_14_2359_1_part12 receipt_1_14_2359_1_part13 rfl rfl rfl
private theorem receipt_1_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1792 143 = 5518552953850558469194192428 :=
  phaseBlock_append receipt_1_14_2359_1_part14 receipt_1_14_2359_1_part15 rfl rfl rfl
private theorem receipt_1_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1536 399 = 44308322803413601357203810831 :=
  phaseBlock_append receipt_1_14_2359_1_join10 receipt_1_14_2359_1_join11 rfl rfl rfl
private theorem receipt_1_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 1024 911 = 243679985488547918978812919032 :=
  phaseBlock_append receipt_1_14_2359_1_join9 receipt_1_14_2359_1_join12 rfl rfl rfl
private theorem receipt_1_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2359 73 1 0 2 1) 0 1935 = 1218225115548612349662522785272 :=
  phaseBlock_append receipt_1_14_2359_1_join6 receipt_1_14_2359_1_join13 rfl rfl rfl

private theorem receipt_1_14_2359_1 : fastPhase (bank 1 14).shape 179818 2359 73 1 0 2 1 = 1218225115548612349662522785272 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2359_1_join14

private theorem receipt_1_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 0 128 = 169295670388438226098533696096 := by decide +kernel
private theorem receipt_1_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 128 128 = 154885475194737368354036126304 := by decide +kernel
private theorem receipt_1_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 256 128 = 140921591108255118180779303520 := by decide +kernel
private theorem receipt_1_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 384 128 = 127396715719080981534045909600 := by decide +kernel
private theorem receipt_1_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 512 128 = 114303569874195124388579787360 := by decide +kernel
private theorem receipt_1_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 640 128 = 101634897652334592458789245536 := by decide +kernel
private theorem receipt_1_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 768 128 = 89383466338859530918950363744 := by decide +kernel
private theorem receipt_1_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 896 128 = 77542066400619404123410297440 := by decide +kernel
private theorem receipt_1_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1024 128 = 66103511460819215326790582880 := by decide +kernel
private theorem receipt_1_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1152 128 = 55060638273885726404190442080 := by decide +kernel
private theorem receipt_1_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1280 128 = 44406313162287149301158490825 := by decide +kernel
private theorem receipt_1_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1408 128 = 34133432545082051069219404206 := by decide +kernel
private theorem receipt_1_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1536 128 = 24234886062502694360709662031 := by decide +kernel
private theorem receipt_1_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1664 128 = 14703580593958029923052356001 := by decide +kernel
private theorem receipt_1_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1792 128 = 5532446128214724389039381752 := by decide +kernel
private theorem receipt_1_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1920 15 = 64374224431682340750268908 := by decide +kernel
private theorem receipt_1_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 0 256 = 324181145583175594452569822400 :=
  phaseBlock_append receipt_1_14_2360_0_part0 receipt_1_14_2360_0_part1 rfl rfl rfl
private theorem receipt_1_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 256 256 = 268318306827336099714825213120 :=
  phaseBlock_append receipt_1_14_2360_0_part2 receipt_1_14_2360_0_part3 rfl rfl rfl
private theorem receipt_1_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 0 512 = 592499452410511694167395035520 :=
  phaseBlock_append receipt_1_14_2360_0_join0 receipt_1_14_2360_0_join1 rfl rfl rfl
private theorem receipt_1_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 512 256 = 215938467526529716847369032896 :=
  phaseBlock_append receipt_1_14_2360_0_part4 receipt_1_14_2360_0_part5 rfl rfl rfl
private theorem receipt_1_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 768 256 = 166925532739478935042360661184 :=
  phaseBlock_append receipt_1_14_2360_0_part6 receipt_1_14_2360_0_part7 rfl rfl rfl
private theorem receipt_1_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 512 512 = 382864000266008651889729694080 :=
  phaseBlock_append receipt_1_14_2360_0_join3 receipt_1_14_2360_0_join4 rfl rfl rfl
private theorem receipt_1_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 0 1024 = 975363452676520346057124729600 :=
  phaseBlock_append receipt_1_14_2360_0_join2 receipt_1_14_2360_0_join5 rfl rfl rfl
private theorem receipt_1_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1024 256 = 121164149734704941730981024960 :=
  phaseBlock_append receipt_1_14_2360_0_part8 receipt_1_14_2360_0_part9 rfl rfl rfl
private theorem receipt_1_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1280 256 = 78539745707369200370377895031 :=
  phaseBlock_append receipt_1_14_2360_0_part10 receipt_1_14_2360_0_part11 rfl rfl rfl
private theorem receipt_1_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1024 512 = 199703895442074142101358919991 :=
  phaseBlock_append receipt_1_14_2360_0_join7 receipt_1_14_2360_0_join8 rfl rfl rfl
private theorem receipt_1_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1536 256 = 38938466656460724283762018032 :=
  phaseBlock_append receipt_1_14_2360_0_part12 receipt_1_14_2360_0_part13 rfl rfl rfl
private theorem receipt_1_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1792 143 = 5596820352646406729789650660 :=
  phaseBlock_append receipt_1_14_2360_0_part14 receipt_1_14_2360_0_part15 rfl rfl rfl
private theorem receipt_1_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1536 399 = 44535287009107131013551668692 :=
  phaseBlock_append receipt_1_14_2360_0_join10 receipt_1_14_2360_0_join11 rfl rfl rfl
private theorem receipt_1_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 1024 911 = 244239182451181273114910588683 :=
  phaseBlock_append receipt_1_14_2360_0_join9 receipt_1_14_2360_0_join12 rfl rfl rfl
private theorem receipt_1_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 0) 0 1935 = 1219602635127701619172035318283 :=
  phaseBlock_append receipt_1_14_2360_0_join6 receipt_1_14_2360_0_join13 rfl rfl rfl

private theorem receipt_1_14_2360_0 : fastPhase (bank 1 14).shape 179818 2360 73 1 0 2 0 = 1219602635127701619172035318283 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2360_0_join14

private theorem receipt_1_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 0 128 = 169182831823818490728387286560 := by decide +kernel
private theorem receipt_1_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 128 128 = 154776037792793170838400951840 := by decide +kernel
private theorem receipt_1_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 256 128 = 140815499520294750917379962400 := by decide +kernel
private theorem receipt_1_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 384 128 = 127293914773762244660387382816 := by decide +kernel
private theorem receipt_1_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 512 128 = 114204004577332860394673853984 := by decide +kernel
private theorem receipt_1_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 640 128 = 101538513186708220799880898080 := by decide +kernel
private theorem receipt_1_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 768 128 = 89290208064020582628244223520 := by decide +kernel
private theorem receipt_1_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 896 128 = 77451879852699056424797029920 := by decide +kernel
private theorem receipt_1_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1024 128 = 66016342352335826247573313056 := by decide +kernel
private theorem receipt_1_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1152 128 = 54976432493552369387811169824 := by decide +kernel
private theorem receipt_1_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1280 128 = 44325016763244238242047295546 := by decide +kernel
private theorem receipt_1_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1408 128 = 34054991717758378631479759518 := by decide +kernel
private theorem receipt_1_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1536 128 = 24159247165450994870193943053 := by decide +kernel
private theorem receipt_1_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1664 128 = 14630690161505141577566057310 := by decide +kernel
private theorem receipt_1_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1792 128 = 5462250870205340698616345025 := by decide +kernel
private theorem receipt_1_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1920 15 = 56322188755690581306010638 := by decide +kernel
private theorem receipt_1_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 0 256 = 323958869616611661566788238400 :=
  phaseBlock_append receipt_1_14_2360_1_part0 receipt_1_14_2360_1_part1 rfl rfl rfl
private theorem receipt_1_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 256 256 = 268109414294056995577767345216 :=
  phaseBlock_append receipt_1_14_2360_1_part2 receipt_1_14_2360_1_part3 rfl rfl rfl
private theorem receipt_1_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 0 512 = 592068283910668657144555583616 :=
  phaseBlock_append receipt_1_14_2360_1_join0 receipt_1_14_2360_1_join1 rfl rfl rfl
private theorem receipt_1_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 512 256 = 215742517764041081194554752064 :=
  phaseBlock_append receipt_1_14_2360_1_part4 receipt_1_14_2360_1_part5 rfl rfl rfl
private theorem receipt_1_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 768 256 = 166742087916719639053041253440 :=
  phaseBlock_append receipt_1_14_2360_1_part6 receipt_1_14_2360_1_part7 rfl rfl rfl
private theorem receipt_1_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 512 512 = 382484605680760720247596005504 :=
  phaseBlock_append receipt_1_14_2360_1_join3 receipt_1_14_2360_1_join4 rfl rfl rfl
private theorem receipt_1_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 0 1024 = 974552889591429377392151589120 :=
  phaseBlock_append receipt_1_14_2360_1_join2 receipt_1_14_2360_1_join5 rfl rfl rfl
private theorem receipt_1_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1024 256 = 120992774845888195635384482880 :=
  phaseBlock_append receipt_1_14_2360_1_part8 receipt_1_14_2360_1_part9 rfl rfl rfl
private theorem receipt_1_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1280 256 = 78380008481002616873527055064 :=
  phaseBlock_append receipt_1_14_2360_1_part10 receipt_1_14_2360_1_part11 rfl rfl rfl
private theorem receipt_1_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1024 512 = 199372783326890812508911537944 :=
  phaseBlock_append receipt_1_14_2360_1_join7 receipt_1_14_2360_1_join8 rfl rfl rfl
private theorem receipt_1_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1536 256 = 38789937326956136447760000363 :=
  phaseBlock_append receipt_1_14_2360_1_part12 receipt_1_14_2360_1_part13 rfl rfl rfl
private theorem receipt_1_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1792 143 = 5518573058961031279922355663 :=
  phaseBlock_append receipt_1_14_2360_1_part14 receipt_1_14_2360_1_part15 rfl rfl rfl
private theorem receipt_1_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1536 399 = 44308510385917167727682356026 :=
  phaseBlock_append receipt_1_14_2360_1_join10 receipt_1_14_2360_1_join11 rfl rfl rfl
private theorem receipt_1_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 1024 911 = 243681293712807980236593893970 :=
  phaseBlock_append receipt_1_14_2360_1_join9 receipt_1_14_2360_1_join12 rfl rfl rfl
private theorem receipt_1_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179818 2360 73 1 0 2 1) 0 1935 = 1218234183304237357628745483090 :=
  phaseBlock_append receipt_1_14_2360_1_join6 receipt_1_14_2360_1_join13 rfl rfl rfl

private theorem receipt_1_14_2360_1 : fastPhase (bank 1 14).shape 179818 2360 73 1 0 2 1 = 1218234183304237357628745483090 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2360_1_join14

theorem receipt_1_14 : Checked (bank 1 14) 73 0 2 := by
  refine checked_from_values (bank 1 14) 73 0 2
    (P3_7_1.checked (bank 1 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_14_2359_0 receipt_1_14_2359_1 receipt_1_14_2360_0 receipt_1_14_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 0 128 = 90838519521199692625970569344 := by decide +kernel
private theorem receipt_2_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 128 128 = 82823142698133512213426282624 := by decide +kernel
private theorem receipt_2_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 256 128 = 75098556398278357419290828928 := by decide +kernel
private theorem receipt_2_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 384 128 = 67658372970121809845200756864 := by decide +kernel
private theorem receipt_2_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 512 128 = 60496274030400087813672902784 := by decide +kernel
private theorem receipt_2_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 640 128 = 53606010156220013154547081344 := by decide +kernel
private theorem receipt_2_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 768 128 = 46981400577180977991428776064 := by decide +kernel
private theorem receipt_2_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 896 128 = 40616332867496911528131829888 := by decide +kernel
private theorem receipt_2_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1024 128 = 34504762638118246835121135744 := by decide +kernel
private theorem receipt_2_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1152 128 = 28640713228853887635955327104 := by decide +kernel
private theorem receipt_2_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1280 128 = 23018278850185764549245576303 := by decide +kernel
private theorem receipt_2_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1408 128 = 17631624211943080357458485964 := by decide +kernel
private theorem receipt_2_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1536 128 = 12474965375482534042584229852 := by decide +kernel
private theorem receipt_2_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1664 128 = 7542582148368837665242626114 := by decide +kernel
private theorem receipt_2_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1792 128 = 2828820740897602517987250756 := by decide +kernel
private theorem receipt_2_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1920 15 = 32836769101845642198160464 := by decide +kernel
private theorem receipt_2_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 0 256 = 173661662219333204839396851968 :=
  phaseBlock_append receipt_2_14_2359_0_part0 receipt_2_14_2359_0_part1 rfl rfl rfl
private theorem receipt_2_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 256 256 = 142756929368400167264491585792 :=
  phaseBlock_append receipt_2_14_2359_0_part2 receipt_2_14_2359_0_part3 rfl rfl rfl
private theorem receipt_2_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 0 512 = 316418591587733372103888437760 :=
  phaseBlock_append receipt_2_14_2359_0_join0 receipt_2_14_2359_0_join1 rfl rfl rfl
private theorem receipt_2_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 512 256 = 114102284186620100968219984128 :=
  phaseBlock_append receipt_2_14_2359_0_part4 receipt_2_14_2359_0_part5 rfl rfl rfl
private theorem receipt_2_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 768 256 = 87597733444677889519560605952 :=
  phaseBlock_append receipt_2_14_2359_0_part6 receipt_2_14_2359_0_part7 rfl rfl rfl
private theorem receipt_2_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 512 512 = 201700017631297990487780590080 :=
  phaseBlock_append receipt_2_14_2359_0_join3 receipt_2_14_2359_0_join4 rfl rfl rfl
private theorem receipt_2_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 0 1024 = 518118609219031362591669027840 :=
  phaseBlock_append receipt_2_14_2359_0_join2 receipt_2_14_2359_0_join5 rfl rfl rfl
private theorem receipt_2_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1024 256 = 63145475866972134471076462848 :=
  phaseBlock_append receipt_2_14_2359_0_part8 receipt_2_14_2359_0_part9 rfl rfl rfl
private theorem receipt_2_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1280 256 = 40649903062128844906704062267 :=
  phaseBlock_append receipt_2_14_2359_0_part10 receipt_2_14_2359_0_part11 rfl rfl rfl
private theorem receipt_2_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1024 512 = 103795378929100979377780525115 :=
  phaseBlock_append receipt_2_14_2359_0_join7 receipt_2_14_2359_0_join8 rfl rfl rfl
private theorem receipt_2_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1536 256 = 20017547523851371707826855966 :=
  phaseBlock_append receipt_2_14_2359_0_part12 receipt_2_14_2359_0_part13 rfl rfl rfl
private theorem receipt_2_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1792 143 = 2861657509999448160185411220 :=
  phaseBlock_append receipt_2_14_2359_0_part14 receipt_2_14_2359_0_part15 rfl rfl rfl
private theorem receipt_2_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1536 399 = 22879205033850819868012267186 :=
  phaseBlock_append receipt_2_14_2359_0_join10 receipt_2_14_2359_0_join11 rfl rfl rfl
private theorem receipt_2_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 1024 911 = 126674583962951799245792792301 :=
  phaseBlock_append receipt_2_14_2359_0_join9 receipt_2_14_2359_0_join12 rfl rfl rfl
private theorem receipt_2_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 0) 0 1935 = 644793193181983161837461820141 :=
  phaseBlock_append receipt_2_14_2359_0_join6 receipt_2_14_2359_0_join13 rfl rfl rfl

private theorem receipt_2_14_2359_0 : fastPhase (bank 2 14).shape 179818 2359 73 1 0 7 0 = 644793193181983161837461820141 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2359_0_join14

private theorem receipt_2_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 0 128 = 90775554762699803654108443200 := by decide +kernel
private theorem receipt_2_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 128 128 = 82762411016321407776652907072 := by decide +kernel
private theorem receipt_2_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 256 128 = 75040008993686569461397860928 := by decide +kernel
private theorem receipt_2_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 384 128 = 67601961572961192351269032512 := by decide +kernel
private theorem receipt_2_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 512 128 = 60441950898202179793803866688 := by decide +kernel
private theorem receipt_2_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 640 128 = 53553728071479401627594216000 := by decide +kernel
private theorem receipt_2_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 768 128 = 46931112844997660968729031232 := by decide +kernel
private theorem receipt_2_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 896 128 = 40567993313218660997237051968 := by decide +kernel
private theorem receipt_2_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1024 128 = 34458325604982971743529497152 := by decide +kernel
private theorem receipt_2_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1152 128 = 28596133575631996874842755648 := by decide +kernel
private theorem receipt_2_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1280 128 = 22975511942553058925193898889 := by decide +kernel
private theorem receipt_2_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1408 128 = 17590625906438318559256723382 := by decide +kernel
private theorem receipt_2_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1536 128 = 12435692033890515552014086776 := by decide +kernel
private theorem receipt_2_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1664 128 = 7504990639380992618618881848 := by decide +kernel
private theorem receipt_2_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1792 128 = 2792868437720488506363725012 := by decide +kernel
private theorem receipt_2_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1920 15 = 28728960173327517431860840 := by decide +kernel
private theorem receipt_2_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 0 256 = 173537965779021211430761350272 :=
  phaseBlock_append receipt_2_14_2359_1_part0 receipt_2_14_2359_1_part1 rfl rfl rfl
private theorem receipt_2_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 256 256 = 142641970566647761812666893440 :=
  phaseBlock_append receipt_2_14_2359_1_part2 receipt_2_14_2359_1_part3 rfl rfl rfl
private theorem receipt_2_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 0 512 = 316179936345668973243428243712 :=
  phaseBlock_append receipt_2_14_2359_1_join0 receipt_2_14_2359_1_join1 rfl rfl rfl
private theorem receipt_2_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 512 256 = 113995678969681581421398082688 :=
  phaseBlock_append receipt_2_14_2359_1_part4 receipt_2_14_2359_1_part5 rfl rfl rfl
private theorem receipt_2_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 768 256 = 87499106158216321965966083200 :=
  phaseBlock_append receipt_2_14_2359_1_part6 receipt_2_14_2359_1_part7 rfl rfl rfl
private theorem receipt_2_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 512 512 = 201494785127897903387364165888 :=
  phaseBlock_append receipt_2_14_2359_1_join3 receipt_2_14_2359_1_join4 rfl rfl rfl
private theorem receipt_2_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 0 1024 = 517674721473566876630792409600 :=
  phaseBlock_append receipt_2_14_2359_1_join2 receipt_2_14_2359_1_join5 rfl rfl rfl
private theorem receipt_2_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1024 256 = 63054459180614968618372252800 :=
  phaseBlock_append receipt_2_14_2359_1_part8 receipt_2_14_2359_1_part9 rfl rfl rfl
private theorem receipt_2_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1280 256 = 40566137848991377484450622271 :=
  phaseBlock_append receipt_2_14_2359_1_part10 receipt_2_14_2359_1_part11 rfl rfl rfl
private theorem receipt_2_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1024 512 = 103620597029606346102822875071 :=
  phaseBlock_append receipt_2_14_2359_1_join7 receipt_2_14_2359_1_join8 rfl rfl rfl
private theorem receipt_2_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1536 256 = 19940682673271508170632968624 :=
  phaseBlock_append receipt_2_14_2359_1_part12 receipt_2_14_2359_1_part13 rfl rfl rfl
private theorem receipt_2_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1792 143 = 2821597397893816023795585852 :=
  phaseBlock_append receipt_2_14_2359_1_part14 receipt_2_14_2359_1_part15 rfl rfl rfl
private theorem receipt_2_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1536 399 = 22762280071165324194428554476 :=
  phaseBlock_append receipt_2_14_2359_1_join10 receipt_2_14_2359_1_join11 rfl rfl rfl
private theorem receipt_2_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 1024 911 = 126382877100771670297251429547 :=
  phaseBlock_append receipt_2_14_2359_1_join9 receipt_2_14_2359_1_join12 rfl rfl rfl
private theorem receipt_2_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2359 73 1 0 7 1) 0 1935 = 644057598574338546928043839147 :=
  phaseBlock_append receipt_2_14_2359_1_join6 receipt_2_14_2359_1_join13 rfl rfl rfl

private theorem receipt_2_14_2359_1 : fastPhase (bank 2 14).shape 179818 2359 73 1 0 7 1 = 644057598574338546928043839147 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2359_1_join14

private theorem receipt_2_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 0 128 = 90839334852890194806965714400 := by decide +kernel
private theorem receipt_2_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 128 128 = 82823858524262072081641516512 := by decide +kernel
private theorem receipt_2_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 256 128 = 75099179956654331985979088352 := by decide +kernel
private theorem receipt_2_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 384 128 = 67658911298511886323322260960 := by decide +kernel
private theorem receipt_2_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 512 128 = 60496733968871321902885666272 := by decide +kernel
private theorem receipt_2_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 640 128 = 53606398349472092112245222880 := by decide +kernel
private theorem receipt_2_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 768 128 = 46981723476867708489828621792 := by decide +kernel
private theorem receipt_2_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 896 128 = 40616596734536932297405812192 := by decide +kernel
private theorem receipt_2_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1024 128 = 34504973544994966092579487200 := by decide +kernel
private theorem receipt_2_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1152 128 = 28640877061904645301275569632 := by decide +kernel
private theorem receipt_2_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1280 128 = 23018401208903953393611025518 := by decide +kernel
private theorem receipt_2_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1408 128 = 17631710607490368776012614680 := by decide +kernel
private theorem receipt_2_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1536 128 = 12475021232988096299838561444 := by decide +kernel
private theorem receipt_2_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1664 128 = 7542612705792217181712655389 := by decide +kernel
private theorem receipt_2_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1792 128 = 2828831051495965609601884813 := by decide +kernel
private theorem receipt_2_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1920 15 = 32836878798581308330728684 := by decide +kernel
private theorem receipt_2_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 0 256 = 173663193377152266888607230912 :=
  phaseBlock_append receipt_2_14_2360_0_part0 receipt_2_14_2360_0_part1 rfl rfl rfl
private theorem receipt_2_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 256 256 = 142758091255166218309301349312 :=
  phaseBlock_append receipt_2_14_2360_0_part2 receipt_2_14_2360_0_part3 rfl rfl rfl
private theorem receipt_2_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 0 512 = 316421284632318485197908580224 :=
  phaseBlock_append receipt_2_14_2360_0_join0 receipt_2_14_2360_0_join1 rfl rfl rfl
private theorem receipt_2_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 512 256 = 114103132318343414015130889152 :=
  phaseBlock_append receipt_2_14_2360_0_part4 receipt_2_14_2360_0_part5 rfl rfl rfl
private theorem receipt_2_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 768 256 = 87598320211404640787234433984 :=
  phaseBlock_append receipt_2_14_2360_0_part6 receipt_2_14_2360_0_part7 rfl rfl rfl
private theorem receipt_2_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 512 512 = 201701452529748054802365323136 :=
  phaseBlock_append receipt_2_14_2360_0_join3 receipt_2_14_2360_0_join4 rfl rfl rfl
private theorem receipt_2_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 0 1024 = 518122737162066540000273903360 :=
  phaseBlock_append receipt_2_14_2360_0_join2 receipt_2_14_2360_0_join5 rfl rfl rfl
private theorem receipt_2_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1024 256 = 63145850606899611393855056832 :=
  phaseBlock_append receipt_2_14_2360_0_part8 receipt_2_14_2360_0_part9 rfl rfl rfl
private theorem receipt_2_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1280 256 = 40650111816394322169623640198 :=
  phaseBlock_append receipt_2_14_2360_0_part10 receipt_2_14_2360_0_part11 rfl rfl rfl
private theorem receipt_2_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1024 512 = 103795962423293933563478697030 :=
  phaseBlock_append receipt_2_14_2360_0_join7 receipt_2_14_2360_0_join8 rfl rfl rfl
private theorem receipt_2_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1536 256 = 20017633938780313481551216833 :=
  phaseBlock_append receipt_2_14_2360_0_part12 receipt_2_14_2360_0_part13 rfl rfl rfl
private theorem receipt_2_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1792 143 = 2861667930294546917932613497 :=
  phaseBlock_append receipt_2_14_2360_0_part14 receipt_2_14_2360_0_part15 rfl rfl rfl
private theorem receipt_2_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1536 399 = 22879301869074860399483830330 :=
  phaseBlock_append receipt_2_14_2360_0_join10 receipt_2_14_2360_0_join11 rfl rfl rfl
private theorem receipt_2_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 1024 911 = 126675264292368793962962527360 :=
  phaseBlock_append receipt_2_14_2360_0_join9 receipt_2_14_2360_0_join12 rfl rfl rfl
private theorem receipt_2_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 0) 0 1935 = 644798001454435333963236430720 :=
  phaseBlock_append receipt_2_14_2360_0_join6 receipt_2_14_2360_0_join13 rfl rfl rfl

private theorem receipt_2_14_2360_0 : fastPhase (bank 2 14).shape 179818 2360 73 1 0 7 0 = 644798001454435333963236430720 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2360_0_join14

private theorem receipt_2_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 0 128 = 90776369627123346255377446752 := by decide +kernel
private theorem receipt_2_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 128 128 = 82763126405523756920281384800 := by decide +kernel
private theorem receipt_2_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 256 128 = 75040632144487300979403446112 := by decide +kernel
private theorem receipt_2_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 384 128 = 67602499522150186781946111840 := by decide +kernel
private theorem receipt_2_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 512 128 = 60442410484882596688881252192 := by decide +kernel
private theorem receipt_2_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 640 128 = 53554115939399878645440612192 := by decide +kernel
private theorem receipt_2_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 768 128 = 46931435444873737753606297440 := by decide +kernel
private theorem receipt_2_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 896 128 = 40568256905043427844601259872 := by decide +kernel
private theorem receipt_2_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1024 128 = 34458536260326943051379783520 := by decide +kernel
private theorem receipt_2_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1152 128 = 28596297179932209381117970272 := by decide +kernel
private theorem receipt_2_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1280 128 = 22975634094598524213698635653 := by decide +kernel
private theorem receipt_2_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1408 128 = 17590712116627970953116201822 := by decide +kernel
private theorem receipt_2_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1536 128 = 12435747726461151987822724005 := by decide +kernel
private theorem receipt_2_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1664 128 = 7505021051412910525427613210 := by decide +kernel
private theorem receipt_2_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1792 128 = 2792878621600326335050380171 := by decide +kernel
private theorem receipt_2_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1920 15 = 28729056202626078791564604 := by decide +kernel
private theorem receipt_2_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 0 256 = 173539496032647103175658831552 :=
  phaseBlock_append receipt_2_14_2360_1_part0 receipt_2_14_2360_1_part1 rfl rfl rfl
private theorem receipt_2_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 256 256 = 142643131666637487761349557952 :=
  phaseBlock_append receipt_2_14_2360_1_part2 receipt_2_14_2360_1_part3 rfl rfl rfl
private theorem receipt_2_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 0 512 = 316182627699284590937008389504 :=
  phaseBlock_append receipt_2_14_2360_1_join0 receipt_2_14_2360_1_join1 rfl rfl rfl
private theorem receipt_2_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 512 256 = 113996526424282475334321864384 :=
  phaseBlock_append receipt_2_14_2360_1_part4 receipt_2_14_2360_1_part5 rfl rfl rfl
private theorem receipt_2_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 768 256 = 87499692349917165598207557312 :=
  phaseBlock_append receipt_2_14_2360_1_part6 receipt_2_14_2360_1_part7 rfl rfl rfl
private theorem receipt_2_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 512 512 = 201496218774199640932529421696 :=
  phaseBlock_append receipt_2_14_2360_1_join3 receipt_2_14_2360_1_join4 rfl rfl rfl
private theorem receipt_2_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 0 1024 = 517678846473484231869537811200 :=
  phaseBlock_append receipt_2_14_2360_1_join2 receipt_2_14_2360_1_join5 rfl rfl rfl
private theorem receipt_2_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1024 256 = 63054833440259152432497753792 :=
  phaseBlock_append receipt_2_14_2360_1_part8 receipt_2_14_2360_1_part9 rfl rfl rfl
private theorem receipt_2_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1280 256 = 40566346211226495166814837475 :=
  phaseBlock_append receipt_2_14_2360_1_part10 receipt_2_14_2360_1_part11 rfl rfl rfl
private theorem receipt_2_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1024 512 = 103621179651485647599312591267 :=
  phaseBlock_append receipt_2_14_2360_1_join7 receipt_2_14_2360_1_join8 rfl rfl rfl
private theorem receipt_2_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1536 256 = 19940768777874062513250337215 :=
  phaseBlock_append receipt_2_14_2360_1_part12 receipt_2_14_2360_1_part13 rfl rfl rfl
private theorem receipt_2_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1792 143 = 2821607677802952413841944775 :=
  phaseBlock_append receipt_2_14_2360_1_part14 receipt_2_14_2360_1_part15 rfl rfl rfl
private theorem receipt_2_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1536 399 = 22762376455677014927092281990 :=
  phaseBlock_append receipt_2_14_2360_1_join10 receipt_2_14_2360_1_join11 rfl rfl rfl
private theorem receipt_2_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 1024 911 = 126383556107162662526404873257 :=
  phaseBlock_append receipt_2_14_2360_1_join9 receipt_2_14_2360_1_join12 rfl rfl rfl
private theorem receipt_2_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179818 2360 73 1 0 7 1) 0 1935 = 644062402580646894395942684457 :=
  phaseBlock_append receipt_2_14_2360_1_join6 receipt_2_14_2360_1_join13 rfl rfl rfl

private theorem receipt_2_14_2360_1 : fastPhase (bank 2 14).shape 179818 2360 73 1 0 7 1 = 644062402580646894395942684457 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2360_1_join14

theorem receipt_2_14 : Checked (bank 2 14) 73 0 7 := by
  refine checked_from_values (bank 2 14) 73 0 7
    (P3_7_1.checked (bank 2 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_14_2359_0 receipt_2_14_2359_1 receipt_2_14_2360_0 receipt_2_14_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 0 128 = 21388498730998469787645260640 := by decide +kernel
private theorem receipt_3_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 128 128 = 19599990061056976437392204640 := by decide +kernel
private theorem receipt_3_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 256 128 = 17861019785256544191271572320 := by decide +kernel
private theorem receipt_3_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 384 128 = 16172542030950350003000099680 := by decide +kernel
private theorem receipt_3_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 512 128 = 14535505298417056752874746720 := by decide +kernel
private theorem receipt_3_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 640 128 = 12950852470315161891297633120 := by decide +kernel
private theorem receipt_3_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 768 128 = 11419520821137346082300973920 := by decide +kernel
private theorem receipt_3_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 896 128 = 9942442026664821847072015200 := by decide +kernel
private theorem receipt_3_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1024 128 = 8520542173421682207477969760 := by decide +kernel
private theorem receipt_3_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1152 128 = 7154741768129249329590952800 := by decide +kernel
private theorem receipt_3_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1280 128 = 5845955747160423167212917600 := by decide +kernel
private theorem receipt_3_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1408 128 = 4595093485994030105400591200 := by decide +kernel
private theorem receipt_3_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1536 128 = 3403058808669171603990410080 := by decide +kernel
private theorem receipt_3_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1664 128 = 2270749997239572841123455840 := by decide +kernel
private theorem receipt_3_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1792 128 = 1199059801227931356770390880 := by decide +kernel
private theorem receipt_3_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1920 88 = 234615434404783652826825450 := by decide +kernel
private theorem receipt_3_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 0 256 = 40988488792055446225037465280 :=
  phaseBlock_append receipt_3_14_2359_0_part0 receipt_3_14_2359_0_part1 rfl rfl rfl
private theorem receipt_3_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 256 256 = 34033561816206894194271672000 :=
  phaseBlock_append receipt_3_14_2359_0_part2 receipt_3_14_2359_0_part3 rfl rfl rfl
private theorem receipt_3_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 0 512 = 75022050608262340419309137280 :=
  phaseBlock_append receipt_3_14_2359_0_join0 receipt_3_14_2359_0_join1 rfl rfl rfl
private theorem receipt_3_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 512 256 = 27486357768732218644172379840 :=
  phaseBlock_append receipt_3_14_2359_0_part4 receipt_3_14_2359_0_part5 rfl rfl rfl
private theorem receipt_3_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 768 256 = 21361962847802167929372989120 :=
  phaseBlock_append receipt_3_14_2359_0_part6 receipt_3_14_2359_0_part7 rfl rfl rfl
private theorem receipt_3_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 512 512 = 48848320616534386573545368960 :=
  phaseBlock_append receipt_3_14_2359_0_join3 receipt_3_14_2359_0_join4 rfl rfl rfl
private theorem receipt_3_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 0 1024 = 123870371224796726992854506240 :=
  phaseBlock_append receipt_3_14_2359_0_join2 receipt_3_14_2359_0_join5 rfl rfl rfl
private theorem receipt_3_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1024 256 = 15675283941550931537068922560 :=
  phaseBlock_append receipt_3_14_2359_0_part8 receipt_3_14_2359_0_part9 rfl rfl rfl
private theorem receipt_3_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1280 256 = 10441049233154453272613508800 :=
  phaseBlock_append receipt_3_14_2359_0_part10 receipt_3_14_2359_0_part11 rfl rfl rfl
private theorem receipt_3_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1024 512 = 26116333174705384809682431360 :=
  phaseBlock_append receipt_3_14_2359_0_join7 receipt_3_14_2359_0_join8 rfl rfl rfl
private theorem receipt_3_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1536 256 = 5673808805908744445113865920 :=
  phaseBlock_append receipt_3_14_2359_0_part12 receipt_3_14_2359_0_part13 rfl rfl rfl
private theorem receipt_3_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1792 216 = 1433675235632715009597216330 :=
  phaseBlock_append receipt_3_14_2359_0_part14 receipt_3_14_2359_0_part15 rfl rfl rfl
private theorem receipt_3_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1536 472 = 7107484041541459454711082250 :=
  phaseBlock_append receipt_3_14_2359_0_join10 receipt_3_14_2359_0_join11 rfl rfl rfl
private theorem receipt_3_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 1024 984 = 33223817216246844264393513610 :=
  phaseBlock_append receipt_3_14_2359_0_join9 receipt_3_14_2359_0_join12 rfl rfl rfl
private theorem receipt_3_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 0) 0 2008 = 157094188441043571257248019850 :=
  phaseBlock_append receipt_3_14_2359_0_join6 receipt_3_14_2359_0_join13 rfl rfl rfl

private theorem receipt_3_14_2359_0 : fastPhase (bank 3 14).shape 179818 2359 73 1 1 1 0 = 157094188441043571257248019850 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2359_0_join14

private theorem receipt_3_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 0 128 = 21374523922617186521617708704 := by decide +kernel
private theorem receipt_3_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 128 128 = 19586381846825224630355797664 := by decide +kernel
private theorem receipt_3_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 256 128 = 17847786267176417854535145120 := by decide +kernel
private theorem receipt_3_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 384 128 = 16159691264725500178418271904 := by decide +kernel
private theorem receipt_3_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 512 128 = 14523045293529471578046625440 := by decide +kernel
private theorem receipt_3_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 640 128 = 12938791190101946664765515424 := by decide +kernel
private theorem receipt_3_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 768 128 = 11407866182867503328749049504 := by decide +kernel
private theorem receipt_3_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 896 128 = 9931201901616031382525068960 := by decide +kernel
private theorem receipt_3_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1024 128 = 8509724386957081204500084384 := by decide +kernel
private theorem receipt_3_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1152 128 = 7144354099774212382484211360 := by decide +kernel
private theorem receipt_3_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1280 128 = 5836005930679342357216106144 := by decide +kernel
private theorem receipt_3_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1408 128 = 4585589209467095065887901344 := by decide +kernel
private theorem receipt_3_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1536 128 = 3394007714569149585670141600 := by decide +kernel
private theorem receipt_3_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1664 128 = 2262159682508588777236719264 := by decide +kernel
private theorem receipt_3_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1792 128 = 1190937817354247928289810080 := by decide +kernel
private theorem receipt_3_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1920 88 = 229307141392722555301681542 := by decide +kernel
private theorem receipt_3_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 0 256 = 40960905769442411151973506368 :=
  phaseBlock_append receipt_3_14_2359_1_part0 receipt_3_14_2359_1_part1 rfl rfl rfl
private theorem receipt_3_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 256 256 = 34007477531901918032953417024 :=
  phaseBlock_append receipt_3_14_2359_1_part2 receipt_3_14_2359_1_part3 rfl rfl rfl
private theorem receipt_3_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 0 512 = 74968383301344329184926923392 :=
  phaseBlock_append receipt_3_14_2359_1_join0 receipt_3_14_2359_1_join1 rfl rfl rfl
private theorem receipt_3_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 512 256 = 27461836483631418242812140864 :=
  phaseBlock_append receipt_3_14_2359_1_part4 receipt_3_14_2359_1_part5 rfl rfl rfl
private theorem receipt_3_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 768 256 = 21339068084483534711274118464 :=
  phaseBlock_append receipt_3_14_2359_1_part6 receipt_3_14_2359_1_part7 rfl rfl rfl
private theorem receipt_3_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 512 512 = 48800904568114952954086259328 :=
  phaseBlock_append receipt_3_14_2359_1_join3 receipt_3_14_2359_1_join4 rfl rfl rfl
private theorem receipt_3_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 0 1024 = 123769287869459282139013182720 :=
  phaseBlock_append receipt_3_14_2359_1_join2 receipt_3_14_2359_1_join5 rfl rfl rfl
private theorem receipt_3_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1024 256 = 15654078486731293586984295744 :=
  phaseBlock_append receipt_3_14_2359_1_part8 receipt_3_14_2359_1_part9 rfl rfl rfl
private theorem receipt_3_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1280 256 = 10421595140146437423104007488 :=
  phaseBlock_append receipt_3_14_2359_1_part10 receipt_3_14_2359_1_part11 rfl rfl rfl
private theorem receipt_3_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1024 512 = 26075673626877731010088303232 :=
  phaseBlock_append receipt_3_14_2359_1_join7 receipt_3_14_2359_1_join8 rfl rfl rfl
private theorem receipt_3_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1536 256 = 5656167397077738362906860864 :=
  phaseBlock_append receipt_3_14_2359_1_part12 receipt_3_14_2359_1_part13 rfl rfl rfl
private theorem receipt_3_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1792 216 = 1420244958746970483591491622 :=
  phaseBlock_append receipt_3_14_2359_1_part14 receipt_3_14_2359_1_part15 rfl rfl rfl
private theorem receipt_3_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1536 472 = 7076412355824708846498352486 :=
  phaseBlock_append receipt_3_14_2359_1_join10 receipt_3_14_2359_1_join11 rfl rfl rfl
private theorem receipt_3_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 1024 984 = 33152085982702439856586655718 :=
  phaseBlock_append receipt_3_14_2359_1_join9 receipt_3_14_2359_1_join12 rfl rfl rfl
private theorem receipt_3_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2359 73 1 1 1 1) 0 2008 = 156921373852161721995599838438 :=
  phaseBlock_append receipt_3_14_2359_1_join6 receipt_3_14_2359_1_join13 rfl rfl rfl

private theorem receipt_3_14_2359_1 : fastPhase (bank 3 14).shape 179818 2359 73 1 1 1 1 = 156921373852161721995599838438 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2359_1_join14

private theorem receipt_3_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 0 128 = 21388689455474147333927291136 := by decide +kernel
private theorem receipt_3_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 128 128 = 19600153437549279151211915520 := by decide +kernel
private theorem receipt_3_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 256 128 = 17861158398018678166074951936 := by decide +kernel
private theorem receipt_3_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 384 128 = 16172658349048962923572521216 := by decide +kernel
private theorem receipt_3_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 512 128 = 14535601676289271651571124480 := by decide +kernel
private theorem receipt_3_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 640 128 = 12950931148324731294970358016 := by decide +kernel
private theorem receipt_3_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 768 128 = 11419583926129926549925628160 := by decide +kernel
private theorem receipt_3_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 896 128 = 9942491572522368898070866176 := by decide +kernel
private theorem receipt_3_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1024 128 = 8520580061615965640741243136 := by decide +kernel
private theorem receipt_3_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1152 128 = 7154769788274488933195884800 := by decide +kernel
private theorem receipt_3_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1280 128 = 5845975577565044818840586496 := by decide +kernel
private theorem receipt_3_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1408 128 = 4595106694211542263450528000 := by decide +kernel
private theorem receipt_3_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1536 128 = 3403066852048162189392988416 := by decide +kernel
private theorem receipt_3_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1664 128 = 2270754223472826509850061056 := by decide +kernel
private theorem receipt_3_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1792 128 = 1199061448900667163041368320 := by decide +kernel
private theorem receipt_3_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1920 88 = 234615663025438681472336928 := by decide +kernel
private theorem receipt_3_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 0 256 = 40988842893023426485139206656 :=
  phaseBlock_append receipt_3_14_2360_0_part0 receipt_3_14_2360_0_part1 rfl rfl rfl
private theorem receipt_3_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 256 256 = 34033816747067641089647473152 :=
  phaseBlock_append receipt_3_14_2360_0_part2 receipt_3_14_2360_0_part3 rfl rfl rfl
private theorem receipt_3_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 0 512 = 75022659640091067574786679808 :=
  phaseBlock_append receipt_3_14_2360_0_join0 receipt_3_14_2360_0_join1 rfl rfl rfl
private theorem receipt_3_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 512 256 = 27486532824614002946541482496 :=
  phaseBlock_append receipt_3_14_2360_0_part4 receipt_3_14_2360_0_part5 rfl rfl rfl
private theorem receipt_3_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 768 256 = 21362075498652295447996494336 :=
  phaseBlock_append receipt_3_14_2360_0_part6 receipt_3_14_2360_0_part7 rfl rfl rfl
private theorem receipt_3_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 512 512 = 48848608323266298394537976832 :=
  phaseBlock_append receipt_3_14_2360_0_join3 receipt_3_14_2360_0_join4 rfl rfl rfl
private theorem receipt_3_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 0 1024 = 123871267963357365969324656640 :=
  phaseBlock_append receipt_3_14_2360_0_join2 receipt_3_14_2360_0_join5 rfl rfl rfl
private theorem receipt_3_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1024 256 = 15675349849890454573937127936 :=
  phaseBlock_append receipt_3_14_2360_0_part8 receipt_3_14_2360_0_part9 rfl rfl rfl
private theorem receipt_3_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1280 256 = 10441082271776587082291114496 :=
  phaseBlock_append receipt_3_14_2360_0_part10 receipt_3_14_2360_0_part11 rfl rfl rfl
private theorem receipt_3_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1024 512 = 26116432121667041656228242432 :=
  phaseBlock_append receipt_3_14_2360_0_join7 receipt_3_14_2360_0_join8 rfl rfl rfl
private theorem receipt_3_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1536 256 = 5673821075520988699243049472 :=
  phaseBlock_append receipt_3_14_2360_0_part12 receipt_3_14_2360_0_part13 rfl rfl rfl
private theorem receipt_3_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1792 216 = 1433677111926105844513705248 :=
  phaseBlock_append receipt_3_14_2360_0_part14 receipt_3_14_2360_0_part15 rfl rfl rfl
private theorem receipt_3_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1536 472 = 7107498187447094543756754720 :=
  phaseBlock_append receipt_3_14_2360_0_join10 receipt_3_14_2360_0_join11 rfl rfl rfl
private theorem receipt_3_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 1024 984 = 33223930309114136199984997152 :=
  phaseBlock_append receipt_3_14_2360_0_join9 receipt_3_14_2360_0_join12 rfl rfl rfl
private theorem receipt_3_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 0) 0 2008 = 157095198272471502169309653792 :=
  phaseBlock_append receipt_3_14_2360_0_join6 receipt_3_14_2360_0_join13 rfl rfl rfl

private theorem receipt_3_14_2360_0 : fastPhase (bank 3 14).shape 179818 2360 73 1 1 1 0 = 157095198272471502169309653792 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2360_0_join14

private theorem receipt_3_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 0 128 = 21374714502583553457613967616 := by decide +kernel
private theorem receipt_3_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 128 128 = 19586545092361157439943086336 := by decide +kernel
private theorem receipt_3_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 256 128 = 17847924761898453824661623040 := by decide +kernel
private theorem receipt_3_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 384 128 = 16159807477066998314285404416 := by decide +kernel
private theorem receipt_3_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 512 128 = 14523141577297640724342247680 := by decide +kernel
private theorem receipt_3_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 640 128 = 12938869785033994017594675456 := by decide +kernel
private theorem receipt_3_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 768 128 = 11407929215185903338262630656 := by decide +kernel
private theorem receipt_3_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 896 128 = 9931251384582915046246191360 := by decide +kernel
private theorem receipt_3_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1024 128 = 8509762221427745751348285696 := by decide +kernel
private theorem receipt_3_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1152 128 = 7144382074749751347497406720 := by decide +kernel
private theorem receipt_3_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1280 128 = 5836025723858396046970327296 := by decide +kernel
private theorem receipt_3_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1408 128 = 4585602387796721414614814976 := by decide +kernel
private theorem receipt_3_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1536 128 = 3394015734794815402072346880 := by decide +kernel
private theorem receipt_3_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1664 128 = 2262163891723281382000824576 := by decide +kernel
private theorem receipt_3_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1792 128 = 1190939453546707182297288960 := by decide +kernel
private theorem receipt_3_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1920 88 = 229307365024949799287119728 := by decide +kernel
private theorem receipt_3_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 0 256 = 40961259594944710897557053952 :=
  phaseBlock_append receipt_3_14_2360_1_part0 receipt_3_14_2360_1_part1 rfl rfl rfl
private theorem receipt_3_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 256 256 = 34007732238965452138947027456 :=
  phaseBlock_append receipt_3_14_2360_1_part2 receipt_3_14_2360_1_part3 rfl rfl rfl
private theorem receipt_3_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 0 512 = 74968991833910163036504081408 :=
  phaseBlock_append receipt_3_14_2360_1_join0 receipt_3_14_2360_1_join1 rfl rfl rfl
private theorem receipt_3_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 512 256 = 27462011362331634741936923136 :=
  phaseBlock_append receipt_3_14_2360_1_part4 receipt_3_14_2360_1_part5 rfl rfl rfl
private theorem receipt_3_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 768 256 = 21339180599768818384508822016 :=
  phaseBlock_append receipt_3_14_2360_1_part6 receipt_3_14_2360_1_part7 rfl rfl rfl
private theorem receipt_3_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 512 512 = 48801191962100453126445745152 :=
  phaseBlock_append receipt_3_14_2360_1_join3 receipt_3_14_2360_1_join4 rfl rfl rfl
private theorem receipt_3_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 0 1024 = 123770183796010616162949826560 :=
  phaseBlock_append receipt_3_14_2360_1_join2 receipt_3_14_2360_1_join5 rfl rfl rfl
private theorem receipt_3_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1024 256 = 15654144296177497098845692416 :=
  phaseBlock_append receipt_3_14_2360_1_part8 receipt_3_14_2360_1_part9 rfl rfl rfl
private theorem receipt_3_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1280 256 = 10421628111655117461585142272 :=
  phaseBlock_append receipt_3_14_2360_1_part10 receipt_3_14_2360_1_part11 rfl rfl rfl
private theorem receipt_3_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1024 512 = 26075772407832614560430834688 :=
  phaseBlock_append receipt_3_14_2360_1_join7 receipt_3_14_2360_1_join8 rfl rfl rfl
private theorem receipt_3_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1536 256 = 5656179626518096784073171456 :=
  phaseBlock_append receipt_3_14_2360_1_part12 receipt_3_14_2360_1_part13 rfl rfl rfl
private theorem receipt_3_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1792 216 = 1420246818571656981584408688 :=
  phaseBlock_append receipt_3_14_2360_1_part14 receipt_3_14_2360_1_part15 rfl rfl rfl
private theorem receipt_3_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1536 472 = 7076426445089753765657580144 :=
  phaseBlock_append receipt_3_14_2360_1_join10 receipt_3_14_2360_1_join11 rfl rfl rfl
private theorem receipt_3_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 1024 984 = 33152198852922368326088414832 :=
  phaseBlock_append receipt_3_14_2360_1_join9 receipt_3_14_2360_1_join12 rfl rfl rfl
private theorem receipt_3_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179818 2360 73 1 1 1 1) 0 2008 = 156922382648932984489038241392 :=
  phaseBlock_append receipt_3_14_2360_1_join6 receipt_3_14_2360_1_join13 rfl rfl rfl

private theorem receipt_3_14_2360_1 : fastPhase (bank 3 14).shape 179818 2360 73 1 1 1 1 = 156922382648932984489038241392 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2360_1_join14

theorem receipt_3_14 : Checked (bank 3 14) 73 1 1 := by
  refine checked_from_values (bank 3 14) 73 1 1
    (P3_7_1.checked (bank 3 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_14_2359_0 receipt_3_14_2359_1 receipt_3_14_2360_0 receipt_3_14_2360_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group5_stage i)).shape
      (cutoff h rect (group5_stage i)), ¬ G∣Q :=
  (group5_checked rect i).avoids Crt word lo hi irr seeded slope hs hj


end Lower6960.RescueSource
