import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0

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
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 0 128 = 23092393695979417353261079776 := by decide +kernel
private theorem receipt_0_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 128 128 = 20047499846913272199944096992 := by decide +kernel
private theorem receipt_0_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 256 128 = 17145341796402117895522991328 := by decide +kernel
private theorem receipt_0_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 384 128 = 14382475737290581710963158240 := by decide +kernel
private theorem receipt_0_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 512 128 = 11755466024865969765248441568 := by decide +kernel
private theorem receipt_0_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 640 128 = 9260885170570643811246410976 := by decide +kernel
private theorem receipt_0_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 768 128 = 6895314228670485668933384824 := by decide +kernel
private theorem receipt_0_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 896 128 = 4655346177621931830626762162 := by decide +kernel
private theorem receipt_0_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 1024 128 = 2537573559839632500906961869 := by decide +kernel
private theorem receipt_0_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 1152 99 = 585678095638929946510028157 := by decide +kernel
private theorem receipt_0_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 0 256 = 43139893542892689553205176768 :=
  phaseBlock_append receipt_0_13_2359_0_part0 receipt_0_13_2359_0_part1 rfl rfl rfl
private theorem receipt_0_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 384 256 = 26137941762156551476211599808 :=
  phaseBlock_append receipt_0_13_2359_0_part3 receipt_0_13_2359_0_part4 rfl rfl rfl
private theorem receipt_0_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 256 384 = 43283283558558669371734591136 :=
  phaseBlock_append receipt_0_13_2359_0_part2 receipt_0_13_2359_0_join1 rfl rfl rfl
private theorem receipt_0_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 0 640 = 86423177101451358924939767904 :=
  phaseBlock_append receipt_0_13_2359_0_join0 receipt_0_13_2359_0_join2 rfl rfl rfl
private theorem receipt_0_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 640 256 = 16156199399241129480179795800 :=
  phaseBlock_append receipt_0_13_2359_0_part5 receipt_0_13_2359_0_part6 rfl rfl rfl
private theorem receipt_0_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 1024 227 = 3123251655478562447416990026 :=
  phaseBlock_append receipt_0_13_2359_0_part8 receipt_0_13_2359_0_part9 rfl rfl rfl
private theorem receipt_0_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 896 355 = 7778597833100494278043752188 :=
  phaseBlock_append receipt_0_13_2359_0_part7 receipt_0_13_2359_0_join5 rfl rfl rfl
private theorem receipt_0_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 640 611 = 23934797232341623758223547988 :=
  phaseBlock_append receipt_0_13_2359_0_join4 receipt_0_13_2359_0_join6 rfl rfl rfl
private theorem receipt_0_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 0) 0 1251 = 110357974333792982683163315892 :=
  phaseBlock_append receipt_0_13_2359_0_join3 receipt_0_13_2359_0_join7 rfl rfl rfl

private theorem receipt_0_13_2359_0 : fastPhase (bank 0 13).shape 179808 2379 44 1 0 1 0 = 110357974333792982683163315892 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2359_0_join8

private theorem receipt_0_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 0 128 = 23068360932318425354278967328 := by decide +kernel
private theorem receipt_0_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 128 128 = 20024557719958057960697317408 := by decide +kernel
private theorem receipt_0_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 256 128 = 17123464244499448041919739936 := by decide +kernel
private theorem receipt_0_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 384 128 = 14361636760998270080906340384 := by decide +kernel
private theorem receipt_0_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 512 128 = 11735639686904736254086174752 := by decide +kernel
private theorem receipt_0_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 640 128 = 9242045595775973217222527008 := by decide +kernel
private theorem receipt_0_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 768 128 = 6877435602890336111862687936 := by decide +kernel
private theorem receipt_0_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 896 128 = 4638402732266072358078256664 := by decide +kernel
private theorem receipt_0_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 1024 128 = 2521539575666592697438391166 := by decide +kernel
private theorem receipt_0_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 1152 99 = 573884269275423491986574883 := by decide +kernel
private theorem receipt_0_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 0 256 = 43092918652276483314976284736 :=
  phaseBlock_append receipt_0_13_2359_1_part0 receipt_0_13_2359_1_part1 rfl rfl rfl
private theorem receipt_0_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 384 256 = 26097276447903006334992515136 :=
  phaseBlock_append receipt_0_13_2359_1_part3 receipt_0_13_2359_1_part4 rfl rfl rfl
private theorem receipt_0_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 256 384 = 43220740692402454376912255072 :=
  phaseBlock_append receipt_0_13_2359_1_part2 receipt_0_13_2359_1_join1 rfl rfl rfl
private theorem receipt_0_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 0 640 = 86313659344678937691888539808 :=
  phaseBlock_append receipt_0_13_2359_1_join0 receipt_0_13_2359_1_join2 rfl rfl rfl
private theorem receipt_0_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 640 256 = 16119481198666309329085214944 :=
  phaseBlock_append receipt_0_13_2359_1_part5 receipt_0_13_2359_1_part6 rfl rfl rfl
private theorem receipt_0_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 1024 227 = 3095423844942016189424966049 :=
  phaseBlock_append receipt_0_13_2359_1_part8 receipt_0_13_2359_1_part9 rfl rfl rfl
private theorem receipt_0_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 896 355 = 7733826577208088547503222713 :=
  phaseBlock_append receipt_0_13_2359_1_part7 receipt_0_13_2359_1_join5 rfl rfl rfl
private theorem receipt_0_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 640 611 = 23853307775874397876588437657 :=
  phaseBlock_append receipt_0_13_2359_1_join4 receipt_0_13_2359_1_join6 rfl rfl rfl
private theorem receipt_0_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2379 44 1 0 1 1) 0 1251 = 110166967120553335568476977465 :=
  phaseBlock_append receipt_0_13_2359_1_join3 receipt_0_13_2359_1_join7 rfl rfl rfl

private theorem receipt_0_13_2359_1 : fastPhase (bank 0 13).shape 179808 2379 44 1 0 1 1 = 110166967120553335568476977465 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2359_1_join8

private theorem receipt_0_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 0 128 = 23092599385139306494776094944 := by decide +kernel
private theorem receipt_0_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 128 128 = 20047667994620153346801451232 := by decide +kernel
private theorem receipt_0_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 256 128 = 17145476406638292322865434848 := by decide +kernel
private theorem receipt_0_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 384 128 = 14382580695336173771621064928 := by decide +kernel
private theorem receipt_0_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 512 128 = 11755545097583329762836017376 := by decide +kernel
private theorem receipt_0_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 640 128 = 9260942006688530970932347104 := by decide +kernel
private theorem receipt_0_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 768 128 = 6895352345267365055737031894 := by decide +kernel
private theorem receipt_0_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 896 128 = 4655368955154551329231086856 := by decide +kernel
private theorem receipt_0_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 1024 128 = 2537584340111133406457081187 := by decide +kernel
private theorem receipt_0_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 1152 99 = 585680254147523756782737948 := by decide +kernel
private theorem receipt_0_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 0 256 = 43140267379759459841577546176 :=
  phaseBlock_append receipt_0_13_2360_0_part0 receipt_0_13_2360_0_part1 rfl rfl rfl
private theorem receipt_0_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 384 256 = 26138125792919503534457082304 :=
  phaseBlock_append receipt_0_13_2360_0_part3 receipt_0_13_2360_0_part4 rfl rfl rfl
private theorem receipt_0_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 256 384 = 43283602199557795857322517152 :=
  phaseBlock_append receipt_0_13_2360_0_part2 receipt_0_13_2360_0_join1 rfl rfl rfl
private theorem receipt_0_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 0 640 = 86423869579317255698900063328 :=
  phaseBlock_append receipt_0_13_2360_0_join0 receipt_0_13_2360_0_join2 rfl rfl rfl
private theorem receipt_0_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 640 256 = 16156294351955896026669378998 :=
  phaseBlock_append receipt_0_13_2360_0_part5 receipt_0_13_2360_0_part6 rfl rfl rfl
private theorem receipt_0_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 1024 227 = 3123264594258657163239819135 :=
  phaseBlock_append receipt_0_13_2360_0_part8 receipt_0_13_2360_0_part9 rfl rfl rfl
private theorem receipt_0_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 896 355 = 7778633549413208492470905991 :=
  phaseBlock_append receipt_0_13_2360_0_part7 receipt_0_13_2360_0_join5 rfl rfl rfl
private theorem receipt_0_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 640 611 = 23934927901369104519140284989 :=
  phaseBlock_append receipt_0_13_2360_0_join4 receipt_0_13_2360_0_join6 rfl rfl rfl
private theorem receipt_0_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 0) 0 1251 = 110358797480686360218040348317 :=
  phaseBlock_append receipt_0_13_2360_0_join3 receipt_0_13_2360_0_join7 rfl rfl rfl

private theorem receipt_0_13_2360_0 : fastPhase (bank 0 13).shape 179808 2380 44 1 0 1 0 = 110358797480686360218040348317 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2360_0_join8

private theorem receipt_0_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 0 128 = 23068566445843616795213429088 := by decide +kernel
private theorem receipt_0_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 128 128 = 20024725707859988935051012448 := by decide +kernel
private theorem receipt_0_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 256 128 = 17123598710199649294159632736 := by decide +kernel
private theorem receipt_0_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 384 128 = 14361741589217653027236104544 := by decide +kernel
private theorem receipt_0_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 512 128 = 11735718643947994549872343392 := by decide +kernel
private theorem receipt_0_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 640 128 = 9242102329815764422095087968 := by decide +kernel
private theorem receipt_0_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 768 128 = 6877473630486984244253658147 := by decide +kernel
private theorem receipt_0_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 896 128 = 4638425433464893813925288275 := by decide +kernel
private theorem receipt_0_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 1024 128 = 2521550291712464884122119979 := by decide +kernel
private theorem receipt_0_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 1152 99 = 573886386047329528496598051 := by decide +kernel
private theorem receipt_0_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 0 256 = 43093292153703605730264441536 :=
  phaseBlock_append receipt_0_13_2360_1_part0 receipt_0_13_2360_1_part1 rfl rfl rfl
private theorem receipt_0_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 384 256 = 26097460233165647577108447936 :=
  phaseBlock_append receipt_0_13_2360_1_part3 receipt_0_13_2360_1_part4 rfl rfl rfl
private theorem receipt_0_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 256 384 = 43221058943365296871268080672 :=
  phaseBlock_append receipt_0_13_2360_1_part2 receipt_0_13_2360_1_join1 rfl rfl rfl
private theorem receipt_0_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 0 640 = 86314351097068902601532522208 :=
  phaseBlock_append receipt_0_13_2360_1_join0 receipt_0_13_2360_1_join2 rfl rfl rfl
private theorem receipt_0_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 640 256 = 16119575960302748666348746115 :=
  phaseBlock_append receipt_0_13_2360_1_part5 receipt_0_13_2360_1_part6 rfl rfl rfl
private theorem receipt_0_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 1024 227 = 3095436677759794412618718030 :=
  phaseBlock_append receipt_0_13_2360_1_part8 receipt_0_13_2360_1_part9 rfl rfl rfl
private theorem receipt_0_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 896 355 = 7733862111224688226544006305 :=
  phaseBlock_append receipt_0_13_2360_1_part7 receipt_0_13_2360_1_join5 rfl rfl rfl
private theorem receipt_0_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 640 611 = 23853438071527436892892752420 :=
  phaseBlock_append receipt_0_13_2360_1_join4 receipt_0_13_2360_1_join6 rfl rfl rfl
private theorem receipt_0_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2380 44 1 0 1 1) 0 1251 = 110167789168596339494425274628 :=
  phaseBlock_append receipt_0_13_2360_1_join3 receipt_0_13_2360_1_join7 rfl rfl rfl

private theorem receipt_0_13_2360_1 : fastPhase (bank 0 13).shape 179808 2380 44 1 0 1 1 = 110167789168596339494425274628 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2360_1_join8

theorem receipt_0_13 : Checked (bank 0 13) 44 0 1 := by
  refine checked_from_values (bank 0 13) 44 0 1
    (P3_7_1.checked (bank 0 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_13_2359_0 receipt_0_13_2359_1 receipt_0_13_2360_0 receipt_0_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 0 128 = 20786772117475507131137847456 := by decide +kernel
private theorem receipt_1_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 128 128 = 18033341076766048856553390240 := by decide +kernel
private theorem receipt_1_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 256 128 = 15412028266525122765443567776 := by decide +kernel
private theorem receipt_1_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 384 128 = 12919473322812445114680647840 := by decide +kernel
private theorem receipt_1_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 512 128 = 10552331697899548688480546976 := by decide +kernel
private theorem receipt_1_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 640 128 = 8307274635119289941863940256 := by decide +kernel
private theorem receipt_1_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 768 128 = 6180989495869491974058061792 := by decide +kernel
private theorem receipt_1_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 896 128 = 4170182767812366732259107414 := by decide +kernel
private theorem receipt_1_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 1024 128 = 2271568970364317790398537363 := by decide +kernel
private theorem receipt_1_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 1152 99 = 523979874500089868195827485 := by decide +kernel
private theorem receipt_1_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 0 256 = 38820113194241555987691237696 :=
  phaseBlock_append receipt_1_13_2359_0_part0 receipt_1_13_2359_0_part1 rfl rfl rfl
private theorem receipt_1_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 384 256 = 23471805020711993803161194816 :=
  phaseBlock_append receipt_1_13_2359_0_part3 receipt_1_13_2359_0_part4 rfl rfl rfl
private theorem receipt_1_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 256 384 = 38883833287237116568604762592 :=
  phaseBlock_append receipt_1_13_2359_0_part2 receipt_1_13_2359_0_join1 rfl rfl rfl
private theorem receipt_1_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 0 640 = 77703946481478672556296000288 :=
  phaseBlock_append receipt_1_13_2359_0_join0 receipt_1_13_2359_0_join2 rfl rfl rfl
private theorem receipt_1_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 640 256 = 14488264130988781915922002048 :=
  phaseBlock_append receipt_1_13_2359_0_part5 receipt_1_13_2359_0_part6 rfl rfl rfl
private theorem receipt_1_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 1024 227 = 2795548844864407658594364848 :=
  phaseBlock_append receipt_1_13_2359_0_part8 receipt_1_13_2359_0_part9 rfl rfl rfl
private theorem receipt_1_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 896 355 = 6965731612676774390853472262 :=
  phaseBlock_append receipt_1_13_2359_0_part7 receipt_1_13_2359_0_join5 rfl rfl rfl
private theorem receipt_1_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 640 611 = 21453995743665556306775474310 :=
  phaseBlock_append receipt_1_13_2359_0_join4 receipt_1_13_2359_0_join6 rfl rfl rfl
private theorem receipt_1_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 0) 0 1251 = 99157942225144228863071474598 :=
  phaseBlock_append receipt_1_13_2359_0_join3 receipt_1_13_2359_0_join7 rfl rfl rfl

private theorem receipt_1_13_2359_0 : fastPhase (bank 1 13).shape 179808 2379 44 1 0 2 0 = 99157942225144228863071474598 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2359_0_join8

private theorem receipt_1_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 0 128 = 20765026050365192811926146464 := by decide +kernel
private theorem receipt_1_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 128 128 = 18012605997635838694828572064 := by decide +kernel
private theorem receipt_1_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 256 128 = 15392278694869477256152395168 := by decide +kernel
private theorem receipt_1_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 384 128 = 12900683898740487751655021984 := by decide +kernel
private theorem receipt_1_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 512 128 = 10534477181942501346239516064 := by decide +kernel
private theorem receipt_1_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 640 128 = 8290329908037908257415708064 := by decide +kernel
private theorem receipt_1_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 768 128 = 6164929557514887089307455338 := by decide +kernel
private theorem receipt_1_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 896 128 = 4154982723121480431529466682 := by decide +kernel
private theorem receipt_1_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 1024 128 = 2257204032681372325324697372 := by decide +kernel
private theorem receipt_1_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 1152 99 = 513426583370254738253487993 := by decide +kernel
private theorem receipt_1_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 0 256 = 38777632048001031506754718528 :=
  phaseBlock_append receipt_1_13_2359_1_part0 receipt_1_13_2359_1_part1 rfl rfl rfl
private theorem receipt_1_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 384 256 = 23435161080682989097894538048 :=
  phaseBlock_append receipt_1_13_2359_1_part3 receipt_1_13_2359_1_part4 rfl rfl rfl
private theorem receipt_1_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 256 384 = 38827439775552466354046933216 :=
  phaseBlock_append receipt_1_13_2359_1_part2 receipt_1_13_2359_1_join1 rfl rfl rfl
private theorem receipt_1_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 0 640 = 77605071823553497860801651744 :=
  phaseBlock_append receipt_1_13_2359_1_join0 receipt_1_13_2359_1_join2 rfl rfl rfl
private theorem receipt_1_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 640 256 = 14455259465552795346723163402 :=
  phaseBlock_append receipt_1_13_2359_1_part5 receipt_1_13_2359_1_part6 rfl rfl rfl
private theorem receipt_1_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 1024 227 = 2770630616051627063578185365 :=
  phaseBlock_append receipt_1_13_2359_1_part8 receipt_1_13_2359_1_part9 rfl rfl rfl
private theorem receipt_1_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 896 355 = 6925613339173107495107652047 :=
  phaseBlock_append receipt_1_13_2359_1_part7 receipt_1_13_2359_1_join5 rfl rfl rfl
private theorem receipt_1_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 640 611 = 21380872804725902841830815449 :=
  phaseBlock_append receipt_1_13_2359_1_join4 receipt_1_13_2359_1_join6 rfl rfl rfl
private theorem receipt_1_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2379 44 1 0 2 1) 0 1251 = 98985944628279400702632467193 :=
  phaseBlock_append receipt_1_13_2359_1_join3 receipt_1_13_2359_1_join7 rfl rfl rfl

private theorem receipt_1_13_2359_1 : fastPhase (bank 1 13).shape 179808 2379 44 1 0 2 1 = 98985944628279400702632467193 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2359_1_join8

private theorem receipt_1_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 0 128 = 20786957270560743675048144864 := by decide +kernel
private theorem receipt_1_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 128 128 = 18033492331339090912731078624 := by decide +kernel
private theorem receipt_1_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 256 128 = 15412149268786564573556740064 := by decide +kernel
private theorem receipt_1_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 384 128 = 12919567604824206937350537184 := by decide +kernel
private theorem receipt_1_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 512 128 = 10552402678133754115378933728 := by decide +kernel
private theorem receipt_1_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 640 128 = 8307325619006263584508338144 := by decide +kernel
private theorem receipt_1_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 768 128 = 6181023663976741957976226200 := by decide +kernel
private theorem receipt_1_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 896 128 = 4170203171709052572126327522 := by decide +kernel
private theorem receipt_1_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 1024 128 = 2271578620663981069467847219 := by decide +kernel
private theorem receipt_1_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 1152 99 = 523981805629257065830783260 := by decide +kernel
private theorem receipt_1_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 0 256 = 38820449601899834587779223488 :=
  phaseBlock_append receipt_1_13_2360_0_part0 receipt_1_13_2360_0_part1 rfl rfl rfl
private theorem receipt_1_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 384 256 = 23471970282957961052729470912 :=
  phaseBlock_append receipt_1_13_2360_0_part3 receipt_1_13_2360_0_part4 rfl rfl rfl
private theorem receipt_1_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 256 384 = 38884119551744525626286210976 :=
  phaseBlock_append receipt_1_13_2360_0_part2 receipt_1_13_2360_0_join1 rfl rfl rfl
private theorem receipt_1_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 0 640 = 77704569153644360214065434464 :=
  phaseBlock_append receipt_1_13_2360_0_join0 receipt_1_13_2360_0_join2 rfl rfl rfl
private theorem receipt_1_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 640 256 = 14488349282983005542484564344 :=
  phaseBlock_append receipt_1_13_2360_0_part5 receipt_1_13_2360_0_part6 rfl rfl rfl
private theorem receipt_1_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 1024 227 = 2795560426293238135298630479 :=
  phaseBlock_append receipt_1_13_2360_0_part8 receipt_1_13_2360_0_part9 rfl rfl rfl
private theorem receipt_1_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 896 355 = 6965763598002290707424958001 :=
  phaseBlock_append receipt_1_13_2360_0_part7 receipt_1_13_2360_0_join5 rfl rfl rfl
private theorem receipt_1_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 640 611 = 21454112880985296249909522345 :=
  phaseBlock_append receipt_1_13_2360_0_join4 receipt_1_13_2360_0_join6 rfl rfl rfl
private theorem receipt_1_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 0) 0 1251 = 99158682034629656463974956809 :=
  phaseBlock_append receipt_1_13_2360_0_join3 receipt_1_13_2360_0_join7 rfl rfl rfl

private theorem receipt_1_13_2360_0 : fastPhase (bank 1 13).shape 179808 2380 44 1 0 2 0 = 99158682034629656463974956809 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2360_0_join8

private theorem receipt_1_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 0 128 = 20765211044346033917585480224 := by decide +kernel
private theorem receipt_1_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 128 128 = 18012757107637272054049802784 := by decide +kernel
private theorem receipt_1_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 256 128 = 15392399566548701304645270048 := by decide +kernel
private theorem receipt_1_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 384 128 = 12900778063619037684186573344 := by decide +kernel
private theorem receipt_1_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 512 128 = 10534548057955121198051236384 := by decide +kernel
private theorem receipt_1_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 640 128 = 8290380800080543376338504224 := by decide +kernel
private theorem receipt_1_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 768 128 = 6164963645656356610126800696 := by decide +kernel
private theorem receipt_1_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 896 128 = 4155003058529476186685895672 := by decide +kernel
private theorem receipt_1_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 1024 128 = 2257213625437477963449811268 := by decide +kernel
private theorem receipt_1_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 1152 99 = 513428477152192894162207502 := by decide +kernel
private theorem receipt_1_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 0 256 = 38777968151983305971635283008 :=
  phaseBlock_append receipt_1_13_2360_1_part0 receipt_1_13_2360_1_part1 rfl rfl rfl
private theorem receipt_1_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 384 256 = 23435326121574158882237809728 :=
  phaseBlock_append receipt_1_13_2360_1_part3 receipt_1_13_2360_1_part4 rfl rfl rfl
private theorem receipt_1_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 256 384 = 38827725688122860186883079776 :=
  phaseBlock_append receipt_1_13_2360_1_part2 receipt_1_13_2360_1_join1 rfl rfl rfl
private theorem receipt_1_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 0 640 = 77605693840106166158518362784 :=
  phaseBlock_append receipt_1_13_2360_1_join0 receipt_1_13_2360_1_join2 rfl rfl rfl
private theorem receipt_1_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 640 256 = 14455344445736899986465304920 :=
  phaseBlock_append receipt_1_13_2360_1_part5 receipt_1_13_2360_1_part6 rfl rfl rfl
private theorem receipt_1_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 1024 227 = 2770642102589670857612018770 :=
  phaseBlock_append receipt_1_13_2360_1_part8 receipt_1_13_2360_1_part9 rfl rfl rfl
private theorem receipt_1_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 896 355 = 6925645161119147044297914442 :=
  phaseBlock_append receipt_1_13_2360_1_part7 receipt_1_13_2360_1_join5 rfl rfl rfl
private theorem receipt_1_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 640 611 = 21380989606856047030763219362 :=
  phaseBlock_append receipt_1_13_2360_1_join4 receipt_1_13_2360_1_join6 rfl rfl rfl
private theorem receipt_1_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2380 44 1 0 2 1) 0 1251 = 98986683446962213189281582146 :=
  phaseBlock_append receipt_1_13_2360_1_join3 receipt_1_13_2360_1_join7 rfl rfl rfl

private theorem receipt_1_13_2360_1 : fastPhase (bank 1 13).shape 179808 2380 44 1 0 2 1 = 98986683446962213189281582146 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2360_1_join8

theorem receipt_1_13 : Checked (bank 1 13) 44 0 2 := by
  refine checked_from_values (bank 1 13) 44 0 2
    (P3_7_1.checked (bank 1 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_13_2359_0 receipt_1_13_2359_1 receipt_1_13_2360_0 receipt_1_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 0 128 = 11139648169855190637576316896 := by decide +kernel
private theorem receipt_2_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 128 128 = 9615771996123003961310042080 := by decide +kernel
private theorem receipt_2_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 256 128 = 8176804042382209305892210656 := by decide +kernel
private theorem receipt_2_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 384 128 = 6819884086950092479693699040 := by decide +kernel
private theorem receipt_2_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 512 128 = 5542198472444024142967973856 := by decide +kernel
private theorem receipt_2_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 640 128 = 4340979797687922315249686496 := by decide +kernel
private theorem receipt_2_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 768 128 = 3213506792348949829429285162 := by decide +kernel
private theorem receipt_2_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 896 128 = 2157105573132471980147519684 := by decide +kernel
private theorem receipt_2_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 1024 128 = 1169143598892040863845702403 := by decide +kernel
private theorem receipt_2_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 1152 99 = 268535503465129689715641435 := by decide +kernel
private theorem receipt_2_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 0 256 = 20755420165978194598886358976 :=
  phaseBlock_append receipt_2_13_2359_0_part0 receipt_2_13_2359_0_part1 rfl rfl rfl
private theorem receipt_2_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 384 256 = 12362082559394116622661672896 :=
  phaseBlock_append receipt_2_13_2359_0_part3 receipt_2_13_2359_0_part4 rfl rfl rfl
private theorem receipt_2_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 256 384 = 20538886601776325928553883552 :=
  phaseBlock_append receipt_2_13_2359_0_part2 receipt_2_13_2359_0_join1 rfl rfl rfl
private theorem receipt_2_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 0 640 = 41294306767754520527440242528 :=
  phaseBlock_append receipt_2_13_2359_0_join0 receipt_2_13_2359_0_join2 rfl rfl rfl
private theorem receipt_2_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 640 256 = 7554486590036872144678971658 :=
  phaseBlock_append receipt_2_13_2359_0_part5 receipt_2_13_2359_0_part6 rfl rfl rfl
private theorem receipt_2_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 1024 227 = 1437679102357170553561343838 :=
  phaseBlock_append receipt_2_13_2359_0_part8 receipt_2_13_2359_0_part9 rfl rfl rfl
private theorem receipt_2_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 896 355 = 3594784675489642533708863522 :=
  phaseBlock_append receipt_2_13_2359_0_part7 receipt_2_13_2359_0_join5 rfl rfl rfl
private theorem receipt_2_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 640 611 = 11149271265526514678387835180 :=
  phaseBlock_append receipt_2_13_2359_0_join4 receipt_2_13_2359_0_join6 rfl rfl rfl
private theorem receipt_2_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 0) 0 1251 = 52443578033281035205828077708 :=
  phaseBlock_append receipt_2_13_2359_0_join3 receipt_2_13_2359_0_join7 rfl rfl rfl

private theorem receipt_2_13_2359_0 : fastPhase (bank 2 13).shape 179808 2379 44 1 0 7 0 = 52443578033281035205828077708 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2359_0_join8

private theorem receipt_2_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 0 128 = 11127559532855169374683142304 := by decide +kernel
private theorem receipt_2_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 128 128 = 9604338882524469200800303264 := by decide +kernel
private theorem receipt_2_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 256 128 = 8166004552110891658715035808 := by decide +kernel
private theorem receipt_2_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 384 128 = 6809696676285933255519709344 := by decide +kernel
private theorem receipt_2_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 512 128 = 5532601951662258777263888544 := by decide +kernel
private theorem receipt_2_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 640 128 = 4331953328700163796352927904 := by decide +kernel
private theorem receipt_2_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 768 128 = 3205029885845784794204739528 := by decide +kernel
private theorem receipt_2_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 896 128 = 2149158079024585261009056932 := by decide +kernel
private theorem receipt_2_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 1024 128 = 1161705706067464295069371872 := by decide +kernel
private theorem receipt_2_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 1152 99 = 263119897949264008947173103 := by decide +kernel
private theorem receipt_2_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 0 256 = 20731898415379638575483445568 :=
  phaseBlock_append receipt_2_13_2359_1_part0 receipt_2_13_2359_1_part1 rfl rfl rfl
private theorem receipt_2_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 384 256 = 12342298627948192032783597888 :=
  phaseBlock_append receipt_2_13_2359_1_part3 receipt_2_13_2359_1_part4 rfl rfl rfl
private theorem receipt_2_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 256 384 = 20508303180059083691498633696 :=
  phaseBlock_append receipt_2_13_2359_1_part2 receipt_2_13_2359_1_join1 rfl rfl rfl
private theorem receipt_2_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 0 640 = 41240201595438722266982079264 :=
  phaseBlock_append receipt_2_13_2359_1_join0 receipt_2_13_2359_1_join2 rfl rfl rfl
private theorem receipt_2_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 640 256 = 7536983214545948590557667432 :=
  phaseBlock_append receipt_2_13_2359_1_part5 receipt_2_13_2359_1_part6 rfl rfl rfl
private theorem receipt_2_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 1024 227 = 1424825604016728304016544975 :=
  phaseBlock_append receipt_2_13_2359_1_part8 receipt_2_13_2359_1_part9 rfl rfl rfl
private theorem receipt_2_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 896 355 = 3573983683041313565025601907 :=
  phaseBlock_append receipt_2_13_2359_1_part7 receipt_2_13_2359_1_join5 rfl rfl rfl
private theorem receipt_2_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 640 611 = 11110966897587262155583269339 :=
  phaseBlock_append receipt_2_13_2359_1_join4 receipt_2_13_2359_1_join6 rfl rfl rfl
private theorem receipt_2_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2379 44 1 0 7 1) 0 1251 = 52351168493025984422565348603 :=
  phaseBlock_append receipt_2_13_2359_1_join3 receipt_2_13_2359_1_join7 rfl rfl rfl

private theorem receipt_2_13_2359_1 : fastPhase (bank 2 13).shape 179808 2379 44 1 0 7 1 = 52351168493025984422565348603 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2359_1_join8

private theorem receipt_2_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 0 128 = 11139747395922881442014392224 := by decide +kernel
private theorem receipt_2_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 128 128 = 9615852650496585370407526304 := by decide +kernel
private theorem receipt_2_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 256 128 = 8176868241631480475600179104 := by decide +kernel
private theorem receipt_2_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 384 128 = 6819933857810049855641927584 := by decide +kernel
private theorem receipt_2_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 512 128 = 5542235753391008527023550368 := by decide +kernel
private theorem receipt_2_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 640 128 = 4341006440504990718123417504 := by decide +kernel
private theorem receipt_2_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 768 128 = 3213524557261066503148749230 := by decide +kernel
private theorem receipt_2_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 896 128 = 2157116128026321798594547072 := by decide +kernel
private theorem receipt_2_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 1024 128 = 1169148566082297416545260219 := by decide +kernel
private theorem receipt_2_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 1152 99 = 268536493185634144793164710 := by decide +kernel
private theorem receipt_2_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 0 256 = 20755600046419466812421918528 :=
  phaseBlock_append receipt_2_13_2360_0_part0 receipt_2_13_2360_0_part1 rfl rfl rfl
private theorem receipt_2_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 384 256 = 12362169611201058382665477952 :=
  phaseBlock_append receipt_2_13_2360_0_part3 receipt_2_13_2360_0_part4 rfl rfl rfl
private theorem receipt_2_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 256 384 = 20539037852832538858265657056 :=
  phaseBlock_append receipt_2_13_2360_0_part2 receipt_2_13_2360_0_join1 rfl rfl rfl
private theorem receipt_2_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 0 640 = 41294637899252005670687575584 :=
  phaseBlock_append receipt_2_13_2360_0_join0 receipt_2_13_2360_0_join2 rfl rfl rfl
private theorem receipt_2_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 640 256 = 7554530997766057221272166734 :=
  phaseBlock_append receipt_2_13_2360_0_part5 receipt_2_13_2360_0_part6 rfl rfl rfl
private theorem receipt_2_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 1024 227 = 1437685059267931561338424929 :=
  phaseBlock_append receipt_2_13_2360_0_part8 receipt_2_13_2360_0_part9 rfl rfl rfl
private theorem receipt_2_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 896 355 = 3594801187294253359932972001 :=
  phaseBlock_append receipt_2_13_2360_0_part7 receipt_2_13_2360_0_join5 rfl rfl rfl
private theorem receipt_2_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 640 611 = 11149332185060310581205138735 :=
  phaseBlock_append receipt_2_13_2360_0_join4 receipt_2_13_2360_0_join6 rfl rfl rfl
private theorem receipt_2_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 0) 0 1251 = 52443970084312316251892714319 :=
  phaseBlock_append receipt_2_13_2360_0_join3 receipt_2_13_2360_0_join7 rfl rfl rfl

private theorem receipt_2_13_2360_0 : fastPhase (bank 2 13).shape 179808 2380 44 1 0 7 0 = 52443970084312316251892714319 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2360_0_join8

private theorem receipt_2_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 0 128 = 11127658669781834442739234464 := by decide +kernel
private theorem receipt_2_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 128 128 = 9604419456646678382060045984 := by decide +kernel
private theorem receipt_2_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 256 128 = 8166068679553891223191869088 := by decide +kernel
private theorem receipt_2_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 384 128 = 6809746383348897343181203104 := by decide +kernel
private theorem receipt_2_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 512 128 = 5532639176394372486757512864 := by decide +kernel
private theorem receipt_2_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 640 128 = 4331979922465931059779618464 := by decide +kernel
private theorem receipt_2_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 768 128 = 3205047608477381267091962121 := by decide +kernel
private theorem receipt_2_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 896 128 = 2149168598073249756315693157 := by decide +kernel
private theorem receipt_2_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 1024 128 = 1161710643449684520391853703 := by decide +kernel
private theorem receipt_2_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 1152 99 = 263120868502039840815359487 := by decide +kernel
private theorem receipt_2_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 0 256 = 20732078126428512824799280448 :=
  phaseBlock_append receipt_2_13_2360_1_part0 receipt_2_13_2360_1_part1 rfl rfl rfl
private theorem receipt_2_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 384 256 = 12342385559743269829938715968 :=
  phaseBlock_append receipt_2_13_2360_1_part3 receipt_2_13_2360_1_part4 rfl rfl rfl
private theorem receipt_2_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 256 384 = 20508454239297161053130585056 :=
  phaseBlock_append receipt_2_13_2360_1_part2 receipt_2_13_2360_1_join1 rfl rfl rfl
private theorem receipt_2_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 0 640 = 41240532365725673877929865504 :=
  phaseBlock_append receipt_2_13_2360_1_join0 receipt_2_13_2360_1_join2 rfl rfl rfl
private theorem receipt_2_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 640 256 = 7537027530943312326871580585 :=
  phaseBlock_append receipt_2_13_2360_1_part5 receipt_2_13_2360_1_part6 rfl rfl rfl
private theorem receipt_2_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 1024 227 = 1424831511951724361207213190 :=
  phaseBlock_append receipt_2_13_2360_1_part8 receipt_2_13_2360_1_part9 rfl rfl rfl
private theorem receipt_2_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 896 355 = 3574000110024974117522906347 :=
  phaseBlock_append receipt_2_13_2360_1_part7 receipt_2_13_2360_1_join5 rfl rfl rfl
private theorem receipt_2_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 640 611 = 11111027640968286444394486932 :=
  phaseBlock_append receipt_2_13_2360_1_join4 receipt_2_13_2360_1_join6 rfl rfl rfl
private theorem receipt_2_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2380 44 1 0 7 1) 0 1251 = 52351560006693960322324352436 :=
  phaseBlock_append receipt_2_13_2360_1_join3 receipt_2_13_2360_1_join7 rfl rfl rfl

private theorem receipt_2_13_2360_1 : fastPhase (bank 2 13).shape 179808 2380 44 1 0 7 1 = 52351560006693960322324352436 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2360_1_join8

theorem receipt_2_13 : Checked (bank 2 13) 44 0 7 := by
  refine checked_from_values (bank 2 13) 44 0 7
    (P3_7_1.checked (bank 2 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_13_2359_0 receipt_2_13_2359_1 receipt_2_13_2360_0 receipt_2_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_13_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 0 128 = 2452216875506718957286966368 := by decide +kernel
private theorem receipt_3_13_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 128 128 = 2132555126157918673705342048 := by decide +kernel
private theorem receipt_3_13_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 256 128 = 1827007185239102772132406368 := by decide +kernel
private theorem receipt_3_13_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 384 128 = 1535985400692238542089434208 := by decide +kernel
private theorem receipt_3_13_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 512 128 = 1259898424724551109149394016 := by decide +kernel
private theorem receipt_3_13_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 640 128 = 999151223245279892417467488 := by decide +kernel
private theorem receipt_3_13_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 768 128 = 754145085302435062011569248 := by decide +kernel
private theorem receipt_3_13_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 896 128 = 525277632519553996542866528 := by decide +kernel
private theorem receipt_3_13_2359_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 1024 128 = 312942828532457740596298848 := by decide +kernel
private theorem receipt_3_13_2359_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 1152 128 = 117530988426007462211097696 := by decide +kernel
private theorem receipt_3_13_2359_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 1280 18 = 1841566081169822363507361 := by decide +kernel
private theorem receipt_3_13_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 0 256 = 4584772001664637630992308416 :=
  phaseBlock_append receipt_3_13_2359_0_part0 receipt_3_13_2359_0_part1 rfl rfl rfl
private theorem receipt_3_13_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 384 256 = 2795883825416789651238828224 :=
  phaseBlock_append receipt_3_13_2359_0_part3 receipt_3_13_2359_0_part4 rfl rfl rfl
private theorem receipt_3_13_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 256 384 = 4622891010655892423371234592 :=
  phaseBlock_append receipt_3_13_2359_0_part2 receipt_3_13_2359_0_join1 rfl rfl rfl
private theorem receipt_3_13_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 0 640 = 9207663012320530054363543008 :=
  phaseBlock_append receipt_3_13_2359_0_join0 receipt_3_13_2359_0_join2 rfl rfl rfl
private theorem receipt_3_13_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 768 256 = 1279422717821989058554435776 :=
  phaseBlock_append receipt_3_13_2359_0_part6 receipt_3_13_2359_0_part7 rfl rfl rfl
private theorem receipt_3_13_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 640 384 = 2278573941067268950971903264 :=
  phaseBlock_append receipt_3_13_2359_0_part5 receipt_3_13_2359_0_join4 rfl rfl rfl
private theorem receipt_3_13_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 1152 146 = 119372554507177284574605057 :=
  phaseBlock_append receipt_3_13_2359_0_part9 receipt_3_13_2359_0_part10 rfl rfl rfl
private theorem receipt_3_13_2359_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 1024 274 = 432315383039635025170903905 :=
  phaseBlock_append receipt_3_13_2359_0_part8 receipt_3_13_2359_0_join6 rfl rfl rfl
private theorem receipt_3_13_2359_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 640 658 = 2710889324106903976142807169 :=
  phaseBlock_append receipt_3_13_2359_0_join5 receipt_3_13_2359_0_join7 rfl rfl rfl
private theorem receipt_3_13_2359_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 0) 0 1298 = 11918552336427434030506350177 :=
  phaseBlock_append receipt_3_13_2359_0_join3 receipt_3_13_2359_0_join8 rfl rfl rfl

private theorem receipt_3_13_2359_0 : fastPhase (bank 3 13).shape 179808 2379 44 1 1 1 0 = 11918552336427434030506350177 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2359_0_join9

private theorem receipt_3_13_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 0 128 = 2449699346790364010215370016 := by decide +kernel
private theorem receipt_3_13_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 128 128 = 2130141620316496586966465824 := by decide +kernel
private theorem receipt_3_13_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 256 128 = 1824701211135622707668913440 := by decide +kernel
private theorem receipt_3_13_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 384 128 = 1533790436753981902637473056 := by decide +kernel
private theorem receipt_3_13_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 512 128 = 1257817919019738903495453984 := by decide +kernel
private theorem receipt_3_13_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 640 128 = 997188593559740100655234336 := by decide +kernel
private theorem receipt_3_13_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 768 128 = 752303719216270000798780704 := by decide +kernel
private theorem receipt_3_13_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 896 128 = 523560887483807684358167840 := by decide +kernel
private theorem receipt_3_13_2359_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 1024 128 = 311354031945783262996098336 := by decide +kernel
private theorem receipt_3_13_2359_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 1152 128 = 116073437711334337086422304 := by decide +kernel
private theorem receipt_3_13_2359_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 1280 18 = 1647311311407553139320896 := by decide +kernel
private theorem receipt_3_13_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 0 256 = 4579840967106860597181835840 :=
  phaseBlock_append receipt_3_13_2359_1_part0 receipt_3_13_2359_1_part1 rfl rfl rfl
private theorem receipt_3_13_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 384 256 = 2791608355773720806132927040 :=
  phaseBlock_append receipt_3_13_2359_1_part3 receipt_3_13_2359_1_part4 rfl rfl rfl
private theorem receipt_3_13_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 256 384 = 4616309566909343513801840480 :=
  phaseBlock_append receipt_3_13_2359_1_part2 receipt_3_13_2359_1_join1 rfl rfl rfl
private theorem receipt_3_13_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 0 640 = 9196150534016204110983676320 :=
  phaseBlock_append receipt_3_13_2359_1_join0 receipt_3_13_2359_1_join2 rfl rfl rfl
private theorem receipt_3_13_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 768 256 = 1275864606700077685156948544 :=
  phaseBlock_append receipt_3_13_2359_1_part6 receipt_3_13_2359_1_part7 rfl rfl rfl
private theorem receipt_3_13_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 640 384 = 2273053200259817785812182880 :=
  phaseBlock_append receipt_3_13_2359_1_part5 receipt_3_13_2359_1_join4 rfl rfl rfl
private theorem receipt_3_13_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 1152 146 = 117720749022741890225743200 :=
  phaseBlock_append receipt_3_13_2359_1_part9 receipt_3_13_2359_1_part10 rfl rfl rfl
private theorem receipt_3_13_2359_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 1024 274 = 429074780968525153221841536 :=
  phaseBlock_append receipt_3_13_2359_1_part8 receipt_3_13_2359_1_join6 rfl rfl rfl
private theorem receipt_3_13_2359_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 640 658 = 2702127981228342939034024416 :=
  phaseBlock_append receipt_3_13_2359_1_join5 receipt_3_13_2359_1_join7 rfl rfl rfl
private theorem receipt_3_13_2359_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2379 44 1 1 1 1) 0 1298 = 11898278515244547050017700736 :=
  phaseBlock_append receipt_3_13_2359_1_join3 receipt_3_13_2359_1_join8 rfl rfl rfl

private theorem receipt_3_13_2359_1 : fastPhase (bank 3 13).shape 179808 2379 44 1 1 1 1 = 11898278515244547050017700736 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2359_1_join9

private theorem receipt_3_13_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 0 128 = 2452238413019825949700389728 := by decide +kernel
private theorem receipt_3_13_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 128 128 = 2132571950359470259807406944 := by decide +kernel
private theorem receipt_3_13_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 256 128 = 1827019995301952241126120288 := by decide +kernel
private theorem receipt_3_13_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 384 128 = 1535994846097822449177324384 := by decide +kernel
private theorem receipt_3_13_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 512 128 = 1259905105629071177803840352 := by decide +kernel
private theorem receipt_3_13_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 640 128 = 999155690845005307348814688 := by decide +kernel
private theorem receipt_3_13_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 768 128 = 754147842198125152834018144 := by decide +kernel
private theorem receipt_3_13_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 896 128 = 525279133080001312138144608 := by decide +kernel
private theorem receipt_3_13_2360_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 1024 128 = 312943479257151514175109984 := by decide +kernel
private theorem receipt_3_13_2360_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 1152 128 = 117531148306917467072351072 := by decide +kernel
private theorem receipt_3_13_2360_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 1280 18 = 1841567621244640344177129 := by decide +kernel
private theorem receipt_3_13_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 0 256 = 4584810363379296209507796672 :=
  phaseBlock_append receipt_3_13_2360_0_part0 receipt_3_13_2360_0_part1 rfl rfl rfl
private theorem receipt_3_13_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 384 256 = 2795899951726893626981164736 :=
  phaseBlock_append receipt_3_13_2360_0_part3 receipt_3_13_2360_0_part4 rfl rfl rfl
private theorem receipt_3_13_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 256 384 = 4622919947028845868107285024 :=
  phaseBlock_append receipt_3_13_2360_0_part2 receipt_3_13_2360_0_join1 rfl rfl rfl
private theorem receipt_3_13_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 0 640 = 9207730310408142077615081696 :=
  phaseBlock_append receipt_3_13_2360_0_join0 receipt_3_13_2360_0_join2 rfl rfl rfl
private theorem receipt_3_13_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 768 256 = 1279426975278126464972162752 :=
  phaseBlock_append receipt_3_13_2360_0_part6 receipt_3_13_2360_0_part7 rfl rfl rfl
private theorem receipt_3_13_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 640 384 = 2278582666123131772320977440 :=
  phaseBlock_append receipt_3_13_2360_0_part5 receipt_3_13_2360_0_join4 rfl rfl rfl
private theorem receipt_3_13_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 1152 146 = 119372715928162107416528201 :=
  phaseBlock_append receipt_3_13_2360_0_part9 receipt_3_13_2360_0_part10 rfl rfl rfl
private theorem receipt_3_13_2360_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 1024 274 = 432316195185313621591638185 :=
  phaseBlock_append receipt_3_13_2360_0_part8 receipt_3_13_2360_0_join6 rfl rfl rfl
private theorem receipt_3_13_2360_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 640 658 = 2710898861308445393912615625 :=
  phaseBlock_append receipt_3_13_2360_0_join5 receipt_3_13_2360_0_join7 rfl rfl rfl
private theorem receipt_3_13_2360_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 0) 0 1298 = 11918629171716587471527697321 :=
  phaseBlock_append receipt_3_13_2360_0_join3 receipt_3_13_2360_0_join8 rfl rfl rfl

private theorem receipt_3_13_2360_0 : fastPhase (bank 3 13).shape 179808 2380 44 1 1 1 0 = 11918629171716587471527697321 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2360_0_join9

private theorem receipt_3_13_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 0 128 = 2449720858707743093417968608 := by decide +kernel
private theorem receipt_3_13_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 128 128 = 2130158422630445125237339104 := by decide +kernel
private theorem receipt_3_13_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 256 128 = 1824714002744132057793946592 := by decide +kernel
private theorem receipt_3_13_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 384 128 = 1533799866865849351768232928 := by decide +kernel
private theorem receipt_3_13_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 512 128 = 1257824587520743936422429664 := by decide +kernel
private theorem receipt_3_13_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 640 128 = 997193051377941057778856928 := by decide +kernel
private theorem receipt_3_13_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 768 128 = 752306468686421126798222304 := by decide +kernel
private theorem receipt_3_13_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 896 128 = 523562382710896567557919712 := by decide +kernel
private theorem receipt_3_13_2360_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 1024 128 = 311354679167688665430328288 := by decide +kernel
private theorem receipt_3_13_2360_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 1152 128 = 116073595660604415261111264 := by decide +kernel
private theorem receipt_3_13_2360_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 1280 18 = 1647312691104348959338914 := by decide +kernel
private theorem receipt_3_13_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 0 256 = 4579879281338188218655307712 :=
  phaseBlock_append receipt_3_13_2360_1_part0 receipt_3_13_2360_1_part1 rfl rfl rfl
private theorem receipt_3_13_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 384 256 = 2791624454386593288190662592 :=
  phaseBlock_append receipt_3_13_2360_1_part3 receipt_3_13_2360_1_part4 rfl rfl rfl
private theorem receipt_3_13_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 256 384 = 4616338457130725345984609184 :=
  phaseBlock_append receipt_3_13_2360_1_part2 receipt_3_13_2360_1_join1 rfl rfl rfl
private theorem receipt_3_13_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 0 640 = 9196217738468913564639916896 :=
  phaseBlock_append receipt_3_13_2360_1_join0 receipt_3_13_2360_1_join2 rfl rfl rfl
private theorem receipt_3_13_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 768 256 = 1275868851397317694356142016 :=
  phaseBlock_append receipt_3_13_2360_1_part6 receipt_3_13_2360_1_part7 rfl rfl rfl
private theorem receipt_3_13_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 640 384 = 2273061902775258752134998944 :=
  phaseBlock_append receipt_3_13_2360_1_part5 receipt_3_13_2360_1_join4 rfl rfl rfl
private theorem receipt_3_13_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 1152 146 = 117720908351708764220450178 :=
  phaseBlock_append receipt_3_13_2360_1_part9 receipt_3_13_2360_1_part10 rfl rfl rfl
private theorem receipt_3_13_2360_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 1024 274 = 429075587519397429650778466 :=
  phaseBlock_append receipt_3_13_2360_1_part8 receipt_3_13_2360_1_join6 rfl rfl rfl
private theorem receipt_3_13_2360_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 640 658 = 2702137490294656181785777410 :=
  phaseBlock_append receipt_3_13_2360_1_join5 receipt_3_13_2360_1_join7 rfl rfl rfl
private theorem receipt_3_13_2360_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2380 44 1 1 1 1) 0 1298 = 11898355228763569746425694306 :=
  phaseBlock_append receipt_3_13_2360_1_join3 receipt_3_13_2360_1_join8 rfl rfl rfl

private theorem receipt_3_13_2360_1 : fastPhase (bank 3 13).shape 179808 2380 44 1 1 1 1 = 11898355228763569746425694306 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2360_1_join9

theorem receipt_3_13 : Checked (bank 3 13) 44 1 1 := by
  refine checked_from_values (bank 3 13) 44 1 1
    (P3_7_1.checked (bank 3 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1297)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_13_2359_0 receipt_3_13_2359_1 receipt_3_13_2360_0 receipt_3_13_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 0 128 = 202310195854741035516935423520 := by decide +kernel
private theorem receipt_0_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 128 128 = 185179191985131933146616075808 := by decide +kernel
private theorem receipt_0_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 256 128 = 168565489161703859813604845088 := by decide +kernel
private theorem receipt_0_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 384 128 = 152461100674375114158557050400 := by decide +kernel
private theorem receipt_0_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 512 128 = 136858052237488795384337368608 := by decide +kernel
private theorem receipt_0_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 640 128 = 121748381983525180041885111840 := by decide +kernel
private theorem receipt_0_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 768 128 = 107124140456814098816079504928 := by decide +kernel
private theorem receipt_0_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 896 128 = 92977390607247313311604962848 := by decide +kernel
private theorem receipt_0_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1024 128 = 79300207783990892838816368160 := by decide +kernel
private theorem receipt_0_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1152 128 = 66084679729197591199604348448 := by decide +kernel
private theorem receipt_0_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1280 128 = 53322912494277243951721835332 := by decide +kernel
private theorem receipt_0_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1408 128 = 41007036341687773726508998692 := by decide +kernel
private theorem receipt_0_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1536 128 = 29129158579976636198098696160 := by decide +kernel
private theorem receipt_0_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1664 128 = 17681389423184843291291441481 := by decide +kernel
private theorem receipt_0_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1792 128 = 6655851470887816815832519812 := by decide +kernel
private theorem receipt_0_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1920 15 = 77471278805275496832215364 := by decide +kernel
private theorem receipt_0_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 0 256 = 387489387839872968663551499328 :=
  phaseBlock_append receipt_0_14_2359_0_part0 receipt_0_14_2359_0_part1 rfl rfl rfl
private theorem receipt_0_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 256 256 = 321026589836078973972161895488 :=
  phaseBlock_append receipt_0_14_2359_0_part2 receipt_0_14_2359_0_part3 rfl rfl rfl
private theorem receipt_0_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 0 512 = 708515977675951942635713394816 :=
  phaseBlock_append receipt_0_14_2359_0_join0 receipt_0_14_2359_0_join1 rfl rfl rfl
private theorem receipt_0_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 512 256 = 258606434221013975426222480448 :=
  phaseBlock_append receipt_0_14_2359_0_part4 receipt_0_14_2359_0_part5 rfl rfl rfl
private theorem receipt_0_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 768 256 = 200101531064061412127684467776 :=
  phaseBlock_append receipt_0_14_2359_0_part6 receipt_0_14_2359_0_part7 rfl rfl rfl
private theorem receipt_0_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 512 512 = 458707965285075387553906948224 :=
  phaseBlock_append receipt_0_14_2359_0_join3 receipt_0_14_2359_0_join4 rfl rfl rfl
private theorem receipt_0_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 0 1024 = 1167223942961027330189620343040 :=
  phaseBlock_append receipt_0_14_2359_0_join2 receipt_0_14_2359_0_join5 rfl rfl rfl
private theorem receipt_0_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1024 256 = 145384887513188484038420716608 :=
  phaseBlock_append receipt_0_14_2359_0_part8 receipt_0_14_2359_0_part9 rfl rfl rfl
private theorem receipt_0_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1280 256 = 94329948835965017678230834024 :=
  phaseBlock_append receipt_0_14_2359_0_part10 receipt_0_14_2359_0_part11 rfl rfl rfl
private theorem receipt_0_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1024 512 = 239714836349153501716651550632 :=
  phaseBlock_append receipt_0_14_2359_0_join7 receipt_0_14_2359_0_join8 rfl rfl rfl
private theorem receipt_0_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1536 256 = 46810548003161479489390137641 :=
  phaseBlock_append receipt_0_14_2359_0_part12 receipt_0_14_2359_0_part13 rfl rfl rfl
private theorem receipt_0_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1792 143 = 6733322749693092312664735176 :=
  phaseBlock_append receipt_0_14_2359_0_part14 receipt_0_14_2359_0_part15 rfl rfl rfl
private theorem receipt_0_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1536 399 = 53543870752854571802054872817 :=
  phaseBlock_append receipt_0_14_2359_0_join10 receipt_0_14_2359_0_join11 rfl rfl rfl
private theorem receipt_0_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 1024 911 = 293258707102008073518706423449 :=
  phaseBlock_append receipt_0_14_2359_0_join9 receipt_0_14_2359_0_join12 rfl rfl rfl
private theorem receipt_0_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 0) 0 1935 = 1460482650063035403708326766489 :=
  phaseBlock_append receipt_0_14_2359_0_join6 receipt_0_14_2359_0_join13 rfl rfl rfl

private theorem receipt_0_14_2359_0 : fastPhase (bank 0 14).shape 179808 2379 73 1 0 1 0 = 1460482650063035403708326766489 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2359_0_join14

private theorem receipt_0_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 0 128 = 202176128858818342841730817056 := by decide +kernel
private theorem receipt_0_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 128 128 = 185049060874144739571784690720 := by decide +kernel
private theorem receipt_0_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 256 128 = 168439233517715560877552630816 := by decide +kernel
private theorem receipt_0_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 384 128 = 152338660174131474390270266400 := by decide +kernel
private theorem receipt_0_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 512 128 = 136739366652369807148833086496 := by decide +kernel
private theorem receipt_0_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 640 128 = 121633391179496922385661717536 := by decide +kernel
private theorem receipt_0_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 768 128 = 107012784394380596312567200800 := by decide +kernel
private theorem receipt_0_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 896 128 = 92869609341402394906616269856 := by decide +kernel
private theorem receipt_0_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1024 128 = 79195941464170050695996628000 := by decide +kernel
private theorem receipt_0_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1152 128 = 65983868599229839545882225696 := by decide +kernel
private theorem receipt_0_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1280 128 = 53225496881692324543451564716 := by decide +kernel
private theorem receipt_0_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1408 128 = 40912956621072376309237835213 := by decide +kernel
private theorem receipt_0_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1536 128 = 29038355207665551502311434754 := by decide +kernel
private theorem receipt_0_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1664 128 = 17593802949857298098651326608 := by decide +kernel
private theorem receipt_0_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1792 128 = 6571422541548002507814363499 := by decide +kernel
private theorem receipt_0_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1920 15 = 67781218485130235796175388 := by decide +kernel
private theorem receipt_0_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 0 256 = 387225189732963082413515507776 :=
  phaseBlock_append receipt_0_14_2359_1_part0 receipt_0_14_2359_1_part1 rfl rfl rfl
private theorem receipt_0_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 256 256 = 320777893691847035267822897216 :=
  phaseBlock_append receipt_0_14_2359_1_part2 receipt_0_14_2359_1_part3 rfl rfl rfl
private theorem receipt_0_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 0 512 = 708003083424810117681338404992 :=
  phaseBlock_append receipt_0_14_2359_1_join0 receipt_0_14_2359_1_join1 rfl rfl rfl
private theorem receipt_0_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 512 256 = 258372757831866729534494804032 :=
  phaseBlock_append receipt_0_14_2359_1_part4 receipt_0_14_2359_1_part5 rfl rfl rfl
private theorem receipt_0_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 768 256 = 199882393735782991219183470656 :=
  phaseBlock_append receipt_0_14_2359_1_part6 receipt_0_14_2359_1_part7 rfl rfl rfl
private theorem receipt_0_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 512 512 = 458255151567649720753678274688 :=
  phaseBlock_append receipt_0_14_2359_1_join3 receipt_0_14_2359_1_join4 rfl rfl rfl
private theorem receipt_0_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 0 1024 = 1166258234992459838435016679680 :=
  phaseBlock_append receipt_0_14_2359_1_join2 receipt_0_14_2359_1_join5 rfl rfl rfl
private theorem receipt_0_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1024 256 = 145179810063399890241878853696 :=
  phaseBlock_append receipt_0_14_2359_1_part8 receipt_0_14_2359_1_part9 rfl rfl rfl
private theorem receipt_0_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1280 256 = 94138453502764700852689399929 :=
  phaseBlock_append receipt_0_14_2359_1_part10 receipt_0_14_2359_1_part11 rfl rfl rfl
private theorem receipt_0_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1024 512 = 239318263566164591094568253625 :=
  phaseBlock_append receipt_0_14_2359_1_join7 receipt_0_14_2359_1_join8 rfl rfl rfl
private theorem receipt_0_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1536 256 = 46632158157522849600962761362 :=
  phaseBlock_append receipt_0_14_2359_1_part12 receipt_0_14_2359_1_part13 rfl rfl rfl
private theorem receipt_0_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1792 143 = 6639203760033132743610538887 :=
  phaseBlock_append receipt_0_14_2359_1_part14 receipt_0_14_2359_1_part15 rfl rfl rfl
private theorem receipt_0_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1536 399 = 53271361917555982344573300249 :=
  phaseBlock_append receipt_0_14_2359_1_join10 receipt_0_14_2359_1_join11 rfl rfl rfl
private theorem receipt_0_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 1024 911 = 292589625483720573439141553874 :=
  phaseBlock_append receipt_0_14_2359_1_join9 receipt_0_14_2359_1_join12 rfl rfl rfl
private theorem receipt_0_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2379 73 1 0 1 1) 0 1935 = 1458847860476180411874158233554 :=
  phaseBlock_append receipt_0_14_2359_1_join6 receipt_0_14_2359_1_join13 rfl rfl rfl

private theorem receipt_0_14_2359_1 : fastPhase (bank 0 14).shape 179808 2379 73 1 0 1 1 = 1458847860476180411874158233554 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2359_1_join14

private theorem receipt_0_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 0 128 = 202312011590133663073574707680 := by decide +kernel
private theorem receipt_0_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 128 128 = 185180792359592918268467646944 := by decide +kernel
private theorem receipt_0_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 256 128 = 168566888719657517351210533344 := by decide +kernel
private theorem receipt_0_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 384 128 = 152462313685024345345830154720 := by decide +kernel
private theorem receipt_0_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 512 128 = 136859092695247961477609202144 := by decide +kernel
private theorem receipt_0_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 640 128 = 121749263608452756056625992160 := by decide +kernel
private theorem receipt_0_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 768 128 = 107124876695045107361294189024 := by decide +kernel
private theorem receipt_0_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 896 128 = 92977994631425538521902526944 := by decide +kernel
private theorem receipt_0_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1024 128 = 79300692493700874404154532320 := by decide +kernel
private theorem receipt_0_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1152 128 = 66085057751396398492708245984 := by decide +kernel
private theorem receipt_0_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1280 128 = 53323195991560855360984691993 := by decide +kernel
private theorem receipt_0_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1408 128 = 41007237308412097083045528933 := by decide +kernel
private theorem receipt_0_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1536 128 = 29129289028311987825247067206 := by decide +kernel
private theorem receipt_0_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1664 128 = 17681461068698429035002477552 := by decide +kernel
private theorem receipt_0_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1792 128 = 6655875734512530074795083641 := by decide +kernel
private theorem receipt_0_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1920 15 = 77471537631127431718835244 := by decide +kernel
private theorem receipt_0_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 0 256 = 387492803949726581342042354624 :=
  phaseBlock_append receipt_0_14_2360_0_part0 receipt_0_14_2360_0_part1 rfl rfl rfl
private theorem receipt_0_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 256 256 = 321029202404681862697040688064 :=
  phaseBlock_append receipt_0_14_2360_0_part2 receipt_0_14_2360_0_part3 rfl rfl rfl
private theorem receipt_0_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 0 512 = 708522006354408444039083042688 :=
  phaseBlock_append receipt_0_14_2360_0_join0 receipt_0_14_2360_0_join1 rfl rfl rfl
private theorem receipt_0_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 512 256 = 258608356303700717534235194304 :=
  phaseBlock_append receipt_0_14_2360_0_part4 receipt_0_14_2360_0_part5 rfl rfl rfl
private theorem receipt_0_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 768 256 = 200102871326470645883196715968 :=
  phaseBlock_append receipt_0_14_2360_0_part6 receipt_0_14_2360_0_part7 rfl rfl rfl
private theorem receipt_0_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 512 512 = 458711227630171363417431910272 :=
  phaseBlock_append receipt_0_14_2360_0_join3 receipt_0_14_2360_0_join4 rfl rfl rfl
private theorem receipt_0_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 0 1024 = 1167233233984579807456514952960 :=
  phaseBlock_append receipt_0_14_2360_0_join2 receipt_0_14_2360_0_join5 rfl rfl rfl
private theorem receipt_0_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1024 256 = 145385750245097272896862778304 :=
  phaseBlock_append receipt_0_14_2360_0_part8 receipt_0_14_2360_0_part9 rfl rfl rfl
private theorem receipt_0_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1280 256 = 94330433299972952444030220926 :=
  phaseBlock_append receipt_0_14_2360_0_part10 receipt_0_14_2360_0_part11 rfl rfl rfl
private theorem receipt_0_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1024 512 = 239716183545070225340892999230 :=
  phaseBlock_append receipt_0_14_2360_0_join7 receipt_0_14_2360_0_join8 rfl rfl rfl
private theorem receipt_0_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1536 256 = 46810750097010416860249544758 :=
  phaseBlock_append receipt_0_14_2360_0_part12 receipt_0_14_2360_0_part13 rfl rfl rfl
private theorem receipt_0_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1792 143 = 6733347272143657506513918885 :=
  phaseBlock_append receipt_0_14_2360_0_part14 receipt_0_14_2360_0_part15 rfl rfl rfl
private theorem receipt_0_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1536 399 = 53544097369154074366763463643 :=
  phaseBlock_append receipt_0_14_2360_0_join10 receipt_0_14_2360_0_join11 rfl rfl rfl
private theorem receipt_0_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 1024 911 = 293260280914224299707656462873 :=
  phaseBlock_append receipt_0_14_2360_0_join9 receipt_0_14_2360_0_join12 rfl rfl rfl
private theorem receipt_0_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 0) 0 1935 = 1460493514898804107164171415833 :=
  phaseBlock_append receipt_0_14_2360_0_join6 receipt_0_14_2360_0_join13 rfl rfl rfl

private theorem receipt_0_14_2360_0 : fastPhase (bank 0 14).shape 179808 2380 73 1 0 1 0 = 1460493514898804107164171415833 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2360_0_join14

private theorem receipt_0_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 0 128 = 202177943608920895001347521504 := by decide +kernel
private theorem receipt_0_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 128 128 = 185050660320628060854794570720 := by decide +kernel
private theorem receipt_0_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 256 128 = 168440632203703909490909715424 := by decide +kernel
private theorem receipt_0_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 384 128 = 152339872367530065488012536800 := by decide +kernel
private theorem receipt_0_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 512 128 = 136740406346297685165458963424 := by decide +kernel
private theorem receipt_0_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 640 128 = 121634272092719613467180993504 := by decide +kernel
private theorem receipt_0_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 768 128 = 107013519971742540845226417120 := by decide +kernel
private theorem receipt_0_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 896 128 = 92870212754259160143298538464 := by decide +kernel
private theorem receipt_0_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1024 128 = 79196425610820323480295898080 := by decide +kernel
private theorem receipt_0_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1152 128 = 65984246105347199133851995104 := by decide +kernel
private theorem receipt_0_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1280 128 = 53225779908930614041231184810 := by decide +kernel
private theorem receipt_0_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1408 128 = 40913157162867882405964565422 := by decide +kernel
private theorem receipt_0_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1536 128 = 29038485274847344871249756781 := by decide +kernel
private theorem receipt_0_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1664 128 = 17593874256655696778654227758 := by decide +kernel
private theorem receipt_0_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1792 128 = 6571446507563659807872841532 := by decide +kernel
private theorem receipt_0_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1920 15 = 67781445067938737006685709 := by decide +kernel
private theorem receipt_0_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 0 256 = 387228603929548955856142092224 :=
  phaseBlock_append receipt_0_14_2360_1_part0 receipt_0_14_2360_1_part1 rfl rfl rfl
private theorem receipt_0_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 256 256 = 320780504571233974978922252224 :=
  phaseBlock_append receipt_0_14_2360_1_part2 receipt_0_14_2360_1_part3 rfl rfl rfl
private theorem receipt_0_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 0 512 = 708009108500782930835064344448 :=
  phaseBlock_append receipt_0_14_2360_1_join0 receipt_0_14_2360_1_join1 rfl rfl rfl
private theorem receipt_0_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 512 256 = 258374678439017298632639956928 :=
  phaseBlock_append receipt_0_14_2360_1_part4 receipt_0_14_2360_1_part5 rfl rfl rfl
private theorem receipt_0_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 768 256 = 199883732726001700988524955584 :=
  phaseBlock_append receipt_0_14_2360_1_part6 receipt_0_14_2360_1_part7 rfl rfl rfl
private theorem receipt_0_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 512 512 = 458258411165018999621164912512 :=
  phaseBlock_append receipt_0_14_2360_1_join3 receipt_0_14_2360_1_join4 rfl rfl rfl
private theorem receipt_0_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 0 1024 = 1166267519665801930456229256960 :=
  phaseBlock_append receipt_0_14_2360_1_join2 receipt_0_14_2360_1_join5 rfl rfl rfl
private theorem receipt_0_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1024 256 = 145180671716167522614147893184 :=
  phaseBlock_append receipt_0_14_2360_1_part8 receipt_0_14_2360_1_part9 rfl rfl rfl
private theorem receipt_0_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1280 256 = 94138937071798496447195750232 :=
  phaseBlock_append receipt_0_14_2360_1_part10 receipt_0_14_2360_1_part11 rfl rfl rfl
private theorem receipt_0_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1024 512 = 239319608787966019061343643416 :=
  phaseBlock_append receipt_0_14_2360_1_join7 receipt_0_14_2360_1_join8 rfl rfl rfl
private theorem receipt_0_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1536 256 = 46632359531503041649903984539 :=
  phaseBlock_append receipt_0_14_2360_1_part12 receipt_0_14_2360_1_part13 rfl rfl rfl
private theorem receipt_0_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1792 143 = 6639227952631598544879527241 :=
  phaseBlock_append receipt_0_14_2360_1_part14 receipt_0_14_2360_1_part15 rfl rfl rfl
private theorem receipt_0_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1536 399 = 53271587484134640194783511780 :=
  phaseBlock_append receipt_0_14_2360_1_join10 receipt_0_14_2360_1_join11 rfl rfl rfl
private theorem receipt_0_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 1024 911 = 292591196272100659256127155196 :=
  phaseBlock_append receipt_0_14_2360_1_join9 receipt_0_14_2360_1_join12 rfl rfl rfl
private theorem receipt_0_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2380 73 1 0 1 1) 0 1935 = 1458858715937902589712356412156 :=
  phaseBlock_append receipt_0_14_2360_1_join6 receipt_0_14_2360_1_join13 rfl rfl rfl

private theorem receipt_0_14_2360_1 : fastPhase (bank 0 14).shape 179808 2380 73 1 0 1 1 = 1458858715937902589712356412156 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2360_1_join14

theorem receipt_0_14 : Checked (bank 0 14) 73 0 1 := by
  refine checked_from_values (bank 0 14) 73 0 1
    (P3_7_1.checked (bank 0 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_14_2359_0 receipt_0_14_2359_1 receipt_0_14_2360_0 receipt_0_14_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 0 128 = 182134781239494369757880259552 := by decide +kernel
private theorem receipt_1_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 128 128 = 166635890866585115857730798560 := by decide +kernel
private theorem receipt_1_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 256 128 = 151616392367802759398431519712 := by decide +kernel
private theorem receipt_1_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 384 128 = 137068469546232017490066400224 := by decide +kernel
private theorem receipt_1_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 512 128 = 122984330305840948861822161888 := by decide +kernel
private theorem receipt_1_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 640 128 = 109356206626330461005449380832 := by decide +kernel
private theorem receipt_1_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 768 128 = 96176354537983817318723597280 := by decide +kernel
private theorem receipt_1_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 896 128 = 83437054096516144248906425312 := by decide +kernel
private theorem receipt_1_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1024 128 = 71130609357923938436206662624 := by decide +kernel
private theorem receipt_1_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1152 128 = 59249348353334573857241400288 := by decide +kernel
private theorem receipt_1_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1280 128 = 47785628370724707307789444761 := by decide +kernel
private theorem receipt_1_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1408 128 = 36731841211405541580357965031 := by decide +kernel
private theorem receipt_1_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1536 128 = 26080370917519500255133773406 := by decide +kernel
private theorem receipt_1_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1664 128 = 15823616965835046214434204158 := by decide +kernel
private theorem receipt_1_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1792 128 = 5954002748623313608308552223 := by decide +kernel
private theorem receipt_1_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1920 15 = 69280429806231733190364476 := by decide +kernel
private theorem receipt_1_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 0 256 = 348770672106079485615611058112 :=
  phaseBlock_append receipt_1_14_2359_0_part0 receipt_1_14_2359_0_part1 rfl rfl rfl
private theorem receipt_1_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 256 256 = 288684861914034776888497919936 :=
  phaseBlock_append receipt_1_14_2359_0_part2 receipt_1_14_2359_0_part3 rfl rfl rfl
private theorem receipt_1_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 0 512 = 637455534020114262504108978048 :=
  phaseBlock_append receipt_1_14_2359_0_join0 receipt_1_14_2359_0_join1 rfl rfl rfl
private theorem receipt_1_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 512 256 = 232340536932171409867271542720 :=
  phaseBlock_append receipt_1_14_2359_0_part4 receipt_1_14_2359_0_part5 rfl rfl rfl
private theorem receipt_1_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 768 256 = 179613408634499961567630022592 :=
  phaseBlock_append receipt_1_14_2359_0_part6 receipt_1_14_2359_0_part7 rfl rfl rfl
private theorem receipt_1_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 512 512 = 411953945566671371434901565312 :=
  phaseBlock_append receipt_1_14_2359_0_join3 receipt_1_14_2359_0_join4 rfl rfl rfl
private theorem receipt_1_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 0 1024 = 1049409479586785633939010543360 :=
  phaseBlock_append receipt_1_14_2359_0_join2 receipt_1_14_2359_0_join5 rfl rfl rfl
private theorem receipt_1_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1024 256 = 130379957711258512293448062912 :=
  phaseBlock_append receipt_1_14_2359_0_part8 receipt_1_14_2359_0_part9 rfl rfl rfl
private theorem receipt_1_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1280 256 = 84517469582130248888147409792 :=
  phaseBlock_append receipt_1_14_2359_0_part10 receipt_1_14_2359_0_part11 rfl rfl rfl
private theorem receipt_1_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1024 512 = 214897427293388761181595472704 :=
  phaseBlock_append receipt_1_14_2359_0_join7 receipt_1_14_2359_0_join8 rfl rfl rfl
private theorem receipt_1_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1536 256 = 41903987883354546469567977564 :=
  phaseBlock_append receipt_1_14_2359_0_part12 receipt_1_14_2359_0_part13 rfl rfl rfl
private theorem receipt_1_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1792 143 = 6023283178429545341498916699 :=
  phaseBlock_append receipt_1_14_2359_0_part14 receipt_1_14_2359_0_part15 rfl rfl rfl
private theorem receipt_1_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1536 399 = 47927271061784091811066894263 :=
  phaseBlock_append receipt_1_14_2359_0_join10 receipt_1_14_2359_0_join11 rfl rfl rfl
private theorem receipt_1_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 1024 911 = 262824698355172852992662366967 :=
  phaseBlock_append receipt_1_14_2359_0_join9 receipt_1_14_2359_0_join12 rfl rfl rfl
private theorem receipt_1_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 0) 0 1935 = 1312234177941958486931672910327 :=
  phaseBlock_append receipt_1_14_2359_0_join6 receipt_1_14_2359_0_join13 rfl rfl rfl

private theorem receipt_1_14_2359_0 : fastPhase (bank 1 14).shape 179808 2379 73 1 0 2 0 = 1312234177941958486931672910327 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2359_0_join14

private theorem receipt_1_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 0 128 = 182013433512096499052424239584 := by decide +kernel
private theorem receipt_1_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 128 128 = 166518195159541671050673088992 := by decide +kernel
private theorem receipt_1_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 256 128 = 151502289458640817543777237472 := by decide +kernel
private theorem receipt_1_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 384 128 = 136957900396224552625101933024 := by decide +kernel
private theorem receipt_1_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 512 128 = 122877236059814267388917176800 := by decide +kernel
private theorem receipt_1_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 640 128 = 109252528612471637073858832864 := by decide +kernel
private theorem receipt_1_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 768 128 = 96076034267648128206389737952 := by decide +kernel
private theorem receipt_1_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 896 128 = 83340033264034505744260811232 := by decide +kernel
private theorem receipt_1_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1024 128 = 71036829840410340219972164064 := by decide +kernel
private theorem receipt_1_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1152 128 = 59158752210493514884234209760 := by decide +kernel
private theorem receipt_1_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1280 128 = 47698157835101526205247247870 := by decide +kernel
private theorem receipt_1_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1408 128 = 36647438655392391482143309274 := by decide +kernel
private theorem receipt_1_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1536 128 = 25998978884456054411457835486 := by decide +kernel
private theorem receipt_1_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1664 128 = 15745178181184085913701323205 := by decide +kernel
private theorem receipt_1_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1792 128 = 5878460119803597564620872603 := by decide +kernel
private theorem receipt_1_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1920 15 = 60614729973801786708169307 := by decide +kernel
private theorem receipt_1_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 0 256 = 348531628671638170103097328576 :=
  phaseBlock_append receipt_1_14_2359_1_part0 receipt_1_14_2359_1_part1 rfl rfl rfl
private theorem receipt_1_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 256 256 = 288460189854865370168879170496 :=
  phaseBlock_append receipt_1_14_2359_1_part2 receipt_1_14_2359_1_part3 rfl rfl rfl
private theorem receipt_1_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 0 512 = 636991818526503540271976499072 :=
  phaseBlock_append receipt_1_14_2359_1_join0 receipt_1_14_2359_1_join1 rfl rfl rfl
private theorem receipt_1_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 512 256 = 232129764672285904462776009664 :=
  phaseBlock_append receipt_1_14_2359_1_part4 receipt_1_14_2359_1_part5 rfl rfl rfl
private theorem receipt_1_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 768 256 = 179416067531682633950650549184 :=
  phaseBlock_append receipt_1_14_2359_1_part6 receipt_1_14_2359_1_part7 rfl rfl rfl
private theorem receipt_1_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 512 512 = 411545832203968538413426558848 :=
  phaseBlock_append receipt_1_14_2359_1_join3 receipt_1_14_2359_1_join4 rfl rfl rfl
private theorem receipt_1_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 0 1024 = 1048537650730472078685403057920 :=
  phaseBlock_append receipt_1_14_2359_1_join2 receipt_1_14_2359_1_join5 rfl rfl rfl
private theorem receipt_1_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1024 256 = 130195582050903855104206373824 :=
  phaseBlock_append receipt_1_14_2359_1_part8 receipt_1_14_2359_1_part9 rfl rfl rfl
private theorem receipt_1_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1280 256 = 84345596490493917687390557144 :=
  phaseBlock_append receipt_1_14_2359_1_part10 receipt_1_14_2359_1_part11 rfl rfl rfl
private theorem receipt_1_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1024 512 = 214541178541397772791596930968 :=
  phaseBlock_append receipt_1_14_2359_1_join7 receipt_1_14_2359_1_join8 rfl rfl rfl
private theorem receipt_1_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1536 256 = 41744157065640140325159158691 :=
  phaseBlock_append receipt_1_14_2359_1_part12 receipt_1_14_2359_1_part13 rfl rfl rfl
private theorem receipt_1_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1792 143 = 5939074849777399351329041910 :=
  phaseBlock_append receipt_1_14_2359_1_part14 receipt_1_14_2359_1_part15 rfl rfl rfl
private theorem receipt_1_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1536 399 = 47683231915417539676488200601 :=
  phaseBlock_append receipt_1_14_2359_1_join10 receipt_1_14_2359_1_join11 rfl rfl rfl
private theorem receipt_1_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 1024 911 = 262224410456815312468085131569 :=
  phaseBlock_append receipt_1_14_2359_1_join9 receipt_1_14_2359_1_join12 rfl rfl rfl
private theorem receipt_1_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2379 73 1 0 2 1) 0 1935 = 1310762061187287391153488189489 :=
  phaseBlock_append receipt_1_14_2359_1_join6 receipt_1_14_2359_1_join13 rfl rfl rfl

private theorem receipt_1_14_2359_1 : fastPhase (bank 1 14).shape 179808 2379 73 1 0 2 1 = 1310762061187287391153488189489 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2359_1_join14

private theorem receipt_1_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 0 128 = 182136415902690364756327249056 := by decide +kernel
private theorem receipt_1_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 128 128 = 166637330986379074004587177120 := by decide +kernel
private theorem receipt_1_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 256 128 = 151617651203544679058251191456 := by decide +kernel
private theorem receipt_1_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 384 128 = 137069560091899535182699381920 := by decide +kernel
private theorem receipt_1_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 512 128 = 122985265290875614887239382176 := by decide +kernel
private theorem receipt_1_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 640 128 = 109356998516473135459265258656 := by decide +kernel
private theorem receipt_1_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 768 128 = 96177015536109186498416399520 := by decide +kernel
private theorem receipt_1_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 896 128 = 83437596143466357450736403616 := by decide +kernel
private theorem receipt_1_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1024 128 = 71131044133341365142831969440 := by decide +kernel
private theorem receipt_1_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1152 128 = 59249687276493681316031784096 := by decide +kernel
private theorem receipt_1_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1280 128 = 47785882429167866207009384938 := by decide +kernel
private theorem receipt_1_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1408 128 = 36732021226903197966035272191 := by decide +kernel
private theorem receipt_1_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1536 128 = 26080487712976470933188291810 := by decide +kernel
private theorem receipt_1_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1664 128 = 15823681083858293683166325182 := by decide +kernel
private theorem receipt_1_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1792 128 = 5954024453768474762874777887 := by decide +kernel
private theorem receipt_1_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1920 15 = 69280661267070345287489561 := by decide +kernel
private theorem receipt_1_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 0 256 = 348773746889069438760914426176 :=
  phaseBlock_append receipt_1_14_2360_0_part0 receipt_1_14_2360_0_part1 rfl rfl rfl
private theorem receipt_1_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 256 256 = 288687211295444214240950573376 :=
  phaseBlock_append receipt_1_14_2360_0_part2 receipt_1_14_2360_0_part3 rfl rfl rfl
private theorem receipt_1_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 0 512 = 637460958184513653001864999552 :=
  phaseBlock_append receipt_1_14_2360_0_join0 receipt_1_14_2360_0_join1 rfl rfl rfl
private theorem receipt_1_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 512 256 = 232342263807348750346504640832 :=
  phaseBlock_append receipt_1_14_2360_0_part4 receipt_1_14_2360_0_part5 rfl rfl rfl
private theorem receipt_1_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 768 256 = 179614611679575543949152803136 :=
  phaseBlock_append receipt_1_14_2360_0_part6 receipt_1_14_2360_0_part7 rfl rfl rfl
private theorem receipt_1_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 512 512 = 411956875486924294295657443968 :=
  phaseBlock_append receipt_1_14_2360_0_join3 receipt_1_14_2360_0_join4 rfl rfl rfl
private theorem receipt_1_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 0 1024 = 1049417833671437947297522443520 :=
  phaseBlock_append receipt_1_14_2360_0_join2 receipt_1_14_2360_0_join5 rfl rfl rfl
private theorem receipt_1_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1024 256 = 130380731409835046458863753536 :=
  phaseBlock_append receipt_1_14_2360_0_part8 receipt_1_14_2360_0_part9 rfl rfl rfl
private theorem receipt_1_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1280 256 = 84517903656071064173044657129 :=
  phaseBlock_append receipt_1_14_2360_0_part10 receipt_1_14_2360_0_part11 rfl rfl rfl
private theorem receipt_1_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1024 512 = 214898635065906110631908410665 :=
  phaseBlock_append receipt_1_14_2360_0_join7 receipt_1_14_2360_0_join8 rfl rfl rfl
private theorem receipt_1_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1536 256 = 41904168796834764616354616992 :=
  phaseBlock_append receipt_1_14_2360_0_part12 receipt_1_14_2360_0_part13 rfl rfl rfl
private theorem receipt_1_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1792 143 = 6023305115035545108162267448 :=
  phaseBlock_append receipt_1_14_2360_0_part14 receipt_1_14_2360_0_part15 rfl rfl rfl
private theorem receipt_1_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1536 399 = 47927473911870309724516884440 :=
  phaseBlock_append receipt_1_14_2360_0_join10 receipt_1_14_2360_0_join11 rfl rfl rfl
private theorem receipt_1_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 1024 911 = 262826108977776420356425295105 :=
  phaseBlock_append receipt_1_14_2360_0_join9 receipt_1_14_2360_0_join12 rfl rfl rfl
private theorem receipt_1_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 0) 0 1935 = 1312243942649214367653947738625 :=
  phaseBlock_append receipt_1_14_2360_0_join6 receipt_1_14_2360_0_join13 rfl rfl rfl

private theorem receipt_1_14_2360_0 : fastPhase (bank 1 14).shape 179808 2380 73 1 0 2 0 = 1312243942649214367653947738625 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2360_0_join14

private theorem receipt_1_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 0 128 = 182015067282419524819243985376 := by decide +kernel
private theorem receipt_1_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 128 128 = 166519634439134025228437084640 := by decide +kernel
private theorem receipt_1_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 256 128 = 151503547505589416738921794016 := by decide +kernel
private theorem receipt_1_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 384 128 = 136958990203248538125678524896 := by decide +kernel
private theorem receipt_1_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 512 128 = 122878170355101275566737009120 := by decide +kernel
private theorem receipt_1_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 640 128 = 109253319860513190177335187936 := by decide +kernel
private theorem receipt_1_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 768 128 = 96076694670074145544078100960 := by decide +kernel
private theorem receipt_1_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 896 128 = 83340574760446935259096775136 := by decide +kernel
private theorem receipt_1_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1024 128 = 71037264109215910454207113696 := by decide +kernel
private theorem receipt_1_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1152 128 = 59159090669735607335068785120 := by decide +kernel
private theorem receipt_1_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1280 128 = 47698411471400357810603201025 := by decide +kernel
private theorem receipt_1_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1408 128 = 36647618289618150203946532544 := by decide +kernel
private theorem receipt_1_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1536 128 = 25999095338236832741548626654 := by decide +kernel
private theorem receipt_1_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1664 128 = 15745241995856610601194972437 := by decide +kernel
private theorem receipt_1_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1792 128 = 5878481558660004301653440975 := by decide +kernel
private theorem receipt_1_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1920 15 = 60614932600084684306254252 := by decide +kernel
private theorem receipt_1_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 0 256 = 348534701721553550047681070016 :=
  phaseBlock_append receipt_1_14_2360_1_part0 receipt_1_14_2360_1_part1 rfl rfl rfl
private theorem receipt_1_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 256 256 = 288462537708837954864600318912 :=
  phaseBlock_append receipt_1_14_2360_1_part2 receipt_1_14_2360_1_part3 rfl rfl rfl
private theorem receipt_1_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 0 512 = 636997239430391504912281388928 :=
  phaseBlock_append receipt_1_14_2360_1_join0 receipt_1_14_2360_1_join1 rfl rfl rfl
private theorem receipt_1_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 512 256 = 232131490215614465744072197056 :=
  phaseBlock_append receipt_1_14_2360_1_part4 receipt_1_14_2360_1_part5 rfl rfl rfl
private theorem receipt_1_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 768 256 = 179417269430521080803174876096 :=
  phaseBlock_append receipt_1_14_2360_1_part6 receipt_1_14_2360_1_part7 rfl rfl rfl
private theorem receipt_1_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 512 512 = 411548759646135546547247073152 :=
  phaseBlock_append receipt_1_14_2360_1_join3 receipt_1_14_2360_1_join4 rfl rfl rfl
private theorem receipt_1_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 0 1024 = 1048545999076527051459528462080 :=
  phaseBlock_append receipt_1_14_2360_1_join2 receipt_1_14_2360_1_join5 rfl rfl rfl
private theorem receipt_1_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1024 256 = 130196354778951517789275898816 :=
  phaseBlock_append receipt_1_14_2360_1_part8 receipt_1_14_2360_1_part9 rfl rfl rfl
private theorem receipt_1_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1280 256 = 84346029761018508014549733569 :=
  phaseBlock_append receipt_1_14_2360_1_part10 receipt_1_14_2360_1_part11 rfl rfl rfl
private theorem receipt_1_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1024 512 = 214542384539970025803825632385 :=
  phaseBlock_append receipt_1_14_2360_1_join7 receipt_1_14_2360_1_join8 rfl rfl rfl
private theorem receipt_1_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1536 256 = 41744337334093443342743599091 :=
  phaseBlock_append receipt_1_14_2360_1_part12 receipt_1_14_2360_1_part13 rfl rfl rfl
private theorem receipt_1_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1792 143 = 5939096491260088985959695227 :=
  phaseBlock_append receipt_1_14_2360_1_part14 receipt_1_14_2360_1_part15 rfl rfl rfl
private theorem receipt_1_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1536 399 = 47683433825353532328703294318 :=
  phaseBlock_append receipt_1_14_2360_1_join10 receipt_1_14_2360_1_join11 rfl rfl rfl
private theorem receipt_1_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 1024 911 = 262225818365323558132528926703 :=
  phaseBlock_append receipt_1_14_2360_1_join9 receipt_1_14_2360_1_join12 rfl rfl rfl
private theorem receipt_1_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2380 73 1 0 2 1) 0 1935 = 1310771817441850609592057388783 :=
  phaseBlock_append receipt_1_14_2360_1_join6 receipt_1_14_2360_1_join13 rfl rfl rfl

private theorem receipt_1_14_2360_1 : fastPhase (bank 1 14).shape 179808 2380 73 1 0 2 1 = 1310771817441850609592057388783 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2360_1_join14

theorem receipt_1_14 : Checked (bank 1 14) 73 0 2 := by
  refine checked_from_values (bank 1 14) 73 0 2
    (P3_7_1.checked (bank 1 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_14_2359_0 receipt_1_14_2359_1 receipt_1_14_2360_0 receipt_1_14_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 0 128 = 97705212630140892123073289472 := by decide +kernel
private theorem receipt_2_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 128 128 = 89097008225166070258101968128 := by decide +kernel
private theorem receipt_2_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 256 128 = 80799178825833843914282016000 := by decide +kernel
private theorem receipt_2_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 384 128 = 72804976106088636031912140032 := by decide +kernel
private theorem receipt_2_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 512 128 = 65107723171908135433578355968 := by decide +kernel
private theorem receipt_2_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 640 128 = 57700814253209759331552582912 := by decide +kernel
private theorem receipt_2_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 768 128 = 50577714395757115835191237888 := by decide +kernel
private theorem receipt_2_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 896 128 = 43731959153066466458333830400 := by decide +kernel
private theorem receipt_2_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1024 128 = 37157154278313188626701556992 := by decide +kernel
private theorem receipt_2_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1152 128 = 30846975416238238185295895808 := by decide +kernel
private theorem receipt_2_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1280 128 = 24795170546173623257887759240 := by decide +kernel
private theorem receipt_2_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1408 128 = 18995562365438974209472344018 := by decide +kernel
private theorem receipt_2_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1536 128 = 13442026113742612091647924556 := by decide +kernel
private theorem receipt_2_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1664 128 = 8128501461836056301173102104 := by decide +kernel
private theorem receipt_2_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1792 128 = 3048996634513185004222813260 := by decide +kernel
private theorem receipt_2_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1920 15 = 35396233347216080964465120 := by decide +kernel
private theorem receipt_2_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 0 256 = 186802220855306962381175257600 :=
  phaseBlock_append receipt_2_14_2359_0_part0 receipt_2_14_2359_0_part1 rfl rfl rfl
private theorem receipt_2_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 256 256 = 153604154931922479946194156032 :=
  phaseBlock_append receipt_2_14_2359_0_part2 receipt_2_14_2359_0_part3 rfl rfl rfl
private theorem receipt_2_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 0 512 = 340406375787229442327369413632 :=
  phaseBlock_append receipt_2_14_2359_0_join0 receipt_2_14_2359_0_join1 rfl rfl rfl
private theorem receipt_2_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 512 256 = 122808537425117894765130938880 :=
  phaseBlock_append receipt_2_14_2359_0_part4 receipt_2_14_2359_0_part5 rfl rfl rfl
private theorem receipt_2_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 768 256 = 94309673548823582293525068288 :=
  phaseBlock_append receipt_2_14_2359_0_part6 receipt_2_14_2359_0_part7 rfl rfl rfl
private theorem receipt_2_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 512 512 = 217118210973941477058656007168 :=
  phaseBlock_append receipt_2_14_2359_0_join3 receipt_2_14_2359_0_join4 rfl rfl rfl
private theorem receipt_2_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 0 1024 = 557524586761170919386025420800 :=
  phaseBlock_append receipt_2_14_2359_0_join2 receipt_2_14_2359_0_join5 rfl rfl rfl
private theorem receipt_2_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1024 256 = 68004129694551426811997452800 :=
  phaseBlock_append receipt_2_14_2359_0_part8 receipt_2_14_2359_0_part9 rfl rfl rfl
private theorem receipt_2_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1280 256 = 43790732911612597467360103258 :=
  phaseBlock_append receipt_2_14_2359_0_part10 receipt_2_14_2359_0_part11 rfl rfl rfl
private theorem receipt_2_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1024 512 = 111794862606164024279357556058 :=
  phaseBlock_append receipt_2_14_2359_0_join7 receipt_2_14_2359_0_join8 rfl rfl rfl
private theorem receipt_2_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1536 256 = 21570527575578668392821026660 :=
  phaseBlock_append receipt_2_14_2359_0_part12 receipt_2_14_2359_0_part13 rfl rfl rfl
private theorem receipt_2_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1792 143 = 3084392867860401085187278380 :=
  phaseBlock_append receipt_2_14_2359_0_part14 receipt_2_14_2359_0_part15 rfl rfl rfl
private theorem receipt_2_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1536 399 = 24654920443439069478008305040 :=
  phaseBlock_append receipt_2_14_2359_0_join10 receipt_2_14_2359_0_join11 rfl rfl rfl
private theorem receipt_2_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 1024 911 = 136449783049603093757365861098 :=
  phaseBlock_append receipt_2_14_2359_0_join9 receipt_2_14_2359_0_join12 rfl rfl rfl
private theorem receipt_2_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 0) 0 1935 = 693974369810774013143391281898 :=
  phaseBlock_append receipt_2_14_2359_0_join6 receipt_2_14_2359_0_join13 rfl rfl rfl

private theorem receipt_2_14_2359_0 : fastPhase (bank 2 14).shape 179808 2379 73 1 0 7 0 = 693974369810774013143391281898 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2359_0_join14

private theorem receipt_2_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 0 128 = 97637607204244864358032708032 := by decide +kernel
private theorem receipt_2_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 128 128 = 89031785017510593744031838656 := by decide +kernel
private theorem receipt_2_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 256 128 = 80736286306652523521073369536 := by decide +kernel
private theorem receipt_2_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 384 128 = 72744363291678412109617738176 := by decide +kernel
private theorem receipt_2_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 512 128 = 65049339622270367239487295936 := by decide +kernel
private theorem receipt_2_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 640 128 = 57644610069691308457264902592 := by decide +kernel
private theorem receipt_2_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 768 128 = 50523640218691429633692520896 := by decide +kernel
private theorem receipt_2_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 896 128 = 43679966159414661471069811136 := by decide +kernel
private theorem receipt_2_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1024 128 = 37107194179305134010652725696 := by decide +kernel
private theorem receipt_2_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1152 128 = 30799000455013639140052103616 := by decide +kernel
private theorem receipt_2_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1280 128 = 24749133490396299448825057669 := by decide +kernel
private theorem receipt_2_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1408 128 = 18951416487895345297165037282 := by decide +kernel
private theorem receipt_2_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1536 128 = 13399725206833295451359538048 := by decide +kernel
private theorem receipt_2_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1664 128 = 8087999841251833911400812036 := by decide +kernel
private theorem receipt_2_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1792 128 = 3010249136884480234686789238 := by decide +kernel
private theorem receipt_2_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1920 15 = 30968268480943903730479586 := by decide +kernel
private theorem receipt_2_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 0 256 = 186669392221755458102064546688 :=
  phaseBlock_append receipt_2_14_2359_1_part0 receipt_2_14_2359_1_part1 rfl rfl rfl
private theorem receipt_2_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 256 256 = 153480649598330935630691107712 :=
  phaseBlock_append receipt_2_14_2359_1_part2 receipt_2_14_2359_1_part3 rfl rfl rfl
private theorem receipt_2_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 0 512 = 340150041820086393732755654400 :=
  phaseBlock_append receipt_2_14_2359_1_join0 receipt_2_14_2359_1_join1 rfl rfl rfl
private theorem receipt_2_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 512 256 = 122693949691961675696752198528 :=
  phaseBlock_append receipt_2_14_2359_1_part4 receipt_2_14_2359_1_part5 rfl rfl rfl
private theorem receipt_2_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 768 256 = 94203606378106091104762332032 :=
  phaseBlock_append receipt_2_14_2359_1_part6 receipt_2_14_2359_1_part7 rfl rfl rfl
private theorem receipt_2_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 512 512 = 216897556070067766801514530560 :=
  phaseBlock_append receipt_2_14_2359_1_join3 receipt_2_14_2359_1_join4 rfl rfl rfl
private theorem receipt_2_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 0 1024 = 557047597890154160534270184960 :=
  phaseBlock_append receipt_2_14_2359_1_join2 receipt_2_14_2359_1_join5 rfl rfl rfl
private theorem receipt_2_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1024 256 = 67906194634318773150704829312 :=
  phaseBlock_append receipt_2_14_2359_1_part8 receipt_2_14_2359_1_part9 rfl rfl rfl
private theorem receipt_2_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1280 256 = 43700549978291644745990094951 :=
  phaseBlock_append receipt_2_14_2359_1_part10 receipt_2_14_2359_1_part11 rfl rfl rfl
private theorem receipt_2_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1024 512 = 111606744612610417896694924263 :=
  phaseBlock_append receipt_2_14_2359_1_join7 receipt_2_14_2359_1_join8 rfl rfl rfl
private theorem receipt_2_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1536 256 = 21487725048085129362760350084 :=
  phaseBlock_append receipt_2_14_2359_1_part12 receipt_2_14_2359_1_part13 rfl rfl rfl
private theorem receipt_2_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1792 143 = 3041217405365424138417268824 :=
  phaseBlock_append receipt_2_14_2359_1_part14 receipt_2_14_2359_1_part15 rfl rfl rfl
private theorem receipt_2_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1536 399 = 24528942453450553501177618908 :=
  phaseBlock_append receipt_2_14_2359_1_join10 receipt_2_14_2359_1_join11 rfl rfl rfl
private theorem receipt_2_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 1024 911 = 136135687066060971397872543171 :=
  phaseBlock_append receipt_2_14_2359_1_join9 receipt_2_14_2359_1_join12 rfl rfl rfl
private theorem receipt_2_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2379 73 1 0 7 1) 0 1935 = 693183284956215131932142728131 :=
  phaseBlock_append receipt_2_14_2359_1_join6 receipt_2_14_2359_1_join13 rfl rfl rfl

private theorem receipt_2_14_2359_1 : fastPhase (bank 2 14).shape 179808 2379 73 1 0 7 1 = 693183284956215131932142728131 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2359_1_join14

private theorem receipt_2_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 0 128 = 97706089545142960744083530400 := by decide +kernel
private theorem receipt_2_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 128 128 = 89097778237772994236709221024 := by decide +kernel
private theorem receipt_2_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 256 128 = 80799849690313714532144628384 := by decide +kernel
private theorem receipt_2_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 384 128 = 72805555364883638871525511840 := by decide +kernel
private theorem receipt_2_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 512 128 = 65108218158051649017733374624 := by decide +kernel
private theorem receipt_2_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 640 128 = 57701232092732678548841853600 := by decide +kernel
private theorem receipt_2_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 768 128 = 50578062010083400151563109024 := by decide +kernel
private theorem receipt_2_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 896 128 = 43732243261397912914694214304 := by decide +kernel
private theorem receipt_2_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1024 128 = 37157381400003429622563545760 := by decide +kernel
private theorem receipt_2_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1152 128 = 30847151873155964048477172384 := by decide +kernel
private theorem receipt_2_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1280 128 = 24795302375761727492359948523 := by decide +kernel
private theorem receipt_2_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1408 128 = 18995655461182384045003099416 := by decide +kernel
private theorem receipt_2_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1536 128 = 13442086312645676206991236732 := by decide +kernel
private theorem receipt_2_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1664 128 = 8128534399876705627489402950 := by decide +kernel
private theorem receipt_2_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1792 128 = 3049007749845719165562569469 := by decide +kernel
private theorem receipt_2_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1920 15 = 35396351603481161577316410 := by decide +kernel
private theorem receipt_2_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 0 256 = 186803867782915954980792751424 :=
  phaseBlock_append receipt_2_14_2360_0_part0 receipt_2_14_2360_0_part1 rfl rfl rfl
private theorem receipt_2_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 256 256 = 153605405055197353403670140224 :=
  phaseBlock_append receipt_2_14_2360_0_part2 receipt_2_14_2360_0_part3 rfl rfl rfl
private theorem receipt_2_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 0 512 = 340409272838113308384462891648 :=
  phaseBlock_append receipt_2_14_2360_0_join0 receipt_2_14_2360_0_join1 rfl rfl rfl
private theorem receipt_2_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 512 256 = 122809450250784327566575228224 :=
  phaseBlock_append receipt_2_14_2360_0_part4 receipt_2_14_2360_0_part5 rfl rfl rfl
private theorem receipt_2_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 768 256 = 94310305271481313066257323328 :=
  phaseBlock_append receipt_2_14_2360_0_part6 receipt_2_14_2360_0_part7 rfl rfl rfl
private theorem receipt_2_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 512 512 = 217119755522265640632832551552 :=
  phaseBlock_append receipt_2_14_2360_0_join3 receipt_2_14_2360_0_join4 rfl rfl rfl
private theorem receipt_2_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 0 1024 = 557529028360378949017295443200 :=
  phaseBlock_append receipt_2_14_2360_0_join2 receipt_2_14_2360_0_join5 rfl rfl rfl
private theorem receipt_2_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1024 256 = 68004533273159393671040718144 :=
  phaseBlock_append receipt_2_14_2360_0_part8 receipt_2_14_2360_0_part9 rfl rfl rfl
private theorem receipt_2_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1280 256 = 43790957836944111537363047939 :=
  phaseBlock_append receipt_2_14_2360_0_part10 receipt_2_14_2360_0_part11 rfl rfl rfl
private theorem receipt_2_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1024 512 = 111795491110103505208403766083 :=
  phaseBlock_append receipt_2_14_2360_0_join7 receipt_2_14_2360_0_join8 rfl rfl rfl
private theorem receipt_2_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1536 256 = 21570620712522381834480639682 :=
  phaseBlock_append receipt_2_14_2360_0_part12 receipt_2_14_2360_0_part13 rfl rfl rfl
private theorem receipt_2_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1792 143 = 3084404101449200327139885879 :=
  phaseBlock_append receipt_2_14_2360_0_part14 receipt_2_14_2360_0_part15 rfl rfl rfl
private theorem receipt_2_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1536 399 = 24655024813971582161620525561 :=
  phaseBlock_append receipt_2_14_2360_0_join10 receipt_2_14_2360_0_join11 rfl rfl rfl
private theorem receipt_2_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 1024 911 = 136450515924075087370024291644 :=
  phaseBlock_append receipt_2_14_2360_0_join9 receipt_2_14_2360_0_join12 rfl rfl rfl
private theorem receipt_2_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 0) 0 1935 = 693979544284454036387319734844 :=
  phaseBlock_append receipt_2_14_2360_0_join6 receipt_2_14_2360_0_join13 rfl rfl rfl

private theorem receipt_2_14_2360_0 : fastPhase (bank 2 14).shape 179808 2380 73 1 0 7 0 = 693979544284454036387319734844 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2360_0_join14

private theorem receipt_2_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 0 128 = 97638483617742651486733418784 := by decide +kernel
private theorem receipt_2_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 128 128 = 89032554561048152937227989280 := by decide +kernel
private theorem receipt_2_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 256 128 = 80736956733451220441739698464 := by decide +kernel
private theorem receipt_2_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 384 128 = 72744942143147086243699003680 := by decide +kernel
private theorem receipt_2_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 512 128 = 65049834230422366557523869984 := by decide +kernel
private theorem receipt_2_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 640 128 = 57645027559550748862066159904 := by decide +kernel
private theorem receipt_2_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 768 128 = 50523987510688679194058023200 := by decide +kernel
private theorem receipt_2_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 896 128 = 43680249971771049441558286624 := by decide +kernel
private theorem receipt_2_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1024 128 = 37107421030406884637398843680 := by decide +kernel
private theorem receipt_2_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1152 128 = 30799176665775030252631044384 := by decide +kernel
private theorem receipt_2_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1280 128 = 24749265097478929197829253279 := by decide +kernel
private theorem receipt_2_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1408 128 = 18951509384022008917895830534 := by decide +kernel
private theorem receipt_2_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1536 128 = 13399785228057332687680911618 := by decide +kernel
private theorem receipt_2_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1664 128 = 8088032622614552335255956288 := by decide +kernel
private theorem receipt_2_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1792 128 = 3010260115617967653053861570 := by decide +kernel
private theorem receipt_2_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1920 15 = 30968372003423537850312418 := by decide +kernel
private theorem receipt_2_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 0 256 = 186671038178790804423961408064 :=
  phaseBlock_append receipt_2_14_2360_1_part0 receipt_2_14_2360_1_part1 rfl rfl rfl
private theorem receipt_2_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 256 256 = 153481898876598306685438702144 :=
  phaseBlock_append receipt_2_14_2360_1_part2 receipt_2_14_2360_1_part3 rfl rfl rfl
private theorem receipt_2_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 0 512 = 340152937055389111109400110208 :=
  phaseBlock_append receipt_2_14_2360_1_join0 receipt_2_14_2360_1_join1 rfl rfl rfl
private theorem receipt_2_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 512 256 = 122694861789973115419590029888 :=
  phaseBlock_append receipt_2_14_2360_1_part4 receipt_2_14_2360_1_part5 rfl rfl rfl
private theorem receipt_2_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 768 256 = 94204237482459728635616309824 :=
  phaseBlock_append receipt_2_14_2360_1_part6 receipt_2_14_2360_1_part7 rfl rfl rfl
private theorem receipt_2_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 512 512 = 216899099272432844055206339712 :=
  phaseBlock_append receipt_2_14_2360_1_join3 receipt_2_14_2360_1_join4 rfl rfl rfl
private theorem receipt_2_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 0 1024 = 557052036327821955164606449920 :=
  phaseBlock_append receipt_2_14_2360_1_join2 receipt_2_14_2360_1_join5 rfl rfl rfl
private theorem receipt_2_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1024 256 = 67906597696181914890029888064 :=
  phaseBlock_append receipt_2_14_2360_1_part8 receipt_2_14_2360_1_part9 rfl rfl rfl
private theorem receipt_2_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1280 256 = 43700774481500938115725083813 :=
  phaseBlock_append receipt_2_14_2360_1_part10 receipt_2_14_2360_1_part11 rfl rfl rfl
private theorem receipt_2_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1024 512 = 111607372177682853005754971877 :=
  phaseBlock_append receipt_2_14_2360_1_join7 receipt_2_14_2360_1_join8 rfl rfl rfl
private theorem receipt_2_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1536 256 = 21487817850671885022936867906 :=
  phaseBlock_append receipt_2_14_2360_1_part12 receipt_2_14_2360_1_part13 rfl rfl rfl
private theorem receipt_2_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1792 143 = 3041228487621391190904173988 :=
  phaseBlock_append receipt_2_14_2360_1_part14 receipt_2_14_2360_1_part15 rfl rfl rfl
private theorem receipt_2_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1536 399 = 24529046338293276213841041894 :=
  phaseBlock_append receipt_2_14_2360_1_join10 receipt_2_14_2360_1_join11 rfl rfl rfl
private theorem receipt_2_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 1024 911 = 136136418515976129219596013771 :=
  phaseBlock_append receipt_2_14_2360_1_join9 receipt_2_14_2360_1_join12 rfl rfl rfl
private theorem receipt_2_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2380 73 1 0 7 1) 0 1935 = 693188454843798084384202463691 :=
  phaseBlock_append receipt_2_14_2360_1_join6 receipt_2_14_2360_1_join13 rfl rfl rfl

private theorem receipt_2_14_2360_1 : fastPhase (bank 2 14).shape 179808 2380 73 1 0 7 1 = 693188454843798084384202463691 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2360_1_join14

theorem receipt_2_14 : Checked (bank 2 14) 73 0 7 := by
  refine checked_from_values (bank 2 14) 73 0 7
    (P3_7_1.checked (bank 2 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_14_2359_0 receipt_2_14_2359_1 receipt_2_14_2360_0 receipt_2_14_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_14_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 0 128 = 21972618511633242164667452448 := by decide +kernel
private theorem receipt_3_14_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 128 128 = 20135393164881917141318392864 := by decide +kernel
private theorem receipt_3_14_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 256 128 = 18349039204216962681722580000 := by decide +kernel
private theorem receipt_3_14_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 384 128 = 16614536994572965535674924064 := by decide +kernel
private theorem receipt_3_14_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 512 128 = 14932861205670447506748918816 := by decide +kernel
private theorem receipt_3_14_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 640 128 = 13304980821452621909777161248 := by decide +kernel
private theorem receipt_3_14_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 768 128 = 11731859149522150028331871264 := by decide +kernel
private theorem receipt_3_14_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 896 128 = 10214453830577897572205411360 := by decide +kernel
private theorem receipt_3_14_2359_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1024 128 = 8753716847851691134890806304 := by decide +kernel
private theorem receipt_3_14_2359_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1152 128 = 7350594536545074651062262816 := by decide +kernel
private theorem receipt_3_14_2359_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1280 128 = 6006027593266065854055689248 := by decide +kernel
private theorem receipt_3_14_2359_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1408 128 = 4720951085465912733349215264 := by decide +kernel
private theorem receipt_3_14_2359_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1536 128 = 3496294460875849992043711520 := by decide +kernel
private theorem receipt_3_14_2359_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1664 128 = 2332981556943855504343309344 := by decide +kernel
private theorem receipt_3_14_2359_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1792 128 = 1231930610271406773035920416 := by decide +kernel
private theorem receipt_3_14_2359_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1920 88 = 241048733508533141530301886 := by decide +kernel
private theorem receipt_3_14_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 0 256 = 42108011676515159305985845312 :=
  phaseBlock_append receipt_3_14_2359_0_part0 receipt_3_14_2359_0_part1 rfl rfl rfl
private theorem receipt_3_14_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 256 256 = 34963576198789928217397504064 :=
  phaseBlock_append receipt_3_14_2359_0_part2 receipt_3_14_2359_0_part3 rfl rfl rfl
private theorem receipt_3_14_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 0 512 = 77071587875305087523383349376 :=
  phaseBlock_append receipt_3_14_2359_0_join0 receipt_3_14_2359_0_join1 rfl rfl rfl
private theorem receipt_3_14_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 512 256 = 28237842027123069416526080064 :=
  phaseBlock_append receipt_3_14_2359_0_part4 receipt_3_14_2359_0_part5 rfl rfl rfl
private theorem receipt_3_14_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 768 256 = 21946312980100047600537282624 :=
  phaseBlock_append receipt_3_14_2359_0_part6 receipt_3_14_2359_0_part7 rfl rfl rfl
private theorem receipt_3_14_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 512 512 = 50184155007223117017063362688 :=
  phaseBlock_append receipt_3_14_2359_0_join3 receipt_3_14_2359_0_join4 rfl rfl rfl
private theorem receipt_3_14_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 0 1024 = 127255742882528204540446712064 :=
  phaseBlock_append receipt_3_14_2359_0_join2 receipt_3_14_2359_0_join5 rfl rfl rfl
private theorem receipt_3_14_2359_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1024 256 = 16104311384396765785953069120 :=
  phaseBlock_append receipt_3_14_2359_0_part8 receipt_3_14_2359_0_part9 rfl rfl rfl
private theorem receipt_3_14_2359_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1280 256 = 10726978678731978587404904512 :=
  phaseBlock_append receipt_3_14_2359_0_part10 receipt_3_14_2359_0_part11 rfl rfl rfl
private theorem receipt_3_14_2359_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1024 512 = 26831290063128744373357973632 :=
  phaseBlock_append receipt_3_14_2359_0_join7 receipt_3_14_2359_0_join8 rfl rfl rfl
private theorem receipt_3_14_2359_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1536 256 = 5829276017819705496387020864 :=
  phaseBlock_append receipt_3_14_2359_0_part12 receipt_3_14_2359_0_part13 rfl rfl rfl
private theorem receipt_3_14_2359_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1792 216 = 1472979343779939914566222302 :=
  phaseBlock_append receipt_3_14_2359_0_part14 receipt_3_14_2359_0_part15 rfl rfl rfl
private theorem receipt_3_14_2359_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1536 472 = 7302255361599645410953243166 :=
  phaseBlock_append receipt_3_14_2359_0_join10 receipt_3_14_2359_0_join11 rfl rfl rfl
private theorem receipt_3_14_2359_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 1024 984 = 34133545424728389784311216798 :=
  phaseBlock_append receipt_3_14_2359_0_join9 receipt_3_14_2359_0_join12 rfl rfl rfl
private theorem receipt_3_14_2359_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 0) 0 2008 = 161389288307256594324757928862 :=
  phaseBlock_append receipt_3_14_2359_0_join6 receipt_3_14_2359_0_join13 rfl rfl rfl

private theorem receipt_3_14_2359_0 : fastPhase (bank 3 14).shape 179808 2379 73 1 1 1 0 = 161389288307256594324757928862 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2359_0_join14

private theorem receipt_3_14_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 0 128 = 21958264746625658929258236960 := by decide +kernel
private theorem receipt_3_14_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 128 128 = 20121415708193603673830521888 := by decide +kernel
private theorem receipt_3_14_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 256 128 = 18335446385038850526372228128 := by decide +kernel
private theorem receipt_3_14_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 384 128 = 16601337095214882127796558880 := by decide +kernel
private theorem receipt_3_14_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 512 128 = 14920062461637783538052156448 := by decide +kernel
private theorem receipt_3_14_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 640 128 = 13292591421522998693603621920 := by decide +kernel
private theorem receipt_3_14_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 768 128 = 11719887235822086864912034848 := by decide +kernel
private theorem receipt_3_14_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 896 128 = 10202907498659479113915472928 := by decide +kernel
private theorem receipt_3_14_2359_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1024 128 = 8742604146769234751509531680 := by decide +kernel
private theorem receipt_3_14_2359_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1152 128 = 7339923468931797795027844128 := by decide +kernel
private theorem receipt_3_14_2359_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1280 128 = 5995806115410753425722600480 := by decide +kernel
private theorem receipt_3_14_2359_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1408 128 = 4711187107389584446245067808 := by decide +kernel
private theorem receipt_3_14_2359_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1536 128 = 3486995846408427738126109728 := by decide +kernel
private theorem receipt_3_14_2359_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1664 128 = 2324156123800830719256706080 := by decide +kernel
private theorem receipt_3_14_2359_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1792 128 = 1223586130130507801368472608 := by decide +kernel
private theorem receipt_3_14_2359_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1920 88 = 235594910285280487931691086 := by decide +kernel
private theorem receipt_3_14_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 0 256 = 42079680454819262603088758848 :=
  phaseBlock_append receipt_3_14_2359_1_part0 receipt_3_14_2359_1_part1 rfl rfl rfl
private theorem receipt_3_14_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 256 256 = 34936783480253732654168787008 :=
  phaseBlock_append receipt_3_14_2359_1_part2 receipt_3_14_2359_1_part3 rfl rfl rfl
private theorem receipt_3_14_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 0 512 = 77016463935072995257257545856 :=
  phaseBlock_append receipt_3_14_2359_1_join0 receipt_3_14_2359_1_join1 rfl rfl rfl
private theorem receipt_3_14_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 512 256 = 28212653883160782231655778368 :=
  phaseBlock_append receipt_3_14_2359_1_part4 receipt_3_14_2359_1_part5 rfl rfl rfl
private theorem receipt_3_14_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 768 256 = 21922794734481565978827507776 :=
  phaseBlock_append receipt_3_14_2359_1_part6 receipt_3_14_2359_1_part7 rfl rfl rfl
private theorem receipt_3_14_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 512 512 = 50135448617642348210483286144 :=
  phaseBlock_append receipt_3_14_2359_1_join3 receipt_3_14_2359_1_join4 rfl rfl rfl
private theorem receipt_3_14_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 0 1024 = 127151912552715343467740832000 :=
  phaseBlock_append receipt_3_14_2359_1_join2 receipt_3_14_2359_1_join5 rfl rfl rfl
private theorem receipt_3_14_2359_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1024 256 = 16082527615701032546537375808 :=
  phaseBlock_append receipt_3_14_2359_1_part8 receipt_3_14_2359_1_part9 rfl rfl rfl
private theorem receipt_3_14_2359_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1280 256 = 10706993222800337871967668288 :=
  phaseBlock_append receipt_3_14_2359_1_part10 receipt_3_14_2359_1_part11 rfl rfl rfl
private theorem receipt_3_14_2359_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1024 512 = 26789520838501370418505044096 :=
  phaseBlock_append receipt_3_14_2359_1_join7 receipt_3_14_2359_1_join8 rfl rfl rfl
private theorem receipt_3_14_2359_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1536 256 = 5811151970209258457382815808 :=
  phaseBlock_append receipt_3_14_2359_1_part12 receipt_3_14_2359_1_part13 rfl rfl rfl
private theorem receipt_3_14_2359_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1792 216 = 1459181040415788289300163694 :=
  phaseBlock_append receipt_3_14_2359_1_part14 receipt_3_14_2359_1_part15 rfl rfl rfl
private theorem receipt_3_14_2359_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1536 472 = 7270333010625046746682979502 :=
  phaseBlock_append receipt_3_14_2359_1_join10 receipt_3_14_2359_1_join11 rfl rfl rfl
private theorem receipt_3_14_2359_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 1024 984 = 34059853849126417165188023598 :=
  phaseBlock_append receipt_3_14_2359_1_join9 receipt_3_14_2359_1_join12 rfl rfl rfl
private theorem receipt_3_14_2359_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2379 73 1 1 1 1) 0 2008 = 161211766401841760632928855598 :=
  phaseBlock_append receipt_3_14_2359_1_join6 receipt_3_14_2359_1_join13 rfl rfl rfl

private theorem receipt_3_14_2359_1 : fastPhase (bank 3 14).shape 179808 2379 73 1 1 1 1 = 161211766401841760632928855598 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2359_1_join14

private theorem receipt_3_14_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 0 128 = 21972814433953961010837061056 := by decide +kernel
private theorem receipt_3_14_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 128 128 = 20135560996790067405046685120 := by decide +kernel
private theorem receipt_3_14_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 256 128 = 18349181599521702001927273920 := by decide +kernel
private theorem receipt_3_14_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 384 128 = 16614656488887256328368315840 := by decide +kernel
private theorem receipt_3_14_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 512 128 = 14932960216975476690627624384 := by decide +kernel
private theorem receipt_3_14_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 640 128 = 13305061650661341022509637056 := by decide +kernel
private theorem receipt_3_14_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 768 128 = 11731923981041935733543714240 := by decide +kernel
private theorem receipt_3_14_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 896 128 = 10214504732872332557162438080 := by decide +kernel
private theorem receipt_3_14_2360_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1024 128 = 8753755774001465398879911360 := by decide +kernel
private theorem receipt_3_14_2360_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1152 128 = 7350623324808007184470056384 := by decide +kernel
private theorem receipt_3_14_2360_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1280 128 = 6006047967636246708144913856 := by decide +kernel
private theorem receipt_3_14_2360_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1408 128 = 4720964656231965480732941760 := by decide +kernel
private theorem receipt_3_14_2360_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1536 128 = 3496302725178314577857314240 := by decide +kernel
private theorem receipt_3_14_2360_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1664 128 = 2332985899331691488114220480 := by decide +kernel
private theorem receipt_3_14_2360_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1792 128 = 1231932303257616961251163584 := by decide +kernel
private theorem receipt_3_14_2360_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1920 88 = 241048968419965760230951236 := by decide +kernel
private theorem receipt_3_14_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 0 256 = 42108375430744028415883746176 :=
  phaseBlock_append receipt_3_14_2360_0_part0 receipt_3_14_2360_0_part1 rfl rfl rfl
private theorem receipt_3_14_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 256 256 = 34963838088408958330295589760 :=
  phaseBlock_append receipt_3_14_2360_0_part2 receipt_3_14_2360_0_part3 rfl rfl rfl
private theorem receipt_3_14_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 0 512 = 77072213519152986746179335936 :=
  phaseBlock_append receipt_3_14_2360_0_join0 receipt_3_14_2360_0_join1 rfl rfl rfl
private theorem receipt_3_14_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 512 256 = 28238021867636817713137261440 :=
  phaseBlock_append receipt_3_14_2360_0_part4 receipt_3_14_2360_0_part5 rfl rfl rfl
private theorem receipt_3_14_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 768 256 = 21946428713914268290706152320 :=
  phaseBlock_append receipt_3_14_2360_0_part6 receipt_3_14_2360_0_part7 rfl rfl rfl
private theorem receipt_3_14_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 512 512 = 50184450581551086003843413760 :=
  phaseBlock_append receipt_3_14_2360_0_join3 receipt_3_14_2360_0_join4 rfl rfl rfl
private theorem receipt_3_14_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 0 1024 = 127256664100704072750022749696 :=
  phaseBlock_append receipt_3_14_2360_0_join2 receipt_3_14_2360_0_join5 rfl rfl rfl
private theorem receipt_3_14_2360_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1024 256 = 16104379098809472583349967744 :=
  phaseBlock_append receipt_3_14_2360_0_part8 receipt_3_14_2360_0_part9 rfl rfl rfl
private theorem receipt_3_14_2360_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1280 256 = 10727012623868212188877855616 :=
  phaseBlock_append receipt_3_14_2360_0_part10 receipt_3_14_2360_0_part11 rfl rfl rfl
private theorem receipt_3_14_2360_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1024 512 = 26831391722677684772227823360 :=
  phaseBlock_append receipt_3_14_2360_0_join7 receipt_3_14_2360_0_join8 rfl rfl rfl
private theorem receipt_3_14_2360_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1536 256 = 5829288624510006065971534720 :=
  phaseBlock_append receipt_3_14_2360_0_part12 receipt_3_14_2360_0_part13 rfl rfl rfl
private theorem receipt_3_14_2360_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1792 216 = 1472981271677582721482114820 :=
  phaseBlock_append receipt_3_14_2360_0_part14 receipt_3_14_2360_0_part15 rfl rfl rfl
private theorem receipt_3_14_2360_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1536 472 = 7302269896187588787453649540 :=
  phaseBlock_append receipt_3_14_2360_0_join10 receipt_3_14_2360_0_join11 rfl rfl rfl
private theorem receipt_3_14_2360_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 1024 984 = 34133661618865273559681472900 :=
  phaseBlock_append receipt_3_14_2360_0_join9 receipt_3_14_2360_0_join12 rfl rfl rfl
private theorem receipt_3_14_2360_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 0) 0 2008 = 161390325719569346309704222596 :=
  phaseBlock_append receipt_3_14_2360_0_join6 receipt_3_14_2360_0_join13 rfl rfl rfl

private theorem receipt_3_14_2360_0 : fastPhase (bank 3 14).shape 179808 2380 73 1 1 1 0 = 161390325719569346309704222596 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2360_0_join14

private theorem receipt_3_14_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 0 128 = 21958460520525058725669796800 := by decide +kernel
private theorem receipt_3_14_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 128 128 = 20121583405596671600666655680 := by decide +kernel
private theorem receipt_3_14_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 256 128 = 18335588659101526831406578624 := by decide +kernel
private theorem receipt_3_14_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 384 128 = 16601456480900336682547624896 := by decide +kernel
private theorem receipt_3_14_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 512 128 = 14920161376280829928375942080 := by decide +kernel
private theorem receipt_3_14_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 640 128 = 13292672165393628700984064960 := by decide +kernel
private theorem receipt_3_14_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 768 128 = 11719951992688125338449214400 := by decide +kernel
private theorem receipt_3_14_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 896 128 = 10202958336348359233011596224 := by decide +kernel
private theorem receipt_3_14_2360_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1024 128 = 8742643017728893679252700096 := by decide +kernel
private theorem receipt_3_14_2360_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1152 128 = 7339952210790692722273598400 := by decide +kernel
private theorem receipt_3_14_2360_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1280 128 = 5995826451536998005873245120 := by decide +kernel
private theorem receipt_3_14_2360_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1408 128 = 4711200647449205620726774720 := by decide +kernel
private theorem receipt_3_14_2360_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1536 128 = 3487004086922742952563801024 := by decide +kernel
private theorem receipt_3_14_2360_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1664 128 = 2324160448702945530346716096 := by decide +kernel
private theorem receipt_3_14_2360_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1792 128 = 1223587811320933874448989120 := by decide +kernel
private theorem receipt_3_14_2360_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1920 88 = 235595140071044958332081140 := by decide +kernel
private theorem receipt_3_14_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 0 256 = 42080043926121730326336452480 :=
  phaseBlock_append receipt_3_14_2360_1_part0 receipt_3_14_2360_1_part1 rfl rfl rfl
private theorem receipt_3_14_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 256 256 = 34937045140001863513954203520 :=
  phaseBlock_append receipt_3_14_2360_1_part2 receipt_3_14_2360_1_part3 rfl rfl rfl
private theorem receipt_3_14_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 0 512 = 77017089066123593840290656000 :=
  phaseBlock_append receipt_3_14_2360_1_join0 receipt_3_14_2360_1_join1 rfl rfl rfl
private theorem receipt_3_14_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 512 256 = 28212833541674458629360007040 :=
  phaseBlock_append receipt_3_14_2360_1_part4 receipt_3_14_2360_1_part5 rfl rfl rfl
private theorem receipt_3_14_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 768 256 = 21922910329036484571460810624 :=
  phaseBlock_append receipt_3_14_2360_1_part6 receipt_3_14_2360_1_part7 rfl rfl rfl
private theorem receipt_3_14_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 512 512 = 50135743870710943200820817664 :=
  phaseBlock_append receipt_3_14_2360_1_join3 receipt_3_14_2360_1_join4 rfl rfl rfl
private theorem receipt_3_14_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 0 1024 = 127152832936834537041111473664 :=
  phaseBlock_append receipt_3_14_2360_1_join2 receipt_3_14_2360_1_join5 rfl rfl rfl
private theorem receipt_3_14_2360_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1024 256 = 16082595228519586401526298496 :=
  phaseBlock_append receipt_3_14_2360_1_part8 receipt_3_14_2360_1_part9 rfl rfl rfl
private theorem receipt_3_14_2360_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1280 256 = 10707027098986203626600019840 :=
  phaseBlock_append receipt_3_14_2360_1_part10 receipt_3_14_2360_1_part11 rfl rfl rfl
private theorem receipt_3_14_2360_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1024 512 = 26789622327505790028126318336 :=
  phaseBlock_append receipt_3_14_2360_1_join7 receipt_3_14_2360_1_join8 rfl rfl rfl
private theorem receipt_3_14_2360_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1536 256 = 5811164535625688482910517120 :=
  phaseBlock_append receipt_3_14_2360_1_part12 receipt_3_14_2360_1_part13 rfl rfl rfl
private theorem receipt_3_14_2360_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1792 216 = 1459182951391978832781070260 :=
  phaseBlock_append receipt_3_14_2360_1_part14 receipt_3_14_2360_1_part15 rfl rfl rfl
private theorem receipt_3_14_2360_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1536 472 = 7270347487017667315691587380 :=
  phaseBlock_append receipt_3_14_2360_1_join10 receipt_3_14_2360_1_join11 rfl rfl rfl
private theorem receipt_3_14_2360_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 1024 984 = 34059969814523457343817905716 :=
  phaseBlock_append receipt_3_14_2360_1_join9 receipt_3_14_2360_1_join12 rfl rfl rfl
private theorem receipt_3_14_2360_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2380 73 1 1 1 1) 0 2008 = 161212802751357994384929379380 :=
  phaseBlock_append receipt_3_14_2360_1_join6 receipt_3_14_2360_1_join13 rfl rfl rfl

private theorem receipt_3_14_2360_1 : fastPhase (bank 3 14).shape 179808 2380 73 1 1 1 1 = 161212802751357994384929379380 :=
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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group5_stage i)).shape
      (cutoff h rect (group5_stage i)), ¬ G∣Q :=
  (group5_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group5_avoids

end Lower6960.RescueSource
