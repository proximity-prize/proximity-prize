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

private theorem receipt_0_13_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 0 128 = 21494910133098420821614715040 := by decide +kernel
private theorem receipt_0_13_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 128 128 = 18660189179415677956012814496 := by decide +kernel
private theorem receipt_0_13_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 256 128 = 15958463752199526941292789920 := by decide +kernel
private theorem receipt_0_13_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 384 128 = 13386519135959200816369914016 := by decide +kernel
private theorem receipt_0_13_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 512 128 = 10941148496705568186769350816 := by decide +kernel
private theorem receipt_0_13_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 640 128 = 8619152875662630401189212320 := by decide +kernel
private theorem receipt_0_13_2383_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 768 128 = 6417341499212721946358643107 := by decide +kernel
private theorem receipt_0_13_2383_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 896 128 = 4332534949476057327147886446 := by decide +kernel
private theorem receipt_0_13_2383_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 1024 128 = 2361554054328282819086006683 := by decide +kernel
private theorem receipt_0_13_2383_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 1152 99 = 545040764022170819062317171 := by decide +kernel
private theorem receipt_0_13_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 0 256 = 40155099312514098777627529536 :=
  phaseBlock_append receipt_0_13_2383_0_part0 receipt_0_13_2383_0_part1 rfl rfl rfl
private theorem receipt_0_13_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 384 256 = 24327667632664769003139264832 :=
  phaseBlock_append receipt_0_13_2383_0_part3 receipt_0_13_2383_0_part4 rfl rfl rfl
private theorem receipt_0_13_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 256 384 = 40286131384864295944432054752 :=
  phaseBlock_append receipt_0_13_2383_0_part2 receipt_0_13_2383_0_join1 rfl rfl rfl
private theorem receipt_0_13_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 0 640 = 80441230697378394722059584288 :=
  phaseBlock_append receipt_0_13_2383_0_join0 receipt_0_13_2383_0_join2 rfl rfl rfl
private theorem receipt_0_13_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 640 256 = 15036494374875352347547855427 :=
  phaseBlock_append receipt_0_13_2383_0_part5 receipt_0_13_2383_0_part6 rfl rfl rfl
private theorem receipt_0_13_2383_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 1024 227 = 2906594818350453638148323854 :=
  phaseBlock_append receipt_0_13_2383_0_part8 receipt_0_13_2383_0_part9 rfl rfl rfl
private theorem receipt_0_13_2383_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 896 355 = 7239129767826510965296210300 :=
  phaseBlock_append receipt_0_13_2383_0_part7 receipt_0_13_2383_0_join5 rfl rfl rfl
private theorem receipt_0_13_2383_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 640 611 = 22275624142701863312844065727 :=
  phaseBlock_append receipt_0_13_2383_0_join4 receipt_0_13_2383_0_join6 rfl rfl rfl
private theorem receipt_0_13_2383_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 0) 0 1251 = 102716854840080258034903650015 :=
  phaseBlock_append receipt_0_13_2383_0_join3 receipt_0_13_2383_0_join7 rfl rfl rfl

private theorem receipt_0_13_2383_0 : fastPhase (bank 0 13).shape 179808 2383 44 1 0 1 0 = 102716854840080258034903650015 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2383_0_join8

private theorem receipt_0_13_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 0 128 = 21472536204661461523102219168 := by decide +kernel
private theorem receipt_0_13_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 128 128 = 18638831457960699454543580064 := by decide +kernel
private theorem receipt_0_13_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 256 128 = 15938097909346669146148297632 := by decide +kernel
private theorem receipt_0_13_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 384 128 = 13367120903397233680613927840 := by decide +kernel
private theorem receipt_0_13_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 512 128 = 10922693666143745330018188192 := by decide +kernel
private theorem receipt_0_13_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 640 128 = 8601617298782542732382014368 := by decide +kernel
private theorem receipt_0_13_2383_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 768 128 = 6400701086769679563937611849 := by decide +kernel
private theorem receipt_0_13_2383_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 896 128 = 4316765657185029466555253738 := by decide +kernel
private theorem receipt_0_13_2383_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 1024 128 = 2346631885435935810563608158 := by decide +kernel
private theorem receipt_0_13_2383_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 1152 99 = 534065195476485200511474144 := by decide +kernel
private theorem receipt_0_13_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 0 256 = 40111367662622160977645799232 :=
  phaseBlock_append receipt_0_13_2383_1_part0 receipt_0_13_2383_1_part1 rfl rfl rfl
private theorem receipt_0_13_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 384 256 = 24289814569540979010632116032 :=
  phaseBlock_append receipt_0_13_2383_1_part3 receipt_0_13_2383_1_part4 rfl rfl rfl
private theorem receipt_0_13_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 256 384 = 40227912478887648156780413664 :=
  phaseBlock_append receipt_0_13_2383_1_part2 receipt_0_13_2383_1_join1 rfl rfl rfl
private theorem receipt_0_13_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 0 640 = 80339280141509809134426212896 :=
  phaseBlock_append receipt_0_13_2383_1_join0 receipt_0_13_2383_1_join2 rfl rfl rfl
private theorem receipt_0_13_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 640 256 = 15002318385552222296319626217 :=
  phaseBlock_append receipt_0_13_2383_1_part5 receipt_0_13_2383_1_part6 rfl rfl rfl
private theorem receipt_0_13_2383_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 1024 227 = 2880697080912421011075082302 :=
  phaseBlock_append receipt_0_13_2383_1_part8 receipt_0_13_2383_1_part9 rfl rfl rfl
private theorem receipt_0_13_2383_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 896 355 = 7197462738097450477630336040 :=
  phaseBlock_append receipt_0_13_2383_1_part7 receipt_0_13_2383_1_join5 rfl rfl rfl
private theorem receipt_0_13_2383_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 640 611 = 22199781123649672773949962257 :=
  phaseBlock_append receipt_0_13_2383_1_join4 receipt_0_13_2383_1_join6 rfl rfl rfl
private theorem receipt_0_13_2383_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2383 44 1 0 1 1) 0 1251 = 102539061265159481908376175153 :=
  phaseBlock_append receipt_0_13_2383_1_join3 receipt_0_13_2383_1_join7 rfl rfl rfl

private theorem receipt_0_13_2383_1 : fastPhase (bank 0 13).shape 179808 2383 44 1 0 1 1 = 102539061265159481908376175153 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2383_1_join8

private theorem receipt_0_13_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 0 128 = 21495101586311602375182247680 := by decide +kernel
private theorem receipt_0_13_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 128 128 = 18660345685870713703637124864 := by decide +kernel
private theorem receipt_0_13_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 256 128 = 15958589040188838495271659264 := by decide +kernel
private theorem receipt_0_13_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 384 128 = 13386616823040795143699777280 := by decide +kernel
private theorem receipt_0_13_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 512 128 = 10941222089977576488550819584 := by decide +kernel
private theorem receipt_0_13_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 640 128 = 8619205772037627089707042560 := by decide +kernel
private theorem receipt_0_13_2384_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 768 128 = 6417376974157183489342823394 := by decide +kernel
private theorem receipt_0_13_2384_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 896 128 = 4332556148433153670280743839 := by decide +kernel
private theorem receipt_0_13_2384_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 1024 128 = 2361564087340163547014705433 := by decide +kernel
private theorem receipt_0_13_2384_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 1152 99 = 545042772898577421138157554 := by decide +kernel
private theorem receipt_0_13_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 0 256 = 40155447272182316078819372544 :=
  phaseBlock_append receipt_0_13_2384_0_part0 receipt_0_13_2384_0_part1 rfl rfl rfl
private theorem receipt_0_13_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 384 256 = 24327838913018371632250596864 :=
  phaseBlock_append receipt_0_13_2384_0_part3 receipt_0_13_2384_0_part4 rfl rfl rfl
private theorem receipt_0_13_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 256 384 = 40286427953207210127522256128 :=
  phaseBlock_append receipt_0_13_2384_0_part2 receipt_0_13_2384_0_join1 rfl rfl rfl
private theorem receipt_0_13_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 0 640 = 80441875225389526206341628672 :=
  phaseBlock_append receipt_0_13_2384_0_join0 receipt_0_13_2384_0_join2 rfl rfl rfl
private theorem receipt_0_13_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 640 256 = 15036582746194810579049865954 :=
  phaseBlock_append receipt_0_13_2384_0_part5 receipt_0_13_2384_0_part6 rfl rfl rfl
private theorem receipt_0_13_2384_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 1024 227 = 2906606860238740968152862987 :=
  phaseBlock_append receipt_0_13_2384_0_part8 receipt_0_13_2384_0_part9 rfl rfl rfl
private theorem receipt_0_13_2384_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 896 355 = 7239163008671894638433606826 :=
  phaseBlock_append receipt_0_13_2384_0_part7 receipt_0_13_2384_0_join5 rfl rfl rfl
private theorem receipt_0_13_2384_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 640 611 = 22275745754866705217483472780 :=
  phaseBlock_append receipt_0_13_2384_0_join4 receipt_0_13_2384_0_join6 rfl rfl rfl
private theorem receipt_0_13_2384_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 0) 0 1251 = 102717620980256231423825101452 :=
  phaseBlock_append receipt_0_13_2384_0_join3 receipt_0_13_2384_0_join7 rfl rfl rfl

private theorem receipt_0_13_2384_0 : fastPhase (bank 0 13).shape 179808 2384 44 1 0 1 0 = 102717620980256231423825101452 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2384_0_join8

private theorem receipt_0_13_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 0 128 = 21472727494361544377353525568 := by decide +kernel
private theorem receipt_0_13_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 128 128 = 18638987815646442641566193984 := by decide +kernel
private theorem receipt_0_13_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 256 128 = 15938223062787224187383929152 := by decide +kernel
private theorem receipt_0_13_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 384 128 = 13367218469628841102536530240 := by decide +kernel
private theorem receipt_0_13_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 512 128 = 10922767151744272237869422912 := by decide +kernel
private theorem receipt_0_13_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 640 128 = 8601670100145800481581160768 := by decide +kernel
private theorem receipt_0_13_2384_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 768 128 = 6400736478875371436291102831 := by decide +kernel
private theorem receipt_0_13_2384_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 896 128 = 4316786785094648925173768984 := by decide +kernel
private theorem receipt_0_13_2384_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 1024 128 = 2346641858672462502476441004 := by decide +kernel
private theorem receipt_0_13_2384_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 1152 99 = 534067165509251463716209521 := by decide +kernel
private theorem receipt_0_13_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 0 256 = 40111715310007987018919719552 :=
  phaseBlock_append receipt_0_13_2384_1_part0 receipt_0_13_2384_1_part1 rfl rfl rfl
private theorem receipt_0_13_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 384 256 = 24289985621373113340405953152 :=
  phaseBlock_append receipt_0_13_2384_1_part3 receipt_0_13_2384_1_part4 rfl rfl rfl
private theorem receipt_0_13_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 256 384 = 40228208684160337527789882304 :=
  phaseBlock_append receipt_0_13_2384_1_part2 receipt_0_13_2384_1_join1 rfl rfl rfl
private theorem receipt_0_13_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 0 640 = 80339923994168324546709601856 :=
  phaseBlock_append receipt_0_13_2384_1_join0 receipt_0_13_2384_1_join2 rfl rfl rfl
private theorem receipt_0_13_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 640 256 = 15002406579021171917872263599 :=
  phaseBlock_append receipt_0_13_2384_1_part5 receipt_0_13_2384_1_part6 rfl rfl rfl
private theorem receipt_0_13_2384_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 1024 227 = 2880709024181713966192650525 :=
  phaseBlock_append receipt_0_13_2384_1_part8 receipt_0_13_2384_1_part9 rfl rfl rfl
private theorem receipt_0_13_2384_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 896 355 = 7197495809276362891366419509 :=
  phaseBlock_append receipt_0_13_2384_1_part7 receipt_0_13_2384_1_join5 rfl rfl rfl
private theorem receipt_0_13_2384_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 640 611 = 22199902388297534809238683108 :=
  phaseBlock_append receipt_0_13_2384_1_join4 receipt_0_13_2384_1_join6 rfl rfl rfl
private theorem receipt_0_13_2384_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179808 2384 44 1 0 1 1) 0 1251 = 102539826382465859355948284964 :=
  phaseBlock_append receipt_0_13_2384_1_join3 receipt_0_13_2384_1_join7 rfl rfl rfl

private theorem receipt_0_13_2384_1 : fastPhase (bank 0 13).shape 179808 2384 44 1 0 1 1 = 102539826382465859355948284964 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2384_1_join8

theorem receipt_0_13 : Checked (bank 0 13) 44 0 1 := by
  refine checked_from_values (bank 0 13) 44 0 1
    (P3_7_1.checked (bank 0 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_13_2383_0 receipt_0_13_2383_1 receipt_0_13_2384_0 receipt_0_13_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_13_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 0 128 = 19348847379620310219563403168 := by decide +kernel
private theorem receipt_1_13_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 128 128 = 16785038739004977137612527520 := by decide +kernel
private theorem receipt_1_13_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 256 128 = 14344453404215655225631319968 := by decide +kernel
private theorem receipt_1_13_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 384 128 = 12023946191444807371683772320 := by decide +kernel
private theorem receipt_1_13_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 512 128 = 9820387200062025647790311328 := by decide +kernel
private theorem receipt_1_13_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 640 128 = 7730661787460020016180025248 := by decide +kernel
private theorem receipt_1_13_2383_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 768 128 = 5751670827251955021877670028 := by decide +kernel
private theorem receipt_1_13_2383_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 896 128 = 3880333528310395798658083654 := by decide +kernel
private theorem receipt_1_13_2383_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 1024 128 = 2113577461936674855031592883 := by decide +kernel
private theorem receipt_1_13_2383_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 1152 99 = 487515395023179774469066203 := by decide +kernel
private theorem receipt_1_13_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 0 256 = 36133886118625287357175930688 :=
  phaseBlock_append receipt_1_13_2383_0_part0 receipt_1_13_2383_0_part1 rfl rfl rfl
private theorem receipt_1_13_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 384 256 = 21844333391506833019474083648 :=
  phaseBlock_append receipt_1_13_2383_0_part3 receipt_1_13_2383_0_part4 rfl rfl rfl
private theorem receipt_1_13_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 256 384 = 36188786795722488245105403616 :=
  phaseBlock_append receipt_1_13_2383_0_part2 receipt_1_13_2383_0_join1 rfl rfl rfl
private theorem receipt_1_13_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 0 640 = 72322672914347775602281334304 :=
  phaseBlock_append receipt_1_13_2383_0_join0 receipt_1_13_2383_0_join2 rfl rfl rfl
private theorem receipt_1_13_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 640 256 = 13482332614711975038057695276 :=
  phaseBlock_append receipt_1_13_2383_0_part5 receipt_1_13_2383_0_part6 rfl rfl rfl
private theorem receipt_1_13_2383_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 1024 227 = 2601092856959854629500659086 :=
  phaseBlock_append receipt_1_13_2383_0_part8 receipt_1_13_2383_0_part9 rfl rfl rfl
private theorem receipt_1_13_2383_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 896 355 = 6481426385270250428158742740 :=
  phaseBlock_append receipt_1_13_2383_0_part7 receipt_1_13_2383_0_join5 rfl rfl rfl
private theorem receipt_1_13_2383_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 640 611 = 19963758999982225466216438016 :=
  phaseBlock_append receipt_1_13_2383_0_join4 receipt_1_13_2383_0_join6 rfl rfl rfl
private theorem receipt_1_13_2383_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 0) 0 1251 = 92286431914330001068497772320 :=
  phaseBlock_append receipt_1_13_2383_0_join3 receipt_1_13_2383_0_join7 rfl rfl rfl

private theorem receipt_1_13_2383_0 : fastPhase (bank 1 13).shape 179808 2383 44 1 0 2 0 = 92286431914330001068497772320 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2383_0_join8

private theorem receipt_1_13_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 0 128 = 19328598430998400252561652832 := by decide +kernel
private theorem receipt_1_13_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 128 128 = 16765732756887651111587933280 := by decide +kernel
private theorem receipt_1_13_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 256 128 = 14326066537865307744749935712 := by decide +kernel
private theorem receipt_1_13_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 384 128 = 12006454706673587296112462944 := by decide +kernel
private theorem receipt_1_13_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 512 128 = 9803767479039250584777833568 := by decide +kernel
private theorem receipt_1_13_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 640 128 = 7714890328519590811138108512 := by decide +kernel
private theorem receipt_1_13_2383_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 768 128 = 5736724243936130388304952522 := by decide +kernel
private theorem receipt_1_13_2383_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 896 128 = 3866188536565132329037548290 := by decide +kernel
private theorem receipt_1_13_2383_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 1024 128 = 2100210882339268692531698828 := by decide +kernel
private theorem receipt_1_13_2383_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 1152 99 = 477696405477905541941612010 := by decide +kernel
private theorem receipt_1_13_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 0 256 = 36094331187886051364149586112 :=
  phaseBlock_append receipt_1_13_2383_1_part0 receipt_1_13_2383_1_part1 rfl rfl rfl
private theorem receipt_1_13_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 384 256 = 21810222185712837880890296512 :=
  phaseBlock_append receipt_1_13_2383_1_part3 receipt_1_13_2383_1_part4 rfl rfl rfl
private theorem receipt_1_13_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 256 384 = 36136288723578145625640232224 :=
  phaseBlock_append receipt_1_13_2383_1_part2 receipt_1_13_2383_1_join1 rfl rfl rfl
private theorem receipt_1_13_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 0 640 = 72230619911464196989789818336 :=
  phaseBlock_append receipt_1_13_2383_1_join0 receipt_1_13_2383_1_join2 rfl rfl rfl
private theorem receipt_1_13_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 640 256 = 13451614572455721199443061034 :=
  phaseBlock_append receipt_1_13_2383_1_part5 receipt_1_13_2383_1_part6 rfl rfl rfl
private theorem receipt_1_13_2383_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 1024 227 = 2577907287817174234473310838 :=
  phaseBlock_append receipt_1_13_2383_1_part8 receipt_1_13_2383_1_part9 rfl rfl rfl
private theorem receipt_1_13_2383_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 896 355 = 6444095824382306563510859128 :=
  phaseBlock_append receipt_1_13_2383_1_part7 receipt_1_13_2383_1_join5 rfl rfl rfl
private theorem receipt_1_13_2383_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 640 611 = 19895710396838027762953920162 :=
  phaseBlock_append receipt_1_13_2383_1_join4 receipt_1_13_2383_1_join6 rfl rfl rfl
private theorem receipt_1_13_2383_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2383 44 1 0 2 1) 0 1251 = 92126330308302224752743738498 :=
  phaseBlock_append receipt_1_13_2383_1_join3 receipt_1_13_2383_1_join7 rfl rfl rfl

private theorem receipt_1_13_2383_1 : fastPhase (bank 1 13).shape 179808 2383 44 1 0 2 1 = 92126330308302224752743738498 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2383_1_join8

private theorem receipt_1_13_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 0 128 = 19349019718642477061659697856 := by decide +kernel
private theorem receipt_1_13_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 128 128 = 16785179518759957810426512064 := by decide +kernel
private theorem receipt_1_13_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 256 128 = 14344566021273571347705553600 := by decide +kernel
private theorem receipt_1_13_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 384 128 = 12024033935663969610577494720 := by decide +kernel
private theorem receipt_1_13_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 512 128 = 9820453255119094587493032640 := by decide +kernel
private theorem receipt_1_13_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 640 128 = 7730709231379287415222895296 := by decide +kernel
private theorem receipt_1_13_2384_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 768 128 = 5751702622598121067702454664 := by decide +kernel
private theorem receipt_1_13_2384_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 896 128 = 3880352514811104442615062137 := by decide +kernel
private theorem receipt_1_13_2384_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 1024 128 = 2113586441507073728434403559 := by decide +kernel
private theorem receipt_1_13_2384_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 1152 99 = 487517191884481680575848218 := by decide +kernel
private theorem receipt_1_13_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 0 256 = 36134199237402434872086209920 :=
  phaseBlock_append receipt_1_13_2384_0_part0 receipt_1_13_2384_0_part1 rfl rfl rfl
private theorem receipt_1_13_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 384 256 = 21844487190783064198070527360 :=
  phaseBlock_append receipt_1_13_2384_0_part3 receipt_1_13_2384_0_part4 rfl rfl rfl
private theorem receipt_1_13_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 256 384 = 36189053212056635545776080960 :=
  phaseBlock_append receipt_1_13_2384_0_part2 receipt_1_13_2384_0_join1 rfl rfl rfl
private theorem receipt_1_13_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 0 640 = 72323252449459070417862290880 :=
  phaseBlock_append receipt_1_13_2384_0_join0 receipt_1_13_2384_0_join2 rfl rfl rfl
private theorem receipt_1_13_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 640 256 = 13482411853977408482925349960 :=
  phaseBlock_append receipt_1_13_2384_0_part5 receipt_1_13_2384_0_part6 rfl rfl rfl
private theorem receipt_1_13_2384_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 1024 227 = 2601103633391555409010251777 :=
  phaseBlock_append receipt_1_13_2384_0_part8 receipt_1_13_2384_0_part9 rfl rfl rfl
private theorem receipt_1_13_2384_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 896 355 = 6481456148202659851625313914 :=
  phaseBlock_append receipt_1_13_2384_0_part7 receipt_1_13_2384_0_join5 rfl rfl rfl
private theorem receipt_1_13_2384_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 640 611 = 19963868002180068334550663874 :=
  phaseBlock_append receipt_1_13_2384_0_join4 receipt_1_13_2384_0_join6 rfl rfl rfl
private theorem receipt_1_13_2384_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 0) 0 1251 = 92287120451639138752412954754 :=
  phaseBlock_append receipt_1_13_2384_0_join3 receipt_1_13_2384_0_join7 rfl rfl rfl

private theorem receipt_1_13_2384_0 : fastPhase (bank 1 13).shape 179808 2384 44 1 0 2 0 = 92287120451639138752412954754 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2384_0_join8

private theorem receipt_1_13_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 0 128 = 19328770621862472639961257792 := by decide +kernel
private theorem receipt_1_13_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 128 128 = 16765873402029887167531087680 := by decide +kernel
private theorem receipt_1_13_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 256 128 = 14326179033347534270698788672 := by decide +kernel
private theorem receipt_1_13_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 384 128 = 12006542341848728523136874304 := by decide +kernel
private theorem receipt_1_13_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 512 128 = 9803833437081483818288731968 := by decide +kernel
private theorem receipt_1_13_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 640 128 = 7714937686953622466318628672 := by decide +kernel
private theorem receipt_1_13_2384_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 768 128 = 5736755964857347106099131755 := by decide +kernel
private theorem receipt_1_13_2384_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 896 128 = 3866207459327587991294043068 := by decide +kernel
private theorem receipt_1_13_2384_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 1024 128 = 2100219808362377041166382430 := by decide +kernel
private theorem receipt_1_13_2384_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 1152 99 = 477698167588217858096953845 := by decide +kernel
private theorem receipt_1_13_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 0 256 = 36094644023892359807492345472 :=
  phaseBlock_append receipt_1_13_2384_1_part0 receipt_1_13_2384_1_part1 rfl rfl rfl
private theorem receipt_1_13_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 384 256 = 21810375778930212341425606272 :=
  phaseBlock_append receipt_1_13_2384_1_part3 receipt_1_13_2384_1_part4 rfl rfl rfl
private theorem receipt_1_13_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 256 384 = 36136554812277746612124394944 :=
  phaseBlock_append receipt_1_13_2384_1_part2 receipt_1_13_2384_1_join1 rfl rfl rfl
private theorem receipt_1_13_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 0 640 = 72231198836170106419616740416 :=
  phaseBlock_append receipt_1_13_2384_1_join0 receipt_1_13_2384_1_join2 rfl rfl rfl
private theorem receipt_1_13_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 640 256 = 13451693651810969572417760427 :=
  phaseBlock_append receipt_1_13_2384_1_part5 receipt_1_13_2384_1_part6 rfl rfl rfl
private theorem receipt_1_13_2384_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 1024 227 = 2577917975950594899263336275 :=
  phaseBlock_append receipt_1_13_2384_1_part8 receipt_1_13_2384_1_part9 rfl rfl rfl
private theorem receipt_1_13_2384_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 896 355 = 6444125435278182890557379343 :=
  phaseBlock_append receipt_1_13_2384_1_part7 receipt_1_13_2384_1_join5 rfl rfl rfl
private theorem receipt_1_13_2384_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 640 611 = 19895819087089152462975139770 :=
  phaseBlock_append receipt_1_13_2384_1_join4 receipt_1_13_2384_1_join6 rfl rfl rfl
private theorem receipt_1_13_2384_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179808 2384 44 1 0 2 1) 0 1251 = 92127017923259258882591880186 :=
  phaseBlock_append receipt_1_13_2384_1_join3 receipt_1_13_2384_1_join7 rfl rfl rfl

private theorem receipt_1_13_2384_1 : fastPhase (bank 1 13).shape 179808 2384 44 1 0 2 1 = 92127017923259258882591880186 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2384_1_join8

theorem receipt_1_13 : Checked (bank 1 13) 44 0 2 := by
  refine checked_from_values (bank 1 13) 44 0 2
    (P3_7_1.checked (bank 1 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_13_2383_0 receipt_1_13_2383_1 receipt_1_13_2384_0 receipt_1_13_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_13_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 0 128 = 10371121096065822472467733920 := by decide +kernel
private theorem receipt_2_13_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 128 128 = 8950291022056706068784262560 := by decide +kernel
private theorem receipt_2_13_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 256 128 = 7609124847646695076961189280 := by decide +kernel
private theorem receipt_2_13_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 384 128 = 6344911842564710566287986080 := by decide +kernel
private theorem receipt_2_13_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 512 128 = 5154986479512892054575422880 := by decide +kernel
private theorem receipt_2_13_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 640 128 = 4036728126029959159745342880 := by decide +kernel
private theorem receipt_2_13_2383_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 768 128 = 2987560883232251314139049203 := by decide +kernel
private theorem receipt_2_13_2383_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 896 128 = 2004954743106455194426528150 := by decide +kernel
private theorem receipt_2_13_2383_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 1024 128 = 1086420129430783373246308545 := by decide +kernel
private theorem receipt_2_13_2383_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 1152 99 = 249484382488372698762216141 := by decide +kernel
private theorem receipt_2_13_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 0 256 = 19321412118122528541251996480 :=
  phaseBlock_append receipt_2_13_2383_0_part0 receipt_2_13_2383_0_part1 rfl rfl rfl
private theorem receipt_2_13_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 384 256 = 11499898322077602620863408960 :=
  phaseBlock_append receipt_2_13_2383_0_part3 receipt_2_13_2383_0_part4 rfl rfl rfl
private theorem receipt_2_13_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 256 384 = 19109023169724297697824598240 :=
  phaseBlock_append receipt_2_13_2383_0_part2 receipt_2_13_2383_0_join1 rfl rfl rfl
private theorem receipt_2_13_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 0 640 = 38430435287846826239076594720 :=
  phaseBlock_append receipt_2_13_2383_0_join0 receipt_2_13_2383_0_join2 rfl rfl rfl
private theorem receipt_2_13_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 640 256 = 7024289009262210473884392083 :=
  phaseBlock_append receipt_2_13_2383_0_part5 receipt_2_13_2383_0_part6 rfl rfl rfl
private theorem receipt_2_13_2383_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 1024 227 = 1335904511919156072008524686 :=
  phaseBlock_append receipt_2_13_2383_0_part8 receipt_2_13_2383_0_part9 rfl rfl rfl
private theorem receipt_2_13_2383_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 896 355 = 3340859255025611266435052836 :=
  phaseBlock_append receipt_2_13_2383_0_part7 receipt_2_13_2383_0_join5 rfl rfl rfl
private theorem receipt_2_13_2383_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 640 611 = 10365148264287821740319444919 :=
  phaseBlock_append receipt_2_13_2383_0_join4 receipt_2_13_2383_0_join6 rfl rfl rfl
private theorem receipt_2_13_2383_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 0) 0 1251 = 48795583552134647979396039639 :=
  phaseBlock_append receipt_2_13_2383_0_join3 receipt_2_13_2383_0_join7 rfl rfl rfl

private theorem receipt_2_13_2383_0 : fastPhase (bank 2 13).shape 179808 2383 44 1 0 7 0 = 48795583552134647979396039639 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2383_0_join8

private theorem receipt_2_13_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 0 128 = 10359847886233507395856314144 := by decide +kernel
private theorem receipt_2_13_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 128 128 = 8939633036208459746189492000 := by decide +kernel
private theorem receipt_2_13_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 256 128 = 7599061324390382094581649184 := by decide +kernel
private theorem receipt_2_13_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 384 128 = 6335422366479815836430556960 := by decide +kernel
private theorem receipt_2_13_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 512 128 = 5146050978791348331398524704 := by decide +kernel
private theorem receipt_2_13_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 640 128 = 4028326870116974555002175264 := by decide +kernel
private theorem receipt_2_13_2383_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 768 128 = 2979674480065212715775586129 := by decide +kernel
private theorem receipt_2_13_2383_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 896 128 = 1997564130185086324744228984 := by decide +kernel
private theorem receipt_2_13_2383_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 1024 128 = 1079506572987546018775774938 := by decide +kernel
private theorem receipt_2_13_2383_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 1152 99 = 244452675289856311652145432 := by decide +kernel
private theorem receipt_2_13_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 0 256 = 19299480922441967142045806144 :=
  phaseBlock_append receipt_2_13_2383_1_part0 receipt_2_13_2383_1_part1 rfl rfl rfl
private theorem receipt_2_13_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 384 256 = 11481473345271164167829081664 :=
  phaseBlock_append receipt_2_13_2383_1_part3 receipt_2_13_2383_1_part4 rfl rfl rfl
private theorem receipt_2_13_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 256 384 = 19080534669661546262410730848 :=
  phaseBlock_append receipt_2_13_2383_1_part2 receipt_2_13_2383_1_join1 rfl rfl rfl
private theorem receipt_2_13_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 0 640 = 38380015592103513404456536992 :=
  phaseBlock_append receipt_2_13_2383_1_join0 receipt_2_13_2383_1_join2 rfl rfl rfl
private theorem receipt_2_13_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 640 256 = 7008001350182187270777761393 :=
  phaseBlock_append receipt_2_13_2383_1_part5 receipt_2_13_2383_1_part6 rfl rfl rfl
private theorem receipt_2_13_2383_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 1024 227 = 1323959248277402330427920370 :=
  phaseBlock_append receipt_2_13_2383_1_part8 receipt_2_13_2383_1_part9 rfl rfl rfl
private theorem receipt_2_13_2383_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 896 355 = 3321523378462488655172149354 :=
  phaseBlock_append receipt_2_13_2383_1_part7 receipt_2_13_2383_1_join5 rfl rfl rfl
private theorem receipt_2_13_2383_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 640 611 = 10329524728644675925949910747 :=
  phaseBlock_append receipt_2_13_2383_1_join4 receipt_2_13_2383_1_join6 rfl rfl rfl
private theorem receipt_2_13_2383_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2383 44 1 0 7 1) 0 1251 = 48709540320748189330406447739 :=
  phaseBlock_append receipt_2_13_2383_1_join3 receipt_2_13_2383_1_join7 rfl rfl rfl

private theorem receipt_2_13_2383_1 : fastPhase (bank 2 13).shape 179808 2383 44 1 0 7 1 = 48709540320748189330406447739 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2383_1_join8

private theorem receipt_2_13_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 0 128 = 10371213473313163635473624640 := by decide +kernel
private theorem receipt_2_13_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 128 128 = 8950366092136925241413692992 := by decide +kernel
private theorem receipt_2_13_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 256 128 = 7609184588031643760070307392 := by decide +kernel
private theorem receipt_2_13_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 384 128 = 6344958145840968108771831360 := by decide +kernel
private theorem receipt_2_13_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 512 128 = 5155021154910088087286885952 := by decide +kernel
private theorem receipt_2_13_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 640 128 = 4036752900938320815461920320 := by decide +kernel
private theorem receipt_2_13_2384_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 768 128 = 2987577399350407553433024162 := by decide +kernel
private theorem receipt_2_13_2384_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 896 128 = 2004964553937575767897710999 := by decide +kernel
private theorem receipt_2_13_2384_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 1024 128 = 1086424745415046646320161081 := by decide +kernel
private theorem receipt_2_13_2384_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 1152 99 = 249485302057240299092541624 := by decide +kernel
private theorem receipt_2_13_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 0 256 = 19321579565450088876887317632 :=
  phaseBlock_append receipt_2_13_2384_0_part0 receipt_2_13_2384_0_part1 rfl rfl rfl
private theorem receipt_2_13_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 384 256 = 11499979300751056196058717312 :=
  phaseBlock_append receipt_2_13_2384_0_part3 receipt_2_13_2384_0_part4 rfl rfl rfl
private theorem receipt_2_13_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 256 384 = 19109163888782699956129024704 :=
  phaseBlock_append receipt_2_13_2384_0_part2 receipt_2_13_2384_0_join1 rfl rfl rfl
private theorem receipt_2_13_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 0 640 = 38430743454232788833016342336 :=
  phaseBlock_append receipt_2_13_2384_0_join0 receipt_2_13_2384_0_join2 rfl rfl rfl
private theorem receipt_2_13_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 640 256 = 7024330300288728368894944482 :=
  phaseBlock_append receipt_2_13_2384_0_part5 receipt_2_13_2384_0_part6 rfl rfl rfl
private theorem receipt_2_13_2384_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 1024 227 = 1335910047472286945412702705 :=
  phaseBlock_append receipt_2_13_2384_0_part8 receipt_2_13_2384_0_part9 rfl rfl rfl
private theorem receipt_2_13_2384_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 896 355 = 3340874601409862713310413704 :=
  phaseBlock_append receipt_2_13_2384_0_part7 receipt_2_13_2384_0_join5 rfl rfl rfl
private theorem receipt_2_13_2384_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 640 611 = 10365204901698591082205358186 :=
  phaseBlock_append receipt_2_13_2384_0_join4 receipt_2_13_2384_0_join6 rfl rfl rfl
private theorem receipt_2_13_2384_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 0) 0 1251 = 48795948355931379915221700522 :=
  phaseBlock_append receipt_2_13_2384_0_join3 receipt_2_13_2384_0_join7 rfl rfl rfl

private theorem receipt_2_13_2384_0 : fastPhase (bank 2 13).shape 179808 2384 44 1 0 7 0 = 48795948355931379915221700522 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2384_0_join8

private theorem receipt_2_13_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 0 128 = 10359940180326482891691961344 := by decide +kernel
private theorem receipt_2_13_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 128 128 = 8939708031457916425346534400 := by decide +kernel
private theorem receipt_2_13_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 256 128 = 7599120997847554292294544384 := by decide +kernel
private theorem receipt_2_13_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 384 128 = 6335468610319134775288335360 := by decide +kernel
private theorem receipt_2_13_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 512 128 = 5146085601838700577430907904 := by decide +kernel
private theorem receipt_2_13_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 640 128 = 4028351599367185259813489664 := by decide +kernel
private theorem receipt_2_13_2384_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 768 128 = 2979690956844203711732871237 := by decide +kernel
private theorem receipt_2_13_2384_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 896 128 = 1997573907679691793638515848 := by decide +kernel
private theorem receipt_2_13_2384_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 1024 128 = 1079511161263099331317577826 := by decide +kernel
private theorem receipt_2_13_2384_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 1152 99 = 244453577048437482013480893 := by decide +kernel
private theorem receipt_2_13_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 0 256 = 19299648211784399317038495744 :=
  phaseBlock_append receipt_2_13_2384_1_part0 receipt_2_13_2384_1_part1 rfl rfl rfl
private theorem receipt_2_13_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 384 256 = 11481554212157835352719243264 :=
  phaseBlock_append receipt_2_13_2384_1_part3 receipt_2_13_2384_1_part4 rfl rfl rfl
private theorem receipt_2_13_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 256 384 = 19080675210005389645013787648 :=
  phaseBlock_append receipt_2_13_2384_1_part2 receipt_2_13_2384_1_join1 rfl rfl rfl
private theorem receipt_2_13_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 0 640 = 38380323421789788962052283392 :=
  phaseBlock_append receipt_2_13_2384_1_join0 receipt_2_13_2384_1_join2 rfl rfl rfl
private theorem receipt_2_13_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 640 256 = 7008042556211388971546360901 :=
  phaseBlock_append receipt_2_13_2384_1_part5 receipt_2_13_2384_1_part6 rfl rfl rfl
private theorem receipt_2_13_2384_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 1024 227 = 1323964738311536813331058719 :=
  phaseBlock_append receipt_2_13_2384_1_part8 receipt_2_13_2384_1_part9 rfl rfl rfl
private theorem receipt_2_13_2384_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 896 355 = 3321538645991228606969574567 :=
  phaseBlock_append receipt_2_13_2384_1_part7 receipt_2_13_2384_1_join5 rfl rfl rfl
private theorem receipt_2_13_2384_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 640 611 = 10329581202202617578515935468 :=
  phaseBlock_append receipt_2_13_2384_1_join4 receipt_2_13_2384_1_join6 rfl rfl rfl
private theorem receipt_2_13_2384_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179808 2384 44 1 0 7 1) 0 1251 = 48709904623992406540568218860 :=
  phaseBlock_append receipt_2_13_2384_1_join3 receipt_2_13_2384_1_join7 rfl rfl rfl

private theorem receipt_2_13_2384_1 : fastPhase (bank 2 13).shape 179808 2384 44 1 0 7 1 = 48709904623992406540568218860 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2384_1_join8

theorem receipt_2_13 : Checked (bank 2 13) 44 0 7 := by
  refine checked_from_values (bank 2 13) 44 0 7
    (P3_7_1.checked (bank 2 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_13_2383_0 receipt_2_13_2383_1 receipt_2_13_2384_0 receipt_2_13_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_13_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 0 128 = 2388939427932615680662633568 := by decide +kernel
private theorem receipt_3_13_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 128 128 = 2077465302434944718177127520 := by decide +kernel
private theorem receipt_3_13_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 256 128 = 1779758302805723052484303968 := by decide +kernel
private theorem receipt_3_13_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 384 128 = 1496218875477333865379785824 := by decide +kernel
private theorem receipt_3_13_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 512 128 = 1227243822755701635298638944 := by decide +kernel
private theorem receipt_3_13_2383_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 640 128 = 973226312253530157587008608 := by decide +kernel
private theorem receipt_3_13_2383_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 768 128 = 734555886323540564773756000 := by decide +kernel
private theorem receipt_3_13_2383_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 896 128 = 511618471491709346842094688 := by decide +kernel
private theorem receipt_3_13_2383_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 1024 128 = 304796387890506371501227104 := by decide +kernel
private theorem receipt_3_13_2383_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 1152 128 = 114468358692132904457981024 := by decide +kernel
private theorem receipt_3_13_2383_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 1280 18 = 1793542628749878248810337 := by decide +kernel
private theorem receipt_3_13_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 0 256 = 4466404730367560398839761088 :=
  phaseBlock_append receipt_3_13_2383_0_part0 receipt_3_13_2383_0_part1 rfl rfl rfl
private theorem receipt_3_13_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 384 256 = 2723462698233035500678424768 :=
  phaseBlock_append receipt_3_13_2383_0_part3 receipt_3_13_2383_0_part4 rfl rfl rfl
private theorem receipt_3_13_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 256 384 = 4503221001038758553162728736 :=
  phaseBlock_append receipt_3_13_2383_0_part2 receipt_3_13_2383_0_join1 rfl rfl rfl
private theorem receipt_3_13_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 0 640 = 8969625731406318952002489824 :=
  phaseBlock_append receipt_3_13_2383_0_join0 receipt_3_13_2383_0_join2 rfl rfl rfl
private theorem receipt_3_13_2383_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 768 256 = 1246174357815249911615850688 :=
  phaseBlock_append receipt_3_13_2383_0_part6 receipt_3_13_2383_0_part7 rfl rfl rfl
private theorem receipt_3_13_2383_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 640 384 = 2219400670068780069202859296 :=
  phaseBlock_append receipt_3_13_2383_0_part5 receipt_3_13_2383_0_join4 rfl rfl rfl
private theorem receipt_3_13_2383_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 1152 146 = 116261901320882782706791361 :=
  phaseBlock_append receipt_3_13_2383_0_part9 receipt_3_13_2383_0_part10 rfl rfl rfl
private theorem receipt_3_13_2383_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 1024 274 = 421058289211389154208018465 :=
  phaseBlock_append receipt_3_13_2383_0_part8 receipt_3_13_2383_0_join6 rfl rfl rfl
private theorem receipt_3_13_2383_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 640 658 = 2640458959280169223410877761 :=
  phaseBlock_append receipt_3_13_2383_0_join5 receipt_3_13_2383_0_join7 rfl rfl rfl
private theorem receipt_3_13_2383_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 0) 0 1298 = 11610084690686488175413367585 :=
  phaseBlock_append receipt_3_13_2383_0_join3 receipt_3_13_2383_0_join8 rfl rfl rfl

private theorem receipt_3_13_2383_0 : fastPhase (bank 3 13).shape 179808 2383 44 1 1 1 0 = 11610084690686488175413367585 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2383_0_join9

private theorem receipt_3_13_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 0 128 = 2386486368152394448403391456 := by decide +kernel
private theorem receipt_3_13_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 128 128 = 2075113714742281043736237024 := by decide +kernel
private theorem receipt_3_13_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 256 128 = 1777511596493511676117894112 := by decide +kernel
private theorem receipt_3_13_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 384 128 = 1494080429822964729726890976 := by decide +kernel
private theorem receipt_3_13_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 512 128 = 1225216987097704710649684960 := by decide +kernel
private theorem receipt_3_13_2383_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 640 128 = 971314406068220267152298976 := by decide +kernel
private theorem receipt_3_13_2383_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 768 128 = 732762199301662209951957984 := by decide +kernel
private theorem receipt_3_13_2383_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 896 128 = 509946263615081532488725472 := by decide +kernel
private theorem receipt_3_13_2383_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 1024 128 = 303248889508667431197139936 := by decide +kernel
private theorem receipt_3_13_2383_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 1152 128 = 113048770598985325777851360 := by decide +kernel
private theorem receipt_3_13_2383_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 1280 18 = 1604353327370833126759644 := by decide +kernel
private theorem receipt_3_13_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 0 256 = 4461600082894675492139628480 :=
  phaseBlock_append receipt_3_13_2383_1_part0 receipt_3_13_2383_1_part1 rfl rfl rfl
private theorem receipt_3_13_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 384 256 = 2719297416920669440376575936 :=
  phaseBlock_append receipt_3_13_2383_1_part3 receipt_3_13_2383_1_part4 rfl rfl rfl
private theorem receipt_3_13_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 256 384 = 4496809013414181116494470048 :=
  phaseBlock_append receipt_3_13_2383_1_part2 receipt_3_13_2383_1_join1 rfl rfl rfl
private theorem receipt_3_13_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 0 640 = 8958409096308856608634098528 :=
  phaseBlock_append receipt_3_13_2383_1_join0 receipt_3_13_2383_1_join2 rfl rfl rfl
private theorem receipt_3_13_2383_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 768 256 = 1242708462916743742440683456 :=
  phaseBlock_append receipt_3_13_2383_1_part6 receipt_3_13_2383_1_part7 rfl rfl rfl
private theorem receipt_3_13_2383_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 640 384 = 2214022868984964009592982432 :=
  phaseBlock_append receipt_3_13_2383_1_part5 receipt_3_13_2383_1_join4 rfl rfl rfl
private theorem receipt_3_13_2383_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 1152 146 = 114653123926356158904611004 :=
  phaseBlock_append receipt_3_13_2383_1_part9 receipt_3_13_2383_1_part10 rfl rfl rfl
private theorem receipt_3_13_2383_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 1024 274 = 417902013435023590101750940 :=
  phaseBlock_append receipt_3_13_2383_1_part8 receipt_3_13_2383_1_join6 rfl rfl rfl
private theorem receipt_3_13_2383_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 640 658 = 2631924882419987599694733372 :=
  phaseBlock_append receipt_3_13_2383_1_join5 receipt_3_13_2383_1_join7 rfl rfl rfl
private theorem receipt_3_13_2383_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2383 44 1 1 1 1) 0 1298 = 11590333978728844208328831900 :=
  phaseBlock_append receipt_3_13_2383_1_join3 receipt_3_13_2383_1_join8 rfl rfl rfl

private theorem receipt_3_13_2383_1 : fastPhase (bank 3 13).shape 179808 2383 44 1 1 1 1 = 11590333978728844208328831900 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2383_1_join9

private theorem receipt_3_13_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 0 128 = 2388960408955372512340671904 := by decide +kernel
private theorem receipt_3_13_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 128 128 = 2077481691507398854935932320 := by decide +kernel
private theorem receipt_3_13_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 256 128 = 1779770781236349813355568544 := by decide +kernel
private theorem receipt_3_13_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 384 128 = 1496228076118655374947667360 := by decide +kernel
private theorem receipt_3_13_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 512 128 = 1227250330365793052772973984 := by decide +kernel
private theorem receipt_3_13_2384_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 640 128 = 973230663856646296574307744 := by decide +kernel
private theorem receipt_3_13_2384_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 768 128 = 734558571569862903745977760 := by decide +kernel
private theorem receipt_3_13_2384_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 896 128 = 511619933016213430303198624 := by decide +kernel
private theorem receipt_3_13_2384_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 1024 128 = 304797021670949601851506080 := by decide +kernel
private theorem receipt_3_13_2384_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 1152 128 = 114468514406162724556172704 := by decide +kernel
private theorem receipt_3_13_2384_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 1280 18 = 1793544128658408454105911 := by decide +kernel
private theorem receipt_3_13_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 0 256 = 4466442100462771367276604224 :=
  phaseBlock_append receipt_3_13_2384_0_part0 receipt_3_13_2384_0_part1 rfl rfl rfl
private theorem receipt_3_13_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 384 256 = 2723478406484448427720641344 :=
  phaseBlock_append receipt_3_13_2384_0_part3 receipt_3_13_2384_0_part4 rfl rfl rfl
private theorem receipt_3_13_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 256 384 = 4503249187720798241076209888 :=
  phaseBlock_append receipt_3_13_2384_0_part2 receipt_3_13_2384_0_join1 rfl rfl rfl
private theorem receipt_3_13_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 0 640 = 8969691288183569608352814112 :=
  phaseBlock_append receipt_3_13_2384_0_join0 receipt_3_13_2384_0_join2 rfl rfl rfl
private theorem receipt_3_13_2384_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 768 256 = 1246178504586076334049176384 :=
  phaseBlock_append receipt_3_13_2384_0_part6 receipt_3_13_2384_0_part7 rfl rfl rfl
private theorem receipt_3_13_2384_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 640 384 = 2219409168442722630623484128 :=
  phaseBlock_append receipt_3_13_2384_0_part5 receipt_3_13_2384_0_join4 rfl rfl rfl
private theorem receipt_3_13_2384_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 1152 146 = 116262058534821133010278615 :=
  phaseBlock_append receipt_3_13_2384_0_part9 receipt_3_13_2384_0_part10 rfl rfl rfl
private theorem receipt_3_13_2384_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 1024 274 = 421059080205770734861784695 :=
  phaseBlock_append receipt_3_13_2384_0_part8 receipt_3_13_2384_0_join6 rfl rfl rfl
private theorem receipt_3_13_2384_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 640 658 = 2640468248648493365485268823 :=
  phaseBlock_append receipt_3_13_2384_0_join5 receipt_3_13_2384_0_join7 rfl rfl rfl
private theorem receipt_3_13_2384_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 0) 0 1298 = 11610159536832062973838082935 :=
  phaseBlock_append receipt_3_13_2384_0_join3 receipt_3_13_2384_0_join8 rfl rfl rfl

private theorem receipt_3_13_2384_0 : fastPhase (bank 3 13).shape 179808 2384 44 1 1 1 0 = 11610159536832062973838082935 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2384_0_join9

private theorem receipt_3_13_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 0 128 = 2386507324236553854962509728 := by decide +kernel
private theorem receipt_3_13_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 128 128 = 2075130082489918217611114400 := by decide +kernel
private theorem receipt_3_13_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 256 128 = 1777524056945036228615849888 := by decide +kernel
private theorem receipt_3_13_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 384 128 = 1494089615565027432333809568 := by decide +kernel
private theorem receipt_3_13_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 512 128 = 1225223482624698089106139040 := by decide +kernel
private theorem receipt_3_13_2384_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 640 128 = 971318748142899586227451808 := by decide +kernel
private theorem receipt_3_13_2384_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 768 128 = 732764877314886848915244960 := by decide +kernel
private theorem receipt_3_13_2384_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 896 128 = 509947719944676751279314848 := by decide +kernel
private theorem receipt_3_13_2384_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 1024 128 = 303249519877406527291172768 := by decide +kernel
private theorem receipt_3_13_2384_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 1152 128 = 113048924431692181753460640 := by decide +kernel
private theorem receipt_3_13_2384_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 1280 18 = 1604354671083930246307092 := by decide +kernel
private theorem receipt_3_13_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 0 256 = 4461637406726472072573624128 :=
  phaseBlock_append receipt_3_13_2384_1_part0 receipt_3_13_2384_1_part1 rfl rfl rfl
private theorem receipt_3_13_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 384 256 = 2719313098189725521439948608 :=
  phaseBlock_append receipt_3_13_2384_1_part3 receipt_3_13_2384_1_part4 rfl rfl rfl
private theorem receipt_3_13_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 256 384 = 4496837155134761750055798496 :=
  phaseBlock_append receipt_3_13_2384_1_part2 receipt_3_13_2384_1_join1 rfl rfl rfl
private theorem receipt_3_13_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 0 640 = 8958474561861233822629422624 :=
  phaseBlock_append receipt_3_13_2384_1_join0 receipt_3_13_2384_1_join2 rfl rfl rfl
private theorem receipt_3_13_2384_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 768 256 = 1242712597259563600194559808 :=
  phaseBlock_append receipt_3_13_2384_1_part6 receipt_3_13_2384_1_part7 rfl rfl rfl
private theorem receipt_3_13_2384_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 640 384 = 2214031345402463186422011616 :=
  phaseBlock_append receipt_3_13_2384_1_part5 receipt_3_13_2384_1_join4 rfl rfl rfl
private theorem receipt_3_13_2384_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 1152 146 = 114653279102776111999767732 :=
  phaseBlock_append receipt_3_13_2384_1_part9 receipt_3_13_2384_1_part10 rfl rfl rfl
private theorem receipt_3_13_2384_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 1024 274 = 417902798980182639290940500 :=
  phaseBlock_append receipt_3_13_2384_1_part8 receipt_3_13_2384_1_join6 rfl rfl rfl
private theorem receipt_3_13_2384_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 640 658 = 2631934144382645825712952116 :=
  phaseBlock_append receipt_3_13_2384_1_join5 receipt_3_13_2384_1_join7 rfl rfl rfl
private theorem receipt_3_13_2384_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179808 2384 44 1 1 1 1) 0 1298 = 11590408706243879648342374740 :=
  phaseBlock_append receipt_3_13_2384_1_join3 receipt_3_13_2384_1_join8 rfl rfl rfl

private theorem receipt_3_13_2384_1 : fastPhase (bank 3 13).shape 179808 2384 44 1 1 1 1 = 11590408706243879648342374740 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2384_1_join9

theorem receipt_3_13 : Checked (bank 3 13) 44 1 1 := by
  refine checked_from_values (bank 3 13) 44 1 1
    (P3_7_1.checked (bank 3 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1297)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_13_2383_0 receipt_3_13_2383_1 receipt_3_13_2384_0 receipt_3_13_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_14_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 0 128 = 188064025262192374737741946080 := by decide +kernel
private theorem receipt_0_14_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 128 128 = 172136468953201719904335711456 := by decide +kernel
private theorem receipt_0_14_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 256 128 = 156690297304747294376281930976 := by decide +kernel
private theorem receipt_0_14_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 384 128 = 141718063697215619776899624160 := by decide +kernel
private theorem receipt_0_14_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 512 128 = 127212333500373688617561152736 := by decide +kernel
private theorem receipt_0_14_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 640 128 = 113165684067080461474255277280 := by decide +kernel
private theorem receipt_0_14_2383_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 768 128 = 99570704726998364164150213856 := by decide +kernel
private theorem receipt_0_14_2383_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 896 128 = 86419996780304784922156690656 := by decide +kernel
private theorem receipt_0_14_2383_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1024 128 = 73706173491403571577491004640 := by decide +kernel
private theorem receipt_0_14_2383_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1152 128 = 61421860082636528730238078176 := by decide +kernel
private theorem receipt_0_14_2383_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1280 128 = 49559698542369881757884997223 := by decide +kernel
private theorem receipt_0_14_2383_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1408 128 = 38112354817956236647246730239 := by decide +kernel
private theorem receipt_0_14_2383_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1536 128 = 27072474744028280728322274950 := by decide +kernel
private theorem receipt_0_14_2383_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1664 128 = 16432706082659642432603678101 := by decide +kernel
private theorem receipt_0_14_2383_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1792 128 = 6185708560627029677195662884 := by decide +kernel
private theorem receipt_0_14_2383_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1920 15 = 71998175452262866944883501 := by decide +kernel
private theorem receipt_0_14_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 0 256 = 360200494215394094642077657536 :=
  phaseBlock_append receipt_0_14_2383_0_part0 receipt_0_14_2383_0_part1 rfl rfl rfl
private theorem receipt_0_14_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 256 256 = 298408361001962914153181555136 :=
  phaseBlock_append receipt_0_14_2383_0_part2 receipt_0_14_2383_0_part3 rfl rfl rfl
private theorem receipt_0_14_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 0 512 = 658608855217357008795259212672 :=
  phaseBlock_append receipt_0_14_2383_0_join0 receipt_0_14_2383_0_join1 rfl rfl rfl
private theorem receipt_0_14_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 512 256 = 240378017567454150091816430016 :=
  phaseBlock_append receipt_0_14_2383_0_part4 receipt_0_14_2383_0_part5 rfl rfl rfl
private theorem receipt_0_14_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 768 256 = 185990701507303149086306904512 :=
  phaseBlock_append receipt_0_14_2383_0_part6 receipt_0_14_2383_0_part7 rfl rfl rfl
private theorem receipt_0_14_2383_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 512 512 = 426368719074757299178123334528 :=
  phaseBlock_append receipt_0_14_2383_0_join3 receipt_0_14_2383_0_join4 rfl rfl rfl
private theorem receipt_0_14_2383_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 0 1024 = 1084977574292114307973382547200 :=
  phaseBlock_append receipt_0_14_2383_0_join2 receipt_0_14_2383_0_join5 rfl rfl rfl
private theorem receipt_0_14_2383_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1024 256 = 135128033574040100307729082816 :=
  phaseBlock_append receipt_0_14_2383_0_part8 receipt_0_14_2383_0_part9 rfl rfl rfl
private theorem receipt_0_14_2383_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1280 256 = 87672053360326118405131727462 :=
  phaseBlock_append receipt_0_14_2383_0_part10 receipt_0_14_2383_0_part11 rfl rfl rfl
private theorem receipt_0_14_2383_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1024 512 = 222800086934366218712860810278 :=
  phaseBlock_append receipt_0_14_2383_0_join7 receipt_0_14_2383_0_join8 rfl rfl rfl
private theorem receipt_0_14_2383_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1536 256 = 43505180826687923160925953051 :=
  phaseBlock_append receipt_0_14_2383_0_part12 receipt_0_14_2383_0_part13 rfl rfl rfl
private theorem receipt_0_14_2383_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1792 143 = 6257706736079292544140546385 :=
  phaseBlock_append receipt_0_14_2383_0_part14 receipt_0_14_2383_0_part15 rfl rfl rfl
private theorem receipt_0_14_2383_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1536 399 = 49762887562767215705066499436 :=
  phaseBlock_append receipt_0_14_2383_0_join10 receipt_0_14_2383_0_join11 rfl rfl rfl
private theorem receipt_0_14_2383_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 1024 911 = 272562974497133434417927309714 :=
  phaseBlock_append receipt_0_14_2383_0_join9 receipt_0_14_2383_0_join12 rfl rfl rfl
private theorem receipt_0_14_2383_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 0) 0 1935 = 1357540548789247742391309856914 :=
  phaseBlock_append receipt_0_14_2383_0_join6 receipt_0_14_2383_0_join13 rfl rfl rfl

private theorem receipt_0_14_2383_0 : fastPhase (bank 0 14).shape 179808 2383 73 1 0 1 0 = 1357540548789247742391309856914 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2383_0_join14

private theorem receipt_0_14_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 0 128 = 187939377175890657497607752352 := by decide +kernel
private theorem receipt_0_14_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 128 128 = 172015483441291405868358761120 := by decide +kernel
private theorem receipt_0_14_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 256 128 = 156572918034680746251436370592 := by decide +kernel
private theorem receipt_0_14_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 384 128 = 141604234427810045780461705888 := by decide +kernel
private theorem receipt_0_14_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 512 128 = 127101998081762996099879504544 := by decide +kernel
private theorem receipt_0_14_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 640 128 = 113058786440667110541521173152 := by decide +kernel
private theorem receipt_0_14_2383_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 768 128 = 99467188925405221301167844000 := by decide +kernel
private theorem receipt_0_14_2383_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 896 128 = 86319806927326976615113431712 := by decide +kernel
private theorem receipt_0_14_2383_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1024 128 = 73609253801960337936727689888 := by decide +kernel
private theorem receipt_0_14_2383_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1152 128 = 61328154862723077113019267744 := by decide +kernel
private theorem receipt_0_14_2383_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1280 128 = 49469152180333636033747300576 := by decide +kernel
private theorem receipt_0_14_2383_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1408 128 = 38024911749383699844753239377 := by decide +kernel
private theorem receipt_0_14_2383_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1536 128 = 26988079482189523648930084180 := by decide +kernel
private theorem receipt_0_14_2383_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1664 128 = 16351303231869515499681259213 := by decide +kernel
private theorem receipt_0_14_2383_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1792 128 = 6107242816211024649062288743 := by decide +kernel
private theorem receipt_0_14_2383_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1920 15 = 62992682977657822741080220 := by decide +kernel
private theorem receipt_0_14_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 0 256 = 359954860617182063365966513472 :=
  phaseBlock_append receipt_0_14_2383_1_part0 receipt_0_14_2383_1_part1 rfl rfl rfl
private theorem receipt_0_14_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 256 256 = 298177152462490792031898076480 :=
  phaseBlock_append receipt_0_14_2383_1_part2 receipt_0_14_2383_1_part3 rfl rfl rfl
private theorem receipt_0_14_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 0 512 = 658132013079672855397864589952 :=
  phaseBlock_append receipt_0_14_2383_1_join0 receipt_0_14_2383_1_join1 rfl rfl rfl
private theorem receipt_0_14_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 512 256 = 240160784522430106641400677696 :=
  phaseBlock_append receipt_0_14_2383_1_part4 receipt_0_14_2383_1_part5 rfl rfl rfl
private theorem receipt_0_14_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 768 256 = 185786995852732197916281275712 :=
  phaseBlock_append receipt_0_14_2383_1_part6 receipt_0_14_2383_1_part7 rfl rfl rfl
private theorem receipt_0_14_2383_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 512 512 = 425947780375162304557681953408 :=
  phaseBlock_append receipt_0_14_2383_1_join3 receipt_0_14_2383_1_join4 rfl rfl rfl
private theorem receipt_0_14_2383_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 0 1024 = 1084079793454835159955546543360 :=
  phaseBlock_append receipt_0_14_2383_1_join2 receipt_0_14_2383_1_join5 rfl rfl rfl
private theorem receipt_0_14_2383_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1024 256 = 134937408664683415049746957632 :=
  phaseBlock_append receipt_0_14_2383_1_part8 receipt_0_14_2383_1_part9 rfl rfl rfl
private theorem receipt_0_14_2383_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1280 256 = 87494063929717335878500539953 :=
  phaseBlock_append receipt_0_14_2383_1_part10 receipt_0_14_2383_1_part11 rfl rfl rfl
private theorem receipt_0_14_2383_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1024 512 = 222431472594400750928247497585 :=
  phaseBlock_append receipt_0_14_2383_1_join7 receipt_0_14_2383_1_join8 rfl rfl rfl
private theorem receipt_0_14_2383_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1536 256 = 43339382714059039148611343393 :=
  phaseBlock_append receipt_0_14_2383_1_part12 receipt_0_14_2383_1_part13 rfl rfl rfl
private theorem receipt_0_14_2383_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1792 143 = 6170235499188682471803368963 :=
  phaseBlock_append receipt_0_14_2383_1_part14 receipt_0_14_2383_1_part15 rfl rfl rfl
private theorem receipt_0_14_2383_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1536 399 = 49509618213247721620414712356 :=
  phaseBlock_append receipt_0_14_2383_1_join10 receipt_0_14_2383_1_join11 rfl rfl rfl
private theorem receipt_0_14_2383_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 1024 911 = 271941090807648472548662209941 :=
  phaseBlock_append receipt_0_14_2383_1_join9 receipt_0_14_2383_1_join12 rfl rfl rfl
private theorem receipt_0_14_2383_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2383 73 1 0 1 1) 0 1935 = 1356020884262483632504208753301 :=
  phaseBlock_append receipt_0_14_2383_1_join6 receipt_0_14_2383_1_join13 rfl rfl rfl

private theorem receipt_0_14_2383_1 : fastPhase (bank 0 14).shape 179808 2383 73 1 0 1 1 = 1356020884262483632504208753301 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2383_1_join14

private theorem receipt_0_14_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 0 128 = 188065713077593118088017903808 := by decide +kernel
private theorem receipt_0_14_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 128 128 = 172137956557163029718155395264 := by decide +kernel
private theorem receipt_0_14_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 256 128 = 156691598222756765444382228672 := by decide +kernel
private theorem receipt_0_14_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 384 128 = 141719191198320553609671672000 := by decide +kernel
private theorem receipt_0_14_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 512 128 = 127213300597598693493197537472 := by decide +kernel
private theorem receipt_0_14_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 640 128 = 113166503517844832584571683008 := by decide +kernel
private theorem receipt_0_14_2384_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 768 128 = 99571389033533243858081513664 := by decide +kernel
private theorem receipt_0_14_2384_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 896 128 = 86420558190070103046927483072 := by decide +kernel
private theorem receipt_0_14_2384_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1024 128 = 73706623997504765917460594880 := by decide +kernel
private theorem receipt_0_14_2384_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1152 128 = 61422211424241045543419904192 := by decide +kernel
private theorem receipt_0_14_2384_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1280 128 = 49559962041992350885529975424 := by decide +kernel
private theorem receipt_0_14_2384_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1408 128 = 38112541606964751118101809076 := by decide +kernel
private theorem receipt_0_14_2384_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1536 128 = 27072595988482047410081062722 := by decide +kernel
private theorem receipt_0_14_2384_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1664 128 = 16432772672162606270703832353 := by decide +kernel
private theorem receipt_0_14_2384_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1792 128 = 6185731111437000252850093931 := by decide +kernel
private theorem receipt_0_14_2384_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1920 15 = 71998416042529173532118866 := by decide +kernel
private theorem receipt_0_14_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 0 256 = 360203669634756147806173299072 :=
  phaseBlock_append receipt_0_14_2384_0_part0 receipt_0_14_2384_0_part1 rfl rfl rfl
private theorem receipt_0_14_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 256 256 = 298410789421077319054053900672 :=
  phaseBlock_append receipt_0_14_2384_0_part2 receipt_0_14_2384_0_part3 rfl rfl rfl
private theorem receipt_0_14_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 0 512 = 658614459055833466860227199744 :=
  phaseBlock_append receipt_0_14_2384_0_join0 receipt_0_14_2384_0_join1 rfl rfl rfl
private theorem receipt_0_14_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 512 256 = 240379804115443526077769220480 :=
  phaseBlock_append receipt_0_14_2384_0_part4 receipt_0_14_2384_0_part5 rfl rfl rfl
private theorem receipt_0_14_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 768 256 = 185991947223603346905008996736 :=
  phaseBlock_append receipt_0_14_2384_0_part6 receipt_0_14_2384_0_part7 rfl rfl rfl
private theorem receipt_0_14_2384_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 512 512 = 426371751339046872982778217216 :=
  phaseBlock_append receipt_0_14_2384_0_join3 receipt_0_14_2384_0_join4 rfl rfl rfl
private theorem receipt_0_14_2384_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 0 1024 = 1084986210394880339843005416960 :=
  phaseBlock_append receipt_0_14_2384_0_join2 receipt_0_14_2384_0_join5 rfl rfl rfl
private theorem receipt_0_14_2384_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1024 256 = 135128835421745811460880499072 :=
  phaseBlock_append receipt_0_14_2384_0_part8 receipt_0_14_2384_0_part9 rfl rfl rfl
private theorem receipt_0_14_2384_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1280 256 = 87672503648957102003631784500 :=
  phaseBlock_append receipt_0_14_2384_0_part10 receipt_0_14_2384_0_part11 rfl rfl rfl
private theorem receipt_0_14_2384_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1024 512 = 222801339070702913464512283572 :=
  phaseBlock_append receipt_0_14_2384_0_join7 receipt_0_14_2384_0_join8 rfl rfl rfl
private theorem receipt_0_14_2384_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1536 256 = 43505368660644653680784895075 :=
  phaseBlock_append receipt_0_14_2384_0_part12 receipt_0_14_2384_0_part13 rfl rfl rfl
private theorem receipt_0_14_2384_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1792 143 = 6257729527479529426382212797 :=
  phaseBlock_append receipt_0_14_2384_0_part14 receipt_0_14_2384_0_part15 rfl rfl rfl
private theorem receipt_0_14_2384_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1536 399 = 49763098188124183107167107872 :=
  phaseBlock_append receipt_0_14_2384_0_join10 receipt_0_14_2384_0_join11 rfl rfl rfl
private theorem receipt_0_14_2384_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 1024 911 = 272564437258827096571679391444 :=
  phaseBlock_append receipt_0_14_2384_0_join9 receipt_0_14_2384_0_join12 rfl rfl rfl
private theorem receipt_0_14_2384_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 0) 0 1935 = 1357550647653707436414684808404 :=
  phaseBlock_append receipt_0_14_2384_0_join6 receipt_0_14_2384_0_join13 rfl rfl rfl

private theorem receipt_0_14_2384_0 : fastPhase (bank 0 14).shape 179808 2384 73 1 0 1 0 = 1357550647653707436414684808404 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2384_0_join14

private theorem receipt_0_14_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 0 128 = 187941064075213304281812451200 := by decide +kernel
private theorem receipt_0_14_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 128 128 = 172016970182486539591709155200 := by decide +kernel
private theorem receipt_0_14_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 256 128 = 156574218142024294326301196160 := by decide +kernel
private theorem receipt_0_14_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 384 128 = 141605361169139929375126200192 := by decide +kernel
private theorem receipt_0_14_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 512 128 = 127102964468896728881022549888 := by decide +kernel
private theorem receipt_0_14_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 640 128 = 113059605229819177514366885760 := by decide +kernel
private theorem receipt_0_14_2384_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 768 128 = 99467872617604237747311607680 := by decide +kernel
private theorem receipt_0_14_2384_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 896 128 = 86320367768832627128022376320 := by decide +kernel
private theorem receipt_0_14_2384_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1024 128 = 73609703784680095554915614592 := by decide +kernel
private theorem receipt_0_14_2384_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1152 128 = 61328505724628702550896009088 := by decide +kernel
private theorem receipt_0_14_2384_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1280 128 = 49469415243034872971362486760 := by decide +kernel
private theorem receipt_0_14_2384_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1408 128 = 38025098143418560035688533580 := by decide +kernel
private theorem receipt_0_14_2384_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1536 128 = 26988200372367584891899995483 := by decide +kernel
private theorem receipt_0_14_2384_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1664 128 = 16351369506551702269128116281 := by decide +kernel
private theorem receipt_0_14_2384_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1792 128 = 6107265090418570595566187205 := by decide +kernel
private theorem receipt_0_14_2384_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1920 15 = 62992893599148673397658995 := by decide +kernel
private theorem receipt_0_14_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 0 256 = 359958034257699843873521606400 :=
  phaseBlock_append receipt_0_14_2384_1_part0 receipt_0_14_2384_1_part1 rfl rfl rfl
private theorem receipt_0_14_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 256 256 = 298179579311164223701427396352 :=
  phaseBlock_append receipt_0_14_2384_1_part2 receipt_0_14_2384_1_part3 rfl rfl rfl
private theorem receipt_0_14_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 0 512 = 658137613568864067574949002752 :=
  phaseBlock_append receipt_0_14_2384_1_join0 receipt_0_14_2384_1_join1 rfl rfl rfl
private theorem receipt_0_14_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 512 256 = 240162569698715906395389435648 :=
  phaseBlock_append receipt_0_14_2384_1_part4 receipt_0_14_2384_1_part5 rfl rfl rfl
private theorem receipt_0_14_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 768 256 = 185788240386436864875333984000 :=
  phaseBlock_append receipt_0_14_2384_1_part6 receipt_0_14_2384_1_part7 rfl rfl rfl
private theorem receipt_0_14_2384_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 512 512 = 425950810085152771270723419648 :=
  phaseBlock_append receipt_0_14_2384_1_join3 receipt_0_14_2384_1_join4 rfl rfl rfl
private theorem receipt_0_14_2384_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 0 1024 = 1084088423654016838845672422400 :=
  phaseBlock_append receipt_0_14_2384_1_join2 receipt_0_14_2384_1_join5 rfl rfl rfl
private theorem receipt_0_14_2384_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1024 256 = 134938209509308798105811623680 :=
  phaseBlock_append receipt_0_14_2384_1_part8 receipt_0_14_2384_1_part9 rfl rfl rfl
private theorem receipt_0_14_2384_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1280 256 = 87494513386453433007051020340 :=
  phaseBlock_append receipt_0_14_2384_1_part10 receipt_0_14_2384_1_part11 rfl rfl rfl
private theorem receipt_0_14_2384_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1024 512 = 222432722895762231112862644020 :=
  phaseBlock_append receipt_0_14_2384_1_join7 receipt_0_14_2384_1_join8 rfl rfl rfl
private theorem receipt_0_14_2384_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1536 256 = 43339569878919287161028111764 :=
  phaseBlock_append receipt_0_14_2384_1_part12 receipt_0_14_2384_1_part13 rfl rfl rfl
private theorem receipt_0_14_2384_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1792 143 = 6170257984017719268963846200 :=
  phaseBlock_append receipt_0_14_2384_1_part14 receipt_0_14_2384_1_part15 rfl rfl rfl
private theorem receipt_0_14_2384_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1536 399 = 49509827862937006429991957964 :=
  phaseBlock_append receipt_0_14_2384_1_join10 receipt_0_14_2384_1_join11 rfl rfl rfl
private theorem receipt_0_14_2384_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 1024 911 = 271942550758699237542854601984 :=
  phaseBlock_append receipt_0_14_2384_1_join9 receipt_0_14_2384_1_join12 rfl rfl rfl
private theorem receipt_0_14_2384_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179808 2384 73 1 0 1 1) 0 1935 = 1356030974412716076388527024384 :=
  phaseBlock_append receipt_0_14_2384_1_join6 receipt_0_14_2384_1_join13 rfl rfl rfl

private theorem receipt_0_14_2384_1 : fastPhase (bank 0 14).shape 179808 2384 73 1 0 1 1 = 1356030974412716076388527024384 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2384_1_join14

theorem receipt_0_14 : Checked (bank 0 14) 73 0 1 := by
  refine checked_from_values (bank 0 14) 73 0 1
    (P3_7_1.checked (bank 0 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_14_2383_0 receipt_0_14_2383_1 receipt_0_14_2384_0 receipt_0_14_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_14_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 0 128 = 169309703131239611591827027680 := by decide +kernel
private theorem receipt_1_14_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 128 128 = 154896947552984254537979094752 := by decide +kernel
private theorem receipt_1_14_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 256 128 = 140930761673393942905350543072 := by decide +kernel
private theorem receipt_1_14_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 384 128 = 127403837444604460058086033120 := by decide +kernel
private theorem receipt_1_14_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 512 128 = 114308890094155361349743032032 := by decide +kernel
private theorem receipt_1_14_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 640 128 = 101638658099835962829544040160 := by decide +kernel
private theorem receipt_1_14_2383_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 768 128 = 89385903164531329948628817632 := by decide +kernel
private theorem receipt_1_14_2383_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 896 128 = 77543410191068266266306610912 := by decide +kernel
private theorem receipt_1_14_2383_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1024 128 = 66103987257061302156308379360 := by decide +kernel
private theorem receipt_1_14_2383_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1152 128 = 55060465589758683513039021792 := by decide +kernel
private theorem receipt_1_14_2383_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1280 128 = 44405703854004577764511224479 := by decide +kernel
private theorem receipt_1_14_2383_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1408 128 = 34132594565688427876222488831 := by decide +kernel
private theorem receipt_1_14_2383_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1536 128 = 24234024595848333223305385456 := by decide +kernel
private theorem receipt_1_14_2383_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1664 128 = 14702894937685194085681254915 := by decide +kernel
private theorem receipt_1_14_2383_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1792 128 = 5532129685671803574955743432 := by decide +kernel
private theorem receipt_1_14_2383_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1920 15 = 64370033816898617248656417 := by decide +kernel
private theorem receipt_1_14_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 0 256 = 324206650684223866129806122432 :=
  phaseBlock_append receipt_1_14_2383_0_part0 receipt_1_14_2383_0_part1 rfl rfl rfl
private theorem receipt_1_14_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 256 256 = 268334599117998402963436576192 :=
  phaseBlock_append receipt_1_14_2383_0_part2 receipt_1_14_2383_0_part3 rfl rfl rfl
private theorem receipt_1_14_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 0 512 = 592541249802222269093242698624 :=
  phaseBlock_append receipt_1_14_2383_0_join0 receipt_1_14_2383_0_join1 rfl rfl rfl
private theorem receipt_1_14_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 512 256 = 215947548193991324179287072192 :=
  phaseBlock_append receipt_1_14_2383_0_part4 receipt_1_14_2383_0_part5 rfl rfl rfl
private theorem receipt_1_14_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 768 256 = 166929313355599596214935428544 :=
  phaseBlock_append receipt_1_14_2383_0_part6 receipt_1_14_2383_0_part7 rfl rfl rfl
private theorem receipt_1_14_2383_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 512 512 = 382876861549590920394222500736 :=
  phaseBlock_append receipt_1_14_2383_0_join3 receipt_1_14_2383_0_join4 rfl rfl rfl
private theorem receipt_1_14_2383_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 0 1024 = 975418111351813189487465199360 :=
  phaseBlock_append receipt_1_14_2383_0_join2 receipt_1_14_2383_0_join5 rfl rfl rfl
private theorem receipt_1_14_2383_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1024 256 = 121164452846819985669347401152 :=
  phaseBlock_append receipt_1_14_2383_0_part8 receipt_1_14_2383_0_part9 rfl rfl rfl
private theorem receipt_1_14_2383_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1280 256 = 78538298419693005640733713310 :=
  phaseBlock_append receipt_1_14_2383_0_part10 receipt_1_14_2383_0_part11 rfl rfl rfl
private theorem receipt_1_14_2383_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1024 512 = 199702751266512991310081114462 :=
  phaseBlock_append receipt_1_14_2383_0_join7 receipt_1_14_2383_0_join8 rfl rfl rfl
private theorem receipt_1_14_2383_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1536 256 = 38936919533533527308986640371 :=
  phaseBlock_append receipt_1_14_2383_0_part12 receipt_1_14_2383_0_part13 rfl rfl rfl
private theorem receipt_1_14_2383_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1792 143 = 5596499719488702192204399849 :=
  phaseBlock_append receipt_1_14_2383_0_part14 receipt_1_14_2383_0_part15 rfl rfl rfl
private theorem receipt_1_14_2383_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1536 399 = 44533419253022229501191040220 :=
  phaseBlock_append receipt_1_14_2383_0_join10 receipt_1_14_2383_0_join11 rfl rfl rfl
private theorem receipt_1_14_2383_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 1024 911 = 244236170519535220811272154682 :=
  phaseBlock_append receipt_1_14_2383_0_join9 receipt_1_14_2383_0_join12 rfl rfl rfl
private theorem receipt_1_14_2383_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 0) 0 1935 = 1219654281871348410298737354042 :=
  phaseBlock_append receipt_1_14_2383_0_join6 receipt_1_14_2383_0_join13 rfl rfl rfl

private theorem receipt_1_14_2383_0 : fastPhase (bank 1 14).shape 179808 2383 73 1 0 2 0 = 1219654281871348410298737354042 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2383_0_join14

private theorem receipt_1_14_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 0 128 = 169196858065168937527542169056 := by decide +kernel
private theorem receipt_1_14_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 128 128 = 154787504580668569879209283040 := by decide +kernel
private theorem receipt_1_14_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 256 128 = 140824665419483613116063866336 := by decide +kernel
private theorem receipt_1_14_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 384 128 = 127301032711200776229962001888 := by decide +kernel
private theorem receipt_1_14_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 512 128 = 114209321860617954693253660128 := by decide +kernel
private theorem receipt_1_14_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 640 128 = 101542271522590219165034925536 := by decide +kernel
private theorem receipt_1_14_2383_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 768 128 = 89292643576875804197400223200 := by decide +kernel
private theorem receipt_1_14_2383_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 896 128 = 77453223102982096941694545376 := by decide +kernel
private theorem receipt_1_14_2383_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1024 128 = 66016818355011625854765678048 := by decide +kernel
private theorem receipt_1_14_2383_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1152 128 = 54976260736508049405216427488 := by decide +kernel
private theorem receipt_1_14_2383_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1280 128 = 44324409080629985019811988504 := by decide +kernel
private theorem receipt_1_14_2383_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1408 128 = 34054156039959766432312284835 := by decide +kernel
private theorem receipt_1_14_2383_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1536 128 = 24158388649511336122286349840 := by decide +kernel
private theorem receipt_1_14_2383_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1664 128 = 14630008078323915573086216031 := by decide +kernel
private theorem receipt_1_14_2383_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1792 128 = 5461938596528252962173564335 := by decide +kernel
private theorem receipt_1_14_2383_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1920 15 = 56318524471119331425773254 := by decide +kernel
private theorem receipt_1_14_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 0 256 = 323984362645837507406751452096 :=
  phaseBlock_append receipt_1_14_2383_1_part0 receipt_1_14_2383_1_part1 rfl rfl rfl
private theorem receipt_1_14_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 256 256 = 268125698130684389346025868224 :=
  phaseBlock_append receipt_1_14_2383_1_part2 receipt_1_14_2383_1_part3 rfl rfl rfl
private theorem receipt_1_14_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 0 512 = 592110060776521896752777320320 :=
  phaseBlock_append receipt_1_14_2383_1_join0 receipt_1_14_2383_1_join1 rfl rfl rfl
private theorem receipt_1_14_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 512 256 = 215751593383208173858288585664 :=
  phaseBlock_append receipt_1_14_2383_1_part4 receipt_1_14_2383_1_part5 rfl rfl rfl
private theorem receipt_1_14_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 768 256 = 166745866679857901139094768576 :=
  phaseBlock_append receipt_1_14_2383_1_part6 receipt_1_14_2383_1_part7 rfl rfl rfl
private theorem receipt_1_14_2383_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 512 512 = 382497460063066074997383354240 :=
  phaseBlock_append receipt_1_14_2383_1_join3 receipt_1_14_2383_1_join4 rfl rfl rfl
private theorem receipt_1_14_2383_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 0 1024 = 974607520839587971750160674560 :=
  phaseBlock_append receipt_1_14_2383_1_join2 receipt_1_14_2383_1_join5 rfl rfl rfl
private theorem receipt_1_14_2383_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1024 256 = 120993079091519675259982105536 :=
  phaseBlock_append receipt_1_14_2383_1_part8 receipt_1_14_2383_1_part9 rfl rfl rfl
private theorem receipt_1_14_2383_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1280 256 = 78378565120589751452124273339 :=
  phaseBlock_append receipt_1_14_2383_1_part10 receipt_1_14_2383_1_part11 rfl rfl rfl
private theorem receipt_1_14_2383_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1024 512 = 199371644212109426712106378875 :=
  phaseBlock_append receipt_1_14_2383_1_join7 receipt_1_14_2383_1_join8 rfl rfl rfl
private theorem receipt_1_14_2383_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1536 256 = 38788396727835251695372565871 :=
  phaseBlock_append receipt_1_14_2383_1_part12 receipt_1_14_2383_1_part13 rfl rfl rfl
private theorem receipt_1_14_2383_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1792 143 = 5518257120999372293599337589 :=
  phaseBlock_append receipt_1_14_2383_1_part14 receipt_1_14_2383_1_part15 rfl rfl rfl
private theorem receipt_1_14_2383_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1536 399 = 44306653848834623988971903460 :=
  phaseBlock_append receipt_1_14_2383_1_join10 receipt_1_14_2383_1_join11 rfl rfl rfl
private theorem receipt_1_14_2383_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 1024 911 = 243678298060944050701078282335 :=
  phaseBlock_append receipt_1_14_2383_1_join9 receipt_1_14_2383_1_join12 rfl rfl rfl
private theorem receipt_1_14_2383_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2383 73 1 0 2 1) 0 1935 = 1218285818900532022451238956895 :=
  phaseBlock_append receipt_1_14_2383_1_join6 receipt_1_14_2383_1_join13 rfl rfl rfl

private theorem receipt_1_14_2383_1 : fastPhase (bank 1 14).shape 179808 2383 73 1 0 2 1 = 1218285818900532022451238956895 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2383_1_join14

private theorem receipt_1_14_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 0 128 = 169311222634710934603814935968 := by decide +kernel
private theorem receipt_1_14_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 128 128 = 154898286175002406262995766688 := by decide +kernel
private theorem receipt_1_14_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 256 128 = 140931931750093713194153835936 := by decide +kernel
private theorem receipt_1_14_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 384 128 = 127404851064282012721149881760 := by decide +kernel
private theorem receipt_1_14_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 512 128 = 114309759098075526655574072736 := by decide +kernel
private theorem receipt_1_14_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 640 128 = 101639394083038650393696013728 := by decide +kernel
private theorem receipt_1_14_2384_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 768 128 = 89386517476637062013414751648 := by decide +kernel
private theorem receipt_1_14_2384_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 896 128 = 77543913937082831371208781216 := by decide +kernel
private theorem receipt_1_14_2384_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1024 128 = 66104391298179529199086050720 := by decide +kernel
private theorem receipt_1_14_2384_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1152 128 = 55060780544167336201533967776 := by decide +kernel
private theorem receipt_1_14_2384_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1280 128 = 44405939951532271359977866245 := by decide +kernel
private theorem receipt_1_14_2384_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1408 128 = 34132761850424869342371965781 := by decide +kernel
private theorem receipt_1_14_2384_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1536 128 = 24234133128674716797895874496 := by decide +kernel
private theorem receipt_1_14_2384_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1664 128 = 14702954517802914208602051960 := by decide +kernel
private theorem receipt_1_14_2384_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1792 128 = 5532149853851802521306750736 := by decide +kernel
private theorem receipt_1_14_2384_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1920 15 = 64370248916855253249725628 := by decide +kernel
private theorem receipt_1_14_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 0 256 = 324209508809713340866810702656 :=
  phaseBlock_append receipt_1_14_2384_0_part0 receipt_1_14_2384_0_part1 rfl rfl rfl
private theorem receipt_1_14_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 256 256 = 268336782814375725915303717696 :=
  phaseBlock_append receipt_1_14_2384_0_part2 receipt_1_14_2384_0_part3 rfl rfl rfl
private theorem receipt_1_14_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 0 512 = 592546291624089066782114420352 :=
  phaseBlock_append receipt_1_14_2384_0_join0 receipt_1_14_2384_0_join1 rfl rfl rfl
private theorem receipt_1_14_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 512 256 = 215949153181114177049270086464 :=
  phaseBlock_append receipt_1_14_2384_0_part4 receipt_1_14_2384_0_part5 rfl rfl rfl
private theorem receipt_1_14_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 768 256 = 166930431413719893384623532864 :=
  phaseBlock_append receipt_1_14_2384_0_part6 receipt_1_14_2384_0_part7 rfl rfl rfl
private theorem receipt_1_14_2384_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 512 512 = 382879584594834070433893619328 :=
  phaseBlock_append receipt_1_14_2384_0_join3 receipt_1_14_2384_0_join4 rfl rfl rfl
private theorem receipt_1_14_2384_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 0 1024 = 975425876218923137216008039680 :=
  phaseBlock_append receipt_1_14_2384_0_join2 receipt_1_14_2384_0_join5 rfl rfl rfl
private theorem receipt_1_14_2384_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1024 256 = 121165171842346865400620018496 :=
  phaseBlock_append receipt_1_14_2384_0_part8 receipt_1_14_2384_0_part9 rfl rfl rfl
private theorem receipt_1_14_2384_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1280 256 = 78538701801957140702349832026 :=
  phaseBlock_append receipt_1_14_2384_0_part10 receipt_1_14_2384_0_part11 rfl rfl rfl
private theorem receipt_1_14_2384_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1024 512 = 199703873644304006102969850522 :=
  phaseBlock_append receipt_1_14_2384_0_join7 receipt_1_14_2384_0_join8 rfl rfl rfl
private theorem receipt_1_14_2384_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1536 256 = 38937087646477631006497926456 :=
  phaseBlock_append receipt_1_14_2384_0_part12 receipt_1_14_2384_0_part13 rfl rfl rfl
private theorem receipt_1_14_2384_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1792 143 = 5596520102768657774556476364 :=
  phaseBlock_append receipt_1_14_2384_0_part14 receipt_1_14_2384_0_part15 rfl rfl rfl
private theorem receipt_1_14_2384_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1536 399 = 44533607749246288781054402820 :=
  phaseBlock_append receipt_1_14_2384_0_join10 receipt_1_14_2384_0_join11 rfl rfl rfl
private theorem receipt_1_14_2384_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 1024 911 = 244237481393550294884024253342 :=
  phaseBlock_append receipt_1_14_2384_0_join9 receipt_1_14_2384_0_join12 rfl rfl rfl
private theorem receipt_1_14_2384_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 0) 0 1935 = 1219663357612473432100032293022 :=
  phaseBlock_append receipt_1_14_2384_0_join6 receipt_1_14_2384_0_join13 rfl rfl rfl

private theorem receipt_1_14_2384_0 : fastPhase (bank 1 14).shape 179808 2384 73 1 0 2 0 = 1219663357612473432100032293022 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2384_0_join14

private theorem receipt_1_14_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 0 128 = 169198376738284702622077537248 := by decide +kernel
private theorem receipt_1_14_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 128 128 = 154788842421362673660605545440 := by decide +kernel
private theorem receipt_1_14_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 256 128 = 140825834762710622466919869408 := by decide +kernel
private theorem receipt_1_14_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 384 128 = 127302045644081060017438628832 := by decide +kernel
private theorem receipt_1_14_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 512 128 = 114210190223244971044710222816 := by decide +kernel
private theorem receipt_1_14_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 640 128 = 101543006908836923134363335648 := by decide +kernel
private theorem receipt_1_14_2384_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 768 128 = 89293257335200175822056942560 := by decide +kernel
private theorem receipt_1_14_2384_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 896 128 = 77453726337231789690430315488 := by decide +kernel
private theorem receipt_1_14_2384_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1024 128 = 66017221925227735466053028832 := by decide +kernel
private theorem receipt_1_14_2384_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1152 128 = 54976575259728003116374965216 := by decide +kernel
private theorem receipt_1_14_2384_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1280 128 = 44324644785796488211732736838 := by decide +kernel
private theorem receipt_1_14_2384_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1408 128 = 34054322970345427528314797946 := by decide +kernel
private theorem receipt_1_14_2384_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1536 128 = 24158496864805591983414453384 := by decide +kernel
private theorem receipt_1_14_2384_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1664 128 = 14630067376544816611579324344 := by decide +kernel
private theorem receipt_1_14_2384_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1792 128 = 5461958517271641834888995421 := by decide +kernel
private theorem receipt_1_14_2384_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1920 15 = 56318712776992167840967959 := by decide +kernel
private theorem receipt_1_14_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 0 256 = 323987219159647376282683082688 :=
  phaseBlock_append receipt_1_14_2384_1_part0 receipt_1_14_2384_1_part1 rfl rfl rfl
private theorem receipt_1_14_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 256 256 = 268127880406791682484358498240 :=
  phaseBlock_append receipt_1_14_2384_1_part2 receipt_1_14_2384_1_part3 rfl rfl rfl
private theorem receipt_1_14_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 0 512 = 592115099566439058767041580928 :=
  phaseBlock_append receipt_1_14_2384_1_join0 receipt_1_14_2384_1_join1 rfl rfl rfl
private theorem receipt_1_14_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 512 256 = 215753197132081894179073558464 :=
  phaseBlock_append receipt_1_14_2384_1_part4 receipt_1_14_2384_1_part5 rfl rfl rfl
private theorem receipt_1_14_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 768 256 = 166746983672431965512487258048 :=
  phaseBlock_append receipt_1_14_2384_1_part6 receipt_1_14_2384_1_part7 rfl rfl rfl
private theorem receipt_1_14_2384_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 512 512 = 382500180804513859691560816512 :=
  phaseBlock_append receipt_1_14_2384_1_join3 receipt_1_14_2384_1_join4 rfl rfl rfl
private theorem receipt_1_14_2384_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 0 1024 = 974615280370952918458602397440 :=
  phaseBlock_append receipt_1_14_2384_1_join2 receipt_1_14_2384_1_join5 rfl rfl rfl
private theorem receipt_1_14_2384_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1024 256 = 120993797184955738582427994048 :=
  phaseBlock_append receipt_1_14_2384_1_part8 receipt_1_14_2384_1_part9 rfl rfl rfl
private theorem receipt_1_14_2384_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1280 256 = 78378967756141915740047534784 :=
  phaseBlock_append receipt_1_14_2384_1_part10 receipt_1_14_2384_1_part11 rfl rfl rfl
private theorem receipt_1_14_2384_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1024 512 = 199372764941097654322475528832 :=
  phaseBlock_append receipt_1_14_2384_1_join7 receipt_1_14_2384_1_join8 rfl rfl rfl
private theorem receipt_1_14_2384_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1536 256 = 38788564241350408594993777728 :=
  phaseBlock_append receipt_1_14_2384_1_part12 receipt_1_14_2384_1_part13 rfl rfl rfl
private theorem receipt_1_14_2384_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1792 143 = 5518277230048634002729963380 :=
  phaseBlock_append receipt_1_14_2384_1_part14 receipt_1_14_2384_1_part15 rfl rfl rfl
private theorem receipt_1_14_2384_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1536 399 = 44306841471399042597723741108 :=
  phaseBlock_append receipt_1_14_2384_1_join10 receipt_1_14_2384_1_join11 rfl rfl rfl
private theorem receipt_1_14_2384_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 1024 911 = 243679606412496696920199269940 :=
  phaseBlock_append receipt_1_14_2384_1_join9 receipt_1_14_2384_1_join12 rfl rfl rfl
private theorem receipt_1_14_2384_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179808 2384 73 1 0 2 1) 0 1935 = 1218294886783449615378801667380 :=
  phaseBlock_append receipt_1_14_2384_1_join6 receipt_1_14_2384_1_join13 rfl rfl rfl

private theorem receipt_1_14_2384_1 : fastPhase (bank 1 14).shape 179808 2384 73 1 0 2 1 = 1218294886783449615378801667380 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2384_1_join14

theorem receipt_1_14 : Checked (bank 1 14) 73 0 2 := by
  refine checked_from_values (bank 1 14) 73 0 2
    (P3_7_1.checked (bank 1 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_14_2383_0 receipt_1_14_2383_1 receipt_1_14_2384_0 receipt_1_14_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_14_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 0 128 = 90846864656846479044946679808 := by decide +kernel
private theorem receipt_2_14_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 128 128 = 82829993492987174337529911296 := by decide +kernel
private theorem receipt_2_14_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 256 128 = 75104067280112751800765405184 := by decide +kernel
private theorem receipt_2_14_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 384 128 = 67662693743593800773230041088 := by decide +kernel
private theorem receipt_2_14_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 512 128 = 60499549932613426385352185856 := by decide +kernel
private theorem receipt_2_14_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 640 128 = 53608381912030611211001468928 := by decide +kernel
private theorem receipt_2_14_2383_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 768 128 = 46983004454243576919078557696 := by decide +kernel
private theorem receipt_2_14_2383_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 896 128 = 40617300731053145925104932864 := by decide +kernel
private theorem receipt_2_14_2383_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1024 128 = 34505222005526103042812663808 := by decide +kernel
private theorem receipt_2_14_2383_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1152 128 = 28640787323858557135734183936 := by decide +kernel
private theorem receipt_2_14_2383_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1280 128 = 23018085440759812804109190422 := by decide +kernel
private theorem receipt_2_14_2383_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1408 128 = 17631277803449144114628882246 := by decide +kernel
private theorem receipt_2_14_2383_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1536 128 = 12474577829481209497075956616 := by decide +kernel
private theorem receipt_2_14_2383_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1664 128 = 7542261003758034740287856898 := by decide +kernel
private theorem receipt_2_14_2383_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1792 128 = 2828669256790559470030944642 := by decide +kernel
private theorem receipt_2_14_2383_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1920 15 = 32834741193974594358672108 := by decide +kernel
private theorem receipt_2_14_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 0 256 = 173676858149833653382476591104 :=
  phaseBlock_append receipt_2_14_2383_0_part0 receipt_2_14_2383_0_part1 rfl rfl rfl
private theorem receipt_2_14_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 256 256 = 142766761023706552573995446272 :=
  phaseBlock_append receipt_2_14_2383_0_part2 receipt_2_14_2383_0_part3 rfl rfl rfl
private theorem receipt_2_14_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 0 512 = 316443619173540205956472037376 :=
  phaseBlock_append receipt_2_14_2383_0_join0 receipt_2_14_2383_0_join1 rfl rfl rfl
private theorem receipt_2_14_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 512 256 = 114107931844644037596353654784 :=
  phaseBlock_append receipt_2_14_2383_0_part4 receipt_2_14_2383_0_part5 rfl rfl rfl
private theorem receipt_2_14_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 768 256 = 87600305185296722844183490560 :=
  phaseBlock_append receipt_2_14_2383_0_part6 receipt_2_14_2383_0_part7 rfl rfl rfl
private theorem receipt_2_14_2383_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 512 512 = 201708237029940760440537145344 :=
  phaseBlock_append receipt_2_14_2383_0_join3 receipt_2_14_2383_0_join4 rfl rfl rfl
private theorem receipt_2_14_2383_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 0 1024 = 518151856203480966397009182720 :=
  phaseBlock_append receipt_2_14_2383_0_join2 receipt_2_14_2383_0_join5 rfl rfl rfl
private theorem receipt_2_14_2383_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1024 256 = 63146009329384660178546847744 :=
  phaseBlock_append receipt_2_14_2383_0_part8 receipt_2_14_2383_0_part9 rfl rfl rfl
private theorem receipt_2_14_2383_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1280 256 = 40649363244208956918738072668 :=
  phaseBlock_append receipt_2_14_2383_0_part10 receipt_2_14_2383_0_part11 rfl rfl rfl
private theorem receipt_2_14_2383_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1024 512 = 103795372573593617097284920412 :=
  phaseBlock_append receipt_2_14_2383_0_join7 receipt_2_14_2383_0_join8 rfl rfl rfl
private theorem receipt_2_14_2383_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1536 256 = 20016838833239244237363813514 :=
  phaseBlock_append receipt_2_14_2383_0_part12 receipt_2_14_2383_0_part13 rfl rfl rfl
private theorem receipt_2_14_2383_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1792 143 = 2861503997984534064389616750 :=
  phaseBlock_append receipt_2_14_2383_0_part14 receipt_2_14_2383_0_part15 rfl rfl rfl
private theorem receipt_2_14_2383_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1536 399 = 22878342831223778301753430264 :=
  phaseBlock_append receipt_2_14_2383_0_join10 receipt_2_14_2383_0_join11 rfl rfl rfl
private theorem receipt_2_14_2383_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 1024 911 = 126673715404817395399038350676 :=
  phaseBlock_append receipt_2_14_2383_0_join9 receipt_2_14_2383_0_join12 rfl rfl rfl
private theorem receipt_2_14_2383_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 0) 0 1935 = 644825571608298361796047533396 :=
  phaseBlock_append receipt_2_14_2383_0_join6 receipt_2_14_2383_0_join13 rfl rfl rfl

private theorem receipt_2_14_2383_0 : fastPhase (bank 2 14).shape 179808 2383 73 1 0 7 0 = 644825571608298361796047533396 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2383_0_join14

private theorem receipt_2_14_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 0 128 = 90783895741876918028037899328 := by decide +kernel
private theorem receipt_2_14_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 128 128 = 82769258231569857017736832064 := by decide +kernel
private theorem receipt_2_14_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 256 128 = 75045516850417953924480599104 := by decide +kernel
private theorem receipt_2_14_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 384 128 = 67606279853776281364608803904 := by decide +kernel
private theorem receipt_2_14_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 512 128 = 60445224818453255262055777344 := by decide +kernel
private theorem receipt_2_14_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 640 128 = 53556098334573996499940353088 := by decide +kernel
private theorem receipt_2_14_2383_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 768 128 = 46932715697443692572155642944 := by decide +kernel
private theorem receipt_2_14_2383_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 896 128 = 40568960599410959234958812224 := by decide +kernel
private theorem receipt_2_14_2383_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1024 128 = 34458784821731202158560855104 := by decide +kernel
private theorem receipt_2_14_2383_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1152 128 = 28596207926429978578716369984 := by decide +kernel
private theorem receipt_2_14_2383_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1280 128 = 22975319177592736279933326758 := by decide +kernel
private theorem receipt_2_14_2383_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1408 128 = 17590280513124591210275871958 := by decide +kernel
private theorem receipt_2_14_2383_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1536 128 = 12435305853733495836897145980 := by decide +kernel
private theorem receipt_2_14_2383_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1664 128 = 7504671191513792713444807518 := by decide +kernel
private theorem receipt_2_14_2383_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1792 128 = 2792718961810803450553795826 := by decide +kernel
private theorem receipt_2_14_2383_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1920 15 = 28727187109961810556660340 := by decide +kernel
private theorem receipt_2_14_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 0 256 = 173553153973446775045774731392 :=
  phaseBlock_append receipt_2_14_2383_1_part0 receipt_2_14_2383_1_part1 rfl rfl rfl
private theorem receipt_2_14_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 256 256 = 142651796704194235289089403008 :=
  phaseBlock_append receipt_2_14_2383_1_part2 receipt_2_14_2383_1_part3 rfl rfl rfl
private theorem receipt_2_14_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 0 512 = 316204950677641010334864134400 :=
  phaseBlock_append receipt_2_14_2383_1_join0 receipt_2_14_2383_1_join1 rfl rfl rfl
private theorem receipt_2_14_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 512 256 = 114001323153027251761996130432 :=
  phaseBlock_append receipt_2_14_2383_1_part4 receipt_2_14_2383_1_part5 rfl rfl rfl
private theorem receipt_2_14_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 768 256 = 87501676296854651807114455168 :=
  phaseBlock_append receipt_2_14_2383_1_part6 receipt_2_14_2383_1_part7 rfl rfl rfl
private theorem receipt_2_14_2383_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 512 512 = 201502999449881903569110585600 :=
  phaseBlock_append receipt_2_14_2383_1_join3 receipt_2_14_2383_1_join4 rfl rfl rfl
private theorem receipt_2_14_2383_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 0 1024 = 517707950127522913903974720000 :=
  phaseBlock_append receipt_2_14_2383_1_join2 receipt_2_14_2383_1_join5 rfl rfl rfl
private theorem receipt_2_14_2383_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1024 256 = 63054992748161180737277225088 :=
  phaseBlock_append receipt_2_14_2383_1_part8 receipt_2_14_2383_1_part9 rfl rfl rfl
private theorem receipt_2_14_2383_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1280 256 = 40565599690717327490209198716 :=
  phaseBlock_append receipt_2_14_2383_1_part10 receipt_2_14_2383_1_part11 rfl rfl rfl
private theorem receipt_2_14_2383_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1024 512 = 103620592438878508227486423804 :=
  phaseBlock_append receipt_2_14_2383_1_join7 receipt_2_14_2383_1_join8 rfl rfl rfl
private theorem receipt_2_14_2383_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1536 256 = 19939977045247288550341953498 :=
  phaseBlock_append receipt_2_14_2383_1_part12 receipt_2_14_2383_1_part13 rfl rfl rfl
private theorem receipt_2_14_2383_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1792 143 = 2821446148920765261110456166 :=
  phaseBlock_append receipt_2_14_2383_1_part14 receipt_2_14_2383_1_part15 rfl rfl rfl
private theorem receipt_2_14_2383_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1536 399 = 22761423194168053811452409664 :=
  phaseBlock_append receipt_2_14_2383_1_join10 receipt_2_14_2383_1_join11 rfl rfl rfl
private theorem receipt_2_14_2383_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 1024 911 = 126382015633046562038938833468 :=
  phaseBlock_append receipt_2_14_2383_1_join9 receipt_2_14_2383_1_join12 rfl rfl rfl
private theorem receipt_2_14_2383_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2383 73 1 0 7 1) 0 1935 = 644089965760569475942913553468 :=
  phaseBlock_append receipt_2_14_2383_1_join6 receipt_2_14_2383_1_join13 rfl rfl rfl

private theorem receipt_2_14_2383_1 : fastPhase (bank 2 14).shape 179808 2383 73 1 0 7 1 = 644089965760569475942913553468 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2383_1_join14

private theorem receipt_2_14_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 0 128 = 90847679988536981225941824864 := by decide +kernel
private theorem receipt_2_14_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 128 128 = 82830709319115734205745145184 := by decide +kernel
private theorem receipt_2_14_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 256 128 = 75104690838488726367453664608 := by decide +kernel
private theorem receipt_2_14_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 384 128 = 67663232071983877251351545184 := by decide +kernel
private theorem receipt_2_14_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 512 128 = 60500009871084660474564949344 := by decide +kernel
private theorem receipt_2_14_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 640 128 = 53608770105282690168699610464 := by decide +kernel
private theorem receipt_2_14_2384_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 768 128 = 46983327353930307417478403424 := by decide +kernel
private theorem receipt_2_14_2384_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 896 128 = 40617564598093166694378915168 := by decide +kernel
private theorem receipt_2_14_2384_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1024 128 = 34505432912402822300271015264 := by decide +kernel
private theorem receipt_2_14_2384_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1152 128 = 28640951156909314801054426464 := by decide +kernel
private theorem receipt_2_14_2384_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1280 128 = 23018207826748538883807087855 := by decide +kernel
private theorem receipt_2_14_2384_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1408 128 = 17631364216965328865342823699 := by decide +kernel
private theorem receipt_2_14_2384_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1536 128 = 12474633698819679262021317894 := by decide +kernel
private theorem receipt_2_14_2384_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1664 128 = 7542291567988159703185997691 := by decide +kernel
private theorem receipt_2_14_2384_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1792 128 = 2828679569406139893955751979 := by decide +kernel
private theorem receipt_2_14_2384_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1920 15 = 32834850915126200079622344 := by decide +kernel
private theorem receipt_2_14_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 0 256 = 173678389307652715431686970048 :=
  phaseBlock_append receipt_2_14_2384_0_part0 receipt_2_14_2384_0_part1 rfl rfl rfl
private theorem receipt_2_14_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 256 256 = 142767922910472603618805209792 :=
  phaseBlock_append receipt_2_14_2384_0_part2 receipt_2_14_2384_0_part3 rfl rfl rfl
private theorem receipt_2_14_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 0 512 = 316446312218125319050492179840 :=
  phaseBlock_append receipt_2_14_2384_0_join0 receipt_2_14_2384_0_join1 rfl rfl rfl
private theorem receipt_2_14_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 512 256 = 114108779976367350643264559808 :=
  phaseBlock_append receipt_2_14_2384_0_part4 receipt_2_14_2384_0_part5 rfl rfl rfl
private theorem receipt_2_14_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 768 256 = 87600891952023474111857318592 :=
  phaseBlock_append receipt_2_14_2384_0_part6 receipt_2_14_2384_0_part7 rfl rfl rfl
private theorem receipt_2_14_2384_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 512 512 = 201709671928390824755121878400 :=
  phaseBlock_append receipt_2_14_2384_0_join3 receipt_2_14_2384_0_join4 rfl rfl rfl
private theorem receipt_2_14_2384_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 0 1024 = 518155984146516143805614058240 :=
  phaseBlock_append receipt_2_14_2384_0_join2 receipt_2_14_2384_0_join5 rfl rfl rfl
private theorem receipt_2_14_2384_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1024 256 = 63146384069312137101325441728 :=
  phaseBlock_append receipt_2_14_2384_0_part8 receipt_2_14_2384_0_part9 rfl rfl rfl
private theorem receipt_2_14_2384_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1280 256 = 40649572043713867749149911554 :=
  phaseBlock_append receipt_2_14_2384_0_part10 receipt_2_14_2384_0_part11 rfl rfl rfl
private theorem receipt_2_14_2384_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1024 512 = 103795956113026004850475353282 :=
  phaseBlock_append receipt_2_14_2384_0_join7 receipt_2_14_2384_0_join8 rfl rfl rfl
private theorem receipt_2_14_2384_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1536 256 = 20016925266807838965207315585 :=
  phaseBlock_append receipt_2_14_2384_0_part12 receipt_2_14_2384_0_part13 rfl rfl rfl
private theorem receipt_2_14_2384_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1792 143 = 2861514420321266094035374323 :=
  phaseBlock_append receipt_2_14_2384_0_part14 receipt_2_14_2384_0_part15 rfl rfl rfl
private theorem receipt_2_14_2384_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1536 399 = 22878439687129105059242689908 :=
  phaseBlock_append receipt_2_14_2384_0_join10 receipt_2_14_2384_0_join11 rfl rfl rfl
private theorem receipt_2_14_2384_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 1024 911 = 126674395800155109909718043190 :=
  phaseBlock_append receipt_2_14_2384_0_join9 receipt_2_14_2384_0_join12 rfl rfl rfl
private theorem receipt_2_14_2384_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 0) 0 1935 = 644830379946671253715332101430 :=
  phaseBlock_append receipt_2_14_2384_0_join6 receipt_2_14_2384_0_join13 rfl rfl rfl

private theorem receipt_2_14_2384_0 : fastPhase (bank 2 14).shape 179808 2384 73 1 0 7 0 = 644830379946671253715332101430 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2384_0_join14

private theorem receipt_2_14_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 0 128 = 90784710606300460629306902880 := by decide +kernel
private theorem receipt_2_14_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 128 128 = 82769973620772206161365309792 := by decide +kernel
private theorem receipt_2_14_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 256 128 = 75046140001218685442486184288 := by decide +kernel
private theorem receipt_2_14_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 384 128 = 67606817802965275795285883232 := by decide +kernel
private theorem receipt_2_14_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 512 128 = 60445684405133672157133162848 := by decide +kernel
private theorem receipt_2_14_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 640 128 = 53556486202494473517786749280 := by decide +kernel
private theorem receipt_2_14_2384_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 768 128 = 46933038297319769357032909152 := by decide +kernel
private theorem receipt_2_14_2384_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 896 128 = 40569224191235726082323020128 := by decide +kernel
private theorem receipt_2_14_2384_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1024 128 = 34458995477075173466411141472 := by decide +kernel
private theorem receipt_2_14_2384_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1152 128 = 28596371530730191084991584608 := by decide +kernel
private theorem receipt_2_14_2384_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1280 128 = 22975441356861586566922180254 := by decide +kernel
private theorem receipt_2_14_2384_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1408 128 = 17590366741243756782157168782 := by decide +kernel
private theorem receipt_2_14_2384_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1536 128 = 12435361558101799981783154697 := by decide +kernel
private theorem receipt_2_14_2384_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1664 128 = 7504701610319631504893837817 := by decide +kernel
private theorem receipt_2_14_2384_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1792 128 = 2792729147681812030116450852 := by decide +kernel
private theorem receipt_2_14_2384_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1920 15 = 28727283161838095493616770 := by decide +kernel
private theorem receipt_2_14_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 0 256 = 173554684227072666790672212672 :=
  phaseBlock_append receipt_2_14_2384_1_part0 receipt_2_14_2384_1_part1 rfl rfl rfl
private theorem receipt_2_14_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 256 256 = 142652957804183961237772067520 :=
  phaseBlock_append receipt_2_14_2384_1_part2 receipt_2_14_2384_1_part3 rfl rfl rfl
private theorem receipt_2_14_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 0 512 = 316207642031256628028444280192 :=
  phaseBlock_append receipt_2_14_2384_1_join0 receipt_2_14_2384_1_join1 rfl rfl rfl
private theorem receipt_2_14_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 512 256 = 114002170607628145674919912128 :=
  phaseBlock_append receipt_2_14_2384_1_part4 receipt_2_14_2384_1_part5 rfl rfl rfl
private theorem receipt_2_14_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 768 256 = 87502262488555495439355929280 :=
  phaseBlock_append receipt_2_14_2384_1_part6 receipt_2_14_2384_1_part7 rfl rfl rfl
private theorem receipt_2_14_2384_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 512 512 = 201504433096183641114275841408 :=
  phaseBlock_append receipt_2_14_2384_1_join3 receipt_2_14_2384_1_join4 rfl rfl rfl
private theorem receipt_2_14_2384_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 0 1024 = 517712075127440269142720121600 :=
  phaseBlock_append receipt_2_14_2384_1_join2 receipt_2_14_2384_1_join5 rfl rfl rfl
private theorem receipt_2_14_2384_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1024 256 = 63055367007805364551402726080 :=
  phaseBlock_append receipt_2_14_2384_1_part8 receipt_2_14_2384_1_part9 rfl rfl rfl
private theorem receipt_2_14_2384_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1280 256 = 40565808098105343349079349036 :=
  phaseBlock_append receipt_2_14_2384_1_part10 receipt_2_14_2384_1_part11 rfl rfl rfl
private theorem receipt_2_14_2384_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1024 512 = 103621175105910707900482075116 :=
  phaseBlock_append receipt_2_14_2384_1_join7 receipt_2_14_2384_1_join8 rfl rfl rfl
private theorem receipt_2_14_2384_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1536 256 = 19940063168421431486676992514 :=
  phaseBlock_append receipt_2_14_2384_1_part12 receipt_2_14_2384_1_part13 rfl rfl rfl
private theorem receipt_2_14_2384_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1792 143 = 2821456430843650125610067622 :=
  phaseBlock_append receipt_2_14_2384_1_part14 receipt_2_14_2384_1_part15 rfl rfl rfl
private theorem receipt_2_14_2384_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1536 399 = 22761519599265081612287060136 :=
  phaseBlock_append receipt_2_14_2384_1_join10 receipt_2_14_2384_1_join11 rfl rfl rfl
private theorem receipt_2_14_2384_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 1024 911 = 126382694705175789512769135252 :=
  phaseBlock_append receipt_2_14_2384_1_join9 receipt_2_14_2384_1_join12 rfl rfl rfl
private theorem receipt_2_14_2384_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179808 2384 73 1 0 7 1) 0 1935 = 644094769832616058655489256852 :=
  phaseBlock_append receipt_2_14_2384_1_join6 receipt_2_14_2384_1_join13 rfl rfl rfl

private theorem receipt_2_14_2384_1 : fastPhase (bank 2 14).shape 179808 2384 73 1 0 7 1 = 644094769832616058655489256852 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2384_1_join14

theorem receipt_2_14 : Checked (bank 2 14) 73 0 7 := by
  refine checked_from_values (bank 2 14) 73 0 7
    (P3_7_1.checked (bank 2 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_14_2383_0 receipt_2_14_2383_1 receipt_2_14_2384_0 receipt_2_14_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_14_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 0 128 = 21390442925860503048725980704 := by decide +kernel
private theorem receipt_3_14_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 128 128 = 19601512573178500272428758560 := by decide +kernel
private theorem receipt_3_14_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 256 128 = 17862173848159687875211986464 := by decide +kernel
private theorem receipt_3_14_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 384 128 = 16173378145970876904130729504 := by decide +kernel
private theorem receipt_3_14_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 512 128 = 14536071248032212863846000160 := by decide +kernel
private theorem receipt_3_14_2383_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 640 128 = 12951193331450413736896394784 := by decide +kernel
private theorem receipt_3_14_2383_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 768 128 = 11419678978452008003969730080 := by decide +kernel
private theorem receipt_3_14_2383_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 896 128 = 9942457185816572664174679584 := by decide +kernel
private theorem receipt_3_14_2383_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1024 128 = 8520451374309971255312410144 := by decide +kernel
private theorem receipt_3_14_2383_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1152 128 = 7154579398117591874148218400 := by decide +kernel
private theorem receipt_3_14_2383_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1280 128 = 5845753554277585196683167264 := by decide +kernel
private theorem receipt_3_14_2383_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1408 128 = 4594880592114102498425722400 := by decide +kernel
private theorem receipt_3_14_2383_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1536 128 = 3402861722670533674663388704 := by decide +kernel
private theorem receipt_3_14_2383_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1664 128 = 2270592628142745260734346784 := by decide +kernel
private theorem receipt_3_14_2383_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1792 128 = 1198963471312318452299089440 := by decide +kernel
private theorem receipt_3_14_2383_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1920 88 = 234594461964498283148110302 := by decide +kernel
private theorem receipt_3_14_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 0 256 = 40991955499039003321154739264 :=
  phaseBlock_append receipt_3_14_2383_0_part0 receipt_3_14_2383_0_part1 rfl rfl rfl
private theorem receipt_3_14_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 256 256 = 34035551994130564779342715968 :=
  phaseBlock_append receipt_3_14_2383_0_part2 receipt_3_14_2383_0_part3 rfl rfl rfl
private theorem receipt_3_14_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 0 512 = 75027507493169568100497455232 :=
  phaseBlock_append receipt_3_14_2383_0_join0 receipt_3_14_2383_0_join1 rfl rfl rfl
private theorem receipt_3_14_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 512 256 = 27487264579482626600742394944 :=
  phaseBlock_append receipt_3_14_2383_0_part4 receipt_3_14_2383_0_part5 rfl rfl rfl
private theorem receipt_3_14_2383_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 768 256 = 21362136164268580668144409664 :=
  phaseBlock_append receipt_3_14_2383_0_part6 receipt_3_14_2383_0_part7 rfl rfl rfl
private theorem receipt_3_14_2383_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 512 512 = 48849400743751207268886804608 :=
  phaseBlock_append receipt_3_14_2383_0_join3 receipt_3_14_2383_0_join4 rfl rfl rfl
private theorem receipt_3_14_2383_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 0 1024 = 123876908236920775369384259840 :=
  phaseBlock_append receipt_3_14_2383_0_join2 receipt_3_14_2383_0_join5 rfl rfl rfl
private theorem receipt_3_14_2383_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1024 256 = 15675030772427563129460628544 :=
  phaseBlock_append receipt_3_14_2383_0_part8 receipt_3_14_2383_0_part9 rfl rfl rfl
private theorem receipt_3_14_2383_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1280 256 = 10440634146391687695108889664 :=
  phaseBlock_append receipt_3_14_2383_0_part10 receipt_3_14_2383_0_part11 rfl rfl rfl
private theorem receipt_3_14_2383_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1024 512 = 26115664918819250824569518208 :=
  phaseBlock_append receipt_3_14_2383_0_join7 receipt_3_14_2383_0_join8 rfl rfl rfl
private theorem receipt_3_14_2383_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1536 256 = 5673454350813278935397735488 :=
  phaseBlock_append receipt_3_14_2383_0_part12 receipt_3_14_2383_0_part13 rfl rfl rfl
private theorem receipt_3_14_2383_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1792 216 = 1433557933276816735447199742 :=
  phaseBlock_append receipt_3_14_2383_0_part14 receipt_3_14_2383_0_part15 rfl rfl rfl
private theorem receipt_3_14_2383_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1536 472 = 7107012284090095670844935230 :=
  phaseBlock_append receipt_3_14_2383_0_join10 receipt_3_14_2383_0_join11 rfl rfl rfl
private theorem receipt_3_14_2383_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 1024 984 = 33222677202909346495414453438 :=
  phaseBlock_append receipt_3_14_2383_0_join9 receipt_3_14_2383_0_join12 rfl rfl rfl
private theorem receipt_3_14_2383_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 0) 0 2008 = 157099585439830121864798713278 :=
  phaseBlock_append receipt_3_14_2383_0_join6 receipt_3_14_2383_0_join13 rfl rfl rfl

private theorem receipt_3_14_2383_0 : fastPhase (bank 3 14).shape 179808 2383 73 1 1 1 0 = 157099585439830121864798713278 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2383_0_join14

private theorem receipt_3_14_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 0 128 = 21376466516751511756118566752 := by decide +kernel
private theorem receipt_3_14_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 128 128 = 19587903014703776037666649952 := by decide +kernel
private theorem receipt_3_14_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 256 128 = 17848939227293705827907061600 := by decide +kernel
private theorem receipt_3_14_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 384 128 = 16160526503470472237730240352 := by decide +kernel
private theorem receipt_3_14_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 512 128 = 14523610578513225660901058400 := by decide +kernel
private theorem receipt_3_14_2383_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 640 128 = 12939131583464333794330457952 := by decide +kernel
private theorem receipt_3_14_2383_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 768 128 = 11408024054562619658347087712 := by decide +kernel
private theorem receipt_3_14_2383_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 896 128 = 9931216942676599616968939360 := by decide +kernel
private theorem receipt_3_14_2383_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1024 128 = 8509633622737721398174984032 := by decide +kernel
private theorem receipt_3_14_2383_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1152 128 = 7144191903173602114176808800 := by decide +kernel
private theorem receipt_3_14_2383_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1280 128 = 5835804035341266281690253152 := by decide +kernel
private theorem receipt_3_14_2383_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1408 128 = 4585376722960383842207045472 := by decide +kernel
private theorem receipt_3_14_2383_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1536 128 = 3393811131546508182266439520 := by decide +kernel
private theorem receipt_3_14_2383_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1664 128 = 2262002897844314153726850912 := by decide +kernel
private theorem receipt_3_14_2383_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1792 128 = 1190842139260836094037493600 := by decide +kernel
private theorem receipt_3_14_2383_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1920 88 = 229286648899481259603964986 := by decide +kernel
private theorem receipt_3_14_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 0 256 = 40964369531455287793785216704 :=
  phaseBlock_append receipt_3_14_2383_1_part0 receipt_3_14_2383_1_part1 rfl rfl rfl
private theorem receipt_3_14_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 256 256 = 34009465730764178065637301952 :=
  phaseBlock_append receipt_3_14_2383_1_part2 receipt_3_14_2383_1_part3 rfl rfl rfl
private theorem receipt_3_14_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 0 512 = 74973835262219465859422518656 :=
  phaseBlock_append receipt_3_14_2383_1_join0 receipt_3_14_2383_1_join1 rfl rfl rfl
private theorem receipt_3_14_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 512 256 = 27462742161977559455231516352 :=
  phaseBlock_append receipt_3_14_2383_1_part4 receipt_3_14_2383_1_part5 rfl rfl rfl
private theorem receipt_3_14_2383_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 768 256 = 21339240997239219275316027072 :=
  phaseBlock_append receipt_3_14_2383_1_part6 receipt_3_14_2383_1_part7 rfl rfl rfl
private theorem receipt_3_14_2383_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 512 512 = 48801983159216778730547543424 :=
  phaseBlock_append receipt_3_14_2383_1_join3 receipt_3_14_2383_1_join4 rfl rfl rfl
private theorem receipt_3_14_2383_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 0 1024 = 123775818421436244589970062080 :=
  phaseBlock_append receipt_3_14_2383_1_join2 receipt_3_14_2383_1_join5 rfl rfl rfl
private theorem receipt_3_14_2383_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1024 256 = 15653825525911323512351792832 :=
  phaseBlock_append receipt_3_14_2383_1_part8 receipt_3_14_2383_1_part9 rfl rfl rfl
private theorem receipt_3_14_2383_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1280 256 = 10421180758301650123897298624 :=
  phaseBlock_append receipt_3_14_2383_1_part10 receipt_3_14_2383_1_part11 rfl rfl rfl
private theorem receipt_3_14_2383_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1024 512 = 26075006284212973636249091456 :=
  phaseBlock_append receipt_3_14_2383_1_join7 receipt_3_14_2383_1_join8 rfl rfl rfl
private theorem receipt_3_14_2383_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1536 256 = 5655814029390822335993290432 :=
  phaseBlock_append receipt_3_14_2383_1_part12 receipt_3_14_2383_1_part13 rfl rfl rfl
private theorem receipt_3_14_2383_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1792 216 = 1420128788160317353641458586 :=
  phaseBlock_append receipt_3_14_2383_1_part14 receipt_3_14_2383_1_part15 rfl rfl rfl
private theorem receipt_3_14_2383_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1536 472 = 7075942817551139689634749018 :=
  phaseBlock_append receipt_3_14_2383_1_join10 receipt_3_14_2383_1_join11 rfl rfl rfl
private theorem receipt_3_14_2383_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 1024 984 = 33150949101764113325883840474 :=
  phaseBlock_append receipt_3_14_2383_1_join9 receipt_3_14_2383_1_join12 rfl rfl rfl
private theorem receipt_3_14_2383_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2383 73 1 1 1 1) 0 2008 = 156926767523200357915853902554 :=
  phaseBlock_append receipt_3_14_2383_1_join6 receipt_3_14_2383_1_join13 rfl rfl rfl

private theorem receipt_3_14_2383_1 : fastPhase (bank 3 14).shape 179808 2383 73 1 1 1 1 = 156926767523200357915853902554 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2383_1_join14

private theorem receipt_3_14_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 0 128 = 21390633650336180595008011200 := by decide +kernel
private theorem receipt_3_14_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 128 128 = 19601675949670802986248469440 := by decide +kernel
private theorem receipt_3_14_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 256 128 = 17862312460921821850015366080 := by decide +kernel
private theorem receipt_3_14_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 384 128 = 16173494464069489824703151040 := by decide +kernel
private theorem receipt_3_14_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 512 128 = 14536167625904427762542377920 := by decide +kernel
private theorem receipt_3_14_2384_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 640 128 = 12951272009459983140569119680 := by decide +kernel
private theorem receipt_3_14_2384_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 768 128 = 11419742083444588471594384320 := by decide +kernel
private theorem receipt_3_14_2384_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 896 128 = 9942506731674119715173530560 := by decide +kernel
private theorem receipt_3_14_2384_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1024 128 = 8520489262504254688575683520 := by decide +kernel
private theorem receipt_3_14_2384_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1152 128 = 7154607418262831477753150400 := by decide +kernel
private theorem receipt_3_14_2384_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1280 128 = 5845773384682206848310836160 := by decide +kernel
private theorem receipt_3_14_2384_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1408 128 = 4594893800331614656475659200 := by decide +kernel
private theorem receipt_3_14_2384_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1536 128 = 3402869766049524260065967040 := by decide +kernel
private theorem receipt_3_14_2384_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1664 128 = 2270596854375998929460952000 := by decide +kernel
private theorem receipt_3_14_2384_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1792 128 = 1198965118985054258570066880 := by decide +kernel
private theorem receipt_3_14_2384_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1920 88 = 234594690585153311793621780 := by decide +kernel
private theorem receipt_3_14_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 0 256 = 40992309600006983581256480640 :=
  phaseBlock_append receipt_3_14_2384_0_part0 receipt_3_14_2384_0_part1 rfl rfl rfl
private theorem receipt_3_14_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 256 256 = 34035806924991311674718517120 :=
  phaseBlock_append receipt_3_14_2384_0_part2 receipt_3_14_2384_0_part3 rfl rfl rfl
private theorem receipt_3_14_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 0 512 = 75028116524998295255974997760 :=
  phaseBlock_append receipt_3_14_2384_0_join0 receipt_3_14_2384_0_join1 rfl rfl rfl
private theorem receipt_3_14_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 512 256 = 27487439635364410903111497600 :=
  phaseBlock_append receipt_3_14_2384_0_part4 receipt_3_14_2384_0_part5 rfl rfl rfl
private theorem receipt_3_14_2384_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 768 256 = 21362248815118708186767914880 :=
  phaseBlock_append receipt_3_14_2384_0_part6 receipt_3_14_2384_0_part7 rfl rfl rfl
private theorem receipt_3_14_2384_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 512 512 = 48849688450483119089879412480 :=
  phaseBlock_append receipt_3_14_2384_0_join3 receipt_3_14_2384_0_join4 rfl rfl rfl
private theorem receipt_3_14_2384_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 0 1024 = 123877804975481414345854410240 :=
  phaseBlock_append receipt_3_14_2384_0_join2 receipt_3_14_2384_0_join5 rfl rfl rfl
private theorem receipt_3_14_2384_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1024 256 = 15675096680767086166328833920 :=
  phaseBlock_append receipt_3_14_2384_0_part8 receipt_3_14_2384_0_part9 rfl rfl rfl
private theorem receipt_3_14_2384_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1280 256 = 10440667185013821504786495360 :=
  phaseBlock_append receipt_3_14_2384_0_part10 receipt_3_14_2384_0_part11 rfl rfl rfl
private theorem receipt_3_14_2384_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1024 512 = 26115763865780907671115329280 :=
  phaseBlock_append receipt_3_14_2384_0_join7 receipt_3_14_2384_0_join8 rfl rfl rfl
private theorem receipt_3_14_2384_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1536 256 = 5673466620425523189526919040 :=
  phaseBlock_append receipt_3_14_2384_0_part12 receipt_3_14_2384_0_part13 rfl rfl rfl
private theorem receipt_3_14_2384_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1792 216 = 1433559809570207570363688660 :=
  phaseBlock_append receipt_3_14_2384_0_part14 receipt_3_14_2384_0_part15 rfl rfl rfl
private theorem receipt_3_14_2384_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1536 472 = 7107026429995730759890607700 :=
  phaseBlock_append receipt_3_14_2384_0_join10 receipt_3_14_2384_0_join11 rfl rfl rfl
private theorem receipt_3_14_2384_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 1024 984 = 33222790295776638431005936980 :=
  phaseBlock_append receipt_3_14_2384_0_join9 receipt_3_14_2384_0_join12 rfl rfl rfl
private theorem receipt_3_14_2384_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 0) 0 2008 = 157100595271258052776860347220 :=
  phaseBlock_append receipt_3_14_2384_0_join6 receipt_3_14_2384_0_join13 rfl rfl rfl

private theorem receipt_3_14_2384_0 : fastPhase (bank 3 14).shape 179808 2384 73 1 1 1 0 = 157100595271258052776860347220 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2384_0_join14

private theorem receipt_3_14_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 0 128 = 21376657096717878692114825664 := by decide +kernel
private theorem receipt_3_14_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 128 128 = 19588066260239708847253938624 := by decide +kernel
private theorem receipt_3_14_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 256 128 = 17849077722015741798033539520 := by decide +kernel
private theorem receipt_3_14_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 384 128 = 16160642715811970373597372864 := by decide +kernel
private theorem receipt_3_14_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 512 128 = 14523706862281394807196680640 := by decide +kernel
private theorem receipt_3_14_2384_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 640 128 = 12939210178396381147159617984 := by decide +kernel
private theorem receipt_3_14_2384_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 768 128 = 11408087086881019667860668864 := by decide +kernel
private theorem receipt_3_14_2384_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 896 128 = 9931266425643483280690061760 := by decide +kernel
private theorem receipt_3_14_2384_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1024 128 = 8509671457208385945023185344 := by decide +kernel
private theorem receipt_3_14_2384_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1152 128 = 7144219878149141079190004160 := by decide +kernel
private theorem receipt_3_14_2384_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1280 128 = 5835823828520319971444474304 := by decide +kernel
private theorem receipt_3_14_2384_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1408 128 = 4585389901290010190933959104 := by decide +kernel
private theorem receipt_3_14_2384_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1536 128 = 3393819151772173998668644800 := by decide +kernel
private theorem receipt_3_14_2384_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1664 128 = 2262007107059006758490956224 := by decide +kernel
private theorem receipt_3_14_2384_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1792 128 = 1190843775453295348044972480 := by decide +kernel
private theorem receipt_3_14_2384_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1920 88 = 229286872531708503589403172 := by decide +kernel
private theorem receipt_3_14_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 0 256 = 40964723356957587539368764288 :=
  phaseBlock_append receipt_3_14_2384_1_part0 receipt_3_14_2384_1_part1 rfl rfl rfl
private theorem receipt_3_14_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 256 256 = 34009720437827712171630912384 :=
  phaseBlock_append receipt_3_14_2384_1_part2 receipt_3_14_2384_1_part3 rfl rfl rfl
private theorem receipt_3_14_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 0 512 = 74974443794785299710999676672 :=
  phaseBlock_append receipt_3_14_2384_1_join0 receipt_3_14_2384_1_join1 rfl rfl rfl
private theorem receipt_3_14_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 512 256 = 27462917040677775954356298624 :=
  phaseBlock_append receipt_3_14_2384_1_part4 receipt_3_14_2384_1_part5 rfl rfl rfl
private theorem receipt_3_14_2384_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 768 256 = 21339353512524502948550730624 :=
  phaseBlock_append receipt_3_14_2384_1_part6 receipt_3_14_2384_1_part7 rfl rfl rfl
private theorem receipt_3_14_2384_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 512 512 = 48802270553202278902907029248 :=
  phaseBlock_append receipt_3_14_2384_1_join3 receipt_3_14_2384_1_join4 rfl rfl rfl
private theorem receipt_3_14_2384_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 0 1024 = 123776714347987578613906705920 :=
  phaseBlock_append receipt_3_14_2384_1_join2 receipt_3_14_2384_1_join5 rfl rfl rfl
private theorem receipt_3_14_2384_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1024 256 = 15653891335357527024213189504 :=
  phaseBlock_append receipt_3_14_2384_1_part8 receipt_3_14_2384_1_part9 rfl rfl rfl
private theorem receipt_3_14_2384_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1280 256 = 10421213729810330162378433408 :=
  phaseBlock_append receipt_3_14_2384_1_part10 receipt_3_14_2384_1_part11 rfl rfl rfl
private theorem receipt_3_14_2384_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1024 512 = 26075105065167857186591622912 :=
  phaseBlock_append receipt_3_14_2384_1_join7 receipt_3_14_2384_1_join8 rfl rfl rfl
private theorem receipt_3_14_2384_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1536 256 = 5655826258831180757159601024 :=
  phaseBlock_append receipt_3_14_2384_1_part12 receipt_3_14_2384_1_part13 rfl rfl rfl
private theorem receipt_3_14_2384_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1792 216 = 1420130647985003851634375652 :=
  phaseBlock_append receipt_3_14_2384_1_part14 receipt_3_14_2384_1_part15 rfl rfl rfl
private theorem receipt_3_14_2384_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1536 472 = 7075956906816184608793976676 :=
  phaseBlock_append receipt_3_14_2384_1_join10 receipt_3_14_2384_1_join11 rfl rfl rfl
private theorem receipt_3_14_2384_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 1024 984 = 33151061971984041795385599588 :=
  phaseBlock_append receipt_3_14_2384_1_join9 receipt_3_14_2384_1_join12 rfl rfl rfl
private theorem receipt_3_14_2384_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179808 2384 73 1 1 1 1) 0 2008 = 156927776319971620409292305508 :=
  phaseBlock_append receipt_3_14_2384_1_join6 receipt_3_14_2384_1_join13 rfl rfl rfl

private theorem receipt_3_14_2384_1 : fastPhase (bank 3 14).shape 179808 2384 73 1 1 1 1 = 156927776319971620409292305508 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2384_1_join14

theorem receipt_3_14 : Checked (bank 3 14) 73 1 1 := by
  refine checked_from_values (bank 3 14) 73 1 1
    (P3_7_1.checked (bank 3 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_14_2383_0 receipt_3_14_2383_1 receipt_3_14_2384_0 receipt_3_14_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group5_stage i)).shape
      (cutoff h rect (group5_stage i)), ¬ G∣Q :=
  (group5_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group5_avoids

end Lower6960.RescueSource
