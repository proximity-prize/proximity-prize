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

private theorem receipt_0_13_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 0 128 = 22391702351139857918003403840 := by decide +kernel
private theorem receipt_0_13_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 128 128 = 19438741913339331942650043456 := by decide +kernel
private theorem receipt_0_13_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 256 128 = 16624311645020876275069770816 := by decide +kernel
private theorem receipt_0_13_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 384 128 = 13945065954865055036141689920 := by decide +kernel
private theorem receipt_0_13_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 512 128 = 11397667297702284996797422656 := by decide +kernel
private theorem receipt_0_13_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 640 128 = 8978786168220154610398616640 := by decide +kernel
private theorem receipt_0_13_2402_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 768 128 = 6685101331336968470020100556 := by decide +kernel
private theorem receipt_0_13_2402_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 896 128 = 4513303134007916844074408049 := by decide +kernel
private theorem receipt_0_13_2402_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 1024 128 = 2460082850762219520753635415 := by decide +kernel
private theorem receipt_0_13_2402_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 1152 99 = 567780135751726081794481473 := by decide +kernel
private theorem receipt_0_13_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 0 256 = 41830444264479189860653447296 :=
  phaseBlock_append receipt_0_13_2402_0_part0 receipt_0_13_2402_0_part1 rfl rfl rfl
private theorem receipt_0_13_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 384 256 = 25342733252567340032939112576 :=
  phaseBlock_append receipt_0_13_2402_0_part3 receipt_0_13_2402_0_part4 rfl rfl rfl
private theorem receipt_0_13_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 256 384 = 41967044897588216308008883392 :=
  phaseBlock_append receipt_0_13_2402_0_part2 receipt_0_13_2402_0_join1 rfl rfl rfl
private theorem receipt_0_13_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 0 640 = 83797489162067406168662330688 :=
  phaseBlock_append receipt_0_13_2402_0_join0 receipt_0_13_2402_0_join2 rfl rfl rfl
private theorem receipt_0_13_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 640 256 = 15663887499557123080418717196 :=
  phaseBlock_append receipt_0_13_2402_0_part5 receipt_0_13_2402_0_part6 rfl rfl rfl
private theorem receipt_0_13_2402_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 1024 227 = 3027862986513945602548116888 :=
  phaseBlock_append receipt_0_13_2402_0_part8 receipt_0_13_2402_0_part9 rfl rfl rfl
private theorem receipt_0_13_2402_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 896 355 = 7541166120521862446622524937 :=
  phaseBlock_append receipt_0_13_2402_0_part7 receipt_0_13_2402_0_join5 rfl rfl rfl
private theorem receipt_0_13_2402_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 640 611 = 23205053620078985527041242133 :=
  phaseBlock_append receipt_0_13_2402_0_join4 receipt_0_13_2402_0_join6 rfl rfl rfl
private theorem receipt_0_13_2402_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 0) 0 1251 = 107002542782146391695703572821 :=
  phaseBlock_append receipt_0_13_2402_0_join3 receipt_0_13_2402_0_join7 rfl rfl rfl

private theorem receipt_0_13_2402_0 : fastPhase (bank 0 13).shape 179798 2402 44 1 0 1 0 = 107002542782146391695703572821 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2402_0_join8

private theorem receipt_0_13_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 0 128 = 22368397686336733517305232640 := by decide +kernel
private theorem receipt_0_13_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 128 128 = 19416495441895467943474863360 := by decide +kernel
private theorem receipt_0_13_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 256 128 = 16603098055340385213648272640 := by decide +kernel
private theorem receipt_0_13_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 384 128 = 13924859996663443826829188352 := by decide +kernel
private theorem receipt_0_13_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 512 128 = 11378443781958283747113024768 := by decide +kernel
private theorem receipt_0_13_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 640 128 = 8960519967127545436064390400 := by decide +kernel
private theorem receipt_0_13_2402_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 768 128 = 6667767377616312658527710490 := by decide +kernel
private theorem receipt_0_13_2402_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 896 128 = 4496876406833608612381303590 := by decide +kernel
private theorem receipt_0_13_2402_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 1024 128 = 2444538376156260796189158255 := by decide +kernel
private theorem receipt_0_13_2402_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 1152 99 = 556346725995245883480954576 := by decide +kernel
private theorem receipt_0_13_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 0 256 = 41784893128232201460780096000 :=
  phaseBlock_append receipt_0_13_2402_1_part0 receipt_0_13_2402_1_part1 rfl rfl rfl
private theorem receipt_0_13_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 384 256 = 25303303778621727573942213120 :=
  phaseBlock_append receipt_0_13_2402_1_part3 receipt_0_13_2402_1_part4 rfl rfl rfl
private theorem receipt_0_13_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 256 384 = 41906401833962112787590485760 :=
  phaseBlock_append receipt_0_13_2402_1_part2 receipt_0_13_2402_1_join1 rfl rfl rfl
private theorem receipt_0_13_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 0 640 = 83691294962194314248370581760 :=
  phaseBlock_append receipt_0_13_2402_1_join0 receipt_0_13_2402_1_join2 rfl rfl rfl
private theorem receipt_0_13_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 640 256 = 15628287344743858094592100890 :=
  phaseBlock_append receipt_0_13_2402_1_part5 receipt_0_13_2402_1_part6 rfl rfl rfl
private theorem receipt_0_13_2402_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 1024 227 = 3000885102151506679670112831 :=
  phaseBlock_append receipt_0_13_2402_1_part8 receipt_0_13_2402_1_part9 rfl rfl rfl
private theorem receipt_0_13_2402_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 896 355 = 7497761508985115292051416421 :=
  phaseBlock_append receipt_0_13_2402_1_part7 receipt_0_13_2402_1_join5 rfl rfl rfl
private theorem receipt_0_13_2402_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 640 611 = 23126048853728973386643517311 :=
  phaseBlock_append receipt_0_13_2402_1_join4 receipt_0_13_2402_1_join6 rfl rfl rfl
private theorem receipt_0_13_2402_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2402 44 1 0 1 1) 0 1251 = 106817343815923287635014099071 :=
  phaseBlock_append receipt_0_13_2402_1_join3 receipt_0_13_2402_1_join7 rfl rfl rfl

private theorem receipt_0_13_2402_1 : fastPhase (bank 0 13).shape 179798 2402 44 1 0 1 1 = 106817343815923287635014099071 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2402_1_join8

private theorem receipt_0_13_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 0 128 = 22391901782935038233619927264 := by decide +kernel
private theorem receipt_0_13_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 128 128 = 19438904944154924583528268000 := by decide +kernel
private theorem receipt_0_13_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 256 128 = 16624442157667104038344192224 := by decide +kernel
private theorem receipt_0_13_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 384 128 = 13945167716951041770177847520 := by decide +kernel
private theorem receipt_0_13_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 512 128 = 11397743961916166255771177184 := by decide +kernel
private theorem receipt_0_13_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 640 128 = 8978841272608968406549872864 := by decide +kernel
private theorem receipt_0_13_2403_0_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 768 128 = 6685138290141618874558026175 := by decide +kernel
private theorem receipt_0_13_2403_0_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 896 128 = 4513325221120001091792518759 := by decide +kernel
private theorem receipt_0_13_2403_0_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 1024 128 = 2460093304410749770762499622 := by decide +kernel
private theorem receipt_0_13_2403_0_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 1152 99 = 567782228845322616698329434 := by decide +kernel
private theorem receipt_0_13_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 0 256 = 41830806727089962817148195264 :=
  phaseBlock_append receipt_0_13_2403_0_part0 receipt_0_13_2403_0_part1 rfl rfl rfl
private theorem receipt_0_13_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 384 256 = 25342911678867208025949024704 :=
  phaseBlock_append receipt_0_13_2403_0_part3 receipt_0_13_2403_0_part4 rfl rfl rfl
private theorem receipt_0_13_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 256 384 = 41967353836534312064293216928 :=
  phaseBlock_append receipt_0_13_2403_0_part2 receipt_0_13_2403_0_join1 rfl rfl rfl
private theorem receipt_0_13_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 0 640 = 83798160563624274881441412192 :=
  phaseBlock_append receipt_0_13_2403_0_join0 receipt_0_13_2403_0_join2 rfl rfl rfl
private theorem receipt_0_13_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 640 256 = 15663979562750587281107899039 :=
  phaseBlock_append receipt_0_13_2403_0_part5 receipt_0_13_2403_0_part6 rfl rfl rfl
private theorem receipt_0_13_2403_0_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 1024 227 = 3027875533256072387460829056 :=
  phaseBlock_append receipt_0_13_2403_0_part8 receipt_0_13_2403_0_part9 rfl rfl rfl
private theorem receipt_0_13_2403_0_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 896 355 = 7541200754376073479253347815 :=
  phaseBlock_append receipt_0_13_2403_0_part7 receipt_0_13_2403_0_join5 rfl rfl rfl
private theorem receipt_0_13_2403_0_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 640 611 = 23205180317126660760361246854 :=
  phaseBlock_append receipt_0_13_2403_0_join4 receipt_0_13_2403_0_join6 rfl rfl rfl
private theorem receipt_0_13_2403_0_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 0) 0 1251 = 107003340880750935641802659046 :=
  phaseBlock_append receipt_0_13_2403_0_join3 receipt_0_13_2403_0_join7 rfl rfl rfl

private theorem receipt_0_13_2403_0 : fastPhase (bank 0 13).shape 179798 2403 44 1 0 1 0 = 107003340880750935641802659046 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2403_0_join8

private theorem receipt_0_13_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 0 128 = 22368596947825069650345719520 := by decide +kernel
private theorem receipt_0_13_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 128 128 = 19416658317756685880690894560 := by decide +kernel
private theorem receipt_0_13_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 256 128 = 16603228427840414471775377120 := by decide +kernel
private theorem receipt_0_13_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 384 128 = 13924961632868649094813009632 := by decide +kernel
private theorem receipt_0_13_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 512 128 = 11378520334015574235018540768 := by decide +kernel
private theorem receipt_0_13_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 640 128 = 8960574972544264321659578080 := by decide +kernel
private theorem receipt_0_13_2403_1_part6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 768 128 = 6667804250120333074365596340 := by decide +kernel
private theorem receipt_0_13_2403_1_part7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 896 128 = 4496898419923803386359401908 := by decide +kernel
private theorem receipt_0_13_2403_1_part8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 1024 128 = 2444548767524569939495487085 := by decide +kernel
private theorem receipt_0_13_2403_1_part9 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 1152 99 = 556348778616757699374941691 := by decide +kernel
private theorem receipt_0_13_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 0 256 = 41785255265581755531036614080 :=
  phaseBlock_append receipt_0_13_2403_1_part0 receipt_0_13_2403_1_part1 rfl rfl rfl
private theorem receipt_0_13_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 384 256 = 25303481966884223329831550400 :=
  phaseBlock_append receipt_0_13_2403_1_part3 receipt_0_13_2403_1_part4 rfl rfl rfl
private theorem receipt_0_13_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 256 384 = 41906710394724637801606927520 :=
  phaseBlock_append receipt_0_13_2403_1_part2 receipt_0_13_2403_1_join1 rfl rfl rfl
private theorem receipt_0_13_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 0 640 = 83691965660306393332643541600 :=
  phaseBlock_append receipt_0_13_2403_1_join0 receipt_0_13_2403_1_join2 rfl rfl rfl
private theorem receipt_0_13_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 640 256 = 15628379222664597396025174420 :=
  phaseBlock_append receipt_0_13_2403_1_part5 receipt_0_13_2403_1_part6 rfl rfl rfl
private theorem receipt_0_13_2403_1_join5 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 1024 227 = 3000897546141327638870428776 :=
  phaseBlock_append receipt_0_13_2403_1_part8 receipt_0_13_2403_1_part9 rfl rfl rfl
private theorem receipt_0_13_2403_1_join6 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 896 355 = 7497795966065131025229830684 :=
  phaseBlock_append receipt_0_13_2403_1_part7 receipt_0_13_2403_1_join5 rfl rfl rfl
private theorem receipt_0_13_2403_1_join7 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 640 611 = 23126175188729728421255005104 :=
  phaseBlock_append receipt_0_13_2403_1_join4 receipt_0_13_2403_1_join6 rfl rfl rfl
private theorem receipt_0_13_2403_1_join8 :
    phaseBlock (fastLayer (bank 0 13).shape 179798 2403 44 1 0 1 1) 0 1251 = 106818140849036121753898546704 :=
  phaseBlock_append receipt_0_13_2403_1_join3 receipt_0_13_2403_1_join7 rfl rfl rfl

private theorem receipt_0_13_2403_1 : fastPhase (bank 0 13).shape 179798 2403 44 1 0 1 1 = 106818140849036121753898546704 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_0_13_2403_1_join8

theorem receipt_0_13 : Checked (bank 0 13) 44 0 1 := by
  refine checked_from_values (bank 0 13) 44 0 1
    (P3_7_1.checked (bank 0 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_13_2402_0 receipt_0_13_2402_1 receipt_0_13_2403_0 receipt_0_13_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_13_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 0 128 = 20155933372589632099656000000 := by decide +kernel
private theorem receipt_1_13_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 128 128 = 17485462512906347193701687808 := by decide +kernel
private theorem receipt_1_13_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 256 128 = 14943268473841689702345466368 := by decide +kernel
private theorem receipt_1_13_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 384 128 = 12526083082237263129299182080 := by decide +kernel
private theorem receipt_1_13_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 512 128 = 10230653760630862335904178688 := by decide +kernel
private theorem receipt_1_13_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 640 128 = 8053743502085749670641328640 := by decide +kernel
private theorem receipt_1_13_2402_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 768 128 = 5992131057092782766501262267 := by decide +kernel
private theorem receipt_1_13_2402_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 896 128 = 4042613879550569092775376810 := by decide +kernel
private theorem receipt_1_13_2402_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 1024 128 = 2201998560731414179807748919 := by decide +kernel
private theorem receipt_1_13_2402_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 1152 99 = 507915980815787648789497455 := by decide +kernel
private theorem receipt_1_13_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 0 256 = 37641395885495979293357687808 :=
  phaseBlock_append receipt_1_13_2402_0_part0 receipt_1_13_2402_0_part1 rfl rfl rfl
private theorem receipt_1_13_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 384 256 = 22756736842868125465203360768 :=
  phaseBlock_append receipt_1_13_2402_0_part3 receipt_1_13_2402_0_part4 rfl rfl rfl
private theorem receipt_1_13_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 256 384 = 37700005316709815167548827136 :=
  phaseBlock_append receipt_1_13_2402_0_part2 receipt_1_13_2402_0_join1 rfl rfl rfl
private theorem receipt_1_13_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 0 640 = 75341401202205794460906514944 :=
  phaseBlock_append receipt_1_13_2402_0_join0 receipt_1_13_2402_0_join2 rfl rfl rfl
private theorem receipt_1_13_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 640 256 = 14045874559178532437142590907 :=
  phaseBlock_append receipt_1_13_2402_0_part5 receipt_1_13_2402_0_part6 rfl rfl rfl
private theorem receipt_1_13_2402_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 1024 227 = 2709914541547201828597246374 :=
  phaseBlock_append receipt_1_13_2402_0_part8 receipt_1_13_2402_0_part9 rfl rfl rfl
private theorem receipt_1_13_2402_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 896 355 = 6752528421097770921372623184 :=
  phaseBlock_append receipt_1_13_2402_0_part7 receipt_1_13_2402_0_join5 rfl rfl rfl
private theorem receipt_1_13_2402_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 640 611 = 20798402980276303358515214091 :=
  phaseBlock_append receipt_1_13_2402_0_join4 receipt_1_13_2402_0_join6 rfl rfl rfl
private theorem receipt_1_13_2402_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 0) 0 1251 = 96139804182482097819421729035 :=
  phaseBlock_append receipt_1_13_2402_0_join3 receipt_1_13_2402_0_join7 rfl rfl rfl

private theorem receipt_1_13_2402_0 : fastPhase (bank 1 13).shape 179798 2402 44 1 0 2 0 = 96139804182482097819421729035 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2402_0_join8

private theorem receipt_1_13_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 0 128 = 20134844539915893328893692544 := by decide +kernel
private theorem receipt_1_13_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 128 128 = 17465355015321638720931154560 := by decide +kernel
private theorem receipt_1_13_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 256 128 = 14924117535727592321455868544 := by decide +kernel
private theorem receipt_1_13_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 384 128 = 12507864046883722323742608000 := by decide +kernel
private theorem receipt_1_13_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 512 128 = 10213342090043503538852317824 := by decide +kernel
private theorem receipt_1_13_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 640 128 = 8037314776793193525142145664 := by decide +kernel
private theorem receipt_1_13_2402_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 768 128 = 5976560975379201071746503075 := by decide +kernel
private theorem receipt_1_13_2402_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 896 128 = 4027878244686202365616031400 := by decide +kernel
private theorem receipt_1_13_2402_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 1024 128 = 2188073281245847549503182160 := by decide +kernel
private theorem receipt_1_13_2402_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 1152 99 = 497686202211946057671296271 := by decide +kernel
private theorem receipt_1_13_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 0 256 = 37600199555237532049824847104 :=
  phaseBlock_append receipt_1_13_2402_1_part0 receipt_1_13_2402_1_part1 rfl rfl rfl
private theorem receipt_1_13_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 384 256 = 22721206136927225862594925824 :=
  phaseBlock_append receipt_1_13_2402_1_part3 receipt_1_13_2402_1_part4 rfl rfl rfl
private theorem receipt_1_13_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 256 384 = 37645323672654818184050794368 :=
  phaseBlock_append receipt_1_13_2402_1_part2 receipt_1_13_2402_1_join1 rfl rfl rfl
private theorem receipt_1_13_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 0 640 = 75245523227892350233875641472 :=
  phaseBlock_append receipt_1_13_2402_1_join0 receipt_1_13_2402_1_join2 rfl rfl rfl
private theorem receipt_1_13_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 640 256 = 14013875752172394596888648739 :=
  phaseBlock_append receipt_1_13_2402_1_part5 receipt_1_13_2402_1_part6 rfl rfl rfl
private theorem receipt_1_13_2402_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 1024 227 = 2685759483457793607174478431 :=
  phaseBlock_append receipt_1_13_2402_1_part8 receipt_1_13_2402_1_part9 rfl rfl rfl
private theorem receipt_1_13_2402_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 896 355 = 6713637728143995972790509831 :=
  phaseBlock_append receipt_1_13_2402_1_part7 receipt_1_13_2402_1_join5 rfl rfl rfl
private theorem receipt_1_13_2402_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 640 611 = 20727513480316390569679158570 :=
  phaseBlock_append receipt_1_13_2402_1_join4 receipt_1_13_2402_1_join6 rfl rfl rfl
private theorem receipt_1_13_2402_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2402 44 1 0 2 1) 0 1251 = 95973036708208740803554800042 :=
  phaseBlock_append receipt_1_13_2402_1_join3 receipt_1_13_2402_1_join7 rfl rfl rfl

private theorem receipt_1_13_2402_1 : fastPhase (bank 1 13).shape 179798 2402 44 1 0 2 1 = 95973036708208740803554800042 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2402_1_join8

private theorem receipt_1_13_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 0 128 = 20156112892105856882475962400 := by decide +kernel
private theorem receipt_1_13_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 128 128 = 17485609162303930673959559200 := by decide +kernel
private theorem receipt_1_13_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 256 128 = 14943385789586174270347030560 := by decide +kernel
private theorem receipt_1_13_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 384 128 = 12526174489918522719247269920 := by decide +kernel
private theorem receipt_1_13_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 512 128 = 10230722575503833723223789600 := by decide +kernel
private theorem receipt_1_13_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 640 128 = 8053792929610284160002531360 := by decide +kernel
private theorem receipt_1_13_2403_0_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 768 128 = 5992164185009082018570533563 := by decide +kernel
private theorem receipt_1_13_2403_0_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 896 128 = 4042633663367127491045095271 := by decide +kernel
private theorem receipt_1_13_2403_0_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 1024 128 = 2202007917783938672242856742 := by decide +kernel
private theorem receipt_1_13_2403_0_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 1152 99 = 507917853231510276902285472 := by decide +kernel
private theorem receipt_1_13_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 0 256 = 37641722054409787556435521600 :=
  phaseBlock_append receipt_1_13_2403_0_part0 receipt_1_13_2403_0_part1 rfl rfl rfl
private theorem receipt_1_13_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 384 256 = 22756897065422356442471059520 :=
  phaseBlock_append receipt_1_13_2403_0_part3 receipt_1_13_2403_0_part4 rfl rfl rfl
private theorem receipt_1_13_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 256 384 = 37700282855008530712818090080 :=
  phaseBlock_append receipt_1_13_2403_0_part2 receipt_1_13_2403_0_join1 rfl rfl rfl
private theorem receipt_1_13_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 0 640 = 75342004909418318269253611680 :=
  phaseBlock_append receipt_1_13_2403_0_join0 receipt_1_13_2403_0_join2 rfl rfl rfl
private theorem receipt_1_13_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 640 256 = 14045957114619366178573064923 :=
  phaseBlock_append receipt_1_13_2403_0_part5 receipt_1_13_2403_0_part6 rfl rfl rfl
private theorem receipt_1_13_2403_0_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 1024 227 = 2709925771015448949145142214 :=
  phaseBlock_append receipt_1_13_2403_0_part8 receipt_1_13_2403_0_part9 rfl rfl rfl
private theorem receipt_1_13_2403_0_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 896 355 = 6752559434382576440190237485 :=
  phaseBlock_append receipt_1_13_2403_0_part7 receipt_1_13_2403_0_join5 rfl rfl rfl
private theorem receipt_1_13_2403_0_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 640 611 = 20798516549001942618763302408 :=
  phaseBlock_append receipt_1_13_2403_0_join4 receipt_1_13_2403_0_join6 rfl rfl rfl
private theorem receipt_1_13_2403_0_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 0) 0 1251 = 96140521458420260888016914088 :=
  phaseBlock_append receipt_1_13_2403_0_join3 receipt_1_13_2403_0_join7 rfl rfl rfl

private theorem receipt_1_13_2403_0 : fastPhase (bank 1 13).shape 179798 2403 44 1 0 2 0 = 96140521458420260888016914088 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2403_0_join8

private theorem receipt_1_13_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 0 128 = 20135023905139852752829189344 := by decide +kernel
private theorem receipt_1_13_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 128 128 = 17465501524525710758376897760 := by decide +kernel
private theorem receipt_1_13_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 256 128 = 14924234724849344055481298144 := by decide +kernel
private theorem receipt_1_13_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 384 128 = 12507955340988018568943820000 := by decide +kernel
private theorem receipt_1_13_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 512 128 = 10213410803863232915996953824 := by decide +kernel
private theorem receipt_1_13_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 640 128 = 8037364115269114926512061664 := by decide +kernel
private theorem receipt_1_13_2403_1_part6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 768 128 = 5976594025757943771881233170 := by decide +kernel
private theorem receipt_1_13_2403_1_part7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 896 128 = 4027897962092109771407480816 := by decide +kernel
private theorem receipt_1_13_2403_1_part8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 1024 128 = 2188082582502190630420243335 := by decide +kernel
private theorem receipt_1_13_2403_1_part9 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 1152 99 = 497688038415597201248058123 := by decide +kernel
private theorem receipt_1_13_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 0 256 = 37600525429665563511206087104 :=
  phaseBlock_append receipt_1_13_2403_1_part0 receipt_1_13_2403_1_part1 rfl rfl rfl
private theorem receipt_1_13_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 384 256 = 22721366144851251484940773824 :=
  phaseBlock_append receipt_1_13_2403_1_part3 receipt_1_13_2403_1_part4 rfl rfl rfl
private theorem receipt_1_13_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 256 384 = 37645600869700595540422071968 :=
  phaseBlock_append receipt_1_13_2403_1_part2 receipt_1_13_2403_1_join1 rfl rfl rfl
private theorem receipt_1_13_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 0 640 = 75246126299366159051628159072 :=
  phaseBlock_append receipt_1_13_2403_1_join0 receipt_1_13_2403_1_join2 rfl rfl rfl
private theorem receipt_1_13_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 640 256 = 14013958141027058698393294834 :=
  phaseBlock_append receipt_1_13_2403_1_part5 receipt_1_13_2403_1_part6 rfl rfl rfl
private theorem receipt_1_13_2403_1_join5 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 1024 227 = 2685770620917787831668301458 :=
  phaseBlock_append receipt_1_13_2403_1_part8 receipt_1_13_2403_1_part9 rfl rfl rfl
private theorem receipt_1_13_2403_1_join6 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 896 355 = 6713668583009897603075782274 :=
  phaseBlock_append receipt_1_13_2403_1_part7 receipt_1_13_2403_1_join5 rfl rfl rfl
private theorem receipt_1_13_2403_1_join7 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 640 611 = 20727626724036956301469077108 :=
  phaseBlock_append receipt_1_13_2403_1_join4 receipt_1_13_2403_1_join6 rfl rfl rfl
private theorem receipt_1_13_2403_1_join8 :
    phaseBlock (fastLayer (bank 1 13).shape 179798 2403 44 1 0 2 1) 0 1251 = 95973753023403115353097236180 :=
  phaseBlock_append receipt_1_13_2403_1_join3 receipt_1_13_2403_1_join7 rfl rfl rfl

private theorem receipt_1_13_2403_1 : fastPhase (bank 1 13).shape 179798 2403 44 1 0 2 1 = 95973753023403115353097236180 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_1_13_2403_1_join8

theorem receipt_1_13 : Checked (bank 1 13) 44 0 2 := by
  refine checked_from_values (bank 1 13) 44 0 2
    (P3_7_1.checked (bank 1 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_13_2402_0 receipt_1_13_2402_1 receipt_1_13_2403_0 receipt_1_13_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_13_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 0 128 = 10802269371708877880176298880 := by decide +kernel
private theorem receipt_2_13_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 128 128 = 9323498188149539080627153792 := by decide +kernel
private theorem receipt_2_13_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 256 128 = 7927369160245952184527981440 := by decide +kernel
private theorem receipt_2_13_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 384 128 = 6611085848176057369650867072 := by decide +kernel
private theorem receipt_2_13_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 512 128 = 5371897816201930317042600832 := by decide +kernel
private theorem receipt_2_13_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 640 128 = 4207100324328414797522561920 := by decide +kernel
private theorem receipt_2_13_2402_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 768 128 = 3114034129942039403564021500 := by decide +kernel
private theorem receipt_2_13_2402_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 896 128 = 2090086712156326256488122561 := by decide +kernel
private theorem receipt_2_13_2402_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 1024 128 = 1132687018668806276452631099 := by decide +kernel
private theorem receipt_2_13_2402_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 1152 99 = 260135833788480997479215929 := by decide +kernel
private theorem receipt_2_13_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 0 256 = 20125767559858416960803452672 :=
  phaseBlock_append receipt_2_13_2402_0_part0 receipt_2_13_2402_0_part1 rfl rfl rfl
private theorem receipt_2_13_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 384 256 = 11982983664377987686693467904 :=
  phaseBlock_append receipt_2_13_2402_0_part3 receipt_2_13_2402_0_part4 rfl rfl rfl
private theorem receipt_2_13_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 256 384 = 19910352824623939871221449344 :=
  phaseBlock_append receipt_2_13_2402_0_part2 receipt_2_13_2402_0_join1 rfl rfl rfl
private theorem receipt_2_13_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 0 640 = 40036120384482356832024902016 :=
  phaseBlock_append receipt_2_13_2402_0_join0 receipt_2_13_2402_0_join2 rfl rfl rfl
private theorem receipt_2_13_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 640 256 = 7321134454270454201086583420 :=
  phaseBlock_append receipt_2_13_2402_0_part5 receipt_2_13_2402_0_part6 rfl rfl rfl
private theorem receipt_2_13_2402_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 1024 227 = 1392822852457287273931847028 :=
  phaseBlock_append receipt_2_13_2402_0_part8 receipt_2_13_2402_0_part9 rfl rfl rfl
private theorem receipt_2_13_2402_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 896 355 = 3482909564613613530419969589 :=
  phaseBlock_append receipt_2_13_2402_0_part7 receipt_2_13_2402_0_join5 rfl rfl rfl
private theorem receipt_2_13_2402_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 640 611 = 10804044018884067731506553009 :=
  phaseBlock_append receipt_2_13_2402_0_join4 receipt_2_13_2402_0_join6 rfl rfl rfl
private theorem receipt_2_13_2402_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 0) 0 1251 = 50840164403366424563531455025 :=
  phaseBlock_append receipt_2_13_2402_0_join3 receipt_2_13_2402_0_join7 rfl rfl rfl

private theorem receipt_2_13_2402_0 : fastPhase (bank 2 13).shape 179798 2402 44 1 0 7 0 = 50840164403366424563531455025 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2402_0_join8

private theorem receipt_2_13_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 0 128 = 10790538849906659819178992064 := by decide +kernel
private theorem receipt_2_13_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 128 128 = 9312405623953846005945246144 := by decide +kernel
private theorem receipt_2_13_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 256 128 = 7916893144379059897528525248 := by decide +kernel
private theorem receipt_2_13_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 384 128 = 6601205323372614734660673984 := by decide +kernel
private theorem receipt_2_13_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 512 128 = 5362592074848571198267498944 := by decide +kernel
private theorem receipt_2_13_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 640 128 = 4198349006103369995966652864 := by decide +kernel
private theorem receipt_2_13_2402_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 768 128 = 3105817219152216719075865144 := by decide +kernel
private theorem receipt_2_13_2402_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 896 128 = 2082384528818984998883608488 := by decide +kernel
private theorem receipt_2_13_2402_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 1024 128 = 1125480216658254667974700647 := by decide +kernel
private theorem receipt_2_13_2402_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 1152 99 = 254889502351877034789398458 := by decide +kernel
private theorem receipt_2_13_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 0 256 = 20102944473860505825124238208 :=
  phaseBlock_append receipt_2_13_2402_1_part0 receipt_2_13_2402_1_part1 rfl rfl rfl
private theorem receipt_2_13_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 384 256 = 11963797398221185932928172928 :=
  phaseBlock_append receipt_2_13_2402_1_part3 receipt_2_13_2402_1_part4 rfl rfl rfl
private theorem receipt_2_13_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 256 384 = 19880690542600245830456698176 :=
  phaseBlock_append receipt_2_13_2402_1_part2 receipt_2_13_2402_1_join1 rfl rfl rfl
private theorem receipt_2_13_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 0 640 = 39983635016460751655580936384 :=
  phaseBlock_append receipt_2_13_2402_1_join0 receipt_2_13_2402_1_join2 rfl rfl rfl
private theorem receipt_2_13_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 640 256 = 7304166225255586715042518008 :=
  phaseBlock_append receipt_2_13_2402_1_part5 receipt_2_13_2402_1_part6 rfl rfl rfl
private theorem receipt_2_13_2402_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 1024 227 = 1380369719010131702764099105 :=
  phaseBlock_append receipt_2_13_2402_1_part8 receipt_2_13_2402_1_part9 rfl rfl rfl
private theorem receipt_2_13_2402_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 896 355 = 3462754247829116701647707593 :=
  phaseBlock_append receipt_2_13_2402_1_part7 receipt_2_13_2402_1_join5 rfl rfl rfl
private theorem receipt_2_13_2402_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 640 611 = 10766920473084703416690225601 :=
  phaseBlock_append receipt_2_13_2402_1_join4 receipt_2_13_2402_1_join6 rfl rfl rfl
private theorem receipt_2_13_2402_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2402 44 1 0 7 1) 0 1251 = 50750555489545455072271161985 :=
  phaseBlock_append receipt_2_13_2402_1_join3 receipt_2_13_2402_1_join7 rfl rfl rfl

private theorem receipt_2_13_2402_1 : fastPhase (bank 2 13).shape 179798 2402 44 1 0 7 1 = 50750555489545455072271161985 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2402_1_join8

private theorem receipt_2_13_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 0 128 = 10802365584834860166813524448 := by decide +kernel
private theorem receipt_2_13_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 128 128 = 9323576385794499925296746976 := by decide +kernel
private theorem receipt_2_13_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 256 128 = 7927431397819092670401937888 := by decide +kernel
private theorem receipt_2_13_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 384 128 = 6611134093423732795551707616 := by decide +kernel
private theorem receipt_2_13_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 512 128 = 5371933950762968390603301344 := by decide +kernel
private theorem receipt_2_13_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 640 128 = 4207126145278658614394278368 := by decide +kernel
private theorem receipt_2_13_2403_0_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 768 128 = 3114051346937874012213984101 := by decide +kernel
private theorem receipt_2_13_2403_0_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 896 128 = 2090096941245111841610317205 := by decide +kernel
private theorem receipt_2_13_2403_0_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 1024 128 = 1132691832163456552424539328 := by decide +kernel
private theorem receipt_2_13_2403_0_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 1152 99 = 260136792802489983140257496 := by decide +kernel
private theorem receipt_2_13_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 0 256 = 20125941970629360092110271424 :=
  phaseBlock_append receipt_2_13_2403_0_part0 receipt_2_13_2403_0_part1 rfl rfl rfl
private theorem receipt_2_13_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 384 256 = 11983068044186701186155008960 :=
  phaseBlock_append receipt_2_13_2403_0_part3 receipt_2_13_2403_0_part4 rfl rfl rfl
private theorem receipt_2_13_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 256 384 = 19910499442005793856556946848 :=
  phaseBlock_append receipt_2_13_2403_0_part2 receipt_2_13_2403_0_join1 rfl rfl rfl
private theorem receipt_2_13_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 0 640 = 40036441412635153948667218272 :=
  phaseBlock_append receipt_2_13_2403_0_join0 receipt_2_13_2403_0_join2 rfl rfl rfl
private theorem receipt_2_13_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 640 256 = 7321177492216532626608262469 :=
  phaseBlock_append receipt_2_13_2403_0_part5 receipt_2_13_2403_0_part6 rfl rfl rfl
private theorem receipt_2_13_2403_0_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 1024 227 = 1392828624965946535564796824 :=
  phaseBlock_append receipt_2_13_2403_0_part8 receipt_2_13_2403_0_part9 rfl rfl rfl
private theorem receipt_2_13_2403_0_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 896 355 = 3482925566211058377175114029 :=
  phaseBlock_append receipt_2_13_2403_0_part7 receipt_2_13_2403_0_join5 rfl rfl rfl
private theorem receipt_2_13_2403_0_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 640 611 = 10804103058427591003783376498 :=
  phaseBlock_append receipt_2_13_2403_0_join4 receipt_2_13_2403_0_join6 rfl rfl rfl
private theorem receipt_2_13_2403_0_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 0) 0 1251 = 50840544471062744952450594770 :=
  phaseBlock_append receipt_2_13_2403_0_join3 receipt_2_13_2403_0_join7 rfl rfl rfl

private theorem receipt_2_13_2403_0 : fastPhase (bank 2 13).shape 179798 2403 44 1 0 7 0 = 50840544471062744952450594770 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2403_0_join8

private theorem receipt_2_13_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 0 128 = 10790634976524518945369661024 := by decide +kernel
private theorem receipt_2_13_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 128 128 = 9312483743731532414657760864 := by decide +kernel
private theorem receipt_2_13_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 256 128 = 7916955312291722856811167328 := by decide +kernel
private theorem receipt_2_13_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 384 128 = 6601253506741174400586280544 := by decide +kernel
private theorem receipt_2_13_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 512 128 = 5362628154894972830260551264 := by decide +kernel
private theorem receipt_2_13_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 640 128 = 4198374779495062958178160224 := by decide +kernel
private theorem receipt_2_13_2403_1_part6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 768 128 = 3105834395157502498816958274 := by decide +kernel
private theorem receipt_2_13_2403_1_part7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 896 128 = 2082394723160874616343439484 := by decide +kernel
private theorem receipt_2_13_2403_1_part8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 1024 128 = 1125485001263627411440427951 := by decide +kernel
private theorem receipt_2_13_2403_1_part9 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 1152 99 = 254890442792252797051405147 := by decide +kernel
private theorem receipt_2_13_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 0 256 = 20103118720256051360027421888 :=
  phaseBlock_append receipt_2_13_2403_1_part0 receipt_2_13_2403_1_part1 rfl rfl rfl
private theorem receipt_2_13_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 384 256 = 11963881661636147230846831808 :=
  phaseBlock_append receipt_2_13_2403_1_part3 receipt_2_13_2403_1_part4 rfl rfl rfl
private theorem receipt_2_13_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 256 384 = 19880836973927870087657999136 :=
  phaseBlock_append receipt_2_13_2403_1_part2 receipt_2_13_2403_1_join1 rfl rfl rfl
private theorem receipt_2_13_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 0 640 = 39983955694183921447685421024 :=
  phaseBlock_append receipt_2_13_2403_1_join0 receipt_2_13_2403_1_join2 rfl rfl rfl
private theorem receipt_2_13_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 640 256 = 7304209174652565456995118498 :=
  phaseBlock_append receipt_2_13_2403_1_part5 receipt_2_13_2403_1_part6 rfl rfl rfl
private theorem receipt_2_13_2403_1_join5 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 1024 227 = 1380375444055880208491833098 :=
  phaseBlock_append receipt_2_13_2403_1_part8 receipt_2_13_2403_1_part9 rfl rfl rfl
private theorem receipt_2_13_2403_1_join6 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 896 355 = 3462770167216754824835272582 :=
  phaseBlock_append receipt_2_13_2403_1_part7 receipt_2_13_2403_1_join5 rfl rfl rfl
private theorem receipt_2_13_2403_1_join7 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 640 611 = 10766979341869320281830391080 :=
  phaseBlock_append receipt_2_13_2403_1_join4 receipt_2_13_2403_1_join6 rfl rfl rfl
private theorem receipt_2_13_2403_1_join8 :
    phaseBlock (fastLayer (bank 2 13).shape 179798 2403 44 1 0 7 1) 0 1251 = 50750935036053241729515812104 :=
  phaseBlock_append receipt_2_13_2403_1_join3 receipt_2_13_2403_1_join7 rfl rfl rfl

private theorem receipt_2_13_2403_1 : fastPhase (bank 2 13).shape 179798 2403 44 1 0 7 1 = 50750935036053241729515812104 :=
  phase_of_block (n := 1251) (by decide +kernel) receipt_2_13_2403_1_join8

theorem receipt_2_13 : Checked (bank 2 13) 44 0 7 := by
  refine checked_from_values (bank 2 13) 44 0 7
    (P3_7_1.checked (bank 2 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1250)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_13_2402_0 receipt_2_13_2402_1 receipt_2_13_2403_0 receipt_2_13_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_13_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 0 128 = 2435940240937153061951579168 := by decide +kernel
private theorem receipt_3_13_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 128 128 = 2118345127389895643075728416 := by decide +kernel
private theorem receipt_3_13_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 256 128 = 1814786554637262004425163808 := by decide +kernel
private theorem receipt_3_13_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 384 128 = 1525672704368307074287186976 := by decide +kernel
private theorem receipt_3_13_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 512 128 = 1251408083880772926879818784 := by decide +kernel
private theorem receipt_3_13_2402_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 640 128 = 992393535497614225881240608 := by decide +kernel
private theorem receipt_3_13_2402_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 768 128 = 749026245983523667959235616 := by decide +kernel
private theorem receipt_3_13_2402_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 896 128 = 521699755961457426300630048 := by decide +kernel
private theorem receipt_3_13_2402_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 1024 128 = 310803969329160594140734496 := by decide +kernel
private theorem receipt_3_13_2402_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 1152 128 = 116725162675692628292785184 := by decide +kernel
private theorem receipt_3_13_2402_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 1280 18 = 1828910658475285063389615 := by decide +kernel
private theorem receipt_3_13_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 0 256 = 4554285368327048705027307584 :=
  phaseBlock_append receipt_3_13_2402_0_part0 receipt_3_13_2402_0_part1 rfl rfl rfl
private theorem receipt_3_13_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 384 256 = 2777080788249080001167005760 :=
  phaseBlock_append receipt_3_13_2402_0_part3 receipt_3_13_2402_0_part4 rfl rfl rfl
private theorem receipt_3_13_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 256 384 = 4591867342886342005592169568 :=
  phaseBlock_append receipt_3_13_2402_0_part2 receipt_3_13_2402_0_join1 rfl rfl rfl
private theorem receipt_3_13_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 0 640 = 9146152711213390710619477152 :=
  phaseBlock_append receipt_3_13_2402_0_join0 receipt_3_13_2402_0_join2 rfl rfl rfl
private theorem receipt_3_13_2402_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 768 256 = 1270726001944981094259865664 :=
  phaseBlock_append receipt_3_13_2402_0_part6 receipt_3_13_2402_0_part7 rfl rfl rfl
private theorem receipt_3_13_2402_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 640 384 = 2263119537442595320141106272 :=
  phaseBlock_append receipt_3_13_2402_0_part5 receipt_3_13_2402_0_join4 rfl rfl rfl
private theorem receipt_3_13_2402_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 1152 146 = 118554073334167913356174799 :=
  phaseBlock_append receipt_3_13_2402_0_part9 receipt_3_13_2402_0_part10 rfl rfl rfl
private theorem receipt_3_13_2402_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 1024 274 = 429358042663328507496909295 :=
  phaseBlock_append receipt_3_13_2402_0_part8 receipt_3_13_2402_0_join6 rfl rfl rfl
private theorem receipt_3_13_2402_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 640 658 = 2692477580105923827638015567 :=
  phaseBlock_append receipt_3_13_2402_0_join5 receipt_3_13_2402_0_join7 rfl rfl rfl
private theorem receipt_3_13_2402_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 0) 0 1298 = 11838630291319314538257492719 :=
  phaseBlock_append receipt_3_13_2402_0_join3 receipt_3_13_2402_0_join8 rfl rfl rfl

private theorem receipt_3_13_2402_0 : fastPhase (bank 3 13).shape 179798 2402 44 1 1 1 0 = 11838630291319314538257492719 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2402_0_join9

private theorem receipt_3_13_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 0 128 = 2433439243117126238741457952 := by decide +kernel
private theorem receipt_3_13_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 128 128 = 2115947551426195514872282144 := by decide +kernel
private theorem receipt_3_13_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 256 128 = 1812495877607013715928648736 := by decide +kernel
private theorem receipt_3_13_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 384 128 = 1523492373070083195497569312 := by decide +kernel
private theorem receipt_3_13_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 512 128 = 1249341514911131213420506144 := by decide +kernel
private theorem receipt_3_13_2402_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 640 128 = 990444115327635379322813472 := by decide +kernel
private theorem receipt_3_13_2402_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 768 128 = 747197331035349096143178784 := by decide +kernel
private theorem receipt_3_13_2402_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 896 128 = 519994672684827003663064096 := by decide +kernel
private theorem receipt_3_13_2402_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 1024 128 = 309226014277950422036147232 := by decide +kernel
private theorem receipt_3_13_2402_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 1152 128 = 115277602584452795317763104 := by decide +kernel
private theorem receipt_3_13_2402_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 1280 18 = 1635990827665838071654950 := by decide +kernel
private theorem receipt_3_13_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 0 256 = 4549386794543321753613740096 :=
  phaseBlock_append receipt_3_13_2402_1_part0 receipt_3_13_2402_1_part1 rfl rfl rfl
private theorem receipt_3_13_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 384 256 = 2772833887981214408918075456 :=
  phaseBlock_append receipt_3_13_2402_1_part3 receipt_3_13_2402_1_part4 rfl rfl rfl
private theorem receipt_3_13_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 256 384 = 4585329765588228124846724192 :=
  phaseBlock_append receipt_3_13_2402_1_part2 receipt_3_13_2402_1_join1 rfl rfl rfl
private theorem receipt_3_13_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 0 640 = 9134716560131549878460464288 :=
  phaseBlock_append receipt_3_13_2402_1_join0 receipt_3_13_2402_1_join2 rfl rfl rfl
private theorem receipt_3_13_2402_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 768 256 = 1267192003720176099806242880 :=
  phaseBlock_append receipt_3_13_2402_1_part6 receipt_3_13_2402_1_part7 rfl rfl rfl
private theorem receipt_3_13_2402_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 640 384 = 2257636119047811479129056352 :=
  phaseBlock_append receipt_3_13_2402_1_part5 receipt_3_13_2402_1_join4 rfl rfl rfl
private theorem receipt_3_13_2402_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 1152 146 = 116913593412118633389418054 :=
  phaseBlock_append receipt_3_13_2402_1_part9 receipt_3_13_2402_1_part10 rfl rfl rfl
private theorem receipt_3_13_2402_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 1024 274 = 426139607690069055425565286 :=
  phaseBlock_append receipt_3_13_2402_1_part8 receipt_3_13_2402_1_join6 rfl rfl rfl
private theorem receipt_3_13_2402_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 640 658 = 2683775726737880534554621638 :=
  phaseBlock_append receipt_3_13_2402_1_join5 receipt_3_13_2402_1_join7 rfl rfl rfl
private theorem receipt_3_13_2402_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2402 44 1 1 1 1) 0 1298 = 11818492286869430413015085926 :=
  phaseBlock_append receipt_3_13_2402_1_join3 receipt_3_13_2402_1_join8 rfl rfl rfl

private theorem receipt_3_13_2402_1 : fastPhase (bank 3 13).shape 179798 2402 44 1 1 1 1 = 11818492286869430413015085926 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2402_1_join9

private theorem receipt_3_13_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 0 128 = 2435961633803770234792102688 := by decide +kernel
private theorem receipt_3_13_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 128 128 = 2118361838489404101376572192 := by decide +kernel
private theorem receipt_3_13_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 256 128 = 1814799278499347973012073248 := by decide +kernel
private theorem receipt_3_13_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 384 128 = 1525682086152308477361969952 := by decide +kernel
private theorem receipt_3_13_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 512 128 = 1251414719740651827500124960 := by decide +kernel
private theorem receipt_3_13_2403_0_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 640 128 = 992397972946049656138119968 := by decide +kernel
private theorem receipt_3_13_2403_0_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 768 128 = 749028984255124849852476192 := by decide +kernel
private theorem receipt_3_13_2403_0_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 896 128 = 521701246375097383311874848 := by decide +kernel
private theorem receipt_3_13_2403_0_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 1024 128 = 310804615649430153504377632 := by decide +kernel
private theorem receipt_3_13_2403_0_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 1152 128 = 116725321473474813964647200 := by decide +kernel
private theorem receipt_3_13_2403_0_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 1280 18 = 1828912188109348135450743 := by decide +kernel
private theorem receipt_3_13_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 0 256 = 4554323472293174336168674880 :=
  phaseBlock_append receipt_3_13_2403_0_part0 receipt_3_13_2403_0_part1 rfl rfl rfl
private theorem receipt_3_13_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 384 256 = 2777096805892960304862094912 :=
  phaseBlock_append receipt_3_13_2403_0_part3 receipt_3_13_2403_0_part4 rfl rfl rfl
private theorem receipt_3_13_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 256 384 = 4591896084392308277874168160 :=
  phaseBlock_append receipt_3_13_2403_0_part2 receipt_3_13_2403_0_join1 rfl rfl rfl
private theorem receipt_3_13_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 0 640 = 9146219556685482614042843040 :=
  phaseBlock_append receipt_3_13_2403_0_join0 receipt_3_13_2403_0_join2 rfl rfl rfl
private theorem receipt_3_13_2403_0_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 768 256 = 1270730230630222233164351040 :=
  phaseBlock_append receipt_3_13_2403_0_part6 receipt_3_13_2403_0_part7 rfl rfl rfl
private theorem receipt_3_13_2403_0_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 640 384 = 2263128203576271889302471008 :=
  phaseBlock_append receipt_3_13_2403_0_part5 receipt_3_13_2403_0_join4 rfl rfl rfl
private theorem receipt_3_13_2403_0_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 1152 146 = 118554233661584162100097943 :=
  phaseBlock_append receipt_3_13_2403_0_part9 receipt_3_13_2403_0_part10 rfl rfl rfl
private theorem receipt_3_13_2403_0_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 1024 274 = 429358849311014315604475575 :=
  phaseBlock_append receipt_3_13_2403_0_part8 receipt_3_13_2403_0_join6 rfl rfl rfl
private theorem receipt_3_13_2403_0_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 640 658 = 2692487052887286204906946583 :=
  phaseBlock_append receipt_3_13_2403_0_join5 receipt_3_13_2403_0_join7 rfl rfl rfl
private theorem receipt_3_13_2403_0_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 0) 0 1298 = 11838706609572768818949789623 :=
  phaseBlock_append receipt_3_13_2403_0_join3 receipt_3_13_2403_0_join8 rfl rfl rfl

private theorem receipt_3_13_2403_0 : fastPhase (bank 3 13).shape 179798 2403 44 1 1 1 0 = 11838706609572768818949789623 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2403_0_join9

private theorem receipt_3_13_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 0 128 = 2433460610558815650394959584 := by decide +kernel
private theorem receipt_3_13_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 128 128 = 2115964240784380338216148704 := by decide +kernel
private theorem receipt_3_13_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 256 128 = 1812508583138284377208835808 := by decide +kernel
private theorem receipt_3_13_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 384 128 = 1523501739662897161783017184 := by decide +kernel
private theorem receipt_3_13_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 512 128 = 1249348138450779797085826784 := by decide +kernel
private theorem receipt_3_13_2403_1_part5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 640 128 = 990448543060330933228756704 := by decide +kernel
private theorem receipt_3_13_2403_1_part6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 768 128 = 747200061931432599514877664 := by decide +kernel
private theorem receipt_3_13_2403_1_part7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 896 128 = 519996157801096038666059488 := by decide +kernel
private theorem receipt_3_13_2403_1_part8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 1024 128 = 309226657119107541050191584 := by decide +kernel
private theorem receipt_3_13_2403_1_part9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 1152 128 = 115277759463674278908403424 := by decide +kernel
private theorem receipt_3_13_2403_1_part10 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 1280 18 = 1635992198009093663197008 := by decide +kernel
private theorem receipt_3_13_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 0 256 = 4549424851343195988611108288 :=
  phaseBlock_append receipt_3_13_2403_1_part0 receipt_3_13_2403_1_part1 rfl rfl rfl
private theorem receipt_3_13_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 384 256 = 2772849878113676958868843968 :=
  phaseBlock_append receipt_3_13_2403_1_part3 receipt_3_13_2403_1_part4 rfl rfl rfl
private theorem receipt_3_13_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 256 384 = 4585358461251961336077679776 :=
  phaseBlock_append receipt_3_13_2403_1_part2 receipt_3_13_2403_1_join1 rfl rfl rfl
private theorem receipt_3_13_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 0 640 = 9134783312595157324688788064 :=
  phaseBlock_append receipt_3_13_2403_1_join0 receipt_3_13_2403_1_join2 rfl rfl rfl
private theorem receipt_3_13_2403_1_join4 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 768 256 = 1267196219732528638180937152 :=
  phaseBlock_append receipt_3_13_2403_1_part6 receipt_3_13_2403_1_part7 rfl rfl rfl
private theorem receipt_3_13_2403_1_join5 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 640 384 = 2257644762792859571409693856 :=
  phaseBlock_append receipt_3_13_2403_1_part5 receipt_3_13_2403_1_join4 rfl rfl rfl
private theorem receipt_3_13_2403_1_join6 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 1152 146 = 116913751661683372571600432 :=
  phaseBlock_append receipt_3_13_2403_1_part9 receipt_3_13_2403_1_part10 rfl rfl rfl
private theorem receipt_3_13_2403_1_join7 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 1024 274 = 426140408780790913621792016 :=
  phaseBlock_append receipt_3_13_2403_1_part8 receipt_3_13_2403_1_join6 rfl rfl rfl
private theorem receipt_3_13_2403_1_join8 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 640 658 = 2683785171573650485031485872 :=
  phaseBlock_append receipt_3_13_2403_1_join5 receipt_3_13_2403_1_join7 rfl rfl rfl
private theorem receipt_3_13_2403_1_join9 :
    phaseBlock (fastLayer (bank 3 13).shape 179798 2403 44 1 1 1 1) 0 1298 = 11818568484168807809720273936 :=
  phaseBlock_append receipt_3_13_2403_1_join3 receipt_3_13_2403_1_join8 rfl rfl rfl

private theorem receipt_3_13_2403_1 : fastPhase (bank 3 13).shape 179798 2403 44 1 1 1 1 = 11818568484168807809720273936 :=
  phase_of_block (n := 1298) (by decide +kernel) receipt_3_13_2403_1_join9

theorem receipt_3_13 : Checked (bank 3 13) 44 1 1 := by
  refine checked_from_values (bank 3 13) 44 1 1
    (P3_7_1.checked (bank 3 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5949_1297)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_13_2402_0 receipt_3_13_2402_1 receipt_3_13_2403_0 receipt_3_13_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_14_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 0 128 = 196845778886387206057285455072 := by decide +kernel
private theorem receipt_0_14_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 128 128 = 180174867308570692422646611168 := by decide +kernel
private theorem receipt_0_14_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 256 128 = 164007725063838463768744324320 := by decide +kernel
private theorem receipt_0_14_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 384 128 = 148336567293703149527608401120 := by decide +kernel
private theorem receipt_0_14_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 512 128 = 133153621407858848089410620640 := by decide +kernel
private theorem receipt_0_14_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 640 128 = 118451127077888445834842242272 := by decide +kernel
private theorem receipt_0_14_2402_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 768 128 = 104221336230970936167491513568 := by decide +kernel
private theorem receipt_0_14_2402_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 896 128 = 90456513043588738546221178080 := by decide +kernel
private theorem receipt_0_14_2402_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1024 128 = 77148933935235017517545983200 := by decide +kernel
private theorem receipt_0_14_2402_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1152 128 = 64290887562121001748010188000 := by decide +kernel
private theorem receipt_0_14_2402_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1280 128 = 51874678515291624554125572085 := by decide +kernel
private theorem receipt_0_14_2402_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1408 128 = 39892637980487933829338919450 := by decide +kernel
private theorem receipt_0_14_2402_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1536 128 = 28337077972568379866076067698 := by decide +kernel
private theorem receipt_0_14_2402_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1664 128 = 17200309206514396998403373334 := by decide +kernel
private theorem receipt_0_14_2402_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1792 128 = 6474654636583021605589502409 := by decide +kernel
private theorem receipt_0_14_2402_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1920 15 = 75361336850541226274448210 := by decide +kernel
private theorem receipt_0_14_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 0 256 = 377020646194957898479932066240 :=
  phaseBlock_append receipt_0_14_2402_0_part0 receipt_0_14_2402_0_part1 rfl rfl rfl
private theorem receipt_0_14_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 256 256 = 312344292357541613296352725440 :=
  phaseBlock_append receipt_0_14_2402_0_part2 receipt_0_14_2402_0_part3 rfl rfl rfl
private theorem receipt_0_14_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 0 512 = 689364938552499511776284791680 :=
  phaseBlock_append receipt_0_14_2402_0_join0 receipt_0_14_2402_0_join1 rfl rfl rfl
private theorem receipt_0_14_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 512 256 = 251604748485747293924252862912 :=
  phaseBlock_append receipt_0_14_2402_0_part4 receipt_0_14_2402_0_part5 rfl rfl rfl
private theorem receipt_0_14_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 768 256 = 194677849274559674713712691648 :=
  phaseBlock_append receipt_0_14_2402_0_part6 receipt_0_14_2402_0_part7 rfl rfl rfl
private theorem receipt_0_14_2402_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 512 512 = 446282597760306968637965554560 :=
  phaseBlock_append receipt_0_14_2402_0_join3 receipt_0_14_2402_0_join4 rfl rfl rfl
private theorem receipt_0_14_2402_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 0 1024 = 1135647536312806480414250346240 :=
  phaseBlock_append receipt_0_14_2402_0_join2 receipt_0_14_2402_0_join5 rfl rfl rfl
private theorem receipt_0_14_2402_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1024 256 = 141439821497356019265556171200 :=
  phaseBlock_append receipt_0_14_2402_0_part8 receipt_0_14_2402_0_part9 rfl rfl rfl
private theorem receipt_0_14_2402_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1280 256 = 91767316495779558383464491535 :=
  phaseBlock_append receipt_0_14_2402_0_part10 receipt_0_14_2402_0_part11 rfl rfl rfl
private theorem receipt_0_14_2402_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1024 512 = 233207137993135577649020662735 :=
  phaseBlock_append receipt_0_14_2402_0_join7 receipt_0_14_2402_0_join8 rfl rfl rfl
private theorem receipt_0_14_2402_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1536 256 = 45537387179082776864479441032 :=
  phaseBlock_append receipt_0_14_2402_0_part12 receipt_0_14_2402_0_part13 rfl rfl rfl
private theorem receipt_0_14_2402_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1792 143 = 6550015973433562831863950619 :=
  phaseBlock_append receipt_0_14_2402_0_part14 receipt_0_14_2402_0_part15 rfl rfl rfl
private theorem receipt_0_14_2402_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1536 399 = 52087403152516339696343391651 :=
  phaseBlock_append receipt_0_14_2402_0_join10 receipt_0_14_2402_0_join11 rfl rfl rfl
private theorem receipt_0_14_2402_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 1024 911 = 285294541145651917345364054386 :=
  phaseBlock_append receipt_0_14_2402_0_join9 receipt_0_14_2402_0_join12 rfl rfl rfl
private theorem receipt_0_14_2402_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 0) 0 1935 = 1420942077458458397759614400626 :=
  phaseBlock_append receipt_0_14_2402_0_join6 receipt_0_14_2402_0_join13 rfl rfl rfl

private theorem receipt_0_14_2402_0 : fastPhase (bank 0 14).shape 179798 2402 73 1 0 1 0 = 1420942077458458397759614400626 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2402_0_join14

private theorem receipt_0_14_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 0 128 = 196715327591797087632547922784 := by decide +kernel
private theorem receipt_0_14_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 128 128 = 180048247804631213803123839840 := by decide +kernel
private theorem receipt_0_14_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 256 128 = 163884878475853724468187095904 := by decide +kernel
private theorem receipt_0_14_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 384 128 = 148217434840448402319895081824 := by decide +kernel
private theorem receipt_0_14_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 512 128 = 133038144401532327823586329440 := by decide +kernel
private theorem receipt_0_14_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 640 128 = 118339246924063198250158019424 := by decide +kernel
private theorem receipt_0_14_2402_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 768 128 = 104112994428546646708443489120 := by decide +kernel
private theorem receipt_0_14_2402_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 896 128 = 90351651184743561177589740384 := by decide +kernel
private theorem receipt_0_14_2402_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1024 128 = 77047493705377403539434947424 := by decide +kernel
private theorem receipt_0_14_2402_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1152 128 = 64192810739841528610885964640 := by decide +kernel
private theorem receipt_0_14_2402_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1280 128 = 51779906965602569823169804938 := by decide +kernel
private theorem receipt_0_14_2402_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1408 128 = 39801113616373427274397138677 := by decide +kernel
private theorem receipt_0_14_2402_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1536 128 = 28248742782040646991357615177 := by decide +kernel
private theorem receipt_0_14_2402_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1664 128 = 17115105270734663974126050240 := by decide +kernel
private theorem receipt_0_14_2402_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1792 128 = 6392524129841749567143261090 := by decide +kernel
private theorem receipt_0_14_2402_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1920 15 = 65935187359518722069215062 := by decide +kernel
private theorem receipt_0_14_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 0 256 = 376763575396428301435671762624 :=
  phaseBlock_append receipt_0_14_2402_1_part0 receipt_0_14_2402_1_part1 rfl rfl rfl
private theorem receipt_0_14_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 256 256 = 312102313316302126788082177728 :=
  phaseBlock_append receipt_0_14_2402_1_part2 receipt_0_14_2402_1_part3 rfl rfl rfl
private theorem receipt_0_14_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 0 512 = 688865888712730428223753940352 :=
  phaseBlock_append receipt_0_14_2402_1_join0 receipt_0_14_2402_1_join1 rfl rfl rfl
private theorem receipt_0_14_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 512 256 = 251377391325595526073744348864 :=
  phaseBlock_append receipt_0_14_2402_1_part4 receipt_0_14_2402_1_part5 rfl rfl rfl
private theorem receipt_0_14_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 768 256 = 194464645613290207886033229504 :=
  phaseBlock_append receipt_0_14_2402_1_part6 receipt_0_14_2402_1_part7 rfl rfl rfl
private theorem receipt_0_14_2402_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 512 512 = 445842036938885733959777578368 :=
  phaseBlock_append receipt_0_14_2402_1_join3 receipt_0_14_2402_1_join4 rfl rfl rfl
private theorem receipt_0_14_2402_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 0 1024 = 1134707925651616162183531518720 :=
  phaseBlock_append receipt_0_14_2402_1_join2 receipt_0_14_2402_1_join5 rfl rfl rfl
private theorem receipt_0_14_2402_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1024 256 = 141240304445218932150320912064 :=
  phaseBlock_append receipt_0_14_2402_1_part8 receipt_0_14_2402_1_part9 rfl rfl rfl
private theorem receipt_0_14_2402_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1280 256 = 91581020581975997097566943615 :=
  phaseBlock_append receipt_0_14_2402_1_part10 receipt_0_14_2402_1_part11 rfl rfl rfl
private theorem receipt_0_14_2402_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1024 512 = 232821325027194929247887855679 :=
  phaseBlock_append receipt_0_14_2402_1_join7 receipt_0_14_2402_1_join8 rfl rfl rfl
private theorem receipt_0_14_2402_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1536 256 = 45363848052775310965483665417 :=
  phaseBlock_append receipt_0_14_2402_1_part12 receipt_0_14_2402_1_part13 rfl rfl rfl
private theorem receipt_0_14_2402_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1792 143 = 6458459317201268289212476152 :=
  phaseBlock_append receipt_0_14_2402_1_part14 receipt_0_14_2402_1_part15 rfl rfl rfl
private theorem receipt_0_14_2402_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1536 399 = 51822307369976579254696141569 :=
  phaseBlock_append receipt_0_14_2402_1_join10 receipt_0_14_2402_1_join11 rfl rfl rfl
private theorem receipt_0_14_2402_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 1024 911 = 284643632397171508502583997248 :=
  phaseBlock_append receipt_0_14_2402_1_join9 receipt_0_14_2402_1_join12 rfl rfl rfl
private theorem receipt_0_14_2402_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2402 73 1 0 1 1) 0 1935 = 1419351558048787670686115515968 :=
  phaseBlock_append receipt_0_14_2402_1_join6 receipt_0_14_2402_1_join13 rfl rfl rfl

private theorem receipt_0_14_2402_1 : fastPhase (bank 0 14).shape 179798 2402 73 1 0 1 1 = 1419351558048787670686115515968 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2402_1_join14

private theorem receipt_0_14_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 0 128 = 196847545432211344250534572800 := by decide +kernel
private theorem receipt_0_14_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 128 128 = 180176424318853893472882782976 := by decide +kernel
private theorem receipt_0_14_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 256 128 = 164009086691214912417410102016 := by decide +kernel
private theorem receipt_0_14_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 384 128 = 148337747422804892185018069760 := by decide +kernel
private theorem receipt_0_14_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 512 128 = 133154633655742858990817784576 := by decide +kernel
private theorem receipt_0_14_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 640 128 = 118451984794463473294181856000 := by decide +kernel
private theorem receipt_0_14_2403_0_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 768 128 = 104222052499424128928796357376 := by decide +kernel
private theorem receipt_0_14_2403_0_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 896 128 = 90457100680812052232712778496 := by decide +kernel
private theorem receipt_0_14_2403_0_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1024 128 = 77149405492251401178399978240 := by decide +kernel
private theorem receipt_0_14_2403_0_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1152 128 = 64291255324510364502796137216 := by decide +kernel
private theorem receipt_0_14_2403_0_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1280 128 = 51874954364429205845104379950 := by decide +kernel
private theorem receipt_0_14_2403_0_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1408 128 = 39892833530876549230512939114 := by decide +kernel
private theorem receipt_0_14_2403_0_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1536 128 = 28337204904136817926482537620 := by decide +kernel
private theorem receipt_0_14_2403_0_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1664 128 = 17200378918594728032912712246 := by decide +kernel
private theorem receipt_0_14_2403_0_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1792 128 = 6474678245404679240789764872 := by decide +kernel
private theorem receipt_0_14_2403_0_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1920 15 = 75361588749289599520461018 := by decide +kernel
private theorem receipt_0_14_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 0 256 = 377023969751065237723417355776 :=
  phaseBlock_append receipt_0_14_2403_0_part0 receipt_0_14_2403_0_part1 rfl rfl rfl
private theorem receipt_0_14_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 256 256 = 312346834114019804602428171776 :=
  phaseBlock_append receipt_0_14_2403_0_part2 receipt_0_14_2403_0_part3 rfl rfl rfl
private theorem receipt_0_14_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 0 512 = 689370803865085042325845527552 :=
  phaseBlock_append receipt_0_14_2403_0_join0 receipt_0_14_2403_0_join1 rfl rfl rfl
private theorem receipt_0_14_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 512 256 = 251606618450206332284999640576 :=
  phaseBlock_append receipt_0_14_2403_0_part4 receipt_0_14_2403_0_part5 rfl rfl rfl
private theorem receipt_0_14_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 768 256 = 194679153180236181161509135872 :=
  phaseBlock_append receipt_0_14_2403_0_part6 receipt_0_14_2403_0_part7 rfl rfl rfl
private theorem receipt_0_14_2403_0_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 512 512 = 446285771630442513446508776448 :=
  phaseBlock_append receipt_0_14_2403_0_join3 receipt_0_14_2403_0_join4 rfl rfl rfl
private theorem receipt_0_14_2403_0_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 0 1024 = 1135656575495527555772354304000 :=
  phaseBlock_append receipt_0_14_2403_0_join2 receipt_0_14_2403_0_join5 rfl rfl rfl
private theorem receipt_0_14_2403_0_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1024 256 = 141440660816761765681196115456 :=
  phaseBlock_append receipt_0_14_2403_0_part8 receipt_0_14_2403_0_part9 rfl rfl rfl
private theorem receipt_0_14_2403_0_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1280 256 = 91767787895305755075617319064 :=
  phaseBlock_append receipt_0_14_2403_0_part10 receipt_0_14_2403_0_part11 rfl rfl rfl
private theorem receipt_0_14_2403_0_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1024 512 = 233208448712067520756813434520 :=
  phaseBlock_append receipt_0_14_2403_0_join7 receipt_0_14_2403_0_join8 rfl rfl rfl
private theorem receipt_0_14_2403_0_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1536 256 = 45537583822731545959395249866 :=
  phaseBlock_append receipt_0_14_2403_0_part12 receipt_0_14_2403_0_part13 rfl rfl rfl
private theorem receipt_0_14_2403_0_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1792 143 = 6550039834153968840310225890 :=
  phaseBlock_append receipt_0_14_2403_0_part14 receipt_0_14_2403_0_part15 rfl rfl rfl
private theorem receipt_0_14_2403_0_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1536 399 = 52087623656885514799705475756 :=
  phaseBlock_append receipt_0_14_2403_0_join10 receipt_0_14_2403_0_join11 rfl rfl rfl
private theorem receipt_0_14_2403_0_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 1024 911 = 285296072368953035556518910276 :=
  phaseBlock_append receipt_0_14_2403_0_join9 receipt_0_14_2403_0_join12 rfl rfl rfl
private theorem receipt_0_14_2403_0_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 0) 0 1935 = 1420952647864480591328873214276 :=
  phaseBlock_append receipt_0_14_2403_0_join6 receipt_0_14_2403_0_join13 rfl rfl rfl

private theorem receipt_0_14_2403_0 : fastPhase (bank 0 14).shape 179798 2403 73 1 0 1 0 = 1420952647864480591328873214276 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2403_0_join14

private theorem receipt_0_14_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 0 128 = 196717093178944596122410861632 := by decide +kernel
private theorem receipt_0_14_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 128 128 = 180049803912012038206827488320 := by decide +kernel
private theorem receipt_0_14_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 256 128 = 163886239254835967367934379072 := by decide +kernel
private theorem receipt_0_14_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 384 128 = 148218614174400366770800600128 := by decide +kernel
private theorem receipt_0_14_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 512 128 = 133039155906249582204073886784 := by decide +kernel
private theorem receipt_0_14_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 640 128 = 118340103948195421210032596032 := by decide +kernel
private theorem receipt_0_14_2403_1_part6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 768 128 = 104113710054024252214637659200 := by decide +kernel
private theorem receipt_0_14_2403_1_part7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 896 128 = 90352238227204103657584534592 := by decide +kernel
private theorem receipt_0_14_2403_1_part8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1024 128 = 77047964714591763122355160128 := by decide +kernel
private theorem receipt_0_14_2403_1_part9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1152 128 = 64193178000139876466269905984 := by decide +kernel
private theorem receipt_0_14_2403_1_part10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1280 128 = 51780182357360943275549654128 := by decide +kernel
private theorem receipt_0_14_2403_1_part11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1408 128 = 39801308753275912785690659378 := by decide +kernel
private theorem receipt_0_14_2403_1_part12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1536 128 = 28248869342723633058391574136 := by decide +kernel
private theorem receipt_0_14_2403_1_part13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1664 128 = 17115174653235455108767686474 := by decide +kernel
private theorem receipt_0_14_2403_1_part14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1792 128 = 6392547449087101365207334558 := by decide +kernel
private theorem receipt_0_14_2403_1_part15 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1920 15 = 65935407880662794045954480 := by decide +kernel
private theorem receipt_0_14_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 0 256 = 376766897090956634329238349952 :=
  phaseBlock_append receipt_0_14_2403_1_part0 receipt_0_14_2403_1_part1 rfl rfl rfl
private theorem receipt_0_14_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 256 256 = 312104853429236334138734979200 :=
  phaseBlock_append receipt_0_14_2403_1_part2 receipt_0_14_2403_1_part3 rfl rfl rfl
private theorem receipt_0_14_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 0 512 = 688871750520192968467973329152 :=
  phaseBlock_append receipt_0_14_2403_1_join0 receipt_0_14_2403_1_join1 rfl rfl rfl
private theorem receipt_0_14_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 512 256 = 251379259854445003414106482816 :=
  phaseBlock_append receipt_0_14_2403_1_part4 receipt_0_14_2403_1_part5 rfl rfl rfl
private theorem receipt_0_14_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 768 256 = 194465948281228355872222193792 :=
  phaseBlock_append receipt_0_14_2403_1_part6 receipt_0_14_2403_1_part7 rfl rfl rfl
private theorem receipt_0_14_2403_1_join5 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 512 512 = 445845208135673359286328676608 :=
  phaseBlock_append receipt_0_14_2403_1_join3 receipt_0_14_2403_1_join4 rfl rfl rfl
private theorem receipt_0_14_2403_1_join6 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 0 1024 = 1134716958655866327754302005760 :=
  phaseBlock_append receipt_0_14_2403_1_join2 receipt_0_14_2403_1_join5 rfl rfl rfl
private theorem receipt_0_14_2403_1_join7 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1024 256 = 141241142714731639588625066112 :=
  phaseBlock_append receipt_0_14_2403_1_part8 receipt_0_14_2403_1_part9 rfl rfl rfl
private theorem receipt_0_14_2403_1_join8 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1280 256 = 91581491110636856061240313506 :=
  phaseBlock_append receipt_0_14_2403_1_part10 receipt_0_14_2403_1_part11 rfl rfl rfl
private theorem receipt_0_14_2403_1_join9 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1024 512 = 232822633825368495649865379618 :=
  phaseBlock_append receipt_0_14_2403_1_join7 receipt_0_14_2403_1_join8 rfl rfl rfl
private theorem receipt_0_14_2403_1_join10 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1536 256 = 45364043995959088167159260610 :=
  phaseBlock_append receipt_0_14_2403_1_part12 receipt_0_14_2403_1_part13 rfl rfl rfl
private theorem receipt_0_14_2403_1_join11 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1792 143 = 6458482856967764159253289038 :=
  phaseBlock_append receipt_0_14_2403_1_part14 receipt_0_14_2403_1_part15 rfl rfl rfl
private theorem receipt_0_14_2403_1_join12 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1536 399 = 51822526852926852326412549648 :=
  phaseBlock_append receipt_0_14_2403_1_join10 receipt_0_14_2403_1_join11 rfl rfl rfl
private theorem receipt_0_14_2403_1_join13 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 1024 911 = 284645160678295347976277929266 :=
  phaseBlock_append receipt_0_14_2403_1_join9 receipt_0_14_2403_1_join12 rfl rfl rfl
private theorem receipt_0_14_2403_1_join14 :
    phaseBlock (fastLayer (bank 0 14).shape 179798 2403 73 1 0 1 1) 0 1935 = 1419362119334161675730579935026 :=
  phaseBlock_append receipt_0_14_2403_1_join6 receipt_0_14_2403_1_join13 rfl rfl rfl

private theorem receipt_0_14_2403_1 : fastPhase (bank 0 14).shape 179798 2403 73 1 0 1 1 = 1419362119334161675730579935026 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_14_2403_1_join14

theorem receipt_0_14 : Checked (bank 0 14) 73 0 1 := by
  refine checked_from_values (bank 0 14) 73 0 1
    (P3_7_1.checked (bank 0 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_14_2402_0 receipt_0_14_2402_1 receipt_0_14_2403_0 receipt_0_14_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_14_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 0 128 = 177214415926183721755425179424 := by decide +kernel
private theorem receipt_1_14_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 128 128 = 162130845383753629020014311200 := by decide +kernel
private theorem receipt_1_14_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 256 128 = 147514298401959060129103013664 := by decide +kernel
private theorem receipt_1_14_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 384 128 = 133357148541810253740450830112 := by decide +kernel
private theorem receipt_1_14_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 512 128 = 119651793168959880508482307872 := by decide +kernel
private theorem receipt_1_14_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 640 128 = 106390653428532319213797029664 := by decide +kernel
private theorem receipt_1_14_2402_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 768 128 = 93566174219952932892679644960 := by decide +kernel
private theorem receipt_1_14_2402_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 896 128 = 81170824171777344966609901344 := by decide +kernel
private theorem receipt_1_14_2402_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1024 128 = 69197095616520715371772675872 := by decide +kernel
private theorem receipt_1_14_2402_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1152 128 = 57637504565487016688568006432 := by decide +kernel
private theorem receipt_1_14_2402_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1280 128 = 46484594002618844086765549246 := by decide +kernel
private theorem receipt_1_14_2402_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1408 128 = 35730943405930996730430958152 := by decide +kernel
private theorem receipt_1_14_2402_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1536 128 = 25369127726841554730069634380 := by decide +kernel
private theorem receipt_1_14_2402_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1664 128 = 15391733425494345213645535842 := by decide +kernel
private theorem receipt_1_14_2402_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1792 128 = 5791370590328703962577522885 := by decide +kernel
private theorem receipt_1_14_2402_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1920 15 = 67386963832155453129152547 := by decide +kernel
private theorem receipt_1_14_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 0 256 = 339345261309937350775439490624 :=
  phaseBlock_append receipt_1_14_2402_0_part0 receipt_1_14_2402_0_part1 rfl rfl rfl
private theorem receipt_1_14_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 256 256 = 280871446943769313869553843776 :=
  phaseBlock_append receipt_1_14_2402_0_part2 receipt_1_14_2402_0_part3 rfl rfl rfl
private theorem receipt_1_14_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 0 512 = 620216708253706664644993334400 :=
  phaseBlock_append receipt_1_14_2402_0_join0 receipt_1_14_2402_0_join1 rfl rfl rfl
private theorem receipt_1_14_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 512 256 = 226042446597492199722279337536 :=
  phaseBlock_append receipt_1_14_2402_0_part4 receipt_1_14_2402_0_part5 rfl rfl rfl
private theorem receipt_1_14_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 768 256 = 174736998391730277859289546304 :=
  phaseBlock_append receipt_1_14_2402_0_part6 receipt_1_14_2402_0_part7 rfl rfl rfl
private theorem receipt_1_14_2402_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 512 512 = 400779444989222477581568883840 :=
  phaseBlock_append receipt_1_14_2402_0_join3 receipt_1_14_2402_0_join4 rfl rfl rfl
private theorem receipt_1_14_2402_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 0 1024 = 1020996153242929142226562218240 :=
  phaseBlock_append receipt_1_14_2402_0_join2 receipt_1_14_2402_0_join5 rfl rfl rfl
private theorem receipt_1_14_2402_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1024 256 = 126834600182007732060340682304 :=
  phaseBlock_append receipt_1_14_2402_0_part8 receipt_1_14_2402_0_part9 rfl rfl rfl
private theorem receipt_1_14_2402_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1280 256 = 82215537408549840817196507398 :=
  phaseBlock_append receipt_1_14_2402_0_part10 receipt_1_14_2402_0_part11 rfl rfl rfl
private theorem receipt_1_14_2402_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1024 512 = 209050137590557572877537189702 :=
  phaseBlock_append receipt_1_14_2402_0_join7 receipt_1_14_2402_0_join8 rfl rfl rfl
private theorem receipt_1_14_2402_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1536 256 = 40760861152335899943715170222 :=
  phaseBlock_append receipt_1_14_2402_0_part12 receipt_1_14_2402_0_part13 rfl rfl rfl
private theorem receipt_1_14_2402_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1792 143 = 5858757554160859415706675432 :=
  phaseBlock_append receipt_1_14_2402_0_part14 receipt_1_14_2402_0_part15 rfl rfl rfl
private theorem receipt_1_14_2402_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1536 399 = 46619618706496759359421845654 :=
  phaseBlock_append receipt_1_14_2402_0_join10 receipt_1_14_2402_0_join11 rfl rfl rfl
private theorem receipt_1_14_2402_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 1024 911 = 255669756297054332236959035356 :=
  phaseBlock_append receipt_1_14_2402_0_join9 receipt_1_14_2402_0_join12 rfl rfl rfl
private theorem receipt_1_14_2402_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 0) 0 1935 = 1276665909539983474463521253596 :=
  phaseBlock_append receipt_1_14_2402_0_join6 receipt_1_14_2402_0_join13 rfl rfl rfl

private theorem receipt_1_14_2402_0 : fastPhase (bank 1 14).shape 179798 2402 73 1 0 2 0 = 1276665909539983474463521253596 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2402_0_join14

private theorem receipt_1_14_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 0 128 = 177096332732213289941071388640 := by decide +kernel
private theorem receipt_1_14_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 128 128 = 162016319014997885749354876896 := by decide +kernel
private theorem receipt_1_14_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 256 128 = 147403271088212005244931424224 := by decide +kernel
private theorem receipt_1_14_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 384 128 = 133249562694314677607760637920 := by decide +kernel
private theorem receipt_1_14_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 512 128 = 119547591380214679274623803360 := by decide +kernel
private theorem receipt_1_14_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 640 128 = 106289778472099810068633915360 := by decide +kernel
private theorem receipt_1_14_2402_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 768 128 = 93468569050266169328745709536 := by decide +kernel
private theorem receipt_1_14_2402_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 896 128 = 81076431923947432039265693664 := by decide +kernel
private theorem receipt_1_14_2402_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1024 128 = 69105859606144124959362179040 := by decide +kernel
private theorem receipt_1_14_2402_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1152 128 = 57549368288452902752575311840 := by decide +kernel
private theorem receipt_1_14_2402_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1280 128 = 46399501128890336393174780070 := by decide +kernel
private theorem receipt_1_14_2402_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1408 128 = 35648837744921698791968970510 := by decide +kernel
private theorem receipt_1_14_2402_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1536 128 = 25289953251663760484189733021 := by decide +kernel
private theorem receipt_1_14_2402_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1664 128 = 15315434289100552046088242913 := by decide +kernel
private theorem receipt_1_14_2402_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1792 128 = 5717891125344053751923030238 := by decide +kernel
private theorem receipt_1_14_2402_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1920 15 = 58958100090275838019261338 := by decide +kernel
private theorem receipt_1_14_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 0 256 = 339112651747211175690426265536 :=
  phaseBlock_append receipt_1_14_2402_1_part0 receipt_1_14_2402_1_part1 rfl rfl rfl
private theorem receipt_1_14_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 256 256 = 280652833782526682852692062144 :=
  phaseBlock_append receipt_1_14_2402_1_part2 receipt_1_14_2402_1_part3 rfl rfl rfl
private theorem receipt_1_14_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 0 512 = 619765485529737858543118327680 :=
  phaseBlock_append receipt_1_14_2402_1_join0 receipt_1_14_2402_1_join1 rfl rfl rfl
private theorem receipt_1_14_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 512 256 = 225837369852314489343257718720 :=
  phaseBlock_append receipt_1_14_2402_1_part4 receipt_1_14_2402_1_part5 rfl rfl rfl
private theorem receipt_1_14_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 768 256 = 174545000974213601368011403200 :=
  phaseBlock_append receipt_1_14_2402_1_part6 receipt_1_14_2402_1_part7 rfl rfl rfl
private theorem receipt_1_14_2402_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 512 512 = 400382370826528090711269121920 :=
  phaseBlock_append receipt_1_14_2402_1_join3 receipt_1_14_2402_1_join4 rfl rfl rfl
private theorem receipt_1_14_2402_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 0 1024 = 1020147856356265949254387449600 :=
  phaseBlock_append receipt_1_14_2402_1_join2 receipt_1_14_2402_1_join5 rfl rfl rfl
private theorem receipt_1_14_2402_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1024 256 = 126655227894597027711937490880 :=
  phaseBlock_append receipt_1_14_2402_1_part8 receipt_1_14_2402_1_part9 rfl rfl rfl
private theorem receipt_1_14_2402_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1280 256 = 82048338873812035185143750580 :=
  phaseBlock_append receipt_1_14_2402_1_part10 receipt_1_14_2402_1_part11 rfl rfl rfl
private theorem receipt_1_14_2402_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1024 512 = 208703566768409062897081241460 :=
  phaseBlock_append receipt_1_14_2402_1_join7 receipt_1_14_2402_1_join8 rfl rfl rfl
private theorem receipt_1_14_2402_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1536 256 = 40605387540764312530277975934 :=
  phaseBlock_append receipt_1_14_2402_1_part12 receipt_1_14_2402_1_part13 rfl rfl rfl
private theorem receipt_1_14_2402_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1792 143 = 5776849225434329589942291576 :=
  phaseBlock_append receipt_1_14_2402_1_part14 receipt_1_14_2402_1_part15 rfl rfl rfl
private theorem receipt_1_14_2402_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1536 399 = 46382236766198642120220267510 :=
  phaseBlock_append receipt_1_14_2402_1_join10 receipt_1_14_2402_1_join11 rfl rfl rfl
private theorem receipt_1_14_2402_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 1024 911 = 255085803534607705017301508970 :=
  phaseBlock_append receipt_1_14_2402_1_join9 receipt_1_14_2402_1_join12 rfl rfl rfl
private theorem receipt_1_14_2402_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2402 73 1 0 2 1) 0 1935 = 1275233659890873654271688958570 :=
  phaseBlock_append receipt_1_14_2402_1_join6 receipt_1_14_2402_1_join13 rfl rfl rfl

private theorem receipt_1_14_2402_1 : fastPhase (bank 1 14).shape 179798 2402 73 1 0 2 1 = 1275233659890873654271688958570 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2402_1_join14

private theorem receipt_1_14_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 0 128 = 177216006297246123176129460768 := by decide +kernel
private theorem receipt_1_14_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 128 128 = 162132246465807980999710181920 := by decide +kernel
private theorem receipt_1_14_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 256 128 = 147515523099321605867968600608 := by decide +kernel
private theorem receipt_1_14_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 384 128 = 133358209500163482234917792288 := by decide +kernel
private theorem receipt_1_14_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 512 128 = 119652702776177779571992181280 := by decide +kernel
private theorem receipt_1_14_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 640 128 = 106391423815504748888255351328 := by decide +kernel
private theorem receipt_1_14_2403_0_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 768 128 = 93566817261409119250607856160 := by decide +kernel
private theorem receipt_1_14_2403_0_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 896 128 = 81171351487108494303995030048 := by decide +kernel
private theorem receipt_1_14_2403_0_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1024 128 = 69197518570601748791614798368 := by decide +kernel
private theorem receipt_1_14_2403_0_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1152 128 = 57637834269497425075125488160 := by decide +kernel
private theorem receipt_1_14_2403_0_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1280 128 = 46484841190151502096289339015 := by decide +kernel
private theorem receipt_1_14_2403_0_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1408 128 = 35731118556623098706445098019 := by decide +kernel
private theorem receipt_1_14_2403_0_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1536 128 = 25369241364355090319551024691 := by decide +kernel
private theorem receipt_1_14_2403_0_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1664 128 = 15391795807753286280896124564 := by decide +kernel
private theorem receipt_1_14_2403_0_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1792 128 = 5791391707740469993252395801 := by decide +kernel
private theorem receipt_1_14_2403_0_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1920 15 = 67387189076205368025356019 := by decide +kernel
private theorem receipt_1_14_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 0 256 = 339348252763054104175839642688 :=
  phaseBlock_append receipt_1_14_2403_0_part0 receipt_1_14_2403_0_part1 rfl rfl rfl
private theorem receipt_1_14_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 256 256 = 280873732599485088102886392896 :=
  phaseBlock_append receipt_1_14_2403_0_part2 receipt_1_14_2403_0_part3 rfl rfl rfl
private theorem receipt_1_14_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 0 512 = 620221985362539192278726035584 :=
  phaseBlock_append receipt_1_14_2403_0_join0 receipt_1_14_2403_0_join1 rfl rfl rfl
private theorem receipt_1_14_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 512 256 = 226044126591682528460247532608 :=
  phaseBlock_append receipt_1_14_2403_0_part4 receipt_1_14_2403_0_part5 rfl rfl rfl
private theorem receipt_1_14_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 768 256 = 174738168748517613554602886208 :=
  phaseBlock_append receipt_1_14_2403_0_part6 receipt_1_14_2403_0_part7 rfl rfl rfl
private theorem receipt_1_14_2403_0_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 512 512 = 400782295340200142014850418816 :=
  phaseBlock_append receipt_1_14_2403_0_join3 receipt_1_14_2403_0_join4 rfl rfl rfl
private theorem receipt_1_14_2403_0_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 0 1024 = 1021004280702739334293576454400 :=
  phaseBlock_append receipt_1_14_2403_0_join2 receipt_1_14_2403_0_join5 rfl rfl rfl
private theorem receipt_1_14_2403_0_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1024 256 = 126835352840099173866740286528 :=
  phaseBlock_append receipt_1_14_2403_0_part8 receipt_1_14_2403_0_part9 rfl rfl rfl
private theorem receipt_1_14_2403_0_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1280 256 = 82215959746774600802734437034 :=
  phaseBlock_append receipt_1_14_2403_0_part10 receipt_1_14_2403_0_part11 rfl rfl rfl
private theorem receipt_1_14_2403_0_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1024 512 = 209051312586873774669474723562 :=
  phaseBlock_append receipt_1_14_2403_0_join7 receipt_1_14_2403_0_join8 rfl rfl rfl
private theorem receipt_1_14_2403_0_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1536 256 = 40761037172108376600447149255 :=
  phaseBlock_append receipt_1_14_2403_0_part12 receipt_1_14_2403_0_part13 rfl rfl rfl
private theorem receipt_1_14_2403_0_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1792 143 = 5858778896816675361277751820 :=
  phaseBlock_append receipt_1_14_2403_0_part14 receipt_1_14_2403_0_part15 rfl rfl rfl
private theorem receipt_1_14_2403_0_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1536 399 = 46619816068925051961724901075 :=
  phaseBlock_append receipt_1_14_2403_0_join10 receipt_1_14_2403_0_join11 rfl rfl rfl
private theorem receipt_1_14_2403_0_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 1024 911 = 255671128655798826631199624637 :=
  phaseBlock_append receipt_1_14_2403_0_join9 receipt_1_14_2403_0_join12 rfl rfl rfl
private theorem receipt_1_14_2403_0_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 0) 0 1935 = 1276675409358538160924776079037 :=
  phaseBlock_append receipt_1_14_2403_0_join6 receipt_1_14_2403_0_join13 rfl rfl rfl

private theorem receipt_1_14_2403_0 : fastPhase (bank 1 14).shape 179798 2403 73 1 0 2 0 = 1276675409358538160924776079037 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2403_0_join14

private theorem receipt_1_14_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 0 128 = 177097922234446128142064070432 := by decide +kernel
private theorem receipt_1_14_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 128 128 = 162017719279494412192746282784 := by decide +kernel
private theorem receipt_1_14_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 256 128 = 147404495018057223177617968928 := by decide +kernel
private theorem receipt_1_14_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 384 128 = 133250622933964362319345319712 := by decide +kernel
private theorem receipt_1_14_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 512 128 = 119548500316320625895492316960 := by decide +kernel
private theorem receipt_1_14_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 640 128 = 106290548234334201758728544032 := by decide +kernel
private theorem receipt_1_14_2403_1_part6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 768 128 = 93469211512145065857036996384 := by decide +kernel
private theorem receipt_1_14_2403_1_part7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 896 128 = 81076958703653378753921892128 := by decide +kernel
private theorem receipt_1_14_2403_1_part8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1024 128 = 69106282067347882148616482592 := by decide +kernel
private theorem receipt_1_14_2403_1_part9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1152 128 = 57549697541134295396290862880 := by decide +kernel
private theorem receipt_1_14_2403_1_part10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1280 128 = 46399747905669907832625378829 := by decide +kernel
private theorem receipt_1_14_2403_1_part11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1408 128 = 35649012524628097435283136761 := by decide +kernel
private theorem receipt_1_14_2403_1_part12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1536 128 = 25290066556727139800405394792 := by decide +kernel
private theorem receipt_1_14_2403_1_part13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1664 128 = 15315496376213437464115885485 := by decide +kernel
private theorem receipt_1_14_2403_1_part14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1792 128 = 5717911983677863783772514328 := by decide +kernel
private theorem receipt_1_14_2403_1_part15 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1920 15 = 58958297276464071650542784 := by decide +kernel
private theorem receipt_1_14_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 0 256 = 339115641513940540334810353216 :=
  phaseBlock_append receipt_1_14_2403_1_part0 receipt_1_14_2403_1_part1 rfl rfl rfl
private theorem receipt_1_14_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 256 256 = 280655117952021585496963288640 :=
  phaseBlock_append receipt_1_14_2403_1_part2 receipt_1_14_2403_1_part3 rfl rfl rfl
private theorem receipt_1_14_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 0 512 = 619770759465962125831773641856 :=
  phaseBlock_append receipt_1_14_2403_1_join0 receipt_1_14_2403_1_join1 rfl rfl rfl
private theorem receipt_1_14_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 512 256 = 225839048550654827654220860992 :=
  phaseBlock_append receipt_1_14_2403_1_part4 receipt_1_14_2403_1_part5 rfl rfl rfl
private theorem receipt_1_14_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 768 256 = 174546170215798444610958888512 :=
  phaseBlock_append receipt_1_14_2403_1_part6 receipt_1_14_2403_1_part7 rfl rfl rfl
private theorem receipt_1_14_2403_1_join5 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 512 512 = 400385218766453272265179749504 :=
  phaseBlock_append receipt_1_14_2403_1_join3 receipt_1_14_2403_1_join4 rfl rfl rfl
private theorem receipt_1_14_2403_1_join6 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 0 1024 = 1020155978232415398096953391360 :=
  phaseBlock_append receipt_1_14_2403_1_join2 receipt_1_14_2403_1_join5 rfl rfl rfl
private theorem receipt_1_14_2403_1_join7 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1024 256 = 126655979608482177544907345472 :=
  phaseBlock_append receipt_1_14_2403_1_part8 receipt_1_14_2403_1_part9 rfl rfl rfl
private theorem receipt_1_14_2403_1_join8 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1280 256 = 82048760430298005267908515590 :=
  phaseBlock_append receipt_1_14_2403_1_part10 receipt_1_14_2403_1_part11 rfl rfl rfl
private theorem receipt_1_14_2403_1_join9 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1024 512 = 208704740038780182812815861062 :=
  phaseBlock_append receipt_1_14_2403_1_join7 receipt_1_14_2403_1_join8 rfl rfl rfl
private theorem receipt_1_14_2403_1_join10 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1536 256 = 40605562932940577264521280277 :=
  phaseBlock_append receipt_1_14_2403_1_part12 receipt_1_14_2403_1_part13 rfl rfl rfl
private theorem receipt_1_14_2403_1_join11 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1792 143 = 5776870280954327855423057112 :=
  phaseBlock_append receipt_1_14_2403_1_part14 receipt_1_14_2403_1_part15 rfl rfl rfl
private theorem receipt_1_14_2403_1_join12 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1536 399 = 46382433213894905119944337389 :=
  phaseBlock_append receipt_1_14_2403_1_join10 receipt_1_14_2403_1_join11 rfl rfl rfl
private theorem receipt_1_14_2403_1_join13 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 1024 911 = 255087173252675087932760198451 :=
  phaseBlock_append receipt_1_14_2403_1_join9 receipt_1_14_2403_1_join12 rfl rfl rfl
private theorem receipt_1_14_2403_1_join14 :
    phaseBlock (fastLayer (bank 1 14).shape 179798 2403 73 1 0 2 1) 0 1935 = 1275243151485090486029713589811 :=
  phaseBlock_append receipt_1_14_2403_1_join6 receipt_1_14_2403_1_join13 rfl rfl rfl

private theorem receipt_1_14_2403_1 : fastPhase (bank 1 14).shape 179798 2403 73 1 0 2 1 = 1275243151485090486029713589811 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_14_2403_1_join14

theorem receipt_1_14 : Checked (bank 1 14) 73 0 2 := by
  refine checked_from_values (bank 1 14) 73 0 2
    (P3_7_1.checked (bank 1 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_14_2402_0 receipt_1_14_2402_1 receipt_1_14_2403_0 receipt_1_14_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_14_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 0 128 = 95072441991510328168832263584 := by decide +kernel
private theorem receipt_2_14_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 128 128 = 86690445797098406526084773280 := by decide +kernel
private theorem receipt_2_14_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 256 128 = 78611499905887969525411775904 := by decide +kernel
private theorem receipt_2_14_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 384 128 = 70828988278568572820764497312 := by decide +kernel
private theorem receipt_2_14_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 512 128 = 63336365556281877746182890912 := by decide +kernel
private theorem receipt_2_14_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 640 128 = 56127156752280283902293521824 := by decide +kernel
private theorem receipt_2_14_2402_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 768 128 = 49194956943585561742807451040 := by decide +kernel
private theorem receipt_2_14_2402_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 896 128 = 42533430962647485161018119584 := by decide +kernel
private theorem receipt_2_14_2402_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1024 128 = 36136313089002464076299232672 := by decide +kernel
private theorem receipt_2_14_2402_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1152 128 = 29997406740932177020602643872 := by decide +kernel
private theorem receipt_2_14_2402_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1280 128 = 24110585886812147132211983776 := by decide +kernel
private theorem receipt_2_14_2402_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1408 128 = 18469799645593790240145838467 := by decide +kernel
private theorem receipt_2_14_2402_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1536 128 = 13069050749790751613313531360 := by decide +kernel
private theorem receipt_2_14_2402_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1664 128 = 7902403721878123975187857242 := by decide +kernel
private theorem receipt_2_14_2402_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1792 128 = 2963990890017136704382790580 := by decide +kernel
private theorem receipt_2_14_2402_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1920 15 = 34407699636161431775814717 := by decide +kernel
private theorem receipt_2_14_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 0 256 = 181762887788608734694917036864 :=
  phaseBlock_append receipt_2_14_2402_0_part0 receipt_2_14_2402_0_part1 rfl rfl rfl
private theorem receipt_2_14_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 256 256 = 149440488184456542346176273216 :=
  phaseBlock_append receipt_2_14_2402_0_part2 receipt_2_14_2402_0_part3 rfl rfl rfl
private theorem receipt_2_14_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 0 512 = 331203375973065277041093310080 :=
  phaseBlock_append receipt_2_14_2402_0_join0 receipt_2_14_2402_0_join1 rfl rfl rfl
private theorem receipt_2_14_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 512 256 = 119463522308562161648476412736 :=
  phaseBlock_append receipt_2_14_2402_0_part4 receipt_2_14_2402_0_part5 rfl rfl rfl
private theorem receipt_2_14_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 768 256 = 91728387906233046903825570624 :=
  phaseBlock_append receipt_2_14_2402_0_part6 receipt_2_14_2402_0_part7 rfl rfl rfl
private theorem receipt_2_14_2402_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 512 512 = 211191910214795208552301983360 :=
  phaseBlock_append receipt_2_14_2402_0_join3 receipt_2_14_2402_0_join4 rfl rfl rfl
private theorem receipt_2_14_2402_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 0 1024 = 542395286187860485593395293440 :=
  phaseBlock_append receipt_2_14_2402_0_join2 receipt_2_14_2402_0_join5 rfl rfl rfl
private theorem receipt_2_14_2402_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1024 256 = 66133719829934641096901876544 :=
  phaseBlock_append receipt_2_14_2402_0_part8 receipt_2_14_2402_0_part9 rfl rfl rfl
private theorem receipt_2_14_2402_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1280 256 = 42580385532405937372357822243 :=
  phaseBlock_append receipt_2_14_2402_0_part10 receipt_2_14_2402_0_part11 rfl rfl rfl
private theorem receipt_2_14_2402_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1024 512 = 108714105362340578469259698787 :=
  phaseBlock_append receipt_2_14_2402_0_join7 receipt_2_14_2402_0_join8 rfl rfl rfl
private theorem receipt_2_14_2402_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1536 256 = 20971454471668875588501388602 :=
  phaseBlock_append receipt_2_14_2402_0_part12 receipt_2_14_2402_0_part13 rfl rfl rfl
private theorem receipt_2_14_2402_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1792 143 = 2998398589653298136158605297 :=
  phaseBlock_append receipt_2_14_2402_0_part14 receipt_2_14_2402_0_part15 rfl rfl rfl
private theorem receipt_2_14_2402_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1536 399 = 23969853061322173724659993899 :=
  phaseBlock_append receipt_2_14_2402_0_join10 receipt_2_14_2402_0_join11 rfl rfl rfl
private theorem receipt_2_14_2402_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 1024 911 = 132683958423662752193919692686 :=
  phaseBlock_append receipt_2_14_2402_0_join9 receipt_2_14_2402_0_join12 rfl rfl rfl
private theorem receipt_2_14_2402_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 0) 0 1935 = 675079244611523237787314986126 :=
  phaseBlock_append receipt_2_14_2402_0_join6 receipt_2_14_2402_0_join13 rfl rfl rfl

private theorem receipt_2_14_2402_0 : fastPhase (bank 2 14).shape 179798 2402 73 1 0 7 0 = 675079244611523237787314986126 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2402_0_join14

private theorem receipt_2_14_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 0 128 = 95006617277649457314506614560 := by decide +kernel
private theorem receipt_2_14_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 128 128 = 86626946732049937548348446496 := by decide +kernel
private theorem receipt_2_14_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 256 128 = 78550275977852436811810899744 := by decide +kernel
private theorem receipt_2_14_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 384 128 = 70769989515970191678667863840 := by decide +kernel
private theorem receipt_2_14_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 512 128 = 63279542525408156339701212960 := by decide +kernel
private theorem receipt_2_14_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 640 128 = 56072460554921635189198690080 := by decide +kernel
private theorem receipt_2_14_2402_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 768 128 = 49142339214674915411451791136 := by decide +kernel
private theorem receipt_2_14_2402_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 896 128 = 42482843867899899567253649184 := by decide +kernel
private theorem receipt_2_14_2402_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1024 128 = 36087709322554738180396918560 := by decide +kernel
private theorem receipt_2_14_2402_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1152 128 = 29950739522982462324171659040 := by decide +kernel
private theorem receipt_2_14_2402_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1280 128 = 24065808958091407444852664295 := by decide +kernel
private theorem receipt_2_14_2402_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1408 128 = 18426867247074055470498569415 := by decide +kernel
private theorem receipt_2_14_2402_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1536 128 = 13027917633581859240748517526 := by decide +kernel
private theorem receipt_2_14_2402_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1664 128 = 7863025157537515008291734703 := by decide +kernel
private theorem receipt_2_14_2402_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1792 128 = 2926322662197357419329837413 := by decide +kernel
private theorem receipt_2_14_2402_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1920 15 = 30103389020313662242045773 := by decide +kernel
private theorem receipt_2_14_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 0 256 = 181633564009699394862855061056 :=
  phaseBlock_append receipt_2_14_2402_1_part0 receipt_2_14_2402_1_part1 rfl rfl rfl
private theorem receipt_2_14_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 256 256 = 149320265493822628490478763584 :=
  phaseBlock_append receipt_2_14_2402_1_part2 receipt_2_14_2402_1_part3 rfl rfl rfl
private theorem receipt_2_14_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 0 512 = 330953829503522023353333824640 :=
  phaseBlock_append receipt_2_14_2402_1_join0 receipt_2_14_2402_1_join1 rfl rfl rfl
private theorem receipt_2_14_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 512 256 = 119352003080329791528899903040 :=
  phaseBlock_append receipt_2_14_2402_1_part4 receipt_2_14_2402_1_part5 rfl rfl rfl
private theorem receipt_2_14_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 768 256 = 91625183082574814978705440320 :=
  phaseBlock_append receipt_2_14_2402_1_part6 receipt_2_14_2402_1_part7 rfl rfl rfl
private theorem receipt_2_14_2402_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 512 512 = 210977186162904606507605343360 :=
  phaseBlock_append receipt_2_14_2402_1_join3 receipt_2_14_2402_1_join4 rfl rfl rfl
private theorem receipt_2_14_2402_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 0 1024 = 541931015666426629860939168000 :=
  phaseBlock_append receipt_2_14_2402_1_join2 receipt_2_14_2402_1_join5 rfl rfl rfl
private theorem receipt_2_14_2402_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1024 256 = 66038448845537200504568577600 :=
  phaseBlock_append receipt_2_14_2402_1_part8 receipt_2_14_2402_1_part9 rfl rfl rfl
private theorem receipt_2_14_2402_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1280 256 = 42492676205165462915351233710 :=
  phaseBlock_append receipt_2_14_2402_1_part10 receipt_2_14_2402_1_part11 rfl rfl rfl
private theorem receipt_2_14_2402_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1024 512 = 108531125050702663419919811310 :=
  phaseBlock_append receipt_2_14_2402_1_join7 receipt_2_14_2402_1_join8 rfl rfl rfl
private theorem receipt_2_14_2402_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1536 256 = 20890942791119374249040252229 :=
  phaseBlock_append receipt_2_14_2402_1_part12 receipt_2_14_2402_1_part13 rfl rfl rfl
private theorem receipt_2_14_2402_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1792 143 = 2956426051217671081571883186 :=
  phaseBlock_append receipt_2_14_2402_1_part14 receipt_2_14_2402_1_part15 rfl rfl rfl
private theorem receipt_2_14_2402_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1536 399 = 23847368842337045330612135415 :=
  phaseBlock_append receipt_2_14_2402_1_join10 receipt_2_14_2402_1_join11 rfl rfl rfl
private theorem receipt_2_14_2402_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 1024 911 = 132378493893039708750531946725 :=
  phaseBlock_append receipt_2_14_2402_1_join9 receipt_2_14_2402_1_join12 rfl rfl rfl
private theorem receipt_2_14_2402_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2402 73 1 0 7 1) 0 1935 = 674309509559466338611471114725 :=
  phaseBlock_append receipt_2_14_2402_1_join6 receipt_2_14_2402_1_join13 rfl rfl rfl

private theorem receipt_2_14_2402_1 : fastPhase (bank 2 14).shape 179798 2402 73 1 0 7 1 = 674309509559466338611471114725 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2402_1_join14

private theorem receipt_2_14_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 0 128 = 95073295206535997845582783968 := by decide +kernel
private theorem receipt_2_14_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 128 128 = 86691194955863509738683520480 := by decide +kernel
private theorem receipt_2_14_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 256 128 = 78612152564027964862908761568 := by decide +kernel
private theorem receipt_2_14_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 384 128 = 70829551784414662155934021088 := by decide +kernel
private theorem receipt_2_14_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 512 128 = 63336847053249920955988239840 := by decide +kernel
private theorem receipt_2_14_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 640 128 = 56127563181248938374399464928 := by decide +kernel
private theorem receipt_2_14_2403_0_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 768 128 = 49195295045263646668140529120 := by decide +kernel
private theorem receipt_2_14_2403_0_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 896 128 = 42533707279930570612374730208 := by decide +kernel
private theorem receipt_2_14_2403_0_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1024 128 = 36136533969318684873001510368 := by decide +kernel
private theorem receipt_2_14_2403_0_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1152 128 = 29997578338577271379202135520 := by decide +kernel
private theorem receipt_2_14_2403_0_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1280 128 = 24110714100641207457613268080 := by decide +kernel
private theorem receipt_2_14_2403_0_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1408 128 = 18469890185530145141546688159 := by decide +kernel
private theorem receipt_2_14_2403_0_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1536 128 = 13069109292396325109373857621 := by decide +kernel
private theorem receipt_2_14_2403_0_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1664 128 = 7902435751061134423854952329 := by decide +kernel
private theorem receipt_2_14_2403_0_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1792 128 = 2964001698088840201591884771 := by decide +kernel
private theorem receipt_2_14_2403_0_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1920 15 = 34407814645535967228932199 := by decide +kernel
private theorem receipt_2_14_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 0 256 = 181764490162399507584266304448 :=
  phaseBlock_append receipt_2_14_2403_0_part0 receipt_2_14_2403_0_part1 rfl rfl rfl
private theorem receipt_2_14_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 256 256 = 149441704348442627018842782656 :=
  phaseBlock_append receipt_2_14_2403_0_part2 receipt_2_14_2403_0_part3 rfl rfl rfl
private theorem receipt_2_14_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 0 512 = 331206194510842134603109087104 :=
  phaseBlock_append receipt_2_14_2403_0_join0 receipt_2_14_2403_0_join1 rfl rfl rfl
private theorem receipt_2_14_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 512 256 = 119464410234498859330387704768 :=
  phaseBlock_append receipt_2_14_2403_0_part4 receipt_2_14_2403_0_part5 rfl rfl rfl
private theorem receipt_2_14_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 768 256 = 91729002325194217280515259328 :=
  phaseBlock_append receipt_2_14_2403_0_part6 receipt_2_14_2403_0_part7 rfl rfl rfl
private theorem receipt_2_14_2403_0_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 512 512 = 211193412559693076610902964096 :=
  phaseBlock_append receipt_2_14_2403_0_join3 receipt_2_14_2403_0_join4 rfl rfl rfl
private theorem receipt_2_14_2403_0_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 0 1024 = 542399607070535211214012051200 :=
  phaseBlock_append receipt_2_14_2403_0_join2 receipt_2_14_2403_0_join5 rfl rfl rfl
private theorem receipt_2_14_2403_0_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1024 256 = 66134112307895956252203645888 :=
  phaseBlock_append receipt_2_14_2403_0_part8 receipt_2_14_2403_0_part9 rfl rfl rfl
private theorem receipt_2_14_2403_0_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1280 256 = 42580604286171352599159956239 :=
  phaseBlock_append receipt_2_14_2403_0_part10 receipt_2_14_2403_0_part11 rfl rfl rfl
private theorem receipt_2_14_2403_0_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1024 512 = 108714716594067308851363602127 :=
  phaseBlock_append receipt_2_14_2403_0_join7 receipt_2_14_2403_0_join8 rfl rfl rfl
private theorem receipt_2_14_2403_0_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1536 256 = 20971545043457459533228809950 :=
  phaseBlock_append receipt_2_14_2403_0_part12 receipt_2_14_2403_0_part13 rfl rfl rfl
private theorem receipt_2_14_2403_0_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1792 143 = 2998409512734376168820816970 :=
  phaseBlock_append receipt_2_14_2403_0_part14 receipt_2_14_2403_0_part15 rfl rfl rfl
private theorem receipt_2_14_2403_0_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1536 399 = 23969954556191835702049626920 :=
  phaseBlock_append receipt_2_14_2403_0_join10 receipt_2_14_2403_0_join11 rfl rfl rfl
private theorem receipt_2_14_2403_0_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 1024 911 = 132684671150259144553413229047 :=
  phaseBlock_append receipt_2_14_2403_0_join9 receipt_2_14_2403_0_join12 rfl rfl rfl
private theorem receipt_2_14_2403_0_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 0) 0 1935 = 675084278220794355767425280247 :=
  phaseBlock_append receipt_2_14_2403_0_join6 receipt_2_14_2403_0_join13 rfl rfl rfl

private theorem receipt_2_14_2403_0 : fastPhase (bank 2 14).shape 179798 2403 73 1 0 7 0 = 675084278220794355767425280247 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2403_0_join14

private theorem receipt_2_14_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 0 128 = 95007470004342508578575548512 := by decide +kernel
private theorem receipt_2_14_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 128 128 = 86627695434112212325628735584 := by decide +kernel
private theorem receipt_2_14_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 256 128 = 78550928209894514246904307808 := by decide +kernel
private theorem receipt_2_14_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 384 128 = 70770552625311619591226413152 := by decide +kernel
private theorem receipt_2_14_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 512 128 = 63280023654466301967059042400 := by decide +kernel
private theorem receipt_2_14_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 640 128 = 56072866643589760715051708512 := by decide +kernel
private theorem receipt_2_14_2403_1_part6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 768 128 = 49142677002689478280585125984 := by decide +kernel
private theorem receipt_2_14_2403_1_part7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 896 128 = 42483119897197077586316890208 := by decide +kernel
private theorem receipt_2_14_2403_1_part8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1024 128 = 36087929939616179404727156832 := by decide +kernel
private theorem receipt_2_14_2403_1_part9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1152 128 = 29950910881170259730664321120 := by decide +kernel
private theorem receipt_2_14_2403_1_part10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1280 128 = 24065936955456999900403911049 := by decide +kernel
private theorem receipt_2_14_2403_1_part11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1408 128 = 18426957592831183487486883551 := by decide +kernel
private theorem receipt_2_14_2403_1_part12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1536 128 = 13027976003368965985889409657 := by decide +kernel
private theorem receipt_2_14_2403_1_part13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1664 128 = 7863057034350277727751194460 := by decide +kernel
private theorem receipt_2_14_2403_1_part14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1792 128 = 2926333337442915826820264563 := by decide +kernel
private theorem receipt_2_14_2403_1_part15 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1920 15 = 30103489701551496846189119 := by decide +kernel
private theorem receipt_2_14_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 0 256 = 181635165438454720904204284096 :=
  phaseBlock_append receipt_2_14_2403_1_part0 receipt_2_14_2403_1_part1 rfl rfl rfl
private theorem receipt_2_14_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 256 256 = 149321480835206133838130720960 :=
  phaseBlock_append receipt_2_14_2403_1_part2 receipt_2_14_2403_1_part3 rfl rfl rfl
private theorem receipt_2_14_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 0 512 = 330956646273660854742335005056 :=
  phaseBlock_append receipt_2_14_2403_1_join0 receipt_2_14_2403_1_join1 rfl rfl rfl
private theorem receipt_2_14_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 512 256 = 119352890298056062682110750912 :=
  phaseBlock_append receipt_2_14_2403_1_part4 receipt_2_14_2403_1_part5 rfl rfl rfl
private theorem receipt_2_14_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 768 256 = 91625796899886555866902016192 :=
  phaseBlock_append receipt_2_14_2403_1_part6 receipt_2_14_2403_1_part7 rfl rfl rfl
private theorem receipt_2_14_2403_1_join5 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 512 512 = 210978687197942618549012767104 :=
  phaseBlock_append receipt_2_14_2403_1_join3 receipt_2_14_2403_1_join4 rfl rfl rfl
private theorem receipt_2_14_2403_1_join6 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 0 1024 = 541935333471603473291347772160 :=
  phaseBlock_append receipt_2_14_2403_1_join2 receipt_2_14_2403_1_join5 rfl rfl rfl
private theorem receipt_2_14_2403_1_join7 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1024 256 = 66038840820786439135391477952 :=
  phaseBlock_append receipt_2_14_2403_1_part8 receipt_2_14_2403_1_part9 rfl rfl rfl
private theorem receipt_2_14_2403_1_join8 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1280 256 = 42492894548288183387890794600 :=
  phaseBlock_append receipt_2_14_2403_1_part10 receipt_2_14_2403_1_part11 rfl rfl rfl
private theorem receipt_2_14_2403_1_join9 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1024 512 = 108531735369074622523282272552 :=
  phaseBlock_append receipt_2_14_2403_1_join7 receipt_2_14_2403_1_join8 rfl rfl rfl
private theorem receipt_2_14_2403_1_join10 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1536 256 = 20891033037719243713640604117 :=
  phaseBlock_append receipt_2_14_2403_1_part12 receipt_2_14_2403_1_part13 rfl rfl rfl
private theorem receipt_2_14_2403_1_join11 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1792 143 = 2956436827144467323666453682 :=
  phaseBlock_append receipt_2_14_2403_1_part14 receipt_2_14_2403_1_part15 rfl rfl rfl
private theorem receipt_2_14_2403_1_join12 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1536 399 = 23847469864863711037307057799 :=
  phaseBlock_append receipt_2_14_2403_1_join10 receipt_2_14_2403_1_join11 rfl rfl rfl
private theorem receipt_2_14_2403_1_join13 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 1024 911 = 132379205233938333560589330351 :=
  phaseBlock_append receipt_2_14_2403_1_join9 receipt_2_14_2403_1_join12 rfl rfl rfl
private theorem receipt_2_14_2403_1_join14 :
    phaseBlock (fastLayer (bank 2 14).shape 179798 2403 73 1 0 7 1) 0 1935 = 674314538705541806851937102511 :=
  phaseBlock_append receipt_2_14_2403_1_join6 receipt_2_14_2403_1_join13 rfl rfl rfl

private theorem receipt_2_14_2403_1 : fastPhase (bank 2 14).shape 179798 2403 73 1 0 7 1 = 674314538705541806851937102511 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_14_2403_1_join14

theorem receipt_2_14 : Checked (bank 2 14) 73 0 7 := by
  refine checked_from_values (bank 2 14) 73 0 7
    (P3_7_1.checked (bank 2 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_14_2402_0 receipt_2_14_2402_1 receipt_2_14_2403_0 receipt_2_14_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_14_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 0 128 = 21849005461907120317189970112 := by decide +kernel
private theorem receipt_3_14_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 128 128 = 20021789919704312811172485312 := by decide +kernel
private theorem receipt_3_14_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 256 128 = 18245220024142396199256250560 := by decide +kernel
private theorem receipt_3_14_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 384 128 = 16520267333447616460458055872 := by decide +kernel
private theorem receipt_3_14_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 512 128 = 14847897740493165853981268160 := by decide +kernel
private theorem receipt_3_14_2402_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 640 128 = 13229071482215708362745272512 := by decide +kernel
private theorem receipt_3_14_2402_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 768 128 = 11664743149031905136914913472 := by decide +kernel
private theorem receipt_3_14_2402_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 896 128 = 10155861694254939937429936320 := by decide +kernel
private theorem receipt_3_14_2402_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1024 128 = 8703370443511044579534428352 := by decide +kernel
private theorem receipt_3_14_2402_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1152 128 = 7308207104156024376306260160 := by decide +kernel
private theorem receipt_3_14_2402_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1280 128 = 5971303774691783582186526912 := by decide +kernel
private theorem receipt_3_14_2402_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1408 128 = 4693586954182850836508989632 := by decide +kernel
private theorem receipt_3_14_2402_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1536 128 = 3475977551672904607029516480 := by decide +kernel
private theorem receipt_3_14_2402_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1664 128 = 2319390895601298633455524032 := by decide +kernel
private theorem receipt_3_14_2402_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1792 128 = 1224736743219587370975418560 := by decide +kernel
private theorem receipt_3_14_2402_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1920 88 = 239638339940360537770898436 := by decide +kernel
private theorem receipt_3_14_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 0 256 = 41870795381611433128362455424 :=
  phaseBlock_append receipt_3_14_2402_0_part0 receipt_3_14_2402_0_part1 rfl rfl rfl
private theorem receipt_3_14_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 256 256 = 34765487357590012659714306432 :=
  phaseBlock_append receipt_3_14_2402_0_part2 receipt_3_14_2402_0_part3 rfl rfl rfl
private theorem receipt_3_14_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 0 512 = 76636282739201445788076761856 :=
  phaseBlock_append receipt_3_14_2402_0_join0 receipt_3_14_2402_0_join1 rfl rfl rfl
private theorem receipt_3_14_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 512 256 = 28076969222708874216726540672 :=
  phaseBlock_append receipt_3_14_2402_0_part4 receipt_3_14_2402_0_part5 rfl rfl rfl
private theorem receipt_3_14_2402_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 768 256 = 21820604843286845074344849792 :=
  phaseBlock_append receipt_3_14_2402_0_part6 receipt_3_14_2402_0_part7 rfl rfl rfl
private theorem receipt_3_14_2402_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 512 512 = 49897574065995719291071390464 :=
  phaseBlock_append receipt_3_14_2402_0_join3 receipt_3_14_2402_0_join4 rfl rfl rfl
private theorem receipt_3_14_2402_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 0 1024 = 126533856805197165079148152320 :=
  phaseBlock_append receipt_3_14_2402_0_join2 receipt_3_14_2402_0_join5 rfl rfl rfl
private theorem receipt_3_14_2402_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1024 256 = 16011577547667068955840688512 :=
  phaseBlock_append receipt_3_14_2402_0_part8 receipt_3_14_2402_0_part9 rfl rfl rfl
private theorem receipt_3_14_2402_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1280 256 = 10664890728874634418695516544 :=
  phaseBlock_append receipt_3_14_2402_0_part10 receipt_3_14_2402_0_part11 rfl rfl rfl
private theorem receipt_3_14_2402_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1024 512 = 26676468276541703374536205056 :=
  phaseBlock_append receipt_3_14_2402_0_join7 receipt_3_14_2402_0_join8 rfl rfl rfl
private theorem receipt_3_14_2402_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1536 256 = 5795368447274203240485040512 :=
  phaseBlock_append receipt_3_14_2402_0_part12 receipt_3_14_2402_0_part13 rfl rfl rfl
private theorem receipt_3_14_2402_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1792 216 = 1464375083159947908746316996 :=
  phaseBlock_append receipt_3_14_2402_0_part14 receipt_3_14_2402_0_part15 rfl rfl rfl
private theorem receipt_3_14_2402_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1536 472 = 7259743530434151149231357508 :=
  phaseBlock_append receipt_3_14_2402_0_join10 receipt_3_14_2402_0_join11 rfl rfl rfl
private theorem receipt_3_14_2402_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 1024 984 = 33936211806975854523767562564 :=
  phaseBlock_append receipt_3_14_2402_0_join9 receipt_3_14_2402_0_join12 rfl rfl rfl
private theorem receipt_3_14_2402_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 0) 0 2008 = 160470068612173019602915714884 :=
  phaseBlock_append receipt_3_14_2402_0_join6 receipt_3_14_2402_0_join13 rfl rfl rfl

private theorem receipt_3_14_2402_0 : fastPhase (bank 3 14).shape 179798 2402 73 1 1 1 0 = 160470068612173019602915714884 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2402_0_join14

private theorem receipt_3_14_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 0 128 = 21834731509067554835649468480 := by decide +kernel
private theorem receipt_3_14_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 128 128 = 20007890477552917535048038464 := by decide +kernel
private theorem receipt_3_14_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 256 128 = 18231703355603903225329866816 := by decide +kernel
private theorem receipt_3_14_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 384 128 = 16507141654782968723691812928 := by decide +kernel
private theorem receipt_3_14_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 512 128 = 14835171221376054887841044544 := by decide +kernel
private theorem receipt_3_14_2402_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 640 128 = 13216752245809112059524479040 := by decide +kernel
private theorem receipt_3_14_2402_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 768 128 = 11652839272064625508058224704 := by decide +kernel
private theorem receipt_3_14_2402_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 896 128 = 10144381207098140873857022016 := by decide +kernel
private theorem receipt_3_14_2402_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1024 128 = 8692321330254789611963684928 := by decide +kernel
private theorem receipt_3_14_2402_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1152 128 = 7297597302685814435578542144 := by decide +kernel
private theorem receipt_3_14_2402_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1280 128 = 5961141176765094759588878400 := by decide +kernel
private theorem receipt_3_14_2402_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1408 128 = 4683879405505672144098375744 := by decide +kernel
private theorem receipt_3_14_2402_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1536 128 = 3466732851976275737956554816 := by decide +kernel
private theorem receipt_3_14_2402_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1664 128 = 2310616798717847722288216128 := by decide +kernel
private theorem receipt_3_14_2402_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1792 128 = 1216440957160068754022881344 := by decide +kernel
private theorem receipt_3_14_2402_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1920 88 = 234216428246894752956005148 := by decide +kernel
private theorem receipt_3_14_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 0 256 = 41842621986620472370697506944 :=
  phaseBlock_append receipt_3_14_2402_1_part0 receipt_3_14_2402_1_part1 rfl rfl rfl
private theorem receipt_3_14_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 256 256 = 34738845010386871949021679744 :=
  phaseBlock_append receipt_3_14_2402_1_part2 receipt_3_14_2402_1_part3 rfl rfl rfl
private theorem receipt_3_14_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 0 512 = 76581466997007344319719186688 :=
  phaseBlock_append receipt_3_14_2402_1_join0 receipt_3_14_2402_1_join1 rfl rfl rfl
private theorem receipt_3_14_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 512 256 = 28051923467185166947365523584 :=
  phaseBlock_append receipt_3_14_2402_1_part4 receipt_3_14_2402_1_part5 rfl rfl rfl
private theorem receipt_3_14_2402_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 768 256 = 21797220479162766381915246720 :=
  phaseBlock_append receipt_3_14_2402_1_part6 receipt_3_14_2402_1_part7 rfl rfl rfl
private theorem receipt_3_14_2402_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 512 512 = 49849143946347933329280770304 :=
  phaseBlock_append receipt_3_14_2402_1_join3 receipt_3_14_2402_1_join4 rfl rfl rfl
private theorem receipt_3_14_2402_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 0 1024 = 126430610943355277648999956992 :=
  phaseBlock_append receipt_3_14_2402_1_join2 receipt_3_14_2402_1_join5 rfl rfl rfl
private theorem receipt_3_14_2402_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1024 256 = 15989918632940604047542227072 :=
  phaseBlock_append receipt_3_14_2402_1_part8 receipt_3_14_2402_1_part9 rfl rfl rfl
private theorem receipt_3_14_2402_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1280 256 = 10645020582270766903687254144 :=
  phaseBlock_append receipt_3_14_2402_1_part10 receipt_3_14_2402_1_part11 rfl rfl rfl
private theorem receipt_3_14_2402_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1024 512 = 26634939215211370951229481216 :=
  phaseBlock_append receipt_3_14_2402_1_join7 receipt_3_14_2402_1_join8 rfl rfl rfl
private theorem receipt_3_14_2402_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1536 256 = 5777349650694123460244770944 :=
  phaseBlock_append receipt_3_14_2402_1_part12 receipt_3_14_2402_1_part13 rfl rfl rfl
private theorem receipt_3_14_2402_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1792 216 = 1450657385406963506978886492 :=
  phaseBlock_append receipt_3_14_2402_1_part14 receipt_3_14_2402_1_part15 rfl rfl rfl
private theorem receipt_3_14_2402_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1536 472 = 7228007036101086967223657436 :=
  phaseBlock_append receipt_3_14_2402_1_join10 receipt_3_14_2402_1_join11 rfl rfl rfl
private theorem receipt_3_14_2402_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 1024 984 = 33862946251312457918453138652 :=
  phaseBlock_append receipt_3_14_2402_1_join9 receipt_3_14_2402_1_join12 rfl rfl rfl
private theorem receipt_3_14_2402_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2402 73 1 1 1 1) 0 2008 = 160293557194667735567453095644 :=
  phaseBlock_append receipt_3_14_2402_1_join6 receipt_3_14_2402_1_join13 rfl rfl rfl

private theorem receipt_3_14_2402_1 : fastPhase (bank 3 14).shape 179798 2402 73 1 1 1 1 = 160293557194667735567453095644 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2402_1_join14

private theorem receipt_3_14_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 0 128 = 21849200266046920178090202720 := by decide +kernel
private theorem receipt_3_14_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 128 128 = 20021956793142613654913091168 := by decide +kernel
private theorem receipt_3_14_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 256 128 = 18245361605726176245034038880 := by decide +kernel
private theorem receipt_3_14_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 384 128 = 16520386144474960701672023648 := by decide +kernel
private theorem receipt_3_14_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 512 128 = 14847996185276105235857413728 := by decide +kernel
private theorem receipt_3_14_2403_0_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 640 128 = 13229151848642179350659188320 := by decide +kernel
private theorem receipt_3_14_2403_0_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 768 128 = 11664807609126829675412158048 := by decide +kernel
private theorem receipt_3_14_2403_0_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 896 128 = 10155912304740425799944185440 := by decide +kernel
private theorem receipt_3_14_2403_0_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1024 128 = 8703409146365706108803405408 := by decide +kernel
private theorem receipt_3_14_2403_0_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1152 128 = 7308235727173423615485445728 := by decide +kernel
private theorem receipt_3_14_2403_0_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1280 128 = 5971324032037991796660647520 := by decide +kernel
private theorem receipt_3_14_2403_0_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1408 128 = 4693600446953130426401285728 := by decide +kernel
private theorem receipt_3_14_2403_0_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1536 128 = 3475985768447511410408789600 := by decide +kernel
private theorem receipt_3_14_2403_0_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1664 128 = 2319395213000404620240963168 := by decide +kernel
private theorem receipt_3_14_2403_0_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1792 128 = 1224738426457323727539205728 := by decide +kernel
private theorem receipt_3_14_2403_0_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1920 88 = 239638573498428548942745786 := by decide +kernel
private theorem receipt_3_14_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 0 256 = 41871157059189533833003293888 :=
  phaseBlock_append receipt_3_14_2403_0_part0 receipt_3_14_2403_0_part1 rfl rfl rfl
private theorem receipt_3_14_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 256 256 = 34765747750201136946706062528 :=
  phaseBlock_append receipt_3_14_2403_0_part2 receipt_3_14_2403_0_part3 rfl rfl rfl
private theorem receipt_3_14_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 0 512 = 76636904809390670779709356416 :=
  phaseBlock_append receipt_3_14_2403_0_join0 receipt_3_14_2403_0_join1 rfl rfl rfl
private theorem receipt_3_14_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 512 256 = 28077148033918284586516602048 :=
  phaseBlock_append receipt_3_14_2403_0_part4 receipt_3_14_2403_0_part5 rfl rfl rfl
private theorem receipt_3_14_2403_0_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 768 256 = 21820719913867255475356343488 :=
  phaseBlock_append receipt_3_14_2403_0_part6 receipt_3_14_2403_0_part7 rfl rfl rfl
private theorem receipt_3_14_2403_0_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 512 512 = 49897867947785540061872945536 :=
  phaseBlock_append receipt_3_14_2403_0_join3 receipt_3_14_2403_0_join4 rfl rfl rfl
private theorem receipt_3_14_2403_0_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 0 1024 = 126534772757176210841582301952 :=
  phaseBlock_append receipt_3_14_2403_0_join2 receipt_3_14_2403_0_join5 rfl rfl rfl
private theorem receipt_3_14_2403_0_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1024 256 = 16011644873539129724288851136 :=
  phaseBlock_append receipt_3_14_2403_0_part8 receipt_3_14_2403_0_part9 rfl rfl rfl
private theorem receipt_3_14_2403_0_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1280 256 = 10664924478991122223061933248 :=
  phaseBlock_append receipt_3_14_2403_0_part10 receipt_3_14_2403_0_part11 rfl rfl rfl
private theorem receipt_3_14_2403_0_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1024 512 = 26676569352530251947350784384 :=
  phaseBlock_append receipt_3_14_2403_0_join7 receipt_3_14_2403_0_join8 rfl rfl rfl
private theorem receipt_3_14_2403_0_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1536 256 = 5795380981447916030649752768 :=
  phaseBlock_append receipt_3_14_2403_0_part12 receipt_3_14_2403_0_part13 rfl rfl rfl
private theorem receipt_3_14_2403_0_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1792 216 = 1464376999955752276481951514 :=
  phaseBlock_append receipt_3_14_2403_0_part14 receipt_3_14_2403_0_part15 rfl rfl rfl
private theorem receipt_3_14_2403_0_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1536 472 = 7259757981403668307131704282 :=
  phaseBlock_append receipt_3_14_2403_0_join10 receipt_3_14_2403_0_join11 rfl rfl rfl
private theorem receipt_3_14_2403_0_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 1024 984 = 33936327333933920254482488666 :=
  phaseBlock_append receipt_3_14_2403_0_join9 receipt_3_14_2403_0_join12 rfl rfl rfl
private theorem receipt_3_14_2403_0_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 0) 0 2008 = 160471100091110131096064790618 :=
  phaseBlock_append receipt_3_14_2403_0_join6 receipt_3_14_2403_0_join13 rfl rfl rfl

private theorem receipt_3_14_2403_0 : fastPhase (bank 3 14).shape 179798 2403 73 1 1 1 0 = 160471100091110131096064790618 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2403_0_join14

private theorem receipt_3_14_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 0 128 = 21834926165627572956996201120 := by decide +kernel
private theorem receipt_3_14_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 128 128 = 20008057217249526417343044256 := by decide +kernel
private theorem receipt_3_14_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 256 128 = 18231844816634422810352241312 := by decide +kernel
private theorem receipt_3_14_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 384 128 = 16507260357799241004349110944 := by decide +kernel
private theorem receipt_3_14_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 512 128 = 14835269570047277450797001376 := by decide +kernel
private theorem receipt_3_14_2403_1_part5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 640 128 = 13216832527383792018524510880 := by decide +kernel
private theorem receipt_3_14_2403_1_part6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 768 128 = 11652903657931653827952708256 := by decide +kernel
private theorem receipt_3_14_2403_1_part7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 896 128 = 10144431753346987085322353312 := by decide +kernel
private theorem receipt_3_14_2403_1_part8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1024 128 = 8692359978234816916921117344 := by decide +kernel
private theorem receipt_3_14_2403_1_part9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1152 128 = 7297625879564715203310803616 := by decide +kernel
private theorem receipt_3_14_2403_1_part10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1280 128 = 5961161396086446413554567840 := by decide +kernel
private theorem receipt_3_14_2403_1_part11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1408 128 = 4683892867745613439444138656 := by decide +kernel
private theorem receipt_3_14_2403_1_part12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1536 128 = 3466741045099303429727038112 := by decide +kernel
private theorem receipt_3_14_2403_1_part13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1664 128 = 2310621098731733624333802144 := by decide +kernel
private theorem receipt_3_14_2403_1_part14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1792 128 = 1216442628669897188605201056 := by decide +kernel
private theorem receipt_3_14_2403_1_part15 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1920 88 = 234216656708819756394650502 := by decide +kernel
private theorem receipt_3_14_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 0 256 = 41842983382877099374339245376 :=
  phaseBlock_append receipt_3_14_2403_1_part0 receipt_3_14_2403_1_part1 rfl rfl rfl
private theorem receipt_3_14_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 256 256 = 34739105174433663814701352256 :=
  phaseBlock_append receipt_3_14_2403_1_part2 receipt_3_14_2403_1_part3 rfl rfl rfl
private theorem receipt_3_14_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 0 512 = 76582088557310763189040597632 :=
  phaseBlock_append receipt_3_14_2403_1_join0 receipt_3_14_2403_1_join1 rfl rfl rfl
private theorem receipt_3_14_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 512 256 = 28052102097431069469321512256 :=
  phaseBlock_append receipt_3_14_2403_1_part4 receipt_3_14_2403_1_part5 rfl rfl rfl
private theorem receipt_3_14_2403_1_join4 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 768 256 = 21797335411278640913275061568 :=
  phaseBlock_append receipt_3_14_2403_1_part6 receipt_3_14_2403_1_part7 rfl rfl rfl
private theorem receipt_3_14_2403_1_join5 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 512 512 = 49849437508709710382596573824 :=
  phaseBlock_append receipt_3_14_2403_1_join3 receipt_3_14_2403_1_join4 rfl rfl rfl
private theorem receipt_3_14_2403_1_join6 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 0 1024 = 126431526066020473571637171456 :=
  phaseBlock_append receipt_3_14_2403_1_join2 receipt_3_14_2403_1_join5 rfl rfl rfl
private theorem receipt_3_14_2403_1_join7 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1024 256 = 15989985857799532120231920960 :=
  phaseBlock_append receipt_3_14_2403_1_part8 receipt_3_14_2403_1_part9 rfl rfl rfl
private theorem receipt_3_14_2403_1_join8 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1280 256 = 10645054263832059852998706496 :=
  phaseBlock_append receipt_3_14_2403_1_part10 receipt_3_14_2403_1_part11 rfl rfl rfl
private theorem receipt_3_14_2403_1_join9 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1024 512 = 26635040121631591973230627456 :=
  phaseBlock_append receipt_3_14_2403_1_join7 receipt_3_14_2403_1_join8 rfl rfl rfl
private theorem receipt_3_14_2403_1_join10 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1536 256 = 5777362143831037054060840256 :=
  phaseBlock_append receipt_3_14_2403_1_part12 receipt_3_14_2403_1_part13 rfl rfl rfl
private theorem receipt_3_14_2403_1_join11 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1792 216 = 1450659285378716944999851558 :=
  phaseBlock_append receipt_3_14_2403_1_part14 receipt_3_14_2403_1_part15 rfl rfl rfl
private theorem receipt_3_14_2403_1_join12 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1536 472 = 7228021429209753999060691814 :=
  phaseBlock_append receipt_3_14_2403_1_join10 receipt_3_14_2403_1_join11 rfl rfl rfl
private theorem receipt_3_14_2403_1_join13 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 1024 984 = 33863061550841345972291319270 :=
  phaseBlock_append receipt_3_14_2403_1_join9 receipt_3_14_2403_1_join12 rfl rfl rfl
private theorem receipt_3_14_2403_1_join14 :
    phaseBlock (fastLayer (bank 3 14).shape 179798 2403 73 1 1 1 1) 0 2008 = 160294587616861819543928490726 :=
  phaseBlock_append receipt_3_14_2403_1_join6 receipt_3_14_2403_1_join13 rfl rfl rfl

private theorem receipt_3_14_2403_1 : fastPhase (bank 3 14).shape 179798 2403 73 1 1 1 1 = 160294587616861819543928490726 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_14_2403_1_join14

theorem receipt_3_14 : Checked (bank 3 14) 73 1 1 := by
  refine checked_from_values (bank 3 14) 73 1 1
    (P3_7_1.checked (bank 3 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9203_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_14_2402_0 receipt_3_14_2402_1 receipt_3_14_2403_0 receipt_3_14_2403_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group5_stage i)).shape
      (cutoff h rect (group5_stage i)), ¬ G∣Q :=
  (group5_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group5_avoids

end Lower6960.RescueSource
