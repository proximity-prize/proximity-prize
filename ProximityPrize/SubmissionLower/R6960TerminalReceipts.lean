import ProximityPrize.SubmissionLower.R6960TerminalArithmetic
import ProximityPrize.SubmissionLower.HighCore82258Source

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6960.TerminalReceipts
open TerminalArithmetic
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

def terminalBank : P1_7.Bank := ⟨⟨4500,6286,1329,748778⟩,2693670660997120,42045879552530⟩

private theorem moment_6286_1329_part0 :
    blockEstimate 6286 1329 1329 128 = 2214802720 := by decide +kernel
private theorem moment_6286_1329_part1 :
    blockEstimate 6286 1329 1457 128 = 15027586336 := by decide +kernel
private theorem moment_6286_1329_part2 :
    blockEstimate 6286 1329 1585 128 = 39811962144 := by decide +kernel
private theorem moment_6286_1329_part3 :
    blockEstimate 6286 1329 1713 128 = 75762623776 := by decide +kernel
private theorem moment_6286_1329_part4 :
    blockEstimate 6286 1329 1841 128 = 122074264864 := by decide +kernel
private theorem moment_6286_1329_part5 :
    blockEstimate 6286 1329 1969 128 = 177941579040 := by decide +kernel
private theorem moment_6286_1329_part6 :
    blockEstimate 6286 1329 2097 128 = 242559259936 := by decide +kernel
private theorem moment_6286_1329_part7 :
    blockEstimate 6286 1329 2225 128 = 315122001184 := by decide +kernel
private theorem moment_6286_1329_part8 :
    blockEstimate 6286 1329 2353 128 = 394824496416 := by decide +kernel
private theorem moment_6286_1329_part9 :
    blockEstimate 6286 1329 2481 128 = 480861439264 := by decide +kernel
private theorem moment_6286_1329_part10 :
    blockEstimate 6286 1329 2609 128 = 572025083140 := by decide +kernel
private theorem moment_6286_1329_part11 :
    blockEstimate 6286 1329 2737 128 = 662020927680 := by decide +kernel
private theorem moment_6286_1329_part12 :
    blockEstimate 6286 1329 2865 128 = 746536235200 := by decide +kernel
private theorem moment_6286_1329_part13 :
    blockEstimate 6286 1329 2993 128 = 825473118400 := by decide +kernel
private theorem moment_6286_1329_part14 :
    blockEstimate 6286 1329 3121 128 = 898831577280 := by decide +kernel
private theorem moment_6286_1329_part15 :
    blockEstimate 6286 1329 3249 128 = 966611611840 := by decide +kernel
private theorem moment_6286_1329_part16 :
    blockEstimate 6286 1329 3377 128 = 1028813222080 := by decide +kernel
private theorem moment_6286_1329_part17 :
    blockEstimate 6286 1329 3505 128 = 1085436408000 := by decide +kernel
private theorem moment_6286_1329_part18 :
    blockEstimate 6286 1329 3633 128 = 1136481169600 := by decide +kernel
private theorem moment_6286_1329_part19 :
    blockEstimate 6286 1329 3761 128 = 1181947506880 := by decide +kernel
private theorem moment_6286_1329_part20 :
    blockEstimate 6286 1329 3889 128 = 1221835419840 := by decide +kernel
private theorem moment_6286_1329_part21 :
    blockEstimate 6286 1329 4017 128 = 1256144908480 := by decide +kernel
private theorem moment_6286_1329_part22 :
    blockEstimate 6286 1329 4145 128 = 1284875972800 := by decide +kernel
private theorem moment_6286_1329_part23 :
    blockEstimate 6286 1329 4273 128 = 1308028612800 := by decide +kernel
private theorem moment_6286_1329_part24 :
    blockEstimate 6286 1329 4401 128 = 1325602828480 := by decide +kernel
private theorem moment_6286_1329_part25 :
    blockEstimate 6286 1329 4529 128 = 1337598619840 := by decide +kernel
private theorem moment_6286_1329_part26 :
    blockEstimate 6286 1329 4657 128 = 1344015986880 := by decide +kernel
private theorem moment_6286_1329_part27 :
    blockEstimate 6286 1329 4785 128 = 1344854929600 := by decide +kernel
private theorem moment_6286_1329_part28 :
    blockEstimate 6286 1329 4913 128 = 1340115448000 := by decide +kernel
private theorem moment_6286_1329_part29 :
    blockEstimate 6286 1329 5041 128 = 1329797542080 := by decide +kernel
private theorem moment_6286_1329_part30 :
    blockEstimate 6286 1329 5169 128 = 1313901211840 := by decide +kernel
private theorem moment_6286_1329_part31 :
    blockEstimate 6286 1329 5297 128 = 1292426457280 := by decide +kernel
private theorem moment_6286_1329_part32 :
    blockEstimate 6286 1329 5425 128 = 1265373278400 := by decide +kernel
private theorem moment_6286_1329_part33 :
    blockEstimate 6286 1329 5553 128 = 1232741675200 := by decide +kernel
private theorem moment_6286_1329_part34 :
    blockEstimate 6286 1329 5681 128 = 1194531647680 := by decide +kernel
private theorem moment_6286_1329_part35 :
    blockEstimate 6286 1329 5809 128 = 1150743195840 := by decide +kernel
private theorem moment_6286_1329_part36 :
    blockEstimate 6286 1329 5937 128 = 1101376319680 := by decide +kernel
private theorem moment_6286_1329_part37 :
    blockEstimate 6286 1329 6065 128 = 1046431019200 := by decide +kernel
private theorem moment_6286_1329_part38 :
    blockEstimate 6286 1329 6193 128 = 985920946437 := by decide +kernel
private theorem moment_6286_1329_part39 :
    blockEstimate 6286 1329 6321 128 = 921179065408 := by decide +kernel
private theorem moment_6286_1329_part40 :
    blockEstimate 6286 1329 6449 128 = 854891400374 := by decide +kernel
private theorem moment_6286_1329_part41 :
    blockEstimate 6286 1329 6577 128 = 787869474317 := by decide +kernel
private theorem moment_6286_1329_part42 :
    blockEstimate 6286 1329 6705 128 = 720673141815 := by decide +kernel
private theorem moment_6286_1329_part43 :
    blockEstimate 6286 1329 6833 128 = 653842881703 := by decide +kernel
private theorem moment_6286_1329_part44 :
    blockEstimate 6286 1329 6961 128 = 587899797345 := by decide +kernel
private theorem moment_6286_1329_part45 :
    blockEstimate 6286 1329 7089 128 = 523345615005 := by decide +kernel
private theorem moment_6286_1329_part46 :
    blockEstimate 6286 1329 7217 128 = 460662686400 := by decide +kernel
private theorem moment_6286_1329_part47 :
    blockEstimate 6286 1329 7345 128 = 400313987006 := by decide +kernel
private theorem moment_6286_1329_part48 :
    blockEstimate 6286 1329 7473 128 = 342743116198 := by decide +kernel
private theorem moment_6286_1329_part49 :
    blockEstimate 6286 1329 7601 128 = 288069435510 := by decide +kernel
private theorem moment_6286_1329_part50 :
    blockEstimate 6286 1329 7729 128 = 236803710816 := by decide +kernel
private theorem moment_6286_1329_part51 :
    blockEstimate 6286 1329 7857 128 = 189859721056 := by decide +kernel
private theorem moment_6286_1329_part52 :
    blockEstimate 6286 1329 7985 128 = 147494272864 := by decide +kernel
private theorem moment_6286_1329_part53 :
    blockEstimate 6286 1329 8113 128 = 109959024480 := by decide +kernel
private theorem moment_6286_1329_part54 :
    blockEstimate 6286 1329 8241 128 = 77505634144 := by decide +kernel
private theorem moment_6286_1329_part55 :
    blockEstimate 6286 1329 8369 128 = 50385760096 := by decide +kernel
private theorem moment_6286_1329_part56 :
    blockEstimate 6286 1329 8497 128 = 28851060576 := by decide +kernel
private theorem moment_6286_1329_part57 :
    blockEstimate 6286 1329 8625 128 = 13153193824 := by decide +kernel
private theorem moment_6286_1329_part58 :
    blockEstimate 6286 1329 8753 128 = 3543818080 := by decide +kernel
private theorem moment_6286_1329_part59 :
    blockEstimate 6286 1329 8881 63 = 139859376 := by decide +kernel
private theorem moment_6286_1329_join0 :
    blockEstimate 6286 1329 1457 256 = 54839548480 :=
  block_append moment_6286_1329_part1 moment_6286_1329_part2 rfl rfl rfl
private theorem moment_6286_1329_join1 :
    blockEstimate 6286 1329 1329 384 = 57054351200 :=
  block_append moment_6286_1329_part0 moment_6286_1329_join0 rfl rfl rfl
private theorem moment_6286_1329_join2 :
    blockEstimate 6286 1329 1713 256 = 197836888640 :=
  block_append moment_6286_1329_part3 moment_6286_1329_part4 rfl rfl rfl
private theorem moment_6286_1329_join3 :
    blockEstimate 6286 1329 1969 256 = 420500838976 :=
  block_append moment_6286_1329_part5 moment_6286_1329_part6 rfl rfl rfl
private theorem moment_6286_1329_join4 :
    blockEstimate 6286 1329 1713 512 = 618337727616 :=
  block_append moment_6286_1329_join2 moment_6286_1329_join3 rfl rfl rfl
private theorem moment_6286_1329_join5 :
    blockEstimate 6286 1329 1329 896 = 675392078816 :=
  block_append moment_6286_1329_join1 moment_6286_1329_join4 rfl rfl rfl
private theorem moment_6286_1329_join6 :
    blockEstimate 6286 1329 2225 256 = 709946497600 :=
  block_append moment_6286_1329_part7 moment_6286_1329_part8 rfl rfl rfl
private theorem moment_6286_1329_join7 :
    blockEstimate 6286 1329 2481 256 = 1052886522404 :=
  block_append moment_6286_1329_part9 moment_6286_1329_part10 rfl rfl rfl
private theorem moment_6286_1329_join8 :
    blockEstimate 6286 1329 2225 512 = 1762833020004 :=
  block_append moment_6286_1329_join6 moment_6286_1329_join7 rfl rfl rfl
private theorem moment_6286_1329_join9 :
    blockEstimate 6286 1329 2737 256 = 1408557162880 :=
  block_append moment_6286_1329_part11 moment_6286_1329_part12 rfl rfl rfl
private theorem moment_6286_1329_join10 :
    blockEstimate 6286 1329 2993 256 = 1724304695680 :=
  block_append moment_6286_1329_part13 moment_6286_1329_part14 rfl rfl rfl
private theorem moment_6286_1329_join11 :
    blockEstimate 6286 1329 2737 512 = 3132861858560 :=
  block_append moment_6286_1329_join9 moment_6286_1329_join10 rfl rfl rfl
private theorem moment_6286_1329_join12 :
    blockEstimate 6286 1329 2225 1024 = 4895694878564 :=
  block_append moment_6286_1329_join8 moment_6286_1329_join11 rfl rfl rfl
private theorem moment_6286_1329_join13 :
    blockEstimate 6286 1329 1329 1920 = 5571086957380 :=
  block_append moment_6286_1329_join5 moment_6286_1329_join12 rfl rfl rfl
private theorem moment_6286_1329_join14 :
    blockEstimate 6286 1329 3377 256 = 2114249630080 :=
  block_append moment_6286_1329_part16 moment_6286_1329_part17 rfl rfl rfl
private theorem moment_6286_1329_join15 :
    blockEstimate 6286 1329 3249 384 = 3080861241920 :=
  block_append moment_6286_1329_part15 moment_6286_1329_join14 rfl rfl rfl
private theorem moment_6286_1329_join16 :
    blockEstimate 6286 1329 3633 256 = 2318428676480 :=
  block_append moment_6286_1329_part18 moment_6286_1329_part19 rfl rfl rfl
private theorem moment_6286_1329_join17 :
    blockEstimate 6286 1329 3889 256 = 2477980328320 :=
  block_append moment_6286_1329_part20 moment_6286_1329_part21 rfl rfl rfl
private theorem moment_6286_1329_join18 :
    blockEstimate 6286 1329 3633 512 = 4796409004800 :=
  block_append moment_6286_1329_join16 moment_6286_1329_join17 rfl rfl rfl
private theorem moment_6286_1329_join19 :
    blockEstimate 6286 1329 3249 896 = 7877270246720 :=
  block_append moment_6286_1329_join15 moment_6286_1329_join18 rfl rfl rfl
private theorem moment_6286_1329_join20 :
    blockEstimate 6286 1329 4145 256 = 2592904585600 :=
  block_append moment_6286_1329_part22 moment_6286_1329_part23 rfl rfl rfl
private theorem moment_6286_1329_join21 :
    blockEstimate 6286 1329 4401 256 = 2663201448320 :=
  block_append moment_6286_1329_part24 moment_6286_1329_part25 rfl rfl rfl
private theorem moment_6286_1329_join22 :
    blockEstimate 6286 1329 4145 512 = 5256106033920 :=
  block_append moment_6286_1329_join20 moment_6286_1329_join21 rfl rfl rfl
private theorem moment_6286_1329_join23 :
    blockEstimate 6286 1329 4657 256 = 2688870916480 :=
  block_append moment_6286_1329_part26 moment_6286_1329_part27 rfl rfl rfl
private theorem moment_6286_1329_join24 :
    blockEstimate 6286 1329 4913 256 = 2669912990080 :=
  block_append moment_6286_1329_part28 moment_6286_1329_part29 rfl rfl rfl
private theorem moment_6286_1329_join25 :
    blockEstimate 6286 1329 4657 512 = 5358783906560 :=
  block_append moment_6286_1329_join23 moment_6286_1329_join24 rfl rfl rfl
private theorem moment_6286_1329_join26 :
    blockEstimate 6286 1329 4145 1024 = 10614889940480 :=
  block_append moment_6286_1329_join22 moment_6286_1329_join25 rfl rfl rfl
private theorem moment_6286_1329_join27 :
    blockEstimate 6286 1329 3249 1920 = 18492160187200 :=
  block_append moment_6286_1329_join19 moment_6286_1329_join26 rfl rfl rfl
private theorem moment_6286_1329_join28 :
    blockEstimate 6286 1329 1329 3840 = 24063247144580 :=
  block_append moment_6286_1329_join13 moment_6286_1329_join27 rfl rfl rfl
private theorem moment_6286_1329_join29 :
    blockEstimate 6286 1329 5297 256 = 2557799735680 :=
  block_append moment_6286_1329_part31 moment_6286_1329_part32 rfl rfl rfl
private theorem moment_6286_1329_join30 :
    blockEstimate 6286 1329 5169 384 = 3871700947520 :=
  block_append moment_6286_1329_part30 moment_6286_1329_join29 rfl rfl rfl
private theorem moment_6286_1329_join31 :
    blockEstimate 6286 1329 5553 256 = 2427273322880 :=
  block_append moment_6286_1329_part33 moment_6286_1329_part34 rfl rfl rfl
private theorem moment_6286_1329_join32 :
    blockEstimate 6286 1329 5809 256 = 2252119515520 :=
  block_append moment_6286_1329_part35 moment_6286_1329_part36 rfl rfl rfl
private theorem moment_6286_1329_join33 :
    blockEstimate 6286 1329 5553 512 = 4679392838400 :=
  block_append moment_6286_1329_join31 moment_6286_1329_join32 rfl rfl rfl
private theorem moment_6286_1329_join34 :
    blockEstimate 6286 1329 5169 896 = 8551093785920 :=
  block_append moment_6286_1329_join30 moment_6286_1329_join33 rfl rfl rfl
private theorem moment_6286_1329_join35 :
    blockEstimate 6286 1329 6065 256 = 2032351965637 :=
  block_append moment_6286_1329_part37 moment_6286_1329_part38 rfl rfl rfl
private theorem moment_6286_1329_join36 :
    blockEstimate 6286 1329 6321 256 = 1776070465782 :=
  block_append moment_6286_1329_part39 moment_6286_1329_part40 rfl rfl rfl
private theorem moment_6286_1329_join37 :
    blockEstimate 6286 1329 6065 512 = 3808422431419 :=
  block_append moment_6286_1329_join35 moment_6286_1329_join36 rfl rfl rfl
private theorem moment_6286_1329_join38 :
    blockEstimate 6286 1329 6577 256 = 1508542616132 :=
  block_append moment_6286_1329_part41 moment_6286_1329_part42 rfl rfl rfl
private theorem moment_6286_1329_join39 :
    blockEstimate 6286 1329 6833 256 = 1241742679048 :=
  block_append moment_6286_1329_part43 moment_6286_1329_part44 rfl rfl rfl
private theorem moment_6286_1329_join40 :
    blockEstimate 6286 1329 6577 512 = 2750285295180 :=
  block_append moment_6286_1329_join38 moment_6286_1329_join39 rfl rfl rfl
private theorem moment_6286_1329_join41 :
    blockEstimate 6286 1329 6065 1024 = 6558707726599 :=
  block_append moment_6286_1329_join37 moment_6286_1329_join40 rfl rfl rfl
private theorem moment_6286_1329_join42 :
    blockEstimate 6286 1329 5169 1920 = 15109801512519 :=
  block_append moment_6286_1329_join34 moment_6286_1329_join41 rfl rfl rfl
private theorem moment_6286_1329_join43 :
    blockEstimate 6286 1329 7217 256 = 860976673406 :=
  block_append moment_6286_1329_part46 moment_6286_1329_part47 rfl rfl rfl
private theorem moment_6286_1329_join44 :
    blockEstimate 6286 1329 7089 384 = 1384322288411 :=
  block_append moment_6286_1329_part45 moment_6286_1329_join43 rfl rfl rfl
private theorem moment_6286_1329_join45 :
    blockEstimate 6286 1329 7473 256 = 630812551708 :=
  block_append moment_6286_1329_part48 moment_6286_1329_part49 rfl rfl rfl
private theorem moment_6286_1329_join46 :
    blockEstimate 6286 1329 7729 256 = 426663431872 :=
  block_append moment_6286_1329_part50 moment_6286_1329_part51 rfl rfl rfl
private theorem moment_6286_1329_join47 :
    blockEstimate 6286 1329 7473 512 = 1057475983580 :=
  block_append moment_6286_1329_join45 moment_6286_1329_join46 rfl rfl rfl
private theorem moment_6286_1329_join48 :
    blockEstimate 6286 1329 7089 896 = 2441798271991 :=
  block_append moment_6286_1329_join44 moment_6286_1329_join47 rfl rfl rfl
private theorem moment_6286_1329_join49 :
    blockEstimate 6286 1329 7985 256 = 257453297344 :=
  block_append moment_6286_1329_part52 moment_6286_1329_part53 rfl rfl rfl
private theorem moment_6286_1329_join50 :
    blockEstimate 6286 1329 8241 256 = 127891394240 :=
  block_append moment_6286_1329_part54 moment_6286_1329_part55 rfl rfl rfl
private theorem moment_6286_1329_join51 :
    blockEstimate 6286 1329 7985 512 = 385344691584 :=
  block_append moment_6286_1329_join49 moment_6286_1329_join50 rfl rfl rfl
private theorem moment_6286_1329_join52 :
    blockEstimate 6286 1329 8497 256 = 42004254400 :=
  block_append moment_6286_1329_part56 moment_6286_1329_part57 rfl rfl rfl
private theorem moment_6286_1329_join53 :
    blockEstimate 6286 1329 8753 191 = 3683677456 :=
  block_append moment_6286_1329_part58 moment_6286_1329_part59 rfl rfl rfl
private theorem moment_6286_1329_join54 :
    blockEstimate 6286 1329 8497 447 = 45687931856 :=
  block_append moment_6286_1329_join52 moment_6286_1329_join53 rfl rfl rfl
private theorem moment_6286_1329_join55 :
    blockEstimate 6286 1329 7985 959 = 431032623440 :=
  block_append moment_6286_1329_join51 moment_6286_1329_join54 rfl rfl rfl
private theorem moment_6286_1329_join56 :
    blockEstimate 6286 1329 7089 1855 = 2872830895431 :=
  block_append moment_6286_1329_join48 moment_6286_1329_join55 rfl rfl rfl
private theorem moment_6286_1329_join57 :
    blockEstimate 6286 1329 5169 3775 = 17982632407950 :=
  block_append moment_6286_1329_join42 moment_6286_1329_join56 rfl rfl rfl
private theorem moment_6286_1329_join58 :
    blockEstimate 6286 1329 1329 7615 = 42045879552530 :=
  block_append moment_6286_1329_join28 moment_6286_1329_join57 rfl rfl rfl

private theorem moment_6286_1329 : momentEstimate 6286 1329 = 42045879552530 := moment_6286_1329_join58


theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment_6286_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![655181, 93597], ![1200, 1201]⟩
  | 1 => ⟨![668256, 80522], ![0, 1167]⟩
  | 2 => ⟨![667439, 81339], ![0, 1162]⟩
  | 3 => ⟨![667789, 80989], ![0, 1157]⟩
  | 4 => ⟨![666987, 81791], ![0, 1152]⟩
  | 5 => ⟨![667342, 81436], ![0, 1147]⟩
  | 6 => ⟨![666555, 82223], ![0, 1142]⟩
  | 7 => ⟨![666915, 81863], ![0, 1137]⟩
  | 8 => ⟨![666143, 82635], ![0, 1132]⟩
  | 9 => ⟨![666581, 82197], ![0, 1126]⟩
  | 10 => ⟨![665825, 82953], ![0, 1121]⟩
  | 11 => ⟨![666269, 82509], ![0, 1115]⟩
  | 12 => ⟨![665529, 83249], ![0, 1110]⟩
  | 13 => ⟨![664875, 83903], ![0, 1104]⟩
  | 14 => ⟨![665255, 83523], ![0, 1099]⟩
  | 15 => ⟨![664618, 84160], ![0, 1093]⟩
  | 16 => ⟨![665080, 83698], ![0, 1087]⟩
  | 17 => ⟨![664461, 84317], ![0, 1081]⟩
  | 18 => ⟨![663854, 84924], ![0, 1075]⟩
  | 19 => ⟨![663259, 85519], ![0, 1069]⟩
  | 20 => ⟨![663739, 85039], ![0, 1063]⟩
  | 21 => ⟨![663243, 85535], ![0, 1056]⟩
  | 22 => ⟨![662679, 86099], ![0, 1050]⟩
  | 23 => ⟨![662210, 86568], ![0, 1043]⟩
  | 24 => ⟨![661671, 87107], ![0, 1037]⟩
  | 25 => ⟨![661229, 87549], ![0, 1030]⟩
  | 26 => ⟨![660801, 87977], ![0, 1023]⟩
  | 27 => ⟨![660474, 88304], ![0, 1015]⟩
  | 28 => ⟨![660075, 88703], ![0, 1008]⟩
  | 29 => ⟨![658779, 89999], ![0, 1000]⟩
  | 30 => ⟨![658416, 90362], ![0, 993]⟩
  | 31 => ⟨![658251, 90527], ![0, 984]⟩
  | 32 => ⟨![657035, 91743], ![0, 976]⟩
  | 33 => ⟨![655947, 92831], ![0, 967]⟩
  | 34 => ⟨![654895, 93883], ![0, 958]⟩
  | 35 => ⟨![653879, 94899], ![0, 949]⟩
  | 36 => ⟨![652213, 96565], ![0, 939]⟩
  | 37 => ⟨![651339, 97439], ![0, 928]⟩
  | 38 => ⟨![648826, 99952], ![0, 917]⟩
  | 39 => ⟨![645893, 102885], ![0, 905]⟩
  | 40 => ⟨![641859, 106919], ![0, 891]⟩
  | 41 => ⟨![630789, 117989], ![0, 874]⟩
  | 42 => ⟨![560486, 188292], ![0, 835]⟩
  | 43 => ⟨![505149, 243629], ![0, 757]⟩
  | 44 => ⟨![465194, 283584], ![0, 649]⟩
  | 45 => ⟨![434665, 314113], ![0, 516]⟩
  | 46 => ⟨![410482, 338296], ![0, 362]⟩
  | 47 => ⟨![390747, 358031], ![0, 189]⟩
  | 48 => ⟨![374389, 374389], ![0, 0]⟩
  | _ => ⟨![0,0],![0,0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 237981634351639402470019032960 237983016197583795606018194880 237974669393747764868183404800 237974714729431480402698700800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 208830063500119727264939106240 208831279067808833265999425280 208830015753767835573581164800 208830061089451551108096460800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 210690025217966817514038297600 210691251201257917813534694400 210689984872625804282538144000 210690030208309519817053440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 209893849353966810641119617600 209895070871221536535174814400 209893814480418356726442144000 209893859816102072260957440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 211716809842756842624006881280 211718041570725436241009786880 211716775953247410193855852800 211716821288931125728371148800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 210910508379593658446552858880 210911735589116016929031312480 210910469625287411611628908800 210910514960971127146144204800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 212696698756103776468951234560 212697935973618183665590844160 212696652500291195744607187200 212696697835974911279122483200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 211880250747771321938975400960 211881483394329302279379135360 211880189251806728704285651200 211880234587490444238800947200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 213629895112304496296185159680 213631137566245215084431646720 213629815595194536105401299200 213629860930878251639916595200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 212637741274985340733747211520 212638978142452076289380570880 212637719394366742067574124800 212637764730050457602089420800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 214349224249132582897634679360 214350470715050562085019104320 214349172102547518121630675200 214349217438231233656145971200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 213344574238038564141700968000 213345815051309974049430216000 213344570544726778375153824000 213344615880410493909669120000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 215018104969678252983561216000 215019355174451589652478064000 215018056843292929160751264000 215018102178976644695266560000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 216493530160745632124718673920 216494788611529116091614136320 216493520609303350098058195200 216493565944987065632573491200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 215636690624229092900655429120 215637944296352835689691275520 215636621373254864953203667200 215636666708938580487718963200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 217072467726241878734927578560 217073729429107546966237618560 217072420084123330913557459200 217072465419807046448072755200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 216031416404561962506067124160 216032672264242960966172952960 216031385176461435486395347200 216031430512145151020910643200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 217425842698621821925909080960 217427106364828663769233606080 217425814725189478176421228800 217425860060873193710936524800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 218790355679247020110736760000 218791626986612137195618920000 218790325117050226813282464000 218790370452733942347797760000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 220125126288870794299497696000 220126405073582551971588595200 220125085874866579631089824000 220125131210550295165605120000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 219048579061503658020294048000 219049851819594299481765849600 219048518201541846764202144000 219048563537225562298717440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 220160946382695051450385489920 220162225344081801121572802560 220160940681140077490658259200 220160986016823793025173555200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 221423602273290620294958720000 221424888321383137886537280000 221423553741173736496277664000 221423599076857452030792960000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 222471627184108978741628418240 222472919083155088618291633920 222471613384631035937741779200 222471658720314751472257075200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 53 223674073029589961317760432640 223675371687653947406872327680 223673992395369047287821676800 223674037731052762822336972800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 53 224658377463185210925267120000 224659681625546888477336208000 224658305906731099826530464000 224658351242414815361045760000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 53 225610074667506390732917418240 225611384157343305893814134400 225609997725155981718353260800 225610043060839697252868556800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 53 226336157165693048699998080000 226337470686568628772081480000 226336150424355869580437664000 226336195760039585114952960000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 53 227221110441966457303539978240 227222428929392717028547153920 227221066344055831599569875200 227221111679739547134085171200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 53 230086868088625006189824000000 230088202605994196804601600000 230086858881383025604143264000 230086904217066741138658560000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 53 230887299570225575532890898240 230888638597980957330731529600 230887210212054690222732652800 230887255547738405757247948800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 53 231250671804627020346666485760 231252012823296903796084930560 231250668342924201473504620800 231250713678607917008019916800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 53 233922771470214561085555138560 233924127462601446013441413120 233922730831277448235899859200 233922776166961163770415155200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 53 236303811393404045788111530240 236305180699698468982963564800 236303800179398377732470124800 236303845515082093266985420800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1427 53 238597367284248984805041008640 238598749427814529692899051520 238597351686761677572594643200 238597397022445393107109939200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 53 240804327080658528310159296000 240805721592590364653338022400 240804266760334508920776864000 240804312096018224455292160000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 53 244405809170127134300939869440 244407223836482910968526284160 244405754478609653935430611200 244405799814293369469945907200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1434 53 246286530411617514627110707200 246287955578138620939053158400 246286519417223425428138144000 246286564752907140962653440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 53 251661282787087631070700328640 251662738047968980052101666080 251661241335656831547503980800 251661286671340547082019276800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1443 54 257872359028714606545943570560 257873849061593624310499234560 257872287569047601327954899200 257872332904731316862470195200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1449 54 266305897658763806110887945600 266307434878505972084668972800 266305842877240648251582624000 266305888212924363786097920000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1464 54 288800488235356486054831123200 288802151336573520433974432000 288800435775714375895722144000 288800481111398091430237440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 55 409468215844277656624666252800 409470554175844752475448271840 409468175151306653981635948800 409468220486990369516151244800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 55 477480262896363051802297368000 477482981760834732436557888000 477480231356726164164552864000 477480276692409879699068160000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 55 511818599033200377683167111200 511821509984733129909793048800 511818570081474345207179424000 511818615417158060741694720000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 55 529709362428810639721068650880 529712373415466619837078543360 529709355951014196013751251200 529709401286697911548266547200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 54 538749068868124896700860278400 538752130368735670742501599680 538749066329868675658970476800 538749111665552391193485772800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 54 542764181102511084969798547200 542767265003788993237764648960 542764180430568593249695084800 542764225766252308784210380800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2359 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 54 543802171484466169451725536000 543805261155401904828952560000 543802108831725101386410144000 543802154167408816920925440000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2359 (max 1 i.val) (witness i.val) := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48

theorem positive {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179818 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

#print axioms bank_checked
#print axioms positive
end Lower6960.TerminalReceipts
