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
    2383 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 237985219718959440678467330880 237986601894656012804267125440 237975757450156937696550508800 237975802785840653231065804800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 208833281898179136626009266560 208834497756007737587409640320 208831103810177008401948268800 208831149145860723936463564800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 210693262383294995112881587200 210694488659165439647321702400 210691072929034977110905248000 210691118264718692645420544000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 209897078339846915733587227200 209898300148574804598085862400 209894902536827529554809248000 209894947872511245089324544000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 211720057281770173040386621440 211721289303595687041809940480 211717864009656583022222956800 211717909345340298556738252800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 210913747641422799972295422240 210914975143682382767154022080 210911557681696584439996012800 210911603017380299974511308800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 212699956180393212632891539200 212701193692974842817332828160 212697740556700368572974291200 212697785892384084107489587200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 211883499997333674118738185600 211884732937825654449637186560 211881277308215901532652755200 211881322643899617067168051200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 213633162256690796847183544320 213634405006846992430547189760 213630903651603708933768403200 213630948987287424468283699200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 212640997712001766056135866880 212642234874307665645072099840 212638807450775914895941228800 212638852786459630430456524800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 214352498314575934782429401280 214353745077563885253605423040 214350260158956690949997779200 214350305494640406484513075200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 213347837562617565343259064000 213349078671565958034868152000 213345658601135951203520928000 213345703936819666738036224000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 215021385678038741045042832000 215022636180669468867515424000 215019144899702101989118368000 215019190235385817523633664000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 216496825386502374160734504960 216498084137050868102622597120 216494608665712522926425299200 216494654001396238460940595200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 215639977717265555641532002560 215641231687967227323716344320 215637709429664037781570771200 215637754765347753316086067200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 217075769103437683926992049600 217077031106736225514868856960 217073508140532503741924563200 217073553476216219276439859200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 216034706997224702457533784000 216035963155897049482489618560 216032473232870608314762451200 216032518568554323849277747200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 217429147339149060462752412480 217430411306143344907480309440 217426902781598651004788332800 217426948117282366539303628800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 218793674120235258849987780000 218794945730137925977634040000 218791413173459399641649568000 218791458509143115176164864000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 220128458299149852783792489600 220129737388103628086776819200 220126173931275752459456928000 220126219266959467993972224000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 219051900301948470003545020800 219053173362792446742074841600 219049606257951019592569248000 219049651593634735127084544000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 220164278263007547759465922560 220165557528541095699465093120 220162028737549250319025363200 220162074073232965853540659200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 221426947320331797509774400000 221428233674168014772550720000 221424641797582909324644768000 221424687133266624859160064000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 222474982419802581772063511520 222476274625888844245515821760 222472701441040208766108883200 222472746776723924300624179200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 52 223677441059189480828720766720 223678740025799201251711848960 223675080451778220116188780800 223675125787461935650704076800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 52 224661755289964692952917216000 224663059762076219065647552000 224659393963140272654897568000 224659439298823988189412864000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 52 225613462104896373509868440640 225614771905641889362798444480 225611085781565154546720364800 225611131117248870081235660800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 52 226339551144707115904456500000 226340864977338881562998520000 226337238480765042408804768000 226337283816448757943320064000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 52 227224513674104618730614814720 227225832474353248286320066560 227222154400465004427936979200 227222199736148719962452275200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 52 230090299877214179616643200000 230091634711045237723574400000 230087946937792198432510368000 230087992273475913967025664000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 52 230890740181668498291254943840 230892079526833900532217382080 230888298268463863051099756800 230888343604147578585615052800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 53 231254115096967769884551505920 231255456433394903118170634240 231251756399333374301871724800 231251801735017089836387020800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 53 233926242066399123035515607040 233927598379900684631432417280 233923818887686621064266963200 233923864223370336598782259200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 53 236307305644951912579510986240 236308675275302985541242074880 236304888235807550560837228800 236304933571491266095352524800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1427 53 238600884637878412027585489920 238602267108307509925913303040 238598439743170850400961747200 238598485078854565935477043200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 53 240807867058861990475697907200 240809261900339548043850643200 240805354816743681749143968000 240805400152427397283659264000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 53 244409385324520194955003391040 244410800324882296601609130240 244406842535018826763797715200 244406887870702542298313011200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1434 53 246290124931698997046063923200 246291550434452176742331187200 246287607473632598256505248000 246287652809316313791020544000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 53 251664931693651659471661484160 251666387297432473423951192320 251662329392066004375871084800 251662374727749719910386380800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1443 53 257876070688280667178801800000 257877561071686105317804048000 257873375625456774156322003200 257873420961140489690837299200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1449 54 266309693894489136071627462400 266311231475079209501109772800 266306930933649821079949728000 266306976269333536614465024000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1464 54 288804510537201708281356809600 288806174026872562316592691200 288801523832123548724089248000 288801569167807264258604544000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 55 409473450150364248598102253760 409475789016738050973056768640 409469263207715826810003052800 409469308543399542344518348800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 55 477486179567307646467367968000 477488899051528057979974848000 477481319413135336992919968000 477481364748819052527435264000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 54 511824859632179550054750938400 511827771241169137156720075200 511819658137883518035546528000 511819703473567233570061824000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 54 529715801456491973393380354560 529718813121583110304059626880 529710444007423368842118355200 529710489343107084376633651200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 54 538755597615114910462006834560 538758659805096826714594622400 538750154386277848487337580800 538750199721961564021852876800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 54 542770749159670660136757223680 542773833754325435897239526400 542765268486977766078062188800 542765313822661481612577484800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2383 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 54 543808749659191483331806272000 543811840027340043887764416000 543803196888134274214777248000 543803242223817989749292544000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2383 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2383≤h) (hi : h≤33599) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179808 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

#print axioms bank_checked
#print axioms positive
end Lower6960.TerminalReceipts
