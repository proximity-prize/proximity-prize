import ProximityPrize.SubmissionLower.R6960TerminalArithmetic
import ProximityPrize.SubmissionLower.HighCore82258Source

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6960.TerminalReceipts
open TerminalArithmetic
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

def terminalBank : P1_7.Bank := ⟨⟨4500,6286,1329,797798⟩,2693670660997120,42045879552530⟩

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
  | 0 => ⟨![710126, 87672], ![1200, 1201]⟩
  | 1 => ⟨![715758, 82040], ![0, 1189]⟩
  | 2 => ⟨![716103, 81695], ![0, 1184]⟩
  | 3 => ⟨![715269, 82529], ![0, 1179]⟩
  | 4 => ⟨![715619, 82179], ![0, 1174]⟩
  | 5 => ⟨![714800, 82998], ![0, 1169]⟩
  | 6 => ⟨![715155, 82643], ![0, 1164]⟩
  | 7 => ⟨![714351, 83447], ![0, 1159]⟩
  | 8 => ⟨![714783, 83015], ![0, 1153]⟩
  | 9 => ⟨![713995, 83803], ![0, 1148]⟩
  | 10 => ⟨![714433, 83365], ![0, 1142]⟩
  | 11 => ⟨![713661, 84137], ![0, 1137]⟩
  | 12 => ⟨![714105, 83693], ![0, 1131]⟩
  | 13 => ⟨![713349, 84449], ![0, 1126]⟩
  | 14 => ⟨![713799, 83999], ![0, 1120]⟩
  | 15 => ⟨![713135, 84663], ![0, 1114]⟩
  | 16 => ⟨![712483, 85315], ![0, 1108]⟩
  | 17 => ⟨![712945, 84853], ![0, 1102]⟩
  | 18 => ⟨![712311, 85487], ![0, 1096]⟩
  | 19 => ⟨![711689, 86109], ![0, 1090]⟩
  | 20 => ⟨![711079, 86719], ![0, 1084]⟩
  | 21 => ⟨![711559, 86239], ![0, 1078]⟩
  | 22 => ⟨![711048, 86750], ![0, 1071]⟩
  | 23 => ⟨![710551, 87247], ![0, 1064]⟩
  | 24 => ⟨![709985, 87813], ![0, 1058]⟩
  | 25 => ⟨![709515, 88283], ![0, 1051]⟩
  | 26 => ⟨![709059, 88739], ![0, 1044]⟩
  | 27 => ⟨![708703, 89095], ![0, 1036]⟩
  | 28 => ⟨![708276, 89522], ![0, 1029]⟩
  | 29 => ⟨![706930, 90868], ![0, 1021]⟩
  | 30 => ⟨![706629, 91169], ![0, 1013]⟩
  | 31 => ⟨![706344, 91454], ![0, 1005]⟩
  | 32 => ⟨![705078, 92720], ![0, 997]⟩
  | 33 => ⟨![703939, 93859], ![0, 988]⟩
  | 34 => ⟨![703815, 93983], ![0, 979]⟩
  | 35 => ⟨![701769, 96029], ![0, 970]⟩
  | 36 => ⟨![700839, 96959], ![0, 960]⟩
  | 37 => ⟨![699103, 98695], ![0, 949]⟩
  | 38 => ⟨![697433, 100365], ![0, 938]⟩
  | 39 => ⟨![695013, 102785], ![0, 926]⟩
  | 40 => ⟨![690978, 106820], ![0, 913]⟩
  | 41 => ⟨![683880, 113918], ![0, 897]⟩
  | 42 => ⟨![623666, 174132], ![0, 868]⟩
  | 43 => ⟨![553751, 244047], ![0, 795]⟩
  | 44 => ⟨![504921, 292877], ![0, 685]⟩
  | 45 => ⟨![468772, 329026], ![0, 548]⟩
  | 46 => ⟨![440496, 357302], ![0, 386]⟩
  | 47 => ⟨![417746, 380052], ![0, 203]⟩
  | 48 => ⟨![398899, 398899], ![0, 0]⟩
  | _ => ⟨![0,0],![0,0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 241615738424692356917161461120 241617144431726119445422595040 241610324598482043712045708800 241610372902133941804190668800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 227889281574866006879805616320 227890608326099248180201800480 227889230352285150088161523200 227889278655937048180306483200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 227040763245405110109985259520 227042085231954910651180769280 227040717364204277852956915200 227040765667856175945101875200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 229090366306885036385954059200 229091699785873765766331196800 229090323372756540786947520000 229090371676408438879092480000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 228230883042027964643412691200 228232211699556323735345164800 228230834049536124769744320000 228230882353188022861889280000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 230240602946147018287761347040 230241942875344960875739394880 230240549143186874828744947200 230240597446838772920889907200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 229370137473291478259969917440 229371472524183508642087111680 229370066146207604323281139200 229370114449859502415426099200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 231340212131876963956502069760 231341558235951430849795061760 231340125967266265535349388800 231340174270918163627494348800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 230282236816098861859392291840 230283576957733465101931376640 230282209714377176271186163200 230282258018029074363331123200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 232210893106223395751929006080 232212244073424663288465308160 232210839187751564754184435200 232210887491403462846329395200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 231139434261739605756576468480 231140779195139885917957426560 231139429113655617947330803200 231139477417307516039475763200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 233026896460410396521803414080 233028251993920656054411400320 233026850359859426829533836800 233026898663511324921678796800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 231941911109959090330802291520 231943260538041791334668542080 231941903548564664168114419200 231941951852216562260259379200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 233788395256221981989707344000 233789755061051817511188096000 233788330495904878700475840000 233788378799556776792620800000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 232689837327247301553699840000 232691190954730564968898560000 232689800959341826418619840000 232689849262993724510764800000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 234310212108818427202545392640 234311574813815826850782228480 234310191145809515140507891200 234310239449461413232652851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 235897978176654843896241085440 235899349777531853971308541440 235897968964181380628900083200 235898017267833278721045043200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 234773233282672719091056887040 234774598569631198549570419840 234773227624417152461596915200 234773275928069050553741875200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 236316295596656851064725432320 236317669537160111830116618240 236316280850528969075196556800 236316329154180867167341516800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 237827128604940530467569072000 237828511020904813197161568000 237827097712214202415527360000 237827146015866100507672320000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 239305907575174411086508108800 239307298290148958124758323200 239305851921492362699421120000 239305900225144260791566080000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 238142576936491642625634547200 238143961138042562594319820800 238142484094367347852916160000 238142532398019245945061120000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 239380974176116392610490384640 239382365299308556068040022880 239380924648231658409847027200 239380972951883556501991987200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 240583509181436582865949378560 240584907029410399453251932160 240583492095239493945655948800 240583540398891392037800908800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 241950774048245665975852375680 241952179589990963371512783360 241950681823554437446002931200 241950730127206335538147891200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 52 243084178373128299067805781120 243085590262503937078916590080 243084092007507728524011763200 243084140311159626616156723200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 52 244182198796345919424874521600 244183616840958478005303590400 244182103154263362455156160000 244182151457915260547301120000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 52 245038225541599951022139863040 245039648349923326037623726080 245038201105608776356882675200 245038249409260674449027635200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 52 246063808257273964706315182560 246065236828130221802172855360 246063740822776868255564428800 246063789126428766347709388800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 53 249287248328449855793021320320 249288694952553897113019955680 249287215779663575152224499200 249287264083315473244369459200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 53 250006165976303794732511145600 250007616619383830457214800000 250006144217063870315574720000 250006192520715768407719680000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 53 250686241767546999058445652000 250687696220453395692376308000 250686209376643772228253120000 250686257680295670320398080000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1422 53 253699585929335658237597650880 253701057286417995519665355360 253699513953123778774853875200 253699562256775676866998835200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1424 53 256399950386380602107001945600 256401436861054441191156480000 256399910588653975665063360000 256399958892305873757208320000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 53 256693332000544700292902027520 256694820111881500366142991360 256693288343722177554442483200 256693336647374075646587443200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1428 53 261516888151586450044016688000 261518403314473425400633632000 261516799747808792873219520000 261516848051460690965364480000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1430 53 263698649804430917211082752000 263700177183565484769662976000 263698569416966886055949760000 263698617720618784148094720000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1433 53 267753278687508650286050411520 267754828760072134083731681280 267753253966785271347177715200 267753302270437169439322675200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1436 53 271631765425370278188035865600 271633337232600154500218315520 271631722583247371719567603200 271631770886899269811712563200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1440 53 277213678011599670066836113920 277215281094436905049063810560 277213625987276972313438451200 277213674290928870405583411200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1446 54 286419708460726333334821473120 286421363140055945553877561920 286419613446041350879209715200 286419661749693248971354675200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1456 54 302307490022676127780830399360 302309233699854912552933500160 302307420411293662323828979200 302307468714945560415973939200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 55 421365896343501818119453421280 421368307020858612298426329600 421365808075307539880215180800 421365856378959437972360140800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 55 524315636360601996811617285120 524318623726077675105064058880 524315556799070537324692108800 524315605102722435416837068800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 55 573726658428570163978670140800 573729922500942929450394853440 573726655363591271763935884800 573726703667243169856080844800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 54 598390314916369326935929744320 598393717098696002848362402240 598390272513869851513062028800 598390320817521749605206988800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 54 610616258612006608986420700800 610619729200387822132418005920 610616232280022813171516044800 610616280583674711263661004800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 54 615950120555292924219808836000 615953620951792000433192736000 615950091956258046192648844800 615950140259909944284793804800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2379 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 54 617327908744790992654180800000 617331416775597264064334400000 617327908671746180130747840000 617327956975398078222892800000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2379 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2379≤h) (hi : h≤33599) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179808 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

#print axioms bank_checked
#print axioms positive
end Lower6960.TerminalReceipts
