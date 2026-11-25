import ProximityPrize.SubmissionLower.R6960TerminalArithmetic
import ProximityPrize.SubmissionLower.HighCore82258Source
set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6960.TerminalReceipts
open TerminalArithmetic
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

def terminalBank : P1_7.Bank := ⟨⟨4500,6286,1329,778757⟩,2693670660997120,42045879552530⟩

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
  | 0 => ⟨![685160, 93597], ![1200, 1201]⟩
  | 1 => ⟨![697338, 81419], ![0, 1180]⟩
  | 2 => ⟨![697683, 81074], ![0, 1175]⟩
  | 3 => ⟨![696858, 81899], ![0, 1170]⟩
  | 4 => ⟨![697208, 81549], ![0, 1165]⟩
  | 5 => ⟨![696398, 82359], ![0, 1160]⟩
  | 6 => ⟨![696753, 82004], ![0, 1155]⟩
  | 7 => ⟨![695958, 82799], ![0, 1150]⟩
  | 8 => ⟨![696318, 82439], ![0, 1145]⟩
  | 9 => ⟨![695611, 83146], ![0, 1139]⟩
  | 10 => ⟨![695976, 82781], ![0, 1134]⟩
  | 11 => ⟨![695212, 83545], ![0, 1129]⟩
  | 12 => ⟨![695622, 83135], ![0, 1123]⟩
  | 13 => ⟨![694983, 83774], ![0, 1117]⟩
  | 14 => ⟨![694246, 84511], ![0, 1112]⟩
  | 15 => ⟨![694702, 84055], ![0, 1106]⟩
  | 16 => ⟨![694058, 84699], ![0, 1100]⟩
  | 17 => ⟨![693426, 85331], ![0, 1094]⟩
  | 18 => ⟨![693894, 84863], ![0, 1088]⟩
  | 19 => ⟨![693280, 85477], ![0, 1082]⟩
  | 20 => ⟨![692678, 86079], ![0, 1076]⟩
  | 21 => ⟨![692169, 86588], ![0, 1069]⟩
  | 22 => ⟨![691592, 87165], ![0, 1063]⟩
  | 23 => ⟨![692166, 86591], ![0, 1056]⟩
  | 24 => ⟨![691691, 87066], ![0, 1049]⟩
  | 25 => ⟨![691230, 87527], ![0, 1042]⟩
  | 26 => ⟨![690783, 87974], ![0, 1035]⟩
  | 27 => ⟨![689322, 89435], ![0, 1028]⟩
  | 28 => ⟨![688910, 89847], ![0, 1021]⟩
  | 29 => ⟨![688601, 90156], ![0, 1013]⟩
  | 30 => ⟨![688308, 90449], ![0, 1005]⟩
  | 31 => ⟨![687034, 91723], ![0, 997]⟩
  | 32 => ⟨![686781, 91976], ![0, 989]⟩
  | 33 => ⟨![685658, 93099], ![0, 980]⟩
  | 34 => ⟨![684571, 94186], ![0, 971]⟩
  | 35 => ⟨![683520, 95237], ![0, 962]⟩
  | 36 => ⟨![681949, 96808], ![0, 952]⟩
  | 37 => ⟨![680894, 97863], ![0, 941]⟩
  | 38 => ⟨![678318, 100439], ![0, 930]⟩
  | 39 => ⟨![675942, 102815], ![0, 918]⟩
  | 40 => ⟨![672086, 106671], ![0, 904]⟩
  | 41 => ⟨![663382, 115375], ![0, 888]⟩
  | 42 => ⟨![598328, 180429], ![0, 855]⟩
  | 43 => ⟨![534494, 244263], ![0, 780]⟩
  | 44 => ⟨![489330, 289427], ![0, 671]⟩
  | 45 => ⟨![455498, 323259], ![0, 536]⟩
  | 46 => ⟨![428834, 349923], ![0, 377]⟩
  | 47 => ⟨![407283, 371474], ![0, 198]⟩
  | 48 => ⟨![389379, 389378], ![0, 0]⟩
  | _ => ⟨![0,0],![0,0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 248870910392765111192005692000 248872355927229084464936689920 248865033006728200837652976000 248865080157522445643795764800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 220346095817754726454956960000 220347378924189204075496963200 220346076713778200504007561600 220346123864572445310150350400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 219521390427815749776828000000 219522668901358040332191792000 219521382624883767857478537600 219521429775678012663621326400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 221491949605593669779794617600 221493239128384011554118163200 221491941146525771101469577600 221491988297320015907612366400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 220656599683657885712040451200 220657884518389561831627718400 220656591486949042738789257600 220656638637743287544932046400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 222588400235481672498310406400 222589695904846354235235110400 222588383997709765767953289600 222588431148504010574096078400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 221742387805510374954481915200 221743678731574940733807907200 221742360730631995652406153600 221742407881426240458548942400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 223635664095599444063230152000 223636965643911683747181672000 223635619381823685842533257600 223635666532617930648676046400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 52 222778968836689163856334197600 222780265586364507809146725600 222778902143094676835892105600 222778949293888921642034894400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 224460456567448387424968857600 224461762719600616408654911360 224460448005991535163780796800 224460495156785779969923585600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 52 223592848637557853279216563200 223594149934264864309682621760 223592807398307923693711036800 223592854549102168499853825600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 225407811772653142991970480480 225409123262308046638862905920 225407727506538217232654832000 225407774657332462038797620800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 224434354315147311390069353760 224435660323187846938185979200 224434315037264379590205936000 224434362188058624396348724800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 225950855190630792179698897920 225952169686728358830439864320 225950846382048018560285577600 225950893532842263366428366400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 227696095816152158615237510400 227697420120901417862512208640 227696026374214039530679996800 227696073525008284336822785600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 226616786797710069615363364800 226618105037360013520690351680 226616737678049936820396528000 226616784828844181626539316800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 228140565529724531873025408000 228141892306043762967687888000 228140526650808405781216137600 228140573801602650587358926400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 229632827598644249767617604800 229634162736682803013977269760 229632793982628924743003836800 229632841133423169549146625600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 228528095903378624971139328000 228529424843739374655285043200 228528058290925107126041481600 228528105441719351932184270400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 229977140262622721478017729280 229978477331087600192600257920 229977086030864581554594288000 229977133181658826360737076800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 231395033650379566399466636160 231396378675407064626392229760 231394954541919671511513993600 231395001692713916317656782400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 232591611106425144581397504000 232592962811917577819904100800 232591590059372739251501961600 232591637210166984057644750400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 233945726310939410136062376480 233947085623302773093197452480 233945659844520673163338224000 233945706995314917969481012800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 232598668518204122928135767040 232600020257310187709256099840 232598636963000215007702716800 232598684113794459813845505600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 233713526671802361501578534400 233714884647923173123410101760 233713516003007255409110716800 233713563153801500215253505600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 52 234793864724897746050679442880 234795228749658145494458637120 234793861726569819403969008000 234793908877364064210111796800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 52 235839834236387853999402393600 235841204122823378410884633600 235839824339659761083841417600 235839871490454005889984206400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 52 239247728272829962159266827520 239249117270461665699292481280 239247694775927536228229616000 239247741926721781034372404800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 52 240205793314596243658434751680 240207187695355140225919367040 240205716330793236945428976000 240205763481587481751571764800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 52 240923411314860651350080550400 240924809697669199874480754240 240923368323864746725519036800 240923415474658991531661825600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 52 241603204722602378877247089600 241604606903200482510394876800 241603176162042757599558537600 241603223312837002405701326400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 52 244551359920905116329586702400 244552778626657110199324070400 244551320523716713716743049600 244551367674510958522885838400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1422 52 245135362301381590110782317440 245136784288495718893518515520 245135285509138846257295036800 245135332659933091063437825600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1424 52 247721404404243683084232297600 247722840867311897781778156800 247721357592123592789031817600 247721404742917837595174606400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1426 53 250215260609302675640967525120 250216711044582167464489585920 250215209856800105747230396800 250215257007594350553373185600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1428 53 252617848740003056375850108480 252619312651827712314098544000 252617753034511830175441392000 252617800185306074981584180800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1431 53 256193103702133426762650024000 256194587639350247667905664000 256193017266381914775059337600 256193064417176159581202126400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1433 53 258583263751171272009213460800 258584761051289249025544560000 258583228287107284469119881600 258583275437901529275262670400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1437 53 264383197846389505768280256000 264384727649277827559193612800 264383140275622207186893705600 264383187426416451993036494400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1441 53 269687184765242725519921664640 269688744284641308141657834240 269687109754751169361338864000 269687156905545414167481652800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1447 53 278201714037457649130249292800 278203321231263555799840197120 278201686685484558321233596800 278201733836278803127376385600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1459 54 296997306165648136672565114880 296999018651266534274256103680 296997264141323237677851120000 296997311292117482483993908800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 55 418864206152226834738837201600 418866601242028632947997868800 418864191577805322356882313600 418864238728599567163025102400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 54 506532408180154055529183244800 506535294281986751850993225600 506532382640627896178539401600 506532429791422140984682190400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 54 549464693528756661144933250080 549467820028182328055535850560 549464689145865364132585968000 549464736296659608938728756800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 54 571258312036094220904877512320 571261560550555757645271104640 571258263326235402923506569600 571258310477029647729649358400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 54 582177556909937637799421911200 582180866505869000528748981600 582177527643935273652681609600 582177574794729518458824398400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 54 586972505312229404146259767680 586975841696903945799975338880 586972471845752311290100617600 586972518996546556096243406400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2402 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 54 588215949293668152376329350400 588219292569870103453036790400 588215930595570372678351753600 588215977746364617484494542400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2402 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2402≤h) (hi : h≤33619) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179798 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

#print axioms bank_checked
#print axioms positive
end Lower6960.TerminalReceipts
