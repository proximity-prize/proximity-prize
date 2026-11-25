import ProximityPrize.SubmissionLower.R6960TerminalArithmetic
import ProximityPrize.SubmissionLower.HighCore82258Source

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000

namespace Lower6962.B1.TerminalReceipts
open Lower6960.TerminalArithmetic
open P1_7_1_3 (blockEstimate block_append momentEstimate)

def terminalBank : P1_7.Bank := ⟨⟨3800,5306,1122,506083⟩,1622051270164480,21353168189835⟩

private theorem moment_5306_1122_part0 :
    blockEstimate 5306 1122 1122 128 = 1864197920 := by decide +kernel
private theorem moment_5306_1122_part1 :
    blockEstimate 5306 1122 1250 128 = 12605716256 := by decide +kernel
private theorem moment_5306_1122_part2 :
    blockEstimate 5306 1122 1378 128 = 33263617824 := by decide +kernel
private theorem moment_5306_1122_part3 :
    blockEstimate 5306 1122 1506 128 = 63032596256 := by decide +kernel
private theorem moment_5306_1122_part4 :
    blockEstimate 5306 1122 1634 128 = 101107345184 := by decide +kernel
private theorem moment_5306_1122_part5 :
    blockEstimate 5306 1122 1762 128 = 146682558240 := by decide +kernel
private theorem moment_5306_1122_part6 :
    blockEstimate 5306 1122 1890 128 = 198952929056 := by decide +kernel
private theorem moment_5306_1122_part7 :
    blockEstimate 5306 1122 2018 128 = 257113151264 := by decide +kernel
private theorem moment_5306_1122_part8 :
    blockEstimate 5306 1122 2146 128 = 320339210306 := by decide +kernel
private theorem moment_5306_1122_part9 :
    blockEstimate 5306 1122 2274 128 = 385227810880 := by decide +kernel
private theorem moment_5306_1122_part10 :
    blockEstimate 5306 1122 2402 128 = 446074071104 := by decide +kernel
private theorem moment_5306_1122_part11 :
    blockEstimate 5306 1122 2530 128 = 502210127936 := by decide +kernel
private theorem moment_5306_1122_part12 :
    blockEstimate 5306 1122 2658 128 = 553635981376 := by decide +kernel
private theorem moment_5306_1122_part13 :
    blockEstimate 5306 1122 2786 128 = 600351631424 := by decide +kernel
private theorem moment_5306_1122_part14 :
    blockEstimate 5306 1122 2914 128 = 642357078080 := by decide +kernel
private theorem moment_5306_1122_part15 :
    blockEstimate 5306 1122 3042 128 = 679652321344 := by decide +kernel
private theorem moment_5306_1122_part16 :
    blockEstimate 5306 1122 3170 128 = 712237361216 := by decide +kernel
private theorem moment_5306_1122_part17 :
    blockEstimate 5306 1122 3298 128 = 740112197696 := by decide +kernel
private theorem moment_5306_1122_part18 :
    blockEstimate 5306 1122 3426 128 = 763276830784 := by decide +kernel
private theorem moment_5306_1122_part19 :
    blockEstimate 5306 1122 3554 128 = 781731260480 := by decide +kernel
private theorem moment_5306_1122_part20 :
    blockEstimate 5306 1122 3682 128 = 795475486784 := by decide +kernel
private theorem moment_5306_1122_part21 :
    blockEstimate 5306 1122 3810 128 = 804509509696 := by decide +kernel
private theorem moment_5306_1122_part22 :
    blockEstimate 5306 1122 3938 128 = 808833329216 := by decide +kernel
private theorem moment_5306_1122_part23 :
    blockEstimate 5306 1122 4066 128 = 808446945344 := by decide +kernel
private theorem moment_5306_1122_part24 :
    blockEstimate 5306 1122 4194 128 = 803350358080 := by decide +kernel
private theorem moment_5306_1122_part25 :
    blockEstimate 5306 1122 4322 128 = 793543567424 := by decide +kernel
private theorem moment_5306_1122_part26 :
    blockEstimate 5306 1122 4450 128 = 779026573376 := by decide +kernel
private theorem moment_5306_1122_part27 :
    blockEstimate 5306 1122 4578 128 = 759799375936 := by decide +kernel
private theorem moment_5306_1122_part28 :
    blockEstimate 5306 1122 4706 128 = 735861975104 := by decide +kernel
private theorem moment_5306_1122_part29 :
    blockEstimate 5306 1122 4834 128 = 707214370880 := by decide +kernel
private theorem moment_5306_1122_part30 :
    blockEstimate 5306 1122 4962 128 = 673856563264 := by decide +kernel
private theorem moment_5306_1122_part31 :
    blockEstimate 5306 1122 5090 128 = 635788552256 := by decide +kernel
private theorem moment_5306_1122_part32 :
    blockEstimate 5306 1122 5218 128 = 593027517186 := by decide +kernel
private theorem moment_5306_1122_part33 :
    blockEstimate 5306 1122 5346 128 = 546800007196 := by decide +kernel
private theorem moment_5306_1122_part34 :
    blockEstimate 5306 1122 5474 128 = 499389744976 := by decide +kernel
private theorem moment_5306_1122_part35 :
    blockEstimate 5306 1122 5602 128 = 451535843934 := by decide +kernel
private theorem moment_5306_1122_part36 :
    blockEstimate 5306 1122 5730 128 = 403789128103 := by decide +kernel
private theorem moment_5306_1122_part37 :
    blockEstimate 5306 1122 5858 128 = 356677475421 := by decide +kernel
private theorem moment_5306_1122_part38 :
    blockEstimate 5306 1122 5986 128 = 310705815495 := by decide +kernel
private theorem moment_5306_1122_part39 :
    blockEstimate 5306 1122 6114 128 = 266356131070 := by decide +kernel
private theorem moment_5306_1122_part40 :
    blockEstimate 5306 1122 6242 128 = 224087457474 := by decide +kernel
private theorem moment_5306_1122_part41 :
    blockEstimate 5306 1122 6370 128 = 184249355271 := by decide +kernel
private theorem moment_5306_1122_part42 :
    blockEstimate 5306 1122 6498 128 = 147062303392 := by decide +kernel
private theorem moment_5306_1122_part43 :
    blockEstimate 5306 1122 6626 128 = 113422676640 := by decide +kernel
private theorem moment_5306_1122_part44 :
    blockEstimate 5306 1122 6754 128 = 83654458016 := by decide +kernel
private theorem moment_5306_1122_part45 :
    blockEstimate 5306 1122 6882 128 = 58009305760 := by decide +kernel
private theorem moment_5306_1122_part46 :
    blockEstimate 5306 1122 7010 128 = 36738878112 := by decide +kernel
private theorem moment_5306_1122_part47 :
    blockEstimate 5306 1122 7138 128 = 20094833312 := by decide +kernel
private theorem moment_5306_1122_part48 :
    blockEstimate 5306 1122 7266 128 = 8328829600 := by decide +kernel
private theorem moment_5306_1122_part49 :
    blockEstimate 5306 1122 7394 128 = 1692525216 := by decide +kernel
private theorem moment_5306_1122_part50 :
    blockEstimate 5306 1122 7522 28 = 11301675 := by decide +kernel
private theorem moment_5306_1122_join0 :
    blockEstimate 5306 1122 1250 256 = 45869334080 :=
  block_append moment_5306_1122_part1 moment_5306_1122_part2 rfl rfl rfl
private theorem moment_5306_1122_join1 :
    blockEstimate 5306 1122 1122 384 = 47733532000 :=
  block_append moment_5306_1122_part0 moment_5306_1122_join0 rfl rfl rfl
private theorem moment_5306_1122_join2 :
    blockEstimate 5306 1122 1634 256 = 247789903424 :=
  block_append moment_5306_1122_part4 moment_5306_1122_part5 rfl rfl rfl
private theorem moment_5306_1122_join3 :
    blockEstimate 5306 1122 1506 384 = 310822499680 :=
  block_append moment_5306_1122_part3 moment_5306_1122_join2 rfl rfl rfl
private theorem moment_5306_1122_join4 :
    blockEstimate 5306 1122 1122 768 = 358556031680 :=
  block_append moment_5306_1122_join1 moment_5306_1122_join3 rfl rfl rfl
private theorem moment_5306_1122_join5 :
    blockEstimate 5306 1122 2018 256 = 577452361570 :=
  block_append moment_5306_1122_part7 moment_5306_1122_part8 rfl rfl rfl
private theorem moment_5306_1122_join6 :
    blockEstimate 5306 1122 1890 384 = 776405290626 :=
  block_append moment_5306_1122_part6 moment_5306_1122_join5 rfl rfl rfl
private theorem moment_5306_1122_join7 :
    blockEstimate 5306 1122 2402 256 = 948284199040 :=
  block_append moment_5306_1122_part10 moment_5306_1122_part11 rfl rfl rfl
private theorem moment_5306_1122_join8 :
    blockEstimate 5306 1122 2274 384 = 1333512009920 :=
  block_append moment_5306_1122_part9 moment_5306_1122_join7 rfl rfl rfl
private theorem moment_5306_1122_join9 :
    blockEstimate 5306 1122 1890 768 = 2109917300546 :=
  block_append moment_5306_1122_join6 moment_5306_1122_join8 rfl rfl rfl
private theorem moment_5306_1122_join10 :
    blockEstimate 5306 1122 1122 1536 = 2468473332226 :=
  block_append moment_5306_1122_join4 moment_5306_1122_join9 rfl rfl rfl
private theorem moment_5306_1122_join11 :
    blockEstimate 5306 1122 2786 256 = 1242708709504 :=
  block_append moment_5306_1122_part13 moment_5306_1122_part14 rfl rfl rfl
private theorem moment_5306_1122_join12 :
    blockEstimate 5306 1122 2658 384 = 1796344690880 :=
  block_append moment_5306_1122_part12 moment_5306_1122_join11 rfl rfl rfl
private theorem moment_5306_1122_join13 :
    blockEstimate 5306 1122 3170 256 = 1452349558912 :=
  block_append moment_5306_1122_part16 moment_5306_1122_part17 rfl rfl rfl
private theorem moment_5306_1122_join14 :
    blockEstimate 5306 1122 3042 384 = 2132001880256 :=
  block_append moment_5306_1122_part15 moment_5306_1122_join13 rfl rfl rfl
private theorem moment_5306_1122_join15 :
    blockEstimate 5306 1122 2658 768 = 3928346571136 :=
  block_append moment_5306_1122_join12 moment_5306_1122_join14 rfl rfl rfl
private theorem moment_5306_1122_join16 :
    blockEstimate 5306 1122 3554 256 = 1577206747264 :=
  block_append moment_5306_1122_part19 moment_5306_1122_part20 rfl rfl rfl
private theorem moment_5306_1122_join17 :
    blockEstimate 5306 1122 3426 384 = 2340483578048 :=
  block_append moment_5306_1122_part18 moment_5306_1122_join16 rfl rfl rfl
private theorem moment_5306_1122_join18 :
    blockEstimate 5306 1122 3810 256 = 1613342838912 :=
  block_append moment_5306_1122_part21 moment_5306_1122_part22 rfl rfl rfl
private theorem moment_5306_1122_join19 :
    blockEstimate 5306 1122 4066 256 = 1611797303424 :=
  block_append moment_5306_1122_part23 moment_5306_1122_part24 rfl rfl rfl
private theorem moment_5306_1122_join20 :
    blockEstimate 5306 1122 3810 512 = 3225140142336 :=
  block_append moment_5306_1122_join18 moment_5306_1122_join19 rfl rfl rfl
private theorem moment_5306_1122_join21 :
    blockEstimate 5306 1122 3426 896 = 5565623720384 :=
  block_append moment_5306_1122_join17 moment_5306_1122_join20 rfl rfl rfl
private theorem moment_5306_1122_join22 :
    blockEstimate 5306 1122 2658 1664 = 9493970291520 :=
  block_append moment_5306_1122_join15 moment_5306_1122_join21 rfl rfl rfl
private theorem moment_5306_1122_join23 :
    blockEstimate 5306 1122 1122 3200 = 11962443623746 :=
  block_append moment_5306_1122_join10 moment_5306_1122_join22 rfl rfl rfl
private theorem moment_5306_1122_join24 :
    blockEstimate 5306 1122 4450 256 = 1538825949312 :=
  block_append moment_5306_1122_part26 moment_5306_1122_part27 rfl rfl rfl
private theorem moment_5306_1122_join25 :
    blockEstimate 5306 1122 4322 384 = 2332369516736 :=
  block_append moment_5306_1122_part25 moment_5306_1122_join24 rfl rfl rfl
private theorem moment_5306_1122_join26 :
    blockEstimate 5306 1122 4834 256 = 1381070934144 :=
  block_append moment_5306_1122_part29 moment_5306_1122_part30 rfl rfl rfl
private theorem moment_5306_1122_join27 :
    blockEstimate 5306 1122 4706 384 = 2116932909248 :=
  block_append moment_5306_1122_part28 moment_5306_1122_join26 rfl rfl rfl
private theorem moment_5306_1122_join28 :
    blockEstimate 5306 1122 4322 768 = 4449302425984 :=
  block_append moment_5306_1122_join25 moment_5306_1122_join27 rfl rfl rfl
private theorem moment_5306_1122_join29 :
    blockEstimate 5306 1122 5218 256 = 1139827524382 :=
  block_append moment_5306_1122_part32 moment_5306_1122_part33 rfl rfl rfl
private theorem moment_5306_1122_join30 :
    blockEstimate 5306 1122 5090 384 = 1775616076638 :=
  block_append moment_5306_1122_part31 moment_5306_1122_join29 rfl rfl rfl
private theorem moment_5306_1122_join31 :
    blockEstimate 5306 1122 5474 256 = 950925588910 :=
  block_append moment_5306_1122_part34 moment_5306_1122_part35 rfl rfl rfl
private theorem moment_5306_1122_join32 :
    blockEstimate 5306 1122 5730 256 = 760466603524 :=
  block_append moment_5306_1122_part36 moment_5306_1122_part37 rfl rfl rfl
private theorem moment_5306_1122_join33 :
    blockEstimate 5306 1122 5474 512 = 1711392192434 :=
  block_append moment_5306_1122_join31 moment_5306_1122_join32 rfl rfl rfl
private theorem moment_5306_1122_join34 :
    blockEstimate 5306 1122 5090 896 = 3487008269072 :=
  block_append moment_5306_1122_join30 moment_5306_1122_join33 rfl rfl rfl
private theorem moment_5306_1122_join35 :
    blockEstimate 5306 1122 4322 1664 = 7936310695056 :=
  block_append moment_5306_1122_join28 moment_5306_1122_join34 rfl rfl rfl
private theorem moment_5306_1122_join36 :
    blockEstimate 5306 1122 6114 256 = 490443588544 :=
  block_append moment_5306_1122_part39 moment_5306_1122_part40 rfl rfl rfl
private theorem moment_5306_1122_join37 :
    blockEstimate 5306 1122 5986 384 = 801149404039 :=
  block_append moment_5306_1122_part38 moment_5306_1122_join36 rfl rfl rfl
private theorem moment_5306_1122_join38 :
    blockEstimate 5306 1122 6498 256 = 260484980032 :=
  block_append moment_5306_1122_part42 moment_5306_1122_part43 rfl rfl rfl
private theorem moment_5306_1122_join39 :
    blockEstimate 5306 1122 6370 384 = 444734335303 :=
  block_append moment_5306_1122_part41 moment_5306_1122_join38 rfl rfl rfl
private theorem moment_5306_1122_join40 :
    blockEstimate 5306 1122 5986 768 = 1245883739342 :=
  block_append moment_5306_1122_join37 moment_5306_1122_join39 rfl rfl rfl
private theorem moment_5306_1122_join41 :
    blockEstimate 5306 1122 6882 256 = 94748183872 :=
  block_append moment_5306_1122_part45 moment_5306_1122_part46 rfl rfl rfl
private theorem moment_5306_1122_join42 :
    blockEstimate 5306 1122 6754 384 = 178402641888 :=
  block_append moment_5306_1122_part44 moment_5306_1122_join41 rfl rfl rfl
private theorem moment_5306_1122_join43 :
    blockEstimate 5306 1122 7138 256 = 28423662912 :=
  block_append moment_5306_1122_part47 moment_5306_1122_part48 rfl rfl rfl
private theorem moment_5306_1122_join44 :
    blockEstimate 5306 1122 7394 156 = 1703826891 :=
  block_append moment_5306_1122_part49 moment_5306_1122_part50 rfl rfl rfl
private theorem moment_5306_1122_join45 :
    blockEstimate 5306 1122 7138 412 = 30127489803 :=
  block_append moment_5306_1122_join43 moment_5306_1122_join44 rfl rfl rfl
private theorem moment_5306_1122_join46 :
    blockEstimate 5306 1122 6754 796 = 208530131691 :=
  block_append moment_5306_1122_join42 moment_5306_1122_join45 rfl rfl rfl
private theorem moment_5306_1122_join47 :
    blockEstimate 5306 1122 5986 1564 = 1454413871033 :=
  block_append moment_5306_1122_join40 moment_5306_1122_join46 rfl rfl rfl
private theorem moment_5306_1122_join48 :
    blockEstimate 5306 1122 4322 3228 = 9390724566089 :=
  block_append moment_5306_1122_join35 moment_5306_1122_join47 rfl rfl rfl
private theorem moment_5306_1122_join49 :
    blockEstimate 5306 1122 1122 6428 = 21353168189835 :=
  block_append moment_5306_1122_join23 moment_5306_1122_join48 rfl rfl rfl

private theorem moment_5306_1122 : momentEstimate 5306 1122 = 21353168189835 := moment_5306_1122_join49

theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment_5306_1122

def witness : ℕ → RectArgs
  | 0 => ⟨![430171, 75912], ![1640, 1640]⟩
  | 1 => ⟨![423512, 82571], ![0, 1723]⟩
  | 2 => ⟨![423729, 82354], ![0, 1717]⟩
  | 3 => ⟨![424114, 81969], ![0, 1711]⟩
  | 4 => ⟨![424114, 81969], ![0, 1705]⟩
  | 5 => ⟨![422862, 83221], ![0, 1699]⟩
  | 6 => ⟨![423247, 82836], ![0, 1693]⟩
  | 7 => ⟨![423440, 82643], ![0, 1687]⟩
  | 8 => ⟨![423440, 82643], ![0, 1681]⟩
  | 9 => ⟨![422429, 83654], ![0, 1674]⟩
  | 10 => ⟨![422738, 83345], ![0, 1668]⟩
  | 11 => ⟨![422738, 83345], ![0, 1662]⟩
  | 12 => ⟨![421727, 84356], ![0, 1655]⟩
  | 13 => ⟨![422112, 83971], ![0, 1649]⟩
  | 14 => ⟨![422305, 83778], ![0, 1642]⟩
  | 15 => ⟨![422112, 83971], ![0, 1636]⟩
  | 16 => ⟨![421438, 84645], ![0, 1629]⟩
  | 17 => ⟨![421655, 84428], ![0, 1622]⟩
  | 18 => ⟨![420788, 85295], ![0, 1615]⟩
  | 19 => ⟨![420788, 85295], ![0, 1608]⟩
  | 20 => ⟨![421173, 84910], ![0, 1601]⟩
  | 21 => ⟨![420265, 85818], ![0, 1594]⟩
  | 22 => ⟨![420265, 85818], ![0, 1587]⟩
  | 23 => ⟨![420650, 85433], ![0, 1580]⟩
  | 24 => ⟨![419615, 86468], ![0, 1572]⟩
  | 25 => ⟨![420000, 86083], ![0, 1565]⟩
  | 26 => ⟨![419133, 86950], ![0, 1557]⟩
  | 27 => ⟨![419399, 86684], ![0, 1549]⟩
  | 28 => ⟨![418436, 87647], ![0, 1541]⟩
  | 29 => ⟨![418436, 87647], ![0, 1533]⟩
  | 30 => ⟨![417786, 88297], ![0, 1525]⟩
  | 31 => ⟨![417882, 88201], ![0, 1517]⟩
  | 32 => ⟨![416974, 89109], ![0, 1508]⟩
  | 33 => ⟨![416685, 89398], ![0, 1500]⟩
  | 34 => ⟨![416709, 89374], ![0, 1491]⟩
  | 35 => ⟨![415842, 90241], ![0, 1482]⟩
  | 36 => ⟨![415024, 91059], ![0, 1473]⟩
  | 37 => ⟨![415444, 90639], ![0, 1463]⟩
  | 38 => ⟨![414433, 91650], ![0, 1454]⟩
  | 39 => ⟨![413648, 92435], ![0, 1444]⟩
  | 40 => ⟨![412830, 93253], ![0, 1434]⟩
  | 41 => ⟨![412239, 93844], ![0, 1423]⟩
  | 42 => ⟨![411387, 94696], ![0, 1412]⟩
  | 43 => ⟨![410665, 95418], ![0, 1401]⟩
  | 44 => ⟨![410074, 96009], ![0, 1390]⟩
  | 45 => ⟨![408326, 97757], ![0, 1377]⟩
  | 46 => ⟨![407714, 98369], ![0, 1365]⟩
  | 47 => ⟨![405867, 100216], ![0, 1351]⟩
  | 48 => ⟨![404337, 101746], ![0, 1337]⟩
  | 49 => ⟨![401427, 104656], ![0, 1321]⟩
  | 50 => ⟨![397746, 108337], ![0, 1304]⟩
  | 51 => ⟨![390610, 115473], ![0, 1283]⟩
  | 52 => ⟨![372372, 133711], ![0, 1255]⟩
  | 53 => ⟨![352430, 153653], ![0, 1211]⟩
  | 54 => ⟨![335910, 170173], ![0, 1154]⟩
  | 55 => ⟨![321696, 184387], ![0, 1083]⟩
  | 56 => ⟨![309843, 196240], ![0, 1001]⟩
  | 57 => ⟨![299392, 206691], ![0, 908]⟩
  | 58 => ⟨![290657, 215426], ![0, 805]⟩
  | 59 => ⟨![282409, 223674], ![0, 693]⟩
  | 60 => ⟨![275411, 230672], ![0, 572]⟩
  | 61 => ⟨![268813, 237270], ![0, 441]⟩
  | 62 => ⟨![263004, 243079], ![0, 303]⟩
  | 63 => ⟨![257706, 248377], ![0, 156]⟩
  | 64 => ⟨![253041, 253042], ![0, 0]⟩
  | _ => ⟨![0,0], ![0,0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1169 42 76312412820394717990887383040 76312860721385385203023979520 76312277475203302256134483200 76312293036589399883944687200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1170 42 81718789557422638916392406400 81719268030784541317930375680 81718773053453904164276563200 81718788614840001792086767200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1170 42 81545869796527447715128579200 81546347289382956377798990400 81545854193710881928549920000 81545869755096979556360124000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1170 42 81238534363031321321739820800 81239010113332189849341873600 81238521310695402736096800000 81238536872081500363907004000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1171 42 81238533149940006708754344000 81239008899035393034061896000 81238521310695402736096800000 81238536872081500363907004000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1171 42 82235427583958655682502554560 82235908978538338804180236480 82235416457507810599881043200 82235432018893908227691247200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1171 42 81929656368544077708457812480 81930136031484528015544619520 81929642900391058118920531200 81929658461777155746730735200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1171 42 81776114422467010673395956480 81776593216073671723671943680 81776098450634301459358444800 81776114012020399087168648800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1172 42 81776115480481239977163256320 81776594273801943534990144480 81776098450634301459358444800 81776114012020399087168648800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1172 42 82578489231124055092992494400 82578972562796550445043529600 82578485122143501251941920000 82578500683529598879752124000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1172 42 82333762233502427366317755840 82334244180899483490400508160 82333751945971675571380972800 82333767507357773199191176800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1173 42 82333767307587288831207336960 82334249256374502660202685760 82333751945971675571380972800 82333767507357773199191176800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1173 42 83132827218467121656212070400 83133313687386526373163463680 83132823145722771979749715200 83132838707108869607559919200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1173 42 82829105215981657253445176640 82829589968179185400013675040 82829090920664906254895443200 82829106482051003882705647200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1174 42 82676576469587869475870181120 82677060353808431920004529600 82676569788018188930212588800 82676585349404286558022792800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1174 42 82829106735215043607069870080 82829591486346342084122574720 82829090920664906254895443200 82829106482051003882705647200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1174 42 83360377024602863202144051840 83360864782365843874229550720 83360364571088398543971052800 83360380132474496171781256800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1175 42 83189556566643901567534398720 83190043354300919505903248640 83189548160738953642599148800 83189563722125051270409352800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1175 42 83870714429141887979433319680 83871205071841309185153541440 83870710315668455821370092800 83870725877054553449180296800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1176 42 83870715084916341857521927680 83871205726924941901617058560 83870710315668455821370092800 83870725877054553449180296800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1176 42 83568672081083912455535025600 83569161011650321546372616640 83568666910701598611038956800 83568682472087696238849160800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1176 42 84279915985932437013214171200 84280408944192583383189519360 84279909417307279747670764800 84279924978693377375480968800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1177 42 84279920927520743423046195840 84280413886865025967858311360 84279909417307279747670764800 84279924978693377375480968800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1177 42 83978822722519478971417939200 83979313977514502123376307200 83978806643764913967686380800 83978822205151011595496584800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1178 42 84786700345959124879804938240 84787196171255695185366113280 84786693370873438730674924800 84786708932259536358485128800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1178 42 84486775725055718393215017600 84487269854547569770290817920 84486759642122505894716140800 84486775203508603522526344800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1178 42 85161227799464012205591788160 85161725744374141863910637760 85161218720786052989018860800 85161234282172150616829064800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1178 42 84954669338774014799072832000 84955166110832599522025568000 84954664660213333398558240000 84954680221599431026368444000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1179 42 85700887046266174409360361600 85701388041992006923501336320 85700884697345213419866451200 85700900258731311047676655200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1180 42 85700887144914462671063111040 85701388139387942925312969120 85700884697345213419866451200 85700900258731311047676655200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1180 42 86202120540241129892349856320 86202624373196198576298141600 86202114929032071481772371200 86202130490418169109582575200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1181 42 86128222257040919084402529600 86128725672412173642378831840 86128211304160732863908179200 86128226865546830491718383200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1182 42 86825495038736296066401216000 86826002396855581470339144000 86825494280780343736964640000 86825509842166441364774844000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1182 42 87046630642027401456110515200 87047139255589622726329320000 87046618843811210076316396800 87046634405197307704126600800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1182 42 87028279275919040867030227200 87028787782758950496992836800 87028270413694348937041440000 87028285975080446564851644000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1183 42 87689408825830832039418880320 87689921074622188037811207360 87689400293571637310507347200 87689415854957734938317551200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1184 42 88309957198797950277220416000 88310472960941453158345188000 88309945838701907186718240000 88309961400088004814528444000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1184 42 87991719042747742552579708800 87992232996378092611942548000 87991718766252417216583200000 87991734327638514844393404000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1186 42 88756354728983959613321051520 88756873016062991904698806080 88756341175400086154207980800 88756356736786183782018184800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1187 42 89346757647887762839515054720 89347279275169140417151294080 89346746003632219444175596800 89346761565018317071985800800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1188 42 89958922656677198740615106880 89959447749452663679773423040 89958907631340605711278828800 89958923192726703339089032800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1188 42 90399250650746189823835046400 90399778230136762460358489600 90399245638947912780256800000 90399261200334010408067004000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1190 43 91031177666473376275727464320 91031708819948177592839053440 91031175979917951992449363200 91031191541304049620259567200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1191 43 91564036937536149741911785920 91564571107369246793722197120 91564030608678166164628204800 91564046170064263792438408800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1192 43 91998411249981525885576360000 91998947882190468913637760000 91998391352164353060279840000 91998406913550450688090044000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1193 43 93273553212417127819428376320 93274097053691664297852896160 93273549710997885404170579200 93273565272383983031980783200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1195 43 93716646765566626100059992000 93717193118874388388397072000 93716627459744991880058400000 93716643021131089507868604000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1197 43 95043225287996242207612715520 95043779143133181469409381760 95043216058056399649098067200 95043231619442497276908271200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1199 43 96130071737832537604353021120 96130631744864063930080301760 96130054297124389471504723200 96130069858510487099314927200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check49 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 49 (witness 49) := by
  apply checks_of_runs _ _ _ _ _ _ 1202 43 98167008331001359941850149120 98167579859664759406470341760 98166999132951603950504275200 98167014694337701578314479200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check50 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 50 (witness 50) := by
  apply checks_of_runs _ _ _ _ _ _ 1206 43 100686976182736589751520020480 100687561971368266050181018560 100686960529330227804227923200 100686976090716325432038127200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check51 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 51 (witness 51) := by
  apply checks_of_runs _ _ _ _ _ _ 1213 43 105391872420492244699839654720 105392484821964782273903136000 105391869766135647293104876800 105391885327521744920915080800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check52 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 52 (witness 52) := by
  apply checks_of_runs _ _ _ _ _ _ 1225 44 116335642694000493362729536800 116336317010624379948889709280 116335633150655257601493331200 116335648712041355229303535200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check53 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 53 (witness 53) := by
  apply checks_of_runs _ _ _ _ _ _ 1223 44 126523478313866852061809378400 126524210257665496807254165600 126523477308296958312407788800 126523492869683055940217992800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check54 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 54 (witness 54) := by
  apply checks_of_runs _ _ _ _ _ _ 1221 44 133556178149094720767054330880 133556949876656866877546143680 133556164970719028621304556800 133556180532105126249114760800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check55 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 55 (witness 55) := by
  apply checks_of_runs _ _ _ _ _ _ 1219 44 138586794666785252740196366400 138587594841068356086729708960 138586789926310690154727763200 138586805487696787782537967200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check56 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 56 (witness 56) := by
  apply checks_of_runs _ _ _ _ _ _ 1217 44 142060131214663917687554977920 142060951029017414754046782720 142060125867959236465484524800 142060141429345334093294728800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check57 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 57 (witness 57) := by
  apply checks_of_runs _ _ _ _ _ _ 1216 43 144578167991039353736109744000 144579002040628222831139957760 144578165550904066198325587200 144578181112290163826135791200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check58 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 58 (witness 58) := by
  apply checks_of_runs _ _ _ _ _ _ 1214 43 146291308490309227285179366720 146292152220340733850199925760 146291307869891879743375699200 146291323431277977371185903200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check59 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 59 (witness 59) := by
  apply checks_of_runs _ _ _ _ _ _ 1212 43 147581760255980637928062787200 147582611276815870930906992000 147581755297820016074987040000 147581770859206113702797244000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check60 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 60 (witness 60) := by
  apply checks_of_runs _ _ _ _ _ _ 1211 43 148427437858930942631696183040 148428293656132627646939942400 148427427878998467309586771200 148427443440384564937396975200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check61 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 61 (witness 61) := by
  apply checks_of_runs _ _ _ _ _ _ 1209 43 149015232685631621126056075200 149016091794883100721417032640 149015230415860624695190252800 149015245977246722323000456800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check62 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 62 (witness 62) := by
  apply checks_of_runs _ _ _ _ _ _ 1208 43 149364408625861116325281868800 149365269703772070356225462400 149364399466873271711077920000 149364415028259369338888124000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check63 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 63 (witness 63) := by
  apply checks_of_runs _ _ _ _ _ _ 1207 43 149545414644219624481673189760 149546276736386889790175284800 149545406014394563786295635200 149545421575780661414105839200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel
private theorem check64 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2360 64 (witness 64) := by
  apply checks_of_runs _ _ _ _ _ _ 1205 43 149596226346601999747401050880 149597088713216142007278447360 149596226318475062818490707200 149596241879861160446300911200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 65) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2360 (max 1 i.val) (witness i.val) := by
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
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58
  · exact check59
  · exact check60
  · exact check61
  · exact check62
  · exact check63
  · exact check64

theorem positive {h : ℕ} (lo : 2360≤h) (hi : h≤2382) (i : Fin 65) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179808 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

#print axioms bank_checked
#print axioms positive
end Lower6962.B1.TerminalReceipts
