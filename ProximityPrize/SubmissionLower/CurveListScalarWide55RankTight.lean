import ProximityPrize.SubmissionLower.CurveListScalarWide55Rank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace CurveListScalarWide55
open Finset CJ0 CurveListSparsePackets
open scoped BigOperators
open CJ1 (total_eq_sum)
open private allowance block grade rank_sum runs
  from ProximityPrize.SubmissionLower.CurveListScalarWide55Rank

def extraWitness : Witness :=
  ⟨true, 131, [(10,1)], [runs [(0, 0, [621456043, -177558868, -799014889, 710235727, 710237410, 11594, -710179440, -710011327, -1064596708, 2185469, -1059889544, 11920740, 22848085, 38665990, 57998985, 77331980, -440844882, -968119624, -440844882, 77331980, 57998985, 38665990]), (1, 0, [621456043, -799014911, 22, 710235705, 1705, 9889, -710189329, 178002, -1064774710, -1063746254, 3856710, 8064030, 14784055, 23881935, 34117050, 43214930, -484059812, -484059812, 43214930, 34117050]), (2, 0, [621456043, 710235479, -710235457, -710235271, 710236976, -710227087, 37758, 140244, -1064914954, 1168700, 2688010, 5376020, 9408035, 14473900, 19643150, 23571780, -507631592, 23571780]), (3, 0, [621456043, 88779436, -799014893, 88779622, 621457354, 799021992, -798984234, 799124478, 266667001, -265498301, 268186311, -262810291, 272218326, -257744426, 277387576, -253815796]), (4, 0, [621456043, -532676607, -266338286, 355117908, 266339446, 532682546, 799039653, 84825, 266582176, -532080477, 800266788, -1063077079, -795411028, 537666602]), (5, 0, [621456043, 976573783, 887794364, -532676456, 799015902, -266333356, -1065333424, -1065288184, -798836073, 266755596, 533511192, 534118162]), (6, 0, [621456043, 355117740, 532676624, -1065353080, -266337451, 4095, -1065337519, 49335, -798885408, -1065065429]), (7, 0, [621456043, -266338303, 799014927, 266338426, -532675877, 532679972, 532688942, -532639607]), (8, 0, [621456043, -887794346, -443897160, 710235586, 887794970, -355114998]), (9, 0, [621456043, 621456044, -1065353204, -355117643]), (10, 0, [621456043, 1])]]⟩

theorem extraBlock : (blockMatrix support 36 ((19 : ℤ)-22)).rank ≤ 131 :=
  (block_rank_le 36 19).trans (rank_witness axes 36 19 extraWitness
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- Recover one rank unit from the packet left at nominal rank in the first ledger. -/
theorem prefix_bound_tight : prefixRank support 76 ≤ 150777 := by
  let r (q u : ℕ) := (blockMatrix support q ((u : ℤ)-22)).rank
  let row (q : ℕ) := ∑ u ∈ range (77-q), r q u
  let cap (q : ℕ) := ∑ u ∈ range (77-q), allowance q u
  have hrow (q : ℕ) : row q ≤ cap q := sum_le_sum fun u _ => block q u
  have hu : 19 ∈ range (77-36) := by decide
  have hpacket : r 36 19 + 1 ≤ allowance 36 19 := by
    have hcap : allowance 36 19 = 132 := by decide +kernel
    have hr : r 36 19 ≤ 131 := extraBlock
    omega
  have hsmall : row 36 + 1 ≤ cap 36 := by
    have hr := sum_erase_add (range (77-36)) (r 36) hu
    have hc := sum_erase_add (range (77-36)) (allowance 36) hu
    change _ + r 36 19 = row 36 at hr
    change _ + allowance 36 19 = cap 36 at hc
    have htail : (∑ u ∈ (range (77-36)).erase 19, r 36 u) ≤
        ∑ u ∈ (range (77-36)).erase 19, allowance 36 u :=
      sum_le_sum fun u _ => block 36 u
    omega
  have hq : 36 ∈ range 76 := by decide
  have hr := sum_erase_add (range 76) row hq
  have hc := sum_erase_add (range 76) cap hq
  have htail : (∑ q ∈ (range 76).erase 36, row q) ≤
      ∑ q ∈ (range 76).erase 36, cap q := sum_le_sum fun q _ => hrow q
  have htotal : (∑ q ∈ range 76, cap q) = 150778 := by
    simpa only [cap, grade, total_eq_sum] using rank_sum
  change (∑ q ∈ range 76, row q) ≤ 150777
  omega

end CurveListScalarWide55
