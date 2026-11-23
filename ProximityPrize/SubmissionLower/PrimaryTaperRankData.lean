import ProximityPrize.SubmissionLower.PrimaryTaperBudget

set_option Elab.async false
set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace TaperBudget

open K1_13 (Geom)
open K1_13_2 (BlockIndex)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

private abbrev row := rowSum 600

open K1_13_2_3_7 (countParts natKernel natDen)

-- Pass the row's high endpoint to each cell. The two clipping cases share
-- that endpoint, and it cancels from the case in which the kernel is positive.
private def plainRank (top low here inner innerLow : ℕ × ℕ) : ℕ :=
  min (top.1 + low.2 - (top.2 + low.1))
    (here.1 + inner.2 + innerLow.1 + low.2 -
      (here.2 + inner.1 + innerLow.2 + low.1))

private theorem plainRank_eq (top low here inner innerLow : ℕ × ℕ) :
    plainRank top low here inner innerLow =
      (top.1 + low.2 - (top.2 + low.1)) -
        (top.1 + here.2 + inner.1 + innerLow.2 -
          (top.2 + here.1 + inner.2 + innerLow.1)) := by
  unfold plainRank
  omega

private def rowRank (d j h r : ℕ) (top : ℕ × ℕ) : ℕ :=
  plainRank top (countParts d (1650 - j)) (natDen h, 0)
    (natDen (h - 3 * r), 0) (countParts (d - r) (1650 - j))

private theorem smallParts (d n : ℕ) (hn : n ≤ d + 1) :
    countParts d n = (natDen n, 0) := by
  have cut : n.min (3 * d + 1) = n := Nat.min_eq_left (by omega)
  simp only [countParts, cut, hn, ite_true]

private theorem rowRank_eq (d j h r : ℕ) (hr : r ≠ 0) (hh : h ≤ d + 1) :
    rowRank d j h r (countParts d 1651) = natOld d j - natKernel d j h r := by
  unfold rowRank
  rw [plainRank_eq]
  unfold natOld natKernel
  cases countParts d 1651
  cases countParts d (1650 - j)
  rw [smallParts d h hh, smallParts (d-r) (h-3*r) (by omega)]
  cases countParts (d - r) (1650 - j)
  simp only [hr, if_false]

private def cell (q d r : ℕ) (top : ℕ × ℕ) (j : ℕ) : ℕ :=
  let h := 4650 - q - j
  let p := valuePower d q j
  let before := rowRank 1650 j h ((4653 - q) / 4) (countParts 1650 1651)
  let plain := rowRank d j h r top
  before - if p = 0 then plain else
    let low := countParts d (1650 - j)
    let other := natKernel (d - p) j h ((3003 + (d - p) - q) / 4)
    min plain (top.1 + low.2 - (top.2 + low.1) - other)

private theorem cell_eq (t j : ℕ) (ht : t < 499) (hj : j < 600) :
    let q := 3514 + t
    let d := cap q
    cell q d ((3003 + d - q) / 4) (countParts d 1651) j = natCell t j := by
  dsimp only
  let q := 3514 + t
  let d := cap q
  let h := 4650 - q - j
  let r := (3003 + d - q) / 4
  let p := valuePower d q j
  have hq : q + j < 4650 := by dsimp [q]; omega
  have hrBefore : (4653 - q) / 4 ≠ 0 := by dsimp [q]; omega
  have hcap : d = (131312 - 26 * q) / 25 := by
    dsimp only [d]
    rw [cap, if_neg (by dsimp [q]; omega)]
  have hr : r ≠ 0 := by
    dsimp only [r]
    rw [hcap]
    dsimp [q]
    omega
  have hSmallBefore : h ≤ 1650 + 1 := by dsimp [h, q]; omega
  have hSmall : h ≤ d + 1 := by
    rw [hcap]
    dsimp [h, q]
    omega
  change cell q d r (countParts d 1651) j = rankNat 1650 q j 0 - rankNat d q j p
  unfold cell rankNat
  simp only [hq, if_true, Nat.sub_zero]
  change (rowRank 1650 j h ((4653 - q) / 4) (countParts 1650 1651) - _) = _
  rw [rowRank_eq _ _ _ _ hrBefore hSmallBefore, rowRank_eq _ _ _ _ hr hSmall]
  change _ = (natOld 1650 j - max (natKernel 1650 j h ((4653 - q) / 4))
    (natKernel 1650 j h ((4653 - q) / 4))) -
    (natOld d j - max (natKernel d j h r)
      (natKernel (d - p) j h ((3003 + (d - p) - q) / 4)))
  rw [max_self]
  change (_ - if p = 0 then _ else _) = _
  by_cases hp : p = 0
  · simp only [hp, ite_true, Nat.sub_zero]
    dsimp only [r]
    simp only [max_self]
  · rw [if_neg hp]
    change _ - min (natOld d j - natKernel d j h r)
      (natOld d j - natKernel (d - p) j h ((3003 + (d - p) - q) / 4)) = _
    omega

private def fastRow (t : ℕ) : ℕ :=
  let q := 3514 + t
  let d := cap q
  sumRange (cell q d ((3003 + d - q) / 4) (countParts d 1651)) 600

private theorem sumRange_congr (f g : ℕ → ℕ) (n : ℕ)
    (he : ∀ j < n, f j = g j) : sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumRange, sumRange, he n (by omega), ih (fun j hj => he j (by omega))]

private theorem fastRow_eq (t : ℕ) (ht : t < 499) : fastRow t = row t := by
  unfold fastRow row rowSum
  apply sumRange_congr
  intro j hj
  exact cell_eq t j ht hj

private theorem fastChunk_eq (lo n : ℕ) (hn : lo + n ≤ 499) :
    sumChunk fastRow lo n = sumChunk row lo n := by
  unfold sumChunk
  apply sumRange_congr
  intro j hj
  exact fastRow_eq (lo + j) (by omega)

private theorem join (lo n m next full : ℕ) (a b result : ℕ)
    (hLen : n+m = full) (hStart : lo+n = next) (hValue : Nat.add a b = result)
    (ha : sumChunk row lo n = a) (hb : sumChunk row next m = b) :
    sumChunk row lo full = result := by
  rw [← hLen, sumChunk_add row, ha, hStart, hb]
  exact hValue

set_option profiler true in
private theorem rows0First : sumChunk row 0 4 = 1485305881 := by
  rw [← fastChunk_eq 0 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows0Last : sumChunk row 4 4 = 1504034732 := by
  rw [← fastChunk_eq 4 4 (by decide)]
  decide +kernel
private theorem rows0 : sumChunk row 0 8 = 2989340613 :=
  join 0 4 4 4 8 1485305881 1504034732 2989340613 rfl rfl rfl rows0First rows0Last
set_option profiler true in
private theorem rows8First : sumChunk row 8 4 = 1522881829 := by
  rw [← fastChunk_eq 8 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows8Last : sumChunk row 12 4 = 1541839881 := by
  rw [← fastChunk_eq 12 4 (by decide)]
  decide +kernel
private theorem rows8 : sumChunk row 8 8 = 3064721710 :=
  join 8 4 4 12 8 1522881829 1541839881 3064721710 rfl rfl rfl rows8First rows8Last
set_option profiler true in
private theorem rows16First : sumChunk row 16 4 = 1560903605 := by
  rw [← fastChunk_eq 16 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows16Last : sumChunk row 20 4 = 1580097712 := by
  rw [← fastChunk_eq 20 4 (by decide)]
  decide +kernel
private theorem rows16 : sumChunk row 16 8 = 3141001317 :=
  join 16 4 4 20 8 1560903605 1580097712 3141001317 rfl rfl rfl rows16First rows16Last
set_option profiler true in
private theorem rows24First : sumChunk row 24 4 = 1601056490 := by
  rw [← fastChunk_eq 24 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows24Last : sumChunk row 28 4 = 1620650452 := by
  rw [← fastChunk_eq 28 4 (by decide)]
  decide +kernel
private theorem rows24 : sumChunk row 24 8 = 3221706942 :=
  join 24 4 4 28 8 1601056490 1620650452 3221706942 rfl rfl rfl rows24First rows24Last
set_option profiler true in
private theorem rows32First : sumChunk row 32 4 = 1640395910 := by
  rw [← fastChunk_eq 32 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows32Last : sumChunk row 36 4 = 1660321337 := by
  rw [← fastChunk_eq 36 4 (by decide)]
  decide +kernel
private theorem rows32 : sumChunk row 32 8 = 3300717247 :=
  join 32 4 4 36 8 1640395910 1660321337 3300717247 rfl rfl rfl rows32First rows32Last
set_option profiler true in
private theorem rows40First : sumChunk row 40 4 = 1680443364 := by
  rw [← fastChunk_eq 40 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows40Last : sumChunk row 44 4 = 1700765316 := by
  rw [← fastChunk_eq 44 4 (by decide)]
  decide +kernel
private theorem rows40 : sumChunk row 40 8 = 3381208680 :=
  join 40 4 4 44 8 1680443364 1700765316 3381208680 rfl rfl rfl rows40First rows40Last
set_option profiler true in
private theorem rows48First : sumChunk row 48 4 = 1723357739 := by
  rw [← fastChunk_eq 48 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows48Last : sumChunk row 52 4 = 1744993180 := by
  rw [← fastChunk_eq 52 4 (by decide)]
  decide +kernel
private theorem rows48 : sumChunk row 48 8 = 3468350919 :=
  join 48 4 4 52 8 1723357739 1744993180 3468350919 rfl rfl rfl rows48First rows48Last
set_option profiler true in
private theorem rows56First : sumChunk row 56 4 = 1766202143 := by
  rw [← fastChunk_eq 56 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows56Last : sumChunk row 60 4 = 1787699073 := by
  rw [← fastChunk_eq 60 4 (by decide)]
  decide +kernel
private theorem rows56 : sumChunk row 56 8 = 3553901216 :=
  join 56 4 4 60 8 1766202143 1787699073 3553901216 rfl rfl rfl rows56First rows56Last
set_option profiler true in
private theorem rows64First : sumChunk row 64 4 = 1809466020 := by
  rw [← fastChunk_eq 64 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows64Last : sumChunk row 68 4 = 1831539028 := by
  rw [← fastChunk_eq 68 4 (by decide)]
  decide +kernel
private theorem rows64 : sumChunk row 64 8 = 3641005048 :=
  join 64 4 4 68 8 1809466020 1831539028 3641005048 rfl rfl rfl rows64First rows64Last
set_option profiler true in
private theorem rows72First : sumChunk row 72 4 = 1855931863 := by
  rw [← fastChunk_eq 72 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows72Last : sumChunk row 76 4 = 1880798280 := by
  rw [← fastChunk_eq 76 4 (by decide)]
  decide +kernel
private theorem rows72 : sumChunk row 72 8 = 3736730143 :=
  join 72 4 4 76 8 1855931863 1880798280 3736730143 rfl rfl rfl rows72First rows72Last
set_option profiler true in
private theorem rows80First : sumChunk row 80 4 = 1904014052 := by
  rw [← fastChunk_eq 80 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows80Last : sumChunk row 84 4 = 1927578002 := by
  rw [← fastChunk_eq 84 4 (by decide)]
  decide +kernel
private theorem rows80 : sumChunk row 80 8 = 3831592054 :=
  join 80 4 4 84 8 1904014052 1927578002 3831592054 rfl rfl rfl rows80First rows80Last
set_option profiler true in
private theorem rows88First : sumChunk row 88 4 = 1951491371 := by
  rw [← fastChunk_eq 88 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows88Last : sumChunk row 92 4 = 1975747103 := by
  rw [← fastChunk_eq 92 4 (by decide)]
  decide +kernel
private theorem rows88 : sumChunk row 88 8 = 3927238474 :=
  join 88 4 4 92 8 1951491371 1975747103 3927238474 rfl rfl rfl rows88First rows88Last
set_option profiler true in
private theorem rows96First : sumChunk row 96 4 = 2001730549 := by
  rw [← fastChunk_eq 96 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows96Last : sumChunk row 100 4 = 2030944498 := by
  rw [← fastChunk_eq 100 4 (by decide)]
  decide +kernel
private theorem rows96 : sumChunk row 96 8 = 4032675047 :=
  join 96 4 4 100 8 2001730549 2030944498 4032675047 rfl rfl rfl rows96First rows96Last
set_option profiler true in
private theorem rows104First : sumChunk row 104 4 = 2056527261 := by
  rw [← fastChunk_eq 104 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows104Last : sumChunk row 108 4 = 2082484478 := by
  rw [← fastChunk_eq 108 4 (by decide)]
  decide +kernel
private theorem rows104 : sumChunk row 104 8 = 4139011739 :=
  join 104 4 4 108 8 2056527261 2082484478 4139011739 rfl rfl rfl rows104First rows104Last
set_option profiler true in
private theorem rows112First : sumChunk row 112 4 = 2108823131 := by
  rw [← fastChunk_eq 112 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows112Last : sumChunk row 116 4 = 2135544491 := by
  rw [← fastChunk_eq 116 4 (by decide)]
  decide +kernel
private theorem rows112 : sumChunk row 112 8 = 4244367622 :=
  join 112 4 4 116 8 2108823131 2135544491 4244367622 rfl rfl rfl rows112First rows112Last
set_option profiler true in
private theorem rows120First : sumChunk row 120 4 = 2162649179 := by
  rw [← fastChunk_eq 120 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows120Last : sumChunk row 124 4 = 2197193819 := by
  rw [← fastChunk_eq 124 4 (by decide)]
  decide +kernel
private theorem rows120 : sumChunk row 120 8 = 4359842998 :=
  join 120 4 4 124 8 2162649179 2197193819 4359842998 rfl rfl rfl rows120First rows120Last
set_option profiler true in
private theorem rows128First : sumChunk row 128 4 = 2225294956 := by
  rw [← fastChunk_eq 128 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows128Last : sumChunk row 132 4 = 2253779578 := by
  rw [← fastChunk_eq 132 4 (by decide)]
  decide +kernel
private theorem rows128 : sumChunk row 128 8 = 4479074534 :=
  join 128 4 4 132 8 2225294956 2253779578 4479074534 rfl rfl rfl rows128First rows128Last
set_option profiler true in
private theorem rows136First : sumChunk row 136 4 = 2282645520 := by
  rw [← fastChunk_eq 136 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows136Last : sumChunk row 140 4 = 2311889969 := by
  rw [← fastChunk_eq 140 4 (by decide)]
  decide +kernel
private theorem rows136 : sumChunk row 136 8 = 4594535489 :=
  join 136 4 4 140 8 2282645520 2311889969 4594535489 rfl rfl rfl rows136First rows136Last
set_option profiler true in
private theorem rows144First : sumChunk row 144 4 = 2341509468 := by
  rw [← fastChunk_eq 144 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows144Last : sumChunk row 148 4 = 2377938403 := by
  rw [← fastChunk_eq 148 4 (by decide)]
  decide +kernel
private theorem rows144 : sumChunk row 144 8 = 4719447871 :=
  join 144 4 4 148 8 2341509468 2377938403 4719447871 rfl rfl rfl rows144First rows144Last
set_option profiler true in
private theorem rows152First : sumChunk row 152 4 = 2410653733 := by
  rw [← fastChunk_eq 152 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows152Last : sumChunk row 156 4 = 2441609258 := by
  rw [← fastChunk_eq 156 4 (by decide)]
  decide +kernel
private theorem rows152 : sumChunk row 152 8 = 4852262991 :=
  join 152 4 4 156 8 2410653733 2441609258 4852262991 rfl rfl rfl rows152First rows152Last
set_option profiler true in
private theorem rows160First : sumChunk row 160 4 = 2472918669 := by
  rw [← fastChunk_eq 160 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows160Last : sumChunk row 164 4 = 2504575080 := by
  rw [← fastChunk_eq 164 4 (by decide)]
  decide +kernel
private theorem rows160 : sumChunk row 160 8 = 4977493749 :=
  join 160 4 4 164 8 2472918669 2504575080 4977493749 rfl rfl rfl rows160First rows160Last
set_option profiler true in
private theorem rows168First : sumChunk row 168 4 = 2536570953 := by
  rw [← fastChunk_eq 168 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows168Last : sumChunk row 172 4 = 2573954773 := by
  rw [← fastChunk_eq 172 4 (by decide)]
  decide +kernel
private theorem rows168 : sumChunk row 168 8 = 5110525726 :=
  join 168 4 4 172 8 2536570953 2573954773 5110525726 rfl rfl rfl rows168First rows168Last
set_option profiler true in
private theorem rows176First : sumChunk row 176 4 = 2611827885 := by
  rw [← fastChunk_eq 176 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows176Last : sumChunk row 180 4 = 2645008211 := by
  rw [← fastChunk_eq 180 4 (by decide)]
  decide +kernel
private theorem rows176 : sumChunk row 176 8 = 5256836096 :=
  join 176 4 4 180 8 2611827885 2645008211 5256836096 rfl rfl rfl rows176First rows176Last
set_option profiler true in
private theorem rows184First : sumChunk row 184 4 = 2678487772 := by
  rw [← fastChunk_eq 184 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows184Last : sumChunk row 188 4 = 2712255605 := by
  rw [← fastChunk_eq 188 4 (by decide)]
  decide +kernel
private theorem rows184 : sumChunk row 184 8 = 5390743377 :=
  join 184 4 4 188 8 2678487772 2712255605 5390743377 rfl rfl rfl rows184First rows184Last
set_option profiler true in
private theorem rows192First : sumChunk row 192 4 = 2746284346 := by
  rw [← fastChunk_eq 192 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows192Last : sumChunk row 196 4 = 2783468781 := by
  rw [← fastChunk_eq 196 4 (by decide)]
  decide +kernel
private theorem rows192 : sumChunk row 192 8 = 5529753127 :=
  join 192 4 4 196 8 2746284346 2783468781 5529753127 rfl rfl rfl rows192First rows192Last
set_option profiler true in
private theorem rows200First : sumChunk row 200 4 = 2826812160 := by
  rw [← fastChunk_eq 200 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows200Last : sumChunk row 204 4 = 2861782494 := by
  rw [← fastChunk_eq 204 4 (by decide)]
  decide +kernel
private theorem rows200 : sumChunk row 200 8 = 5688594654 :=
  join 200 4 4 204 8 2826812160 2861782494 5688594654 rfl rfl rfl rows200First rows200Last
set_option profiler true in
private theorem rows208First : sumChunk row 208 4 = 2896967273 := by
  rw [← fastChunk_eq 208 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows208Last : sumChunk row 212 4 = 2932341517 := by
  rw [← fastChunk_eq 212 4 (by decide)]
  decide +kernel
private theorem rows208 : sumChunk row 208 8 = 5829308790 :=
  join 208 4 4 212 8 2896967273 2932341517 5829308790 rfl rfl rfl rows208First rows208Last
set_option profiler true in
private theorem rows216First : sumChunk row 216 4 = 2967887257 := by
  rw [← fastChunk_eq 216 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows216Last : sumChunk row 220 4 = 3003601861 := by
  rw [← fastChunk_eq 220 4 (by decide)]
  decide +kernel
private theorem rows216 : sumChunk row 216 8 = 5971489118 :=
  join 216 4 4 220 8 2967887257 3003601861 5971489118 rfl rfl rfl rows216First rows216Last
set_option profiler true in
private theorem rows224First : sumChunk row 224 4 = 3052480342 := by
  rw [← fastChunk_eq 224 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows224Last : sumChunk row 228 4 = 3088642075 := by
  rw [← fastChunk_eq 228 4 (by decide)]
  decide +kernel
private theorem rows224 : sumChunk row 224 8 = 6141122417 :=
  join 224 4 4 228 8 3052480342 3088642075 6141122417 rfl rfl rfl rows224First rows224Last
set_option profiler true in
private theorem rows232First : sumChunk row 232 4 = 3124891453 := by
  rw [← fastChunk_eq 232 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows232Last : sumChunk row 236 4 = 3161217155 := by
  rw [← fastChunk_eq 236 4 (by decide)]
  decide +kernel
private theorem rows232 : sumChunk row 232 8 = 6286108608 :=
  join 232 4 4 236 8 3124891453 3161217155 6286108608 rfl rfl rfl rows232First rows232Last
set_option profiler true in
private theorem rows240First : sumChunk row 240 4 = 3197577569 := by
  rw [← fastChunk_eq 240 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows240Last : sumChunk row 244 4 = 3233962856 := by
  rw [← fastChunk_eq 244 4 (by decide)]
  decide +kernel
private theorem rows240 : sumChunk row 240 8 = 6431540425 :=
  join 240 4 4 244 8 3197577569 3233962856 6431540425 rfl rfl rfl rows240First rows240Last
set_option profiler true in
private theorem rows248First : sumChunk row 248 4 = 3280981029 := by
  rw [← fastChunk_eq 248 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows248Last : sumChunk row 252 4 = 3321060487 := by
  rw [← fastChunk_eq 252 4 (by decide)]
  decide +kernel
private theorem rows248 : sumChunk row 248 8 = 6602041516 :=
  join 248 4 4 252 8 3280981029 3321060487 6602041516 rfl rfl rfl rows248First rows248Last
set_option profiler true in
private theorem rows256First : sumChunk row 256 4 = 3357553905 := by
  rw [← fastChunk_eq 256 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows256Last : sumChunk row 260 4 = 3393955917 := by
  rw [← fastChunk_eq 260 4 (by decide)]
  decide +kernel
private theorem rows256 : sumChunk row 256 8 = 6751509822 :=
  join 256 4 4 260 8 3357553905 3393955917 6751509822 rfl rfl rfl rows256First rows256Last
set_option profiler true in
private theorem rows264First : sumChunk row 264 4 = 3430246264 := by
  rw [← fastChunk_eq 264 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows264Last : sumChunk row 268 4 = 3466394735 := by
  rw [← fastChunk_eq 268 4 (by decide)]
  decide +kernel
private theorem rows264 : sumChunk row 264 8 = 6896640999 :=
  join 264 4 4 268 8 3430246264 3466394735 6896640999 rfl rfl rfl rows264First rows264Last
set_option profiler true in
private theorem rows272First : sumChunk row 272 4 = 3509977905 := by
  rw [← fastChunk_eq 272 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows272Last : sumChunk row 276 4 = 3553472327 := by
  rw [← fastChunk_eq 276 4 (by decide)]
  decide +kernel
private theorem rows272 : sumChunk row 272 8 = 7063450232 :=
  join 272 4 4 276 8 3509977905 3553472327 7063450232 rfl rfl rfl rows272First rows272Last
set_option profiler true in
private theorem rows280First : sumChunk row 280 4 = 3589183148 := by
  rw [← fastChunk_eq 280 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows280Last : sumChunk row 284 4 = 3624623652 := by
  rw [← fastChunk_eq 284 4 (by decide)]
  decide +kernel
private theorem rows280 : sumChunk row 280 8 = 7213806800 :=
  join 280 4 4 284 8 3589183148 3624623652 7213806800 rfl rfl rfl rows280First rows280Last
set_option profiler true in
private theorem rows288First : sumChunk row 288 4 = 3659760311 := by
  rw [← fastChunk_eq 288 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows288Last : sumChunk row 292 4 = 3694603898 := by
  rw [← fastChunk_eq 292 4 (by decide)]
  decide +kernel
private theorem rows288 : sumChunk row 288 8 = 7354364209 :=
  join 288 4 4 292 8 3659760311 3694603898 7354364209 rfl rfl rfl rows288First rows288Last
set_option profiler true in
private theorem rows296First : sumChunk row 296 4 = 3733061761 := by
  rw [← fastChunk_eq 296 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows296Last : sumChunk row 300 4 = 3779052960 := by
  rw [← fastChunk_eq 300 4 (by decide)]
  decide +kernel
private theorem rows296 : sumChunk row 296 8 = 7512114721 :=
  join 296 4 4 300 8 3733061761 3779052960 7512114721 rfl rfl rfl rows296First rows296Last
set_option profiler true in
private theorem rows304First : sumChunk row 304 4 = 3812764742 := by
  rw [← fastChunk_eq 304 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows304Last : sumChunk row 308 4 = 3846024453 := by
  rw [← fastChunk_eq 308 4 (by decide)]
  decide +kernel
private theorem rows304 : sumChunk row 304 8 = 7658789195 :=
  join 304 4 4 308 8 3812764742 3846024453 7658789195 rfl rfl rfl rows304First rows304Last
set_option profiler true in
private theorem rows312First : sumChunk row 312 4 = 3878809052 := by
  rw [← fastChunk_eq 312 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows312Last : sumChunk row 316 4 = 3911033741 := by
  rw [← fastChunk_eq 316 4 (by decide)]
  decide +kernel
private theorem rows312 : sumChunk row 312 8 = 7789842793 :=
  join 312 4 4 316 8 3878809052 3911033741 7789842793 rfl rfl rfl rows312First rows312Last
set_option profiler true in
private theorem rows320First : sumChunk row 320 4 = 3942647488 := by
  rw [← fastChunk_eq 320 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows320Last : sumChunk row 324 4 = 3989923521 := by
  rw [← fastChunk_eq 324 4 (by decide)]
  decide +kernel
private theorem rows320 : sumChunk row 320 8 = 7932571009 :=
  join 320 4 4 324 8 3942647488 3989923521 7932571009 rfl rfl rfl rows320First rows320Last
set_option profiler true in
private theorem rows328First : sumChunk row 328 4 = 4020335609 := by
  rw [← fastChunk_eq 328 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows328Last : sumChunk row 332 4 = 4049999674 := by
  rw [← fastChunk_eq 332 4 (by decide)]
  decide +kernel
private theorem rows328 : sumChunk row 328 8 = 8070335283 :=
  join 328 4 4 332 8 4020335609 4049999674 8070335283 rfl rfl rfl rows328First rows328Last
set_option profiler true in
private theorem rows336First : sumChunk row 336 4 = 4078895217 := by
  rw [← fastChunk_eq 336 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows336Last : sumChunk row 340 4 = 4107053072 := by
  rw [← fastChunk_eq 340 4 (by decide)]
  decide +kernel
private theorem rows336 : sumChunk row 336 8 = 8185948289 :=
  join 336 4 4 340 8 4078895217 4107053072 8185948289 rfl rfl rfl rows336First rows336Last
set_option profiler true in
private theorem rows344First : sumChunk row 344 4 = 4134356936 := by
  rw [← fastChunk_eq 344 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows344Last : sumChunk row 348 4 = 4172876765 := by
  rw [← fastChunk_eq 348 4 (by decide)]
  decide +kernel
private theorem rows344 : sumChunk row 344 8 = 8307233701 :=
  join 344 4 4 348 8 4134356936 4172876765 8307233701 rfl rfl rfl rows344First rows344Last
set_option profiler true in
private theorem rows352First : sumChunk row 352 4 = 4202385662 := by
  rw [← fastChunk_eq 352 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows352Last : sumChunk row 356 4 = 4226856550 := by
  rw [← fastChunk_eq 356 4 (by decide)]
  decide +kernel
private theorem rows352 : sumChunk row 352 8 = 8429242212 :=
  join 352 4 4 356 8 4202385662 4226856550 8429242212 rfl rfl rfl rows352First rows352Last
set_option profiler true in
private theorem rows360First : sumChunk row 360 4 = 4250243983 := by
  rw [← fastChunk_eq 360 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows360Last : sumChunk row 364 4 = 4272559094 := by
  rw [← fastChunk_eq 364 4 (by decide)]
  decide +kernel
private theorem rows360 : sumChunk row 360 8 = 8522803077 :=
  join 360 4 4 364 8 4250243983 4272559094 8522803077 rfl rfl rfl rows360First rows360Last
set_option profiler true in
private theorem rows368First : sumChunk row 368 4 = 4293777656 := by
  rw [← fastChunk_eq 368 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows368Last : sumChunk row 372 4 = 4321666584 := by
  rw [← fastChunk_eq 372 4 (by decide)]
  decide +kernel
private theorem rows368 : sumChunk row 368 8 = 8615444240 :=
  join 368 4 4 372 8 4293777656 4321666584 8615444240 rfl rfl rfl rows368First rows368Last
set_option profiler true in
private theorem rows376First : sumChunk row 376 4 = 4348245954 := by
  rw [← fastChunk_eq 376 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows376Last : sumChunk row 380 4 = 4365613973 := by
  rw [← fastChunk_eq 380 4 (by decide)]
  decide +kernel
private theorem rows376 : sumChunk row 376 8 = 8713859927 :=
  join 376 4 4 380 8 4348245954 4365613973 8713859927 rfl rfl rfl rows376First rows376Last
set_option profiler true in
private theorem rows384First : sumChunk row 384 4 = 4381552393 := by
  rw [← fastChunk_eq 384 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows384Last : sumChunk row 388 4 = 4396118260 := by
  rw [← fastChunk_eq 388 4 (by decide)]
  decide +kernel
private theorem rows384 : sumChunk row 384 8 = 8777670653 :=
  join 384 4 4 388 8 4381552393 4396118260 8777670653 rfl rfl rfl rows384First rows384Last
set_option profiler true in
private theorem rows392First : sumChunk row 392 4 = 4409219770 := by
  rw [← fastChunk_eq 392 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows392Last : sumChunk row 396 4 = 4424452632 := by
  rw [← fastChunk_eq 396 4 (by decide)]
  decide +kernel
private theorem rows392 : sumChunk row 392 8 = 8833672402 :=
  join 392 4 4 396 8 4409219770 4424452632 8833672402 rfl rfl rfl rows392First rows392Last
set_option profiler true in
private theorem rows400First : sumChunk row 400 4 = 4445481744 := by
  rw [← fastChunk_eq 400 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows400Last : sumChunk row 404 4 = 4453571650 := by
  rw [← fastChunk_eq 404 4 (by decide)]
  decide +kernel
private theorem rows400 : sumChunk row 400 8 = 8899053394 :=
  join 400 4 4 404 8 4445481744 4453571650 8899053394 rfl rfl rfl rows400First rows400Last
set_option profiler true in
private theorem rows408First : sumChunk row 408 4 = 4459903253 := by
  rw [← fastChunk_eq 408 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows408Last : sumChunk row 412 4 = 4464518633 := by
  rw [← fastChunk_eq 412 4 (by decide)]
  decide +kernel
private theorem rows408 : sumChunk row 408 8 = 8924421886 :=
  join 408 4 4 412 8 4459903253 4464518633 8924421886 rfl rfl rfl rows408First rows408Last
set_option profiler true in
private theorem rows416First : sumChunk row 416 4 = 4467189844 := by
  rw [← fastChunk_eq 416 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows416Last : sumChunk row 420 4 = 4468020194 := by
  rw [← fastChunk_eq 420 4 (by decide)]
  decide +kernel
private theorem rows416 : sumChunk row 416 8 = 8935210038 :=
  join 416 4 4 420 8 4467189844 4468020194 8935210038 rfl rfl rfl rows416First rows416Last
set_option profiler true in
private theorem rows424First : sumChunk row 424 4 = 4480264126 := by
  rw [← fastChunk_eq 424 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows424Last : sumChunk row 428 4 = 4476707414 := by
  rw [← fastChunk_eq 428 4 (by decide)]
  decide +kernel
private theorem rows424 : sumChunk row 424 8 = 8956971540 :=
  join 424 4 4 428 8 4480264126 4476707414 8956971540 rfl rfl rfl rows424First rows424Last
set_option profiler true in
private theorem rows432First : sumChunk row 432 4 = 4471092046 := by
  rw [← fastChunk_eq 432 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows432Last : sumChunk row 436 4 = 4463173086 := by
  rw [← fastChunk_eq 436 4 (by decide)]
  decide +kernel
private theorem rows432 : sumChunk row 432 8 = 8934265132 :=
  join 432 4 4 436 8 4471092046 4463173086 8934265132 rfl rfl rfl rows432First rows432Last
set_option profiler true in
private theorem rows440First : sumChunk row 440 4 = 4453089426 := by
  rw [← fastChunk_eq 440 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows440Last : sumChunk row 444 4 = 4440561982 := by
  rw [← fastChunk_eq 444 4 (by decide)]
  decide +kernel
private theorem rows440 : sumChunk row 440 8 = 8893651408 :=
  join 440 4 4 444 8 4453089426 4440561982 8893651408 rfl rfl rfl rows440First rows440Last
set_option profiler true in
private theorem rows448First : sumChunk row 448 4 = 4434210117 := by
  rw [← fastChunk_eq 448 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows448Last : sumChunk row 452 4 = 4419338610 := by
  rw [← fastChunk_eq 452 4 (by decide)]
  decide +kernel
private theorem rows448 : sumChunk row 448 8 = 8853548727 :=
  join 448 4 4 452 8 4434210117 4419338610 8853548727 rfl rfl rfl rows448First rows448Last
set_option profiler true in
private theorem rows456First : sumChunk row 456 4 = 4398984483 := by
  rw [← fastChunk_eq 456 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows456Last : sumChunk row 460 4 = 4376009494 := by
  rw [← fastChunk_eq 460 4 (by decide)]
  decide +kernel
private theorem rows456 : sumChunk row 456 8 = 8774993977 :=
  join 456 4 4 460 8 4398984483 4376009494 8774993977 rfl rfl rfl rows456First rows456Last
set_option profiler true in
private theorem rows464First : sumChunk row 464 4 = 4350241414 := by
  rw [← fastChunk_eq 464 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows464Last : sumChunk row 468 4 = 4321747037 := by
  rw [← fastChunk_eq 468 4 (by decide)]
  decide +kernel
private theorem rows464 : sumChunk row 464 8 = 8671988451 :=
  join 464 4 4 468 8 4350241414 4321747037 8671988451 rfl rfl rfl rows464First rows464Last
set_option profiler true in
private theorem rows472First : sumChunk row 472 4 = 4294691941 := by
  rw [← fastChunk_eq 472 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows472Last : sumChunk row 476 4 = 4264420887 := by
  rw [← fastChunk_eq 476 4 (by decide)]
  decide +kernel
private theorem rows472 : sumChunk row 472 8 = 8559112828 :=
  join 472 4 4 476 8 4294691941 4264420887 8559112828 rfl rfl rfl rows472First rows472Last
set_option profiler true in
private theorem rows480First : sumChunk row 480 4 = 4226431548 := by
  rw [← fastChunk_eq 480 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows480Last : sumChunk row 484 4 = 4185417933 := by
  rw [← fastChunk_eq 484 4 (by decide)]
  decide +kernel
private theorem rows480 : sumChunk row 480 8 = 8411849481 :=
  join 480 4 4 484 8 4226431548 4185417933 8411849481 rfl rfl rfl rows480First rows480Last
set_option profiler true in
private theorem rows488First : sumChunk row 488 4 = 4141054965 := by
  rw [← fastChunk_eq 488 4 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows488Last : sumChunk row 492 4 = 4093504838 := by
  rw [← fastChunk_eq 492 4 (by decide)]
  decide +kernel
private theorem rows488 : sumChunk row 488 8 = 8234559803 :=
  join 488 4 4 492 8 4141054965 4093504838 8234559803 rfl rfl rfl rows488First rows488Last
set_option profiler true in
private theorem rows496 : sumChunk row 496 3 = 3036818172 := by
  rw [← fastChunk_eq 496 3 (by decide)]
  decide +kernel

private theorem sum_checked : sumChunk row 0 499 = 396610034658 := by
  have tail496 : sumChunk row 496 3 = 3036818172 :=
    rows496
  have tail488 : sumChunk row 488 11 = 11271377975 :=
    join 488 8 3 496 11 8234559803 3036818172 11271377975 (by decide) (by decide) (by decide) rows488 tail496
  have tail480 : sumChunk row 480 19 = 19683227456 :=
    join 480 8 11 488 19 8411849481 11271377975 19683227456 (by decide) (by decide) (by decide) rows480 tail488
  have tail472 : sumChunk row 472 27 = 28242340284 :=
    join 472 8 19 480 27 8559112828 19683227456 28242340284 (by decide) (by decide) (by decide) rows472 tail480
  have tail464 : sumChunk row 464 35 = 36914328735 :=
    join 464 8 27 472 35 8671988451 28242340284 36914328735 (by decide) (by decide) (by decide) rows464 tail472
  have tail456 : sumChunk row 456 43 = 45689322712 :=
    join 456 8 35 464 43 8774993977 36914328735 45689322712 (by decide) (by decide) (by decide) rows456 tail464
  have tail448 : sumChunk row 448 51 = 54542871439 :=
    join 448 8 43 456 51 8853548727 45689322712 54542871439 (by decide) (by decide) (by decide) rows448 tail456
  have tail440 : sumChunk row 440 59 = 63436522847 :=
    join 440 8 51 448 59 8893651408 54542871439 63436522847 (by decide) (by decide) (by decide) rows440 tail448
  have tail432 : sumChunk row 432 67 = 72370787979 :=
    join 432 8 59 440 67 8934265132 63436522847 72370787979 (by decide) (by decide) (by decide) rows432 tail440
  have tail424 : sumChunk row 424 75 = 81327759519 :=
    join 424 8 67 432 75 8956971540 72370787979 81327759519 (by decide) (by decide) (by decide) rows424 tail432
  have tail416 : sumChunk row 416 83 = 90262969557 :=
    join 416 8 75 424 83 8935210038 81327759519 90262969557 (by decide) (by decide) (by decide) rows416 tail424
  have tail408 : sumChunk row 408 91 = 99187391443 :=
    join 408 8 83 416 91 8924421886 90262969557 99187391443 (by decide) (by decide) (by decide) rows408 tail416
  have tail400 : sumChunk row 400 99 = 108086444837 :=
    join 400 8 91 408 99 8899053394 99187391443 108086444837 (by decide) (by decide) (by decide) rows400 tail408
  have tail392 : sumChunk row 392 107 = 116920117239 :=
    join 392 8 99 400 107 8833672402 108086444837 116920117239 (by decide) (by decide) (by decide) rows392 tail400
  have tail384 : sumChunk row 384 115 = 125697787892 :=
    join 384 8 107 392 115 8777670653 116920117239 125697787892 (by decide) (by decide) (by decide) rows384 tail392
  have tail376 : sumChunk row 376 123 = 134411647819 :=
    join 376 8 115 384 123 8713859927 125697787892 134411647819 (by decide) (by decide) (by decide) rows376 tail384
  have tail368 : sumChunk row 368 131 = 143027092059 :=
    join 368 8 123 376 131 8615444240 134411647819 143027092059 (by decide) (by decide) (by decide) rows368 tail376
  have tail360 : sumChunk row 360 139 = 151549895136 :=
    join 360 8 131 368 139 8522803077 143027092059 151549895136 (by decide) (by decide) (by decide) rows360 tail368
  have tail352 : sumChunk row 352 147 = 159979137348 :=
    join 352 8 139 360 147 8429242212 151549895136 159979137348 (by decide) (by decide) (by decide) rows352 tail360
  have tail344 : sumChunk row 344 155 = 168286371049 :=
    join 344 8 147 352 155 8307233701 159979137348 168286371049 (by decide) (by decide) (by decide) rows344 tail352
  have tail336 : sumChunk row 336 163 = 176472319338 :=
    join 336 8 155 344 163 8185948289 168286371049 176472319338 (by decide) (by decide) (by decide) rows336 tail344
  have tail328 : sumChunk row 328 171 = 184542654621 :=
    join 328 8 163 336 171 8070335283 176472319338 184542654621 (by decide) (by decide) (by decide) rows328 tail336
  have tail320 : sumChunk row 320 179 = 192475225630 :=
    join 320 8 171 328 179 7932571009 184542654621 192475225630 (by decide) (by decide) (by decide) rows320 tail328
  have tail312 : sumChunk row 312 187 = 200265068423 :=
    join 312 8 179 320 187 7789842793 192475225630 200265068423 (by decide) (by decide) (by decide) rows312 tail320
  have tail304 : sumChunk row 304 195 = 207923857618 :=
    join 304 8 187 312 195 7658789195 200265068423 207923857618 (by decide) (by decide) (by decide) rows304 tail312
  have tail296 : sumChunk row 296 203 = 215435972339 :=
    join 296 8 195 304 203 7512114721 207923857618 215435972339 (by decide) (by decide) (by decide) rows296 tail304
  have tail288 : sumChunk row 288 211 = 222790336548 :=
    join 288 8 203 296 211 7354364209 215435972339 222790336548 (by decide) (by decide) (by decide) rows288 tail296
  have tail280 : sumChunk row 280 219 = 230004143348 :=
    join 280 8 211 288 219 7213806800 222790336548 230004143348 (by decide) (by decide) (by decide) rows280 tail288
  have tail272 : sumChunk row 272 227 = 237067593580 :=
    join 272 8 219 280 227 7063450232 230004143348 237067593580 (by decide) (by decide) (by decide) rows272 tail280
  have tail264 : sumChunk row 264 235 = 243964234579 :=
    join 264 8 227 272 235 6896640999 237067593580 243964234579 (by decide) (by decide) (by decide) rows264 tail272
  have tail256 : sumChunk row 256 243 = 250715744401 :=
    join 256 8 235 264 243 6751509822 243964234579 250715744401 (by decide) (by decide) (by decide) rows256 tail264
  have tail248 : sumChunk row 248 251 = 257317785917 :=
    join 248 8 243 256 251 6602041516 250715744401 257317785917 (by decide) (by decide) (by decide) rows248 tail256
  have tail240 : sumChunk row 240 259 = 263749326342 :=
    join 240 8 251 248 259 6431540425 257317785917 263749326342 (by decide) (by decide) (by decide) rows240 tail248
  have tail232 : sumChunk row 232 267 = 270035434950 :=
    join 232 8 259 240 267 6286108608 263749326342 270035434950 (by decide) (by decide) (by decide) rows232 tail240
  have tail224 : sumChunk row 224 275 = 276176557367 :=
    join 224 8 267 232 275 6141122417 270035434950 276176557367 (by decide) (by decide) (by decide) rows224 tail232
  have tail216 : sumChunk row 216 283 = 282148046485 :=
    join 216 8 275 224 283 5971489118 276176557367 282148046485 (by decide) (by decide) (by decide) rows216 tail224
  have tail208 : sumChunk row 208 291 = 287977355275 :=
    join 208 8 283 216 291 5829308790 282148046485 287977355275 (by decide) (by decide) (by decide) rows208 tail216
  have tail200 : sumChunk row 200 299 = 293665949929 :=
    join 200 8 291 208 299 5688594654 287977355275 293665949929 (by decide) (by decide) (by decide) rows200 tail208
  have tail192 : sumChunk row 192 307 = 299195703056 :=
    join 192 8 299 200 307 5529753127 293665949929 299195703056 (by decide) (by decide) (by decide) rows192 tail200
  have tail184 : sumChunk row 184 315 = 304586446433 :=
    join 184 8 307 192 315 5390743377 299195703056 304586446433 (by decide) (by decide) (by decide) rows184 tail192
  have tail176 : sumChunk row 176 323 = 309843282529 :=
    join 176 8 315 184 323 5256836096 304586446433 309843282529 (by decide) (by decide) (by decide) rows176 tail184
  have tail168 : sumChunk row 168 331 = 314953808255 :=
    join 168 8 323 176 331 5110525726 309843282529 314953808255 (by decide) (by decide) (by decide) rows168 tail176
  have tail160 : sumChunk row 160 339 = 319931302004 :=
    join 160 8 331 168 339 4977493749 314953808255 319931302004 (by decide) (by decide) (by decide) rows160 tail168
  have tail152 : sumChunk row 152 347 = 324783564995 :=
    join 152 8 339 160 347 4852262991 319931302004 324783564995 (by decide) (by decide) (by decide) rows152 tail160
  have tail144 : sumChunk row 144 355 = 329503012866 :=
    join 144 8 347 152 355 4719447871 324783564995 329503012866 (by decide) (by decide) (by decide) rows144 tail152
  have tail136 : sumChunk row 136 363 = 334097548355 :=
    join 136 8 355 144 363 4594535489 329503012866 334097548355 (by decide) (by decide) (by decide) rows136 tail144
  have tail128 : sumChunk row 128 371 = 338576622889 :=
    join 128 8 363 136 371 4479074534 334097548355 338576622889 (by decide) (by decide) (by decide) rows128 tail136
  have tail120 : sumChunk row 120 379 = 342936465887 :=
    join 120 8 371 128 379 4359842998 338576622889 342936465887 (by decide) (by decide) (by decide) rows120 tail128
  have tail112 : sumChunk row 112 387 = 347180833509 :=
    join 112 8 379 120 387 4244367622 342936465887 347180833509 (by decide) (by decide) (by decide) rows112 tail120
  have tail104 : sumChunk row 104 395 = 351319845248 :=
    join 104 8 387 112 395 4139011739 347180833509 351319845248 (by decide) (by decide) (by decide) rows104 tail112
  have tail96 : sumChunk row 96 403 = 355352520295 :=
    join 96 8 395 104 403 4032675047 351319845248 355352520295 (by decide) (by decide) (by decide) rows96 tail104
  have tail88 : sumChunk row 88 411 = 359279758769 :=
    join 88 8 403 96 411 3927238474 355352520295 359279758769 (by decide) (by decide) (by decide) rows88 tail96
  have tail80 : sumChunk row 80 419 = 363111350823 :=
    join 80 8 411 88 419 3831592054 359279758769 363111350823 (by decide) (by decide) (by decide) rows80 tail88
  have tail72 : sumChunk row 72 427 = 366848080966 :=
    join 72 8 419 80 427 3736730143 363111350823 366848080966 (by decide) (by decide) (by decide) rows72 tail80
  have tail64 : sumChunk row 64 435 = 370489086014 :=
    join 64 8 427 72 435 3641005048 366848080966 370489086014 (by decide) (by decide) (by decide) rows64 tail72
  have tail56 : sumChunk row 56 443 = 374042987230 :=
    join 56 8 435 64 443 3553901216 370489086014 374042987230 (by decide) (by decide) (by decide) rows56 tail64
  have tail48 : sumChunk row 48 451 = 377511338149 :=
    join 48 8 443 56 451 3468350919 374042987230 377511338149 (by decide) (by decide) (by decide) rows48 tail56
  have tail40 : sumChunk row 40 459 = 380892546829 :=
    join 40 8 451 48 459 3381208680 377511338149 380892546829 (by decide) (by decide) (by decide) rows40 tail48
  have tail32 : sumChunk row 32 467 = 384193264076 :=
    join 32 8 459 40 467 3300717247 380892546829 384193264076 (by decide) (by decide) (by decide) rows32 tail40
  have tail24 : sumChunk row 24 475 = 387414971018 :=
    join 24 8 467 32 475 3221706942 384193264076 387414971018 (by decide) (by decide) (by decide) rows24 tail32
  have tail16 : sumChunk row 16 483 = 390555972335 :=
    join 16 8 475 24 483 3141001317 387414971018 390555972335 (by decide) (by decide) (by decide) rows16 tail24
  have tail8 : sumChunk row 8 491 = 393620694045 :=
    join 8 8 483 16 491 3064721710 390555972335 393620694045 (by decide) (by decide) (by decide) rows8 tail16
  have tail0 : sumChunk row 0 499 = 396610034658 :=
    join 0 8 491 8 499 2989340613 393620694045 396610034658 (by decide) (by decide) (by decide) rows0 tail8
  exact tail0

end TaperBudget
