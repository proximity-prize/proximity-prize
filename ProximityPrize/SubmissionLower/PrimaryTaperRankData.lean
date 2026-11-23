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

set_option profiler true in
private theorem rows0 : sumChunk row 0 8 = 2989340613 := by
  rw [← fastChunk_eq 0 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows8 : sumChunk row 8 8 = 3064721710 := by
  rw [← fastChunk_eq 8 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows16 : sumChunk row 16 8 = 3141001317 := by
  rw [← fastChunk_eq 16 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows24 : sumChunk row 24 8 = 3221706942 := by
  rw [← fastChunk_eq 24 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows32 : sumChunk row 32 8 = 3300717247 := by
  rw [← fastChunk_eq 32 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows40 : sumChunk row 40 8 = 3381208680 := by
  rw [← fastChunk_eq 40 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows48 : sumChunk row 48 8 = 3468350919 := by
  rw [← fastChunk_eq 48 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows56 : sumChunk row 56 8 = 3553901216 := by
  rw [← fastChunk_eq 56 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows64 : sumChunk row 64 8 = 3641005048 := by
  rw [← fastChunk_eq 64 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows72 : sumChunk row 72 8 = 3736730143 := by
  rw [← fastChunk_eq 72 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows80 : sumChunk row 80 8 = 3831592054 := by
  rw [← fastChunk_eq 80 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows88 : sumChunk row 88 8 = 3927238474 := by
  rw [← fastChunk_eq 88 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows96 : sumChunk row 96 8 = 4032675047 := by
  rw [← fastChunk_eq 96 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows104 : sumChunk row 104 8 = 4139011739 := by
  rw [← fastChunk_eq 104 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows112 : sumChunk row 112 8 = 4244367622 := by
  rw [← fastChunk_eq 112 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows120 : sumChunk row 120 8 = 4359842998 := by
  rw [← fastChunk_eq 120 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows128 : sumChunk row 128 8 = 4479074534 := by
  rw [← fastChunk_eq 128 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows136 : sumChunk row 136 8 = 4594535489 := by
  rw [← fastChunk_eq 136 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows144 : sumChunk row 144 8 = 4719447871 := by
  rw [← fastChunk_eq 144 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows152 : sumChunk row 152 8 = 4852262991 := by
  rw [← fastChunk_eq 152 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows160 : sumChunk row 160 8 = 4977493749 := by
  rw [← fastChunk_eq 160 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows168 : sumChunk row 168 8 = 5110525726 := by
  rw [← fastChunk_eq 168 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows176 : sumChunk row 176 8 = 5256836096 := by
  rw [← fastChunk_eq 176 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows184 : sumChunk row 184 8 = 5390743377 := by
  rw [← fastChunk_eq 184 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows192 : sumChunk row 192 8 = 5529753127 := by
  rw [← fastChunk_eq 192 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows200 : sumChunk row 200 8 = 5688594654 := by
  rw [← fastChunk_eq 200 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows208 : sumChunk row 208 8 = 5829308790 := by
  rw [← fastChunk_eq 208 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows216 : sumChunk row 216 8 = 5971489118 := by
  rw [← fastChunk_eq 216 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows224 : sumChunk row 224 8 = 6141122417 := by
  rw [← fastChunk_eq 224 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows232 : sumChunk row 232 8 = 6286108608 := by
  rw [← fastChunk_eq 232 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows240 : sumChunk row 240 8 = 6431540425 := by
  rw [← fastChunk_eq 240 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows248 : sumChunk row 248 8 = 6602041516 := by
  rw [← fastChunk_eq 248 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows256 : sumChunk row 256 8 = 6751509822 := by
  rw [← fastChunk_eq 256 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows264 : sumChunk row 264 8 = 6896640999 := by
  rw [← fastChunk_eq 264 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows272 : sumChunk row 272 8 = 7063450232 := by
  rw [← fastChunk_eq 272 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows280 : sumChunk row 280 8 = 7213806800 := by
  rw [← fastChunk_eq 280 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows288 : sumChunk row 288 8 = 7354364209 := by
  rw [← fastChunk_eq 288 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows296 : sumChunk row 296 8 = 7512114721 := by
  rw [← fastChunk_eq 296 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows304 : sumChunk row 304 8 = 7658789195 := by
  rw [← fastChunk_eq 304 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows312 : sumChunk row 312 8 = 7789842793 := by
  rw [← fastChunk_eq 312 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows320 : sumChunk row 320 8 = 7932571009 := by
  rw [← fastChunk_eq 320 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows328 : sumChunk row 328 8 = 8070335283 := by
  rw [← fastChunk_eq 328 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows336 : sumChunk row 336 8 = 8185948289 := by
  rw [← fastChunk_eq 336 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows344 : sumChunk row 344 8 = 8307233701 := by
  rw [← fastChunk_eq 344 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows352 : sumChunk row 352 8 = 8429242212 := by
  rw [← fastChunk_eq 352 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows360 : sumChunk row 360 8 = 8522803077 := by
  rw [← fastChunk_eq 360 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows368 : sumChunk row 368 8 = 8615444240 := by
  rw [← fastChunk_eq 368 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows376 : sumChunk row 376 8 = 8713859927 := by
  rw [← fastChunk_eq 376 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows384 : sumChunk row 384 8 = 8777670653 := by
  rw [← fastChunk_eq 384 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows392 : sumChunk row 392 8 = 8833672402 := by
  rw [← fastChunk_eq 392 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows400 : sumChunk row 400 8 = 8899053394 := by
  rw [← fastChunk_eq 400 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows408 : sumChunk row 408 8 = 8924421886 := by
  rw [← fastChunk_eq 408 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows416 : sumChunk row 416 8 = 8935210038 := by
  rw [← fastChunk_eq 416 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows424 : sumChunk row 424 8 = 8956971540 := by
  rw [← fastChunk_eq 424 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows432 : sumChunk row 432 8 = 8934265132 := by
  rw [← fastChunk_eq 432 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows440 : sumChunk row 440 8 = 8893651408 := by
  rw [← fastChunk_eq 440 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows448 : sumChunk row 448 8 = 8853548727 := by
  rw [← fastChunk_eq 448 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows456 : sumChunk row 456 8 = 8774993977 := by
  rw [← fastChunk_eq 456 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows464 : sumChunk row 464 8 = 8671988451 := by
  rw [← fastChunk_eq 464 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows472 : sumChunk row 472 8 = 8559112828 := by
  rw [← fastChunk_eq 472 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows480 : sumChunk row 480 8 = 8411849481 := by
  rw [← fastChunk_eq 480 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows488 : sumChunk row 488 8 = 8234559803 := by
  rw [← fastChunk_eq 488 8 (by decide)]
  decide +kernel
set_option profiler true in
private theorem rows496 : sumChunk row 496 3 = 3036818172 := by
  rw [← fastChunk_eq 496 3 (by decide)]
  decide +kernel

private theorem join (lo n m next full : ℕ) (a b result : ℕ)
    (hLen : n+m = full) (hStart : lo+n = next) (hValue : Nat.add a b = result)
    (ha : sumChunk row lo n = a) (hb : sumChunk row next m = b) :
    sumChunk row lo full = result := by
  rw [← hLen, sumChunk_add row, ha, hStart, hb]
  exact hValue

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
