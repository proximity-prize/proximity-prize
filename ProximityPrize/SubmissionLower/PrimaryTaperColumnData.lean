import ProximityPrize.SubmissionLower.PrimaryTaperColumns

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace TaperColumns

open K1_13_2 (cumulative)
open TaperMoments
open Finset
open scoped BigOperators

private abbrev Moments := ℤ × ℤ × ℤ
private def combine (a b : Moments) : Moments := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)
open K1_13_2 (denominator)
open TaperMoments (basePrefix)

private theorem upper_den : denominator 1650 = 125576826 := by decide +kernel
private theorem upper_prefix : denPrefix 1650 = 1244339514000 := by decide +kernel

private def fastCount (d : ℕ) : ℤ :=
  if 824 ≤ d then
    125576826 - denominator (1650-d-1) - denominator (1650-d-2) -
      denominator (1650-d-3)
  else cumulative d 1650

private def fastPrefix (d : ℕ) : ℤ :=
  if 824 ≤ d then
    1244339514000 - denPrefix (1650-(d+1)) - denPrefix (1650-(d+2)) -
      denPrefix (1650-(d+3))
  else cumPrefix d 1650

private theorem fastCount_eq (d : ℕ) : fastCount d = cumulative d 1650 := by
  by_cases hd : 824 ≤ d
  · have hz : ¬ (d : ℤ) < 0 := by omega
    have hmin : (1650 : ℤ) ≤ 3*d := by omega
    have h1 : (1650 : ℤ) - 2*d - 3 < 0 := by omega
    have h2 : (1650 : ℤ) - 2*d - 4 < 0 := by omega
    have h3 : (1650 : ℤ) - 2*d - 5 < 0 := by omega
    have h4 : (1650 : ℤ) - 3*d - 6 < 0 := by omega
    simp only [fastCount, if_pos hd, cumulative, hz, not_lt.mpr (by decide : (0 : ℤ) ≤ 1650),
      decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_left hmin]
    have hn (u : ℤ) (hu : u < 0) : denominator u = 0 := by simp [denominator, hu]
    rw [hn _ h1, hn _ h2, hn _ h3, hn _ h4, upper_den]
    simp
  · simp [fastCount, hd]

private theorem fastPrefix_eq (d : ℕ) : fastPrefix d = cumPrefix d 1650 := by
  by_cases hd : 824 ≤ d
  · have hmin : 1650 ≤ 3*d+1 := by omega
    have h1 : (1650 : ℤ) - (2*d+3) < 0 := by omega
    have h2 : (1650 : ℤ) - (2*d+4) < 0 := by omega
    have h3 : (1650 : ℤ) - (2*d+5) < 0 := by omega
    have h4 : (1650 : ℤ) - (3*d+6) < 0 := by omega
    have hn (u : ℤ) (hu : u < 0) : denPrefix u = 0 := by simp [denPrefix, hu]
    simp only [fastPrefix, if_pos hd, cumPrefix, min_eq_left hmin, Nat.sub_self,
      Nat.cast_zero, mul_zero, zero_mul, add_zero, basePrefix, Nat.cast_ofNat,
      hn _ h1, hn _ h2, hn _ h3, hn _ h4, upper_prefix, sub_zero]
  · simp [fastPrefix, hd]

private def oneRow (q : ℕ) : Moments :=
  let d := gradeCap q
  let n := fastCount d
  (n, (q : ℤ)*n, fastPrefix d)

private def moments (lo : ℕ) : ℕ → Moments
  | 0 => (0,0,0)
  | n+1 => combine (moments lo n) (oneRow (lo+n))

/-! Fast evaluator for the chunk checks: Nat polynomials behind an `Int.ofNat` match
(kernel ~5x faster than the `Int` formulas), proved equal to `oneRow`. -/
private def twiceDenN (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  2 + r * (r + 1) + q * (11 + r * (7 + r) + q * (21 + 6 * r + 12 * q))

private def denPrefixN (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  r * (20 + 4 * r * r) +
    q * (60 + r * (92 + r * (36 + 4 * r)) +
      q * (276 + r * (216 + 36 * r) + q * (432 + 144 * r + 216 * q)))

private def fden : ℤ → ℤ
  | Int.ofNat n => Int.ofNat (twiceDenN n / 2)
  | Int.negSucc _ => 0

private def fpre : ℤ → ℤ
  | Int.ofNat n => Int.ofNat (denPrefixN n)
  | Int.negSucc _ => 0

private theorem twice_pred (q : ℤ) : 2 * (q * (q - 1) / 2) = q * (q - 1) := by
  have h : (2 : ℤ) ∣ q * (q - 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]

private theorem twice_succ (q : ℤ) : 2 * (q * (q + 1) / 2) = q * (q + 1) := by
  have h : (2 : ℤ) ∣ q * (q + 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q + 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]

private theorem den_nat (n : ℕ) : 2 * K1_13_2.denominator (n : ℤ) = (twiceDenN n : ℤ) := by
  have hn : ¬ (n : ℤ) < 0 := by omega
  have h1 := twice_succ ((n : ℤ) % 6)
  have h2 := twice_pred ((n : ℤ) % 6)
  have h3 := twice_pred ((n : ℤ) / 6)
  simp only [K1_13_2.denominator, hn, ite_false]
  unfold twiceDenN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  linear_combination h1 + ((n : ℤ) / 6) * h2 + (57 + 6 * ((n : ℤ) % 6)) * h3

private theorem fden_eq (u : ℤ) : fden u = K1_13_2.denominator u := by
  rcases u with n | m
  · show ((twiceDenN n / 2 : ℕ) : ℤ) = K1_13_2.denominator (n : ℤ)
    have h := den_nat n
    omega
  · show (0 : ℤ) = K1_13_2.denominator (Int.negSucc m)
    simp [K1_13_2.denominator, Int.negSucc_lt_zero]

private theorem pre_nat (n : ℕ) : TaperMoments.denPrefix (n : ℤ) = (denPrefixN n : ℤ) := by
  have hn : ¬ (n : ℤ) < 0 := by omega
  simp only [TaperMoments.denPrefix, hn, ite_false]
  unfold denPrefixN
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  ring

private theorem fpre_eq (u : ℤ) : fpre u = TaperMoments.denPrefix u := by
  rcases u with n | m
  · show ((denPrefixN n : ℕ) : ℤ) = TaperMoments.denPrefix (n : ℤ)
    exact (pre_nat n).symm
  · show (0 : ℤ) = TaperMoments.denPrefix (Int.negSucc m)
    simp [TaperMoments.denPrefix, Int.negSucc_lt_zero]

private def fcum (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    fden v - fden (v - d - 1) - fden (v - d - 2) -
      fden (v - d - 3) + fden (v - 2 * d - 3) +
      fden (v - 2 * d - 4) + fden (v - 2 * d - 5) -
      fden (v - 3 * d - 6)

private theorem fcum_eq (d u : ℤ) : fcum d u = cumulative d u := by
  unfold fcum cumulative
  rw [show fden = K1_13_2.denominator from funext fden_eq]

private def fbase (d u : ℤ) : ℤ :=
  fpre u - fpre (u-(d+1)) - fpre (u-(d+2)) - fpre (u-(d+3)) +
  fpre (u-(2*d+3)) + fpre (u-(2*d+4)) + fpre (u-(2*d+5)) -
  fpre (u-(3*d+6))

private theorem fbase_eq (d u : ℤ) : fbase d u = basePrefix d u := by
  unfold fbase basePrefix
  rw [show fpre = TaperMoments.denPrefix from funext fpre_eq]

private def fcumPrefix (d n : ℕ) : ℤ :=
  let u := min n (3*d+1)
  fbase d u + 24 * ((n-u : ℕ) : ℤ) * fcum d (3*d)

private theorem fcumPrefix_eq (d n : ℕ) : fcumPrefix d n = cumPrefix d n := by
  unfold fcumPrefix cumPrefix
  rw [show fbase = basePrefix from funext₂ fbase_eq, show fcum = cumulative from funext₂ fcum_eq]

private def ffastCount (d : ℕ) : ℤ :=
  if 824 ≤ d then
    125576826 - fden (1650-d-1) - fden (1650-d-2) -
      fden (1650-d-3)
  else fcum d 1650

private theorem ffastCount_eq (d : ℕ) : ffastCount d = fastCount d := by
  unfold ffastCount fastCount
  simp only [fden_eq, fcum_eq]

private def ffastPrefix (d : ℕ) : ℤ :=
  if 824 ≤ d then
    1244339514000 - fpre (1650-(d+1)) - fpre (1650-(d+2)) -
      fpre (1650-(d+3))
  else fcumPrefix d 1650

private theorem ffastPrefix_eq (d : ℕ) : ffastPrefix d = fastPrefix d := by
  unfold ffastPrefix fastPrefix
  simp only [fpre_eq, fcumPrefix_eq]

private def foneRow (q : ℕ) : Moments :=
  let d := gradeCap q
  let n := ffastCount d
  (n, (q : ℤ)*n, ffastPrefix d)

private theorem foneRow_eq (q : ℕ) : foneRow q = oneRow q := by
  unfold foneRow oneRow
  simp only [ffastCount_eq, ffastPrefix_eq]

private def fmoments (lo : ℕ) : ℕ → Moments
  | 0 => (0,0,0)
  | n+1 => combine (fmoments lo n) (foneRow (lo+n))

private theorem moments_fast (lo n : ℕ) : moments lo n = fmoments lo n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [moments, fmoments, ih, foneRow_eq]

private theorem moments_split (lo a b : ℕ) :
    moments lo (a+b) = combine (moments lo a) (moments (lo+a) b) := by
  induction b with
  | zero => simp [moments, combine]
  | succ b ih => rw [Nat.add_succ, moments, moments, ih, Nat.add_assoc]
                 simp only [combine, Int.add_assoc]

private theorem moments_eq (n : ℕ) :
    moments 0 n =
      (∑ q ∈ range n, cumulative (gradeCap q) 1650,
       ∑ q ∈ range n, (q : ℤ)*cumulative (gradeCap q) 1650,
       ∑ q ∈ range n, cumPrefix (gradeCap q) 1650) := by
  induction n with
  | zero => simp [moments]
  | succ n ih => simp only [moments, ih, sum_range_succ, oneRow, combine, Nat.zero_add, fastCount_eq, fastPrefix_eq]

private theorem plateau_count : cumulative ((1650 : ℕ) : ℤ) 1650 = 125576826 := by decide +kernel

private theorem plateau_prefix : cumPrefix 1650 1650 = 1244339514000 := by decide +kernel

private theorem plateau_row (q : ℕ) (lo : 1650 ≤ q) (hi : q < 3514) :
    oneRow q = (125576826, (q : ℤ) * 125576826, 1244339514000) := by
  have hcap : gradeCap q = 1650 := by
    simp only [gradeCap, TaperBudget.cap, if_pos hi, min_eq_right lo]
  simp only [oneRow, hcap, fastCount_eq, fastPrefix_eq, plateau_count, plateau_prefix]

private theorem plateau_components (lo n : ℕ) (start : 1650 ≤ lo) (finish : lo + n ≤ 3514) :
    (moments lo n).1 = (n : ℤ) * 125576826 ∧
    2 * (moments lo n).2.1 = (2 * (lo : ℤ) + (n : ℤ) - 1) * (n : ℤ) * 125576826 ∧
    (moments lo n).2.2 = (n : ℤ) * 1244339514000 := by
  induction n with
  | zero => norm_num [moments]
  | succ n ih =>
    obtain ⟨hc, hd, hj⟩ := ih (by omega)
    have hr := plateau_row (lo + n) (by omega) (by omega)
    simp only [moments, hr, combine, Nat.cast_succ, Nat.cast_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      ring
    · rw [mul_add, hd]
      ring
    · rw [hj]
      ring

private theorem plateau_value (lo n : ℕ) (s : ℤ) (start : 1650 ≤ lo)
    (finish : lo + n ≤ 3514)
    (mid : 2 * s = (2 * (lo : ℤ) + (n : ℤ) - 1) * (n : ℤ) * 125576826) :
    moments lo n = ((n : ℤ) * 125576826, s, (n : ℤ) * 1244339514000) := by
  obtain ⟨hc, hd, hj⟩ := plateau_components lo n start finish
  have hs : (moments lo n).2.1 = s := by linarith only [hd, mid]
  exact Prod.ext hc (Prod.ext hs hj)

private theorem chunk0 : moments 0 64 = (766480, 38630592, 28961906688) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk64 : moments 64 64 = (10950160, 1151780032, 392162254848) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk128 : moments 128 64 = (46692880, 7734564032, 1570593742848) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk192 : moments 192 64 = (124771856, 28444026048, 3916980559872) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk256 : moments 256 64 = (261964304, 76232176832, 7629428072448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk320 : moments 320 64 = (475047440, 168345994432, 12751422824448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk384 : moments 384 64 = (780798480, 326327424192, 19171832537088) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk448 : moments 448 64 = (1195994640, 576013378752, 26624906108928) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk512 : moments 512 64 = (1737323150, 947484425540, 34690308784824) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk576 : moments 576 64 = (2409438080, 1467615274816, 42809297555328) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk640 : moments 640 64 = (3172139904, 2134302060352, 50424594575232) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk704 : moments 704 64 = (3967085440, 2922016831296, 57144114876288) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk768 : moments 768 64 = (4735554768, 3790003814602, 62768847096768) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk832 : moments 832 64 = (5423001088, 4686152908112, 67290168195456) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk896 : moments 896 64 = (6008952320, 5576166392144, 70835420387712) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk960 : moments 960 64 = (6500007424, 6447136851280, 73555743947136) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1024 : moments 1024 64 = (6904555008, 7289698404688, 75590356212096) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1088 : moments 1088 64 = (7230983680, 8096632655184, 77065589619072) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1152 : moments 1152 64 = (7487682048, 8862868689232, 78094891702656) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1216 : moments 1216 64 = (7683038720, 9585483076944, 78778825095552) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1280 : moments 1280 64 = (7825442304, 10263699872080, 79205067528576) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1344 : moments 1344 64 = (7923281408, 10898890612048, 79448411830656) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1408 : moments 1408 64 = (7984944640, 11494574317904, 79570765928832) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1472 : moments 1472 64 = (8018820608, 12056417494352, 79621152848256) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1536 : moments 1536 64 = (8033297920, 12592234129744, 79635710712192) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1600 : moments 1600 50 = (6278689200, 10199732826645, 62216939575080) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk1650 : moments 1650 1864 = (234075203664, 604265138258616, 2319448854096000) :=
  plateau_value 1650 1864 604265138258616 (by decide) (by decide) (by decide)

private theorem chunk3514 : moments 3514 6 = (753368160, 2649219120421, 7466006383320) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3520 : moments 3520 64 = (8032072282, 28525854344641, 79634768477448) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3584 : moments 3584 64 = (8014274720, 28975464060405, 79615399984032) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3648 : moments 3648 64 = (7973908122, 29339703821282, 79551178982208) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3712 : moments 3712 64 = (7901339158, 29578175247143, 79398146595168) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3776 : moments 3776 64 = (7787486114, 29650119438357, 79098473674512) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3840 : moments 3840 64 = (7622412918, 29509140942244, 78577078832208) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3904 : moments 3904 64 = (7397254232, 29110514169461, 77746943352288) := by
  rw [moments_fast]
  decide +kernel
private theorem chunk3968 : moments 3968 45 = (5029151191, 20065722297522, 53950645283400) := by
  rw [moments_fast]
  decide +kernel

private theorem join (lo n m next full : ℕ) (a b result : Moments)
    (hLen : n+m = full) (hStart : lo+n = next) (hValue : combine a b = result)
    (ha : moments lo n = a) (hb : moments next m = b) :
    moments lo full = result := by
  rw [← hLen, moments_split, ha, hStart, hb]
  exact hValue

private theorem checked : moments 0 4013 = (406807694511, 962164450311967, 4235319990139464) := by
  have tail3968 := chunk3968
  have tail3904 : moments 3904 109 = (12426405423, 49176236466983, 131697588635688) :=
    join 3904 64 45 3968 109 (7397254232, 29110514169461, 77746943352288) (5029151191, 20065722297522, 53950645283400) (12426405423, 49176236466983, 131697588635688) (by decide) (by decide) (by decide) chunk3904 tail3968
  have tail3840 : moments 3840 173 = (20048818341, 78685377409227, 210274667467896) :=
    join 3840 64 109 3904 173 (7622412918, 29509140942244, 78577078832208) (12426405423, 49176236466983, 131697588635688) (20048818341, 78685377409227, 210274667467896) (by decide) (by decide) (by decide) chunk3840 tail3904
  have tail3776 : moments 3776 237 = (27836304455, 108335496847584, 289373141142408) :=
    join 3776 64 173 3840 237 (7787486114, 29650119438357, 79098473674512) (20048818341, 78685377409227, 210274667467896) (27836304455, 108335496847584, 289373141142408) (by decide) (by decide) (by decide) chunk3776 tail3840
  have tail3712 : moments 3712 301 = (35737643613, 137913672094727, 368771287737576) :=
    join 3712 64 237 3776 301 (7901339158, 29578175247143, 79398146595168) (27836304455, 108335496847584, 289373141142408) (35737643613, 137913672094727, 368771287737576) (by decide) (by decide) (by decide) chunk3712 tail3776
  have tail3648 : moments 3648 365 = (43711551735, 167253375916009, 448322466719784) :=
    join 3648 64 301 3712 365 (7973908122, 29339703821282, 79551178982208) (35737643613, 137913672094727, 368771287737576) (43711551735, 167253375916009, 448322466719784) (by decide) (by decide) (by decide) chunk3648 tail3712
  have tail3584 : moments 3584 429 = (51725826455, 196228839976414, 527937866703816) :=
    join 3584 64 365 3648 429 (8014274720, 28975464060405, 79615399984032) (43711551735, 167253375916009, 448322466719784) (51725826455, 196228839976414, 527937866703816) (by decide) (by decide) (by decide) chunk3584 tail3648
  have tail3520 : moments 3520 493 = (59757898737, 224754694321055, 607572635181264) :=
    join 3520 64 429 3584 493 (8032072282, 28525854344641, 79634768477448) (51725826455, 196228839976414, 527937866703816) (59757898737, 224754694321055, 607572635181264) (by decide) (by decide) (by decide) chunk3520 tail3584
  have tail3514 : moments 3514 499 = (60511266897, 227403913441476, 615038641564584) :=
    join 3514 6 493 3520 499 (753368160, 2649219120421, 7466006383320) (59757898737, 224754694321055, 607572635181264) (60511266897, 227403913441476, 615038641564584) (by decide) (by decide) (by decide) chunk3514 tail3520
  have tail1650 : moments 1650 2363 = (294586470561, 831669051700092, 2934487495660584) :=
    join 1650 1864 499 3514 2363 (234075203664, 604265138258616, 2319448854096000) (60511266897, 227403913441476, 615038641564584) (294586470561, 831669051700092, 2934487495660584) (by decide) (by decide) (by decide) chunk1650 tail3514
  have tail1600 : moments 1600 2413 = (300865159761, 841868784526737, 2996704435235664) :=
    join 1600 50 2363 1650 2413 (6278689200, 10199732826645, 62216939575080) (294586470561, 831669051700092, 2934487495660584) (300865159761, 841868784526737, 2996704435235664) (by decide) (by decide) (by decide) chunk1600 tail1650
  have tail1536 : moments 1536 2477 = (308898457681, 854461018656481, 3076340145947856) :=
    join 1536 64 2413 1600 2477 (8033297920, 12592234129744, 79635710712192) (300865159761, 841868784526737, 2996704435235664) (308898457681, 854461018656481, 3076340145947856) (by decide) (by decide) (by decide) chunk1536 tail1600
  have tail1472 : moments 1472 2541 = (316917278289, 866517436150833, 3155961298796112) :=
    join 1472 64 2477 1536 2541 (8018820608, 12056417494352, 79621152848256) (308898457681, 854461018656481, 3076340145947856) (316917278289, 866517436150833, 3155961298796112) (by decide) (by decide) (by decide) chunk1472 tail1536
  have tail1408 : moments 1408 2605 = (324902222929, 878012010468737, 3235532064724944) :=
    join 1408 64 2541 1472 2605 (7984944640, 11494574317904, 79570765928832) (316917278289, 866517436150833, 3155961298796112) (324902222929, 878012010468737, 3235532064724944) (by decide) (by decide) (by decide) chunk1408 tail1472
  have tail1344 : moments 1344 2669 = (332825504337, 888910901080785, 3314980476555600) :=
    join 1344 64 2605 1408 2669 (7923281408, 10898890612048, 79448411830656) (324902222929, 878012010468737, 3235532064724944) (332825504337, 888910901080785, 3314980476555600) (by decide) (by decide) (by decide) chunk1344 tail1408
  have tail1280 : moments 1280 2733 = (340650946641, 899174600952865, 3394185544084176) :=
    join 1280 64 2669 1344 2733 (7825442304, 10263699872080, 79205067528576) (332825504337, 888910901080785, 3314980476555600) (340650946641, 899174600952865, 3394185544084176) (by decide) (by decide) (by decide) chunk1280 tail1344
  have tail1216 : moments 1216 2797 = (348333985361, 908760084029809, 3472964369179728) :=
    join 1216 64 2733 1280 2797 (7683038720, 9585483076944, 78778825095552) (340650946641, 899174600952865, 3394185544084176) (348333985361, 908760084029809, 3472964369179728) (by decide) (by decide) (by decide) chunk1216 tail1280
  have tail1152 : moments 1152 2861 = (355821667409, 917622952719041, 3551059260882384) :=
    join 1152 64 2797 1216 2861 (7487682048, 8862868689232, 78094891702656) (348333985361, 908760084029809, 3472964369179728) (355821667409, 917622952719041, 3551059260882384) (by decide) (by decide) (by decide) chunk1152 tail1216
  have tail1088 : moments 1088 2925 = (363052651089, 925719585374225, 3628124850501456) :=
    join 1088 64 2861 1152 2925 (7230983680, 8096632655184, 77065589619072) (355821667409, 917622952719041, 3551059260882384) (363052651089, 925719585374225, 3628124850501456) (by decide) (by decide) (by decide) chunk1088 tail1152
  have tail1024 : moments 1024 2989 = (369957206097, 933009283778913, 3703715206713552) :=
    join 1024 64 2925 1088 2989 (6904555008, 7289698404688, 75590356212096) (363052651089, 925719585374225, 3628124850501456) (369957206097, 933009283778913, 3703715206713552) (by decide) (by decide) (by decide) chunk1024 tail1088
  have tail960 : moments 960 3053 = (376457213521, 939456420630193, 3777270950660688) :=
    join 960 64 2989 1024 3053 (6500007424, 6447136851280, 73555743947136) (369957206097, 933009283778913, 3703715206713552) (376457213521, 939456420630193, 3777270950660688) (by decide) (by decide) (by decide) chunk960 tail1024
  have tail896 : moments 896 3117 = (382466165841, 945032587022337, 3848106371048400) :=
    join 896 64 3053 960 3117 (6008952320, 5576166392144, 70835420387712) (376457213521, 939456420630193, 3777270950660688) (382466165841, 945032587022337, 3848106371048400) (by decide) (by decide) (by decide) chunk896 tail960
  have tail832 : moments 832 3181 = (387889166929, 949718739930449, 3915396539243856) :=
    join 832 64 3117 896 3181 (5423001088, 4686152908112, 67290168195456) (382466165841, 945032587022337, 3848106371048400) (387889166929, 949718739930449, 3915396539243856) (by decide) (by decide) (by decide) chunk832 tail896
  have tail768 : moments 768 3245 = (392624721697, 953508743745051, 3978165386340624) :=
    join 768 64 3181 832 3245 (4735554768, 3790003814602, 62768847096768) (387889166929, 949718739930449, 3915396539243856) (392624721697, 953508743745051, 3978165386340624) (by decide) (by decide) (by decide) chunk768 tail832
  have tail704 : moments 704 3309 = (396591807137, 956430760576347, 4035309501216912) :=
    join 704 64 3245 768 3309 (3967085440, 2922016831296, 57144114876288) (392624721697, 953508743745051, 3978165386340624) (396591807137, 956430760576347, 4035309501216912) (by decide) (by decide) (by decide) chunk704 tail768
  have tail640 : moments 640 3373 = (399763947041, 958565062636699, 4085734095792144) :=
    join 640 64 3309 704 3373 (3172139904, 2134302060352, 50424594575232) (396591807137, 956430760576347, 4035309501216912) (399763947041, 958565062636699, 4085734095792144) (by decide) (by decide) (by decide) chunk640 tail704
  have tail576 : moments 576 3437 = (402173385121, 960032677911515, 4128543393347472) :=
    join 576 64 3373 640 3437 (2409438080, 1467615274816, 42809297555328) (399763947041, 958565062636699, 4085734095792144) (402173385121, 960032677911515, 4128543393347472) (by decide) (by decide) (by decide) chunk576 tail640
  have tail512 : moments 512 3501 = (403910708271, 960980162337055, 4163233702132296) :=
    join 512 64 3437 576 3501 (1737323150, 947484425540, 34690308784824) (402173385121, 960032677911515, 4128543393347472) (403910708271, 960980162337055, 4163233702132296) (by decide) (by decide) (by decide) chunk512 tail576
  have tail448 : moments 448 3565 = (405106702911, 961556175715807, 4189858608241224) :=
    join 448 64 3501 512 3565 (1195994640, 576013378752, 26624906108928) (403910708271, 960980162337055, 4163233702132296) (405106702911, 961556175715807, 4189858608241224) (by decide) (by decide) (by decide) chunk448 tail512
  have tail384 : moments 384 3629 = (405887501391, 961882503139999, 4209030440778312) :=
    join 384 64 3565 448 3629 (780798480, 326327424192, 19171832537088) (405106702911, 961556175715807, 4189858608241224) (405887501391, 961882503139999, 4209030440778312) (by decide) (by decide) (by decide) chunk384 tail448
  have tail320 : moments 320 3693 = (406362548831, 962050849134431, 4221781863602760) :=
    join 320 64 3629 384 3693 (475047440, 168345994432, 12751422824448) (405887501391, 961882503139999, 4209030440778312) (406362548831, 962050849134431, 4221781863602760) (by decide) (by decide) (by decide) chunk320 tail384
  have tail256 : moments 256 3757 = (406624513135, 962127081311263, 4229411291675208) :=
    join 256 64 3693 320 3757 (261964304, 76232176832, 7629428072448) (406362548831, 962050849134431, 4221781863602760) (406624513135, 962127081311263, 4229411291675208) (by decide) (by decide) (by decide) chunk256 tail320
  have tail192 : moments 192 3821 = (406749284991, 962155525337311, 4233328272235080) :=
    join 192 64 3757 256 3821 (124771856, 28444026048, 3916980559872) (406624513135, 962127081311263, 4229411291675208) (406749284991, 962155525337311, 4233328272235080) (by decide) (by decide) (by decide) chunk192 tail256
  have tail128 : moments 128 3885 = (406795977871, 962163259901343, 4234898865977928) :=
    join 128 64 3821 192 3885 (46692880, 7734564032, 1570593742848) (406749284991, 962155525337311, 4233328272235080) (406795977871, 962163259901343, 4234898865977928) (by decide) (by decide) (by decide) chunk128 tail192
  have tail64 : moments 64 3949 = (406806928031, 962164411681375, 4235291028232776) :=
    join 64 64 3885 128 3949 (10950160, 1151780032, 392162254848) (406795977871, 962163259901343, 4234898865977928) (406806928031, 962164411681375, 4235291028232776) (by decide) (by decide) (by decide) chunk64 tail128
  have tail0 : moments 0 4013 = (406807694511, 962164450311967, 4235319990139464) :=
    join 0 64 3949 64 4013 (766480, 38630592, 28961906688) (406806928031, 962164411681375, 4235291028232776) (406807694511, 962164450311967, 4235319990139464) (by decide) (by decide) (by decide) chunk0 tail64
  exact tail0

theorem sourceCount_eq : sourceCount = 406807694511 := by
  have e := (moments_eq 4013).symm.trans checked
  have h := Prod.mk.inj e
  rw [sourceCount]; exact h.1

theorem sourceDegree_eq : sourceDegree = 962164450311967 := by
  have e := (moments_eq 4013).symm.trans checked
  have h := Prod.mk.inj (Prod.mk.inj e).2
  rw [sourceDegree]; exact h.1

theorem sourceIndex24_eq : sourceIndex24 = 11874264712496136 := by
  have hp := congrArg (fun x : Moments => x.2.2) ((moments_eq 4013).symm.trans checked)
  change (∑ q ∈ range 4013, cumPrefix (gradeCap q) 1650) = 4235319990139464 at hp
  unfold sourceIndex24
  simp only [indexMoment, sum_sub_distrib, ← mul_sum]
  change (24 * 1650) * sourceCount - (∑ q ∈ range 4013, cumPrefix (gradeCap q) 1650) = _
  rw [sourceCount_eq, hp]
  decide

/-- Exact column count when the weighted cutoff is above the entire grade range. -/
def compactCount (A D : ℕ) : ℕ :=
  3000*A*406807694511 + 494761029687339 - D*962164450311967

theorem exact_columns (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A) :
    (columns A D hD).card = compactCount A D := by
  have h := scaled_columns A D hA hD hBudget
  rw [sourceCount_eq, sourceDegree_eq, sourceIndex24_eq] at h
  unfold compactCount
  push_cast at h
  omega

#print axioms exact_columns
end TaperColumns
