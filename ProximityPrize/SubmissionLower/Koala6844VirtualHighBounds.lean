import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators

structure SourceShape where
  ordinaryOrder : ℕ
  virtualOrder : ℕ
  valueCap : ℕ
  seedCap : ℕ
  room : ℕ

def primary : SourceShape := ⟨124, 179, 179, 3800, 0⟩
def roomSource : SourceShape := ⟨1000, 1440, 1451, 32586, 31⟩
def adaptive : SourceShape := ⟨4800, 6912, 6975, 133094, 0⟩

def normalizedDegree (content moving : ℤ) : ℤ := 131071 + content - moving

def cutoff (source : SourceShape) (content : ℤ) : ℤ :=
  source.ordinaryOrder * 180961 + (2 * (source.virtualOrder : ℤ) - source.room) * content

def virtualRankPerDegree (source : SourceShape) : ℤ :=
  let m : ℤ := source.virtualOrder
  let y : ℤ := source.valueCap
  let b : ℤ := source.seedCap
  (b + 1) * ((b + y + 1) * (m * (m + 1) / 2) - (m - 1) * m * (m + 1) / 3)

def twiceGap (source : SourceShape) (content moving : ℤ) : ℤ :=
  let m : ℤ := source.ordinaryOrder
  let y : ℤ := source.valueCap
  let b : ℤ := source.seedCap
  (y + 1) * (b + 1)^2 * (2 * cutoff source content - y * normalizedDegree content moving) -
    262144 * m * (m + 1) * (b + 1)^2 - 4 * content * virtualRankPerDegree source

def Passes (source : SourceShape) (content moving perContent : ℤ) : Prop :=
  source.valueCap * normalizedDegree content moving < cutoff source content ∧
    0 < twiceGap source content moving ∧
    2 * perContent * content ≤ twiceGap source content moving

theorem primary_passes {d a : ℤ} (_hd : 0 ≤ d) (ha : 0 ≤ a)
    (hstart : 6675 ≤ d + a) (hend : d + a ≤ 10000) : Passes primary d a 377230 := by
  norm_num [Passes, primary, cutoff, normalizedDegree, twiceGap, virtualRankPerDegree]
  omega

theorem room_passes {d a : ℤ} (_hd : 0 ≤ d) (ha : 0 ≤ a)
    (hstart : 6675 ≤ d + a) (hend : d + a ≤ 10000) : Passes roomSource d a 539504259 := by
  norm_num [Passes, roomSource, cutoff, normalizedDegree, twiceGap, virtualRankPerDegree]
  omega

def adaptiveGap : ℕ := 18069004619508102

theorem adaptive_passes {d a : ℤ} (_hd : 0 ≤ d) (ha : 0 ≤ a)
    (hstart : 6675 ≤ d + a) (hend : d + a ≤ 10000) : Passes adaptive d a adaptiveGap := by
  norm_num [Passes, adaptive, adaptiveGap, cutoff, normalizedDegree, twiceGap, virtualRankPerDegree]
  omega



structure Rectangle where
  value : ℕ
  first : ℕ
  second : ℕ

def mixedDegree (f g h : Rectangle) : ℕ :=
  f.value * (g.first * h.second + g.second * h.first) +
  g.value * (f.first * h.second + f.second * h.first) +
  h.value * (f.first * g.second + f.second * g.first)

def bandFuel (sourceValue sourceSeed y b c : ℕ) : ℕ :=
  min (sourceValue / y) (sourceSeed / max b c)

def bandRectangle (sourceValue sourceSeed y b c : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (bandFuel sourceValue sourceSeed y b c),
    (sourceValue + 1 - (i + 1) * y) *
      (sourceSeed + 1 - (i + 1) * b) * (sourceSeed + 1 - (i + 1) * c)

private theorem le_max_of_product_le {b c t : ℕ} (h : t * t ≤ b * c) : t ≤ max b c := by
  by_contra! hlt
  have hmul : b * c ≤ max b c * max b c := Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
  have hsquare : max b c * max b c < t * t := Nat.mul_self_lt_mul_self hlt
  omega

private theorem seed_band_comparison {cap k b c t : ℕ}
    (hprod : t * t ≤ b * c) (hb : k * b ≤ cap) (hc : k * c ≤ cap) :
    (cap - k * b) * (cap - k * c) ≤ (cap - k * t) * (cap - k * t) := by
  have hkt : k * t ≤ cap := by
    have h := le_max_of_product_le hprod
    rcases le_total b c with hbc | hcb
    · rw [max_eq_right hbc] at h
      exact (Nat.mul_le_mul_left k h).trans hc
    · rw [max_eq_left hcb] at h
      exact (Nat.mul_le_mul_left k h).trans hb
  have hprodZ : (t : ℤ) * t ≤ b * c := by exact_mod_cast hprod
  have hsum : 0 ≤ (b : ℤ) + c - 2 * t := by
    by_contra! hneg
    have hpos : (0 : ℤ) < (2 * t - ((b : ℤ) + c)) * (2 * t + ((b : ℤ) + c)) := by
      apply mul_pos (by omega)
      omega
    nlinarith only [hpos, hprodZ, sq_nonneg ((b : ℤ) - c)]
  have hcZ : 0 ≤ (cap : ℤ) - (k : ℤ) * c := sub_nonneg.mpr (by exact_mod_cast hc)
  have hkZ : 0 ≤ (k : ℤ) := Int.natCast_nonneg _
  have hp := mul_nonneg (mul_nonneg hkZ hcZ) hsum
  have hs := sq_nonneg ((k : ℤ) * ((c : ℤ) - t))
  zify [hb, hc, hkt]
  nlinarith only [hp, hs]

theorem bandRectangle_le_symmetric {sourceValue sourceSeed y b c t : ℕ}
    (ht : 0 < t) (hprod : t * t ≤ b * c) :
    bandRectangle sourceValue sourceSeed y b c ≤
      bandRectangle sourceValue sourceSeed y t t := by
  classical
  have hmax := le_max_of_product_le hprod
  have hmax_pos := ht.trans_le hmax
  have hfuel : bandFuel sourceValue sourceSeed y b c ≤
      bandFuel sourceValue sourceSeed y t t := by
    unfold bandFuel
    rw [max_self]
    exact min_le_min le_rfl (Nat.div_le_div_left hmax ht)
  unfold bandRectangle
  calc
    _ ≤ ∑ i ∈ Finset.range (bandFuel sourceValue sourceSeed y b c),
        (sourceValue + 1 - (i + 1) * y) *
          (sourceSeed + 1 - (i + 1) * t) * (sourceSeed + 1 - (i + 1) * t) := by
        apply Finset.sum_le_sum
        intro i hi
        have h : i + 1 ≤ sourceSeed / max b c :=
          (Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans (min_le_right _ _)
        have hkmax := (Nat.le_div_iff_mul_le hmax_pos).mp h
        have hb := ((Nat.mul_le_mul_left (i + 1) (le_max_left b c)).trans hkmax).trans
          (Nat.le_succ sourceSeed)
        have hc := ((Nat.mul_le_mul_left (i + 1) (le_max_right b c)).trans hkmax).trans
          (Nat.le_succ sourceSeed)
        simpa only [← mul_assoc] using Nat.mul_le_mul_left
          (sourceValue + 1 - (i + 1) * y) (seed_band_comparison hprod hb hc)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hfuel) (by intros; positivity)

private def bandPolynomial (u v w a b c t : ℤ) : ℤ :=
  12 * t * u * v * w -
  6 * t * (t+1) * (a*v*w + b*u*w + c*u*v) +
  2 * t * (t+1) * (2*t+1) * (a*b*w + a*c*v + b*c*u) -
  3 * t^2 * (t+1)^2 * a*b*c

private theorem bandPolynomial_eq_sum (u v w a b c : ℤ) (t : ℕ) :
    bandPolynomial u v w a b c t =
      12 * ∑ i ∈ Finset.range t,
        (u - ((i : ℤ) + 1)*a) * (v - ((i : ℤ) + 1)*b) * (w - ((i : ℤ) + 1)*c) := by
  induction t with
  | zero => simp [bandPolynomial]
  | succ t ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih, Nat.cast_succ]
    unfold bandPolynomial
    ring

private theorem eq_bandPolynomial {u v a b c : ℕ} (ha : 0 < a) (hbc : 0 < max b c) :
    12 * (bandRectangle u v a b c : ℤ) =
      bandPolynomial (u+1 : ℤ) (v+1 : ℤ) (v+1 : ℤ) a b c (bandFuel u v a b c) := by
  rw [bandPolynomial_eq_sum]
  unfold bandRectangle
  rw [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hmain := (Nat.le_div_iff_mul_le ha).mp (hi.trans (min_le_left _ _))
  have hseed := (Nat.le_div_iff_mul_le hbc).mp (hi.trans (min_le_right _ _))
  have hfirst := (Nat.mul_le_mul_left (i+1) (le_max_left b c)).trans hseed
  have hsecond := (Nat.mul_le_mul_left (i+1) (le_max_right b c)).trans hseed
  simp only [Nat.cast_mul, Nat.cast_sub (hmain.trans (Nat.le_succ _)),
    Nat.cast_sub (hfirst.trans (Nat.le_succ _)), Nat.cast_sub (hsecond.trans (Nat.le_succ _)),
    Nat.cast_succ]

def seedThreshold (y : ℕ) : ℕ :=
  match y with
  | 1 => 298
  | 2 => 293
  | 3 => 288
  | 4 => 282
  | 5 => 277
  | 6 => 271
  | 7 => 265
  | 8 => 258
  | 9 => 251
  | 10 => 244
  | 11 => 235
  | 12 => 226
  | 13 => 216
  | 14 => 204
  | 15 => 190
  | 16 => 175
  | 17 => 158
  | 18 => 140
  | 19 => 119
  | 20 => 98
  | 21 => 74
  | 22 => 49
  | 23 => 22
  | _ => 1

def tailValue (order y : ℕ) : ℕ :=
  1 + (2 * order - 1) * (y - 1)

def tailRectangle (order : ℕ) (f : Rectangle) : Rectangle :=
  ⟨tailValue order f.value, (2 * order - 1) * f.first + 10000,
    (2 * order - 1) * f.second + 10000⟩

def residualConstant (y : ℕ) : ℕ := 2 * y * 10000^2

def residualLinear (y : ℕ) : ℕ :=
  (y * (248793 + 248795) + tailValue 124397 y + tailValue 124398 y) * 10000

def residualProduct (y : ℕ) : ℕ :=
  2 * (y * 248793 * 248795 + tailValue 124397 y * 248795 +
    tailValue 124398 y * 248793)

theorem residual_price_eq (y b c : ℕ) :
    mixedDegree ⟨y,b,c⟩ (tailRectangle 124397 ⟨y,b,c⟩) (tailRectangle 124398 ⟨y,b,c⟩) =
      residualConstant y + residualLinear y * (b + c) + residualProduct y * (b * c) := by
  simp only [mixedDegree, tailRectangle, residualConstant, residualLinear, residualProduct]
  norm_num
  ring

private theorem thresholds {y : ℕ} (hy0 : 1 ≤ y) (hy1 : y ≤ 45) :
    0 < seedThreshold y ∧
    bandPolynomial 6976 133095 133095 y (seedThreshold y) (seedThreshold y)
      (bandFuel 6975 133094 y (seedThreshold y) (seedThreshold y)) <
      12 * (adaptiveGap : ℤ) ∧
    residualConstant y + residualLinear y * 2036 +
        residualProduct y * (seedThreshold y ^ 2 - 1) ≤ 215212585876172700 := by
  interval_cases y <;> decide +kernel

theorem surviving_seed_product_le {y b c : ℕ} (hy0 : 1 ≤ y) (hy1 : y ≤ 45)
    (hsurvives : adaptiveGap ≤ bandRectangle 6975 133094 y b c) :
    b*c ≤ seedThreshold y ^ 2 - 1 := by
  obtain ⟨ht, hband, _⟩ := thresholds hy0 hy1
  have hsmall : bandRectangle 6975 133094 y (seedThreshold y) (seedThreshold y) <
      adaptiveGap := by
    have heq := eq_bandPolynomial (u := 6975) (v := 133094) (a := y)
      (b := seedThreshold y) (c := seedThreshold y)
      (by omega) (by simpa only [max_self] using ht)
    norm_num at heq
    rw [← heq] at hband
    exact_mod_cast (show (bandRectangle 6975 133094 y (seedThreshold y) (seedThreshold y) : ℤ) <
      (adaptiveGap : ℤ) by omega)
  by_contra! hlarge
  have hprod : seedThreshold y * seedThreshold y ≤ b*c := by
    rw [pow_two] at hlarge
    omega
  exact (not_lt_of_ge (hsurvives.trans (bandRectangle_le_symmetric ht hprod))) hsmall



theorem residual_price_le {y b c : ℕ} (hy0 : 1 ≤ y) (hy1 : y ≤ 45)
    (hb : b ≤ 1018) (hc : c ≤ 1018)
    (hsurvives : adaptiveGap ≤ bandRectangle 6975 133094 y b c) :
    mixedDegree ⟨y,b,c⟩ (tailRectangle 124397 ⟨y,b,c⟩) (tailRectangle 124398 ⟨y,b,c⟩) ≤
      215212585876172700 := by
  have hcert := (thresholds hy0 hy1).2.2
  have htprod := surviving_seed_product_le hy0 hy1 hsurvives
  rw [residual_price_eq]
  exact (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (show b+c ≤ 2036 by omega)) _)
    (Nat.mul_le_mul_left _ htprod)).trans hcert

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
