import ProximityPrize.SubmissionLower.FiltrationLift
import ProximityPrize.SubmissionLower.Numeric6Defs
set_option autoImplicit true
section
namespace CJ6_8
open CJ6 (VectorDots belowSucc belowZero block_rank_le rank_of_dots)
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l =>
  CJ6.Fast.vector b (buckets side q l) rfl rfl rfl (id (α := good side q l b) rfl)
end CJ6_8
end
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
def shifted (F : Flag) (p : Powers) : Flag :=
  ⟨F.degree - ((p.value : ℤ) + p.top + 3 * p.cubic),
    F.lower - (3 * (p.top : ℤ) + 2 * p.cubic),
    F.upper - (3 * (p.top : ℤ) + 3 * p.cubic),
    F.cap - ((p.top : ℤ) + p.cubic),
    F.order - (2 * (p.top : ℤ) + 3 * p.cubic)⟩
private theorem shifted_eq (F : Flag) (p : Powers) :
    shifted F p = residualFlag F p.expand :=
  (residualFlag_expand F p).symm
def discounted (s j : ℕ) (p : Powers) : ℕ :=
  let F : Flag := ⟨1650, 1650 - j, 1650, 550, 4650 - s - j⟩
  let full := oldCount F
  let starting := kernelLower F
  (full - max 0 starting).toNat -
    (full - max 0 (max starting (kernelLower (shifted F p)))).toNat
theorem discounted_eq (i : BlockIndex) (p : Powers) (hi : w2.Contains i) :
    discounted i.1.val i.2.val p = savings i p := by
  have hb : 2008 ≤ i.1.val ∧ i.1.val < 3012 ∧
      322 ≤ i.2.val ∧ i.2.val ≤ 1062 ∧
      3000 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 3419 := hi
  have hf : initialFlag i = ⟨1650, 1650 - i.2.val, 1650, 550,
      4650 - i.1.val - i.2.val⟩ := by
    unfold initialFlag offset
    rw [min_eq_right (show (1650 : ℤ) ≤ i.1.val by omega)]
    congr 1 <;> omega
  have ho : ¬ (initialFlag i).order ≤ 0 := by rw [hf]; dsimp; omega
  have hu : min (initialFlag i).upper (2999 - offset i) = (initialFlag i).upper := by
    rw [min_eq_left]
    rw [hf, offset]
    dsimp
    omega
  have hr : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases initialFlag i
    simp [residualFlag]
  unfold savings baseline blockBound
  simp only [ho, ite_false, hu, hr, max_self]
  unfold discounted
  rw [← hf]
  dsimp only
  rw [shifted_eq]
  rw [min_eq_right (sub_le_self _ (le_max_left _ _)),
    min_eq_right (sub_le_self _ (le_max_left _ _))]
def denFast (u : ℕ) : ℕ :=
  if u == 0 then 0 else
    let q := (u - 1) / 6
    let r := (u - 1) % 6
    (q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1)) / 2
def cumFast (d u : ℕ) : ℕ :=
  if u ≤ d+1 then denFast u else
    let u := min u (3*d+1)
    (denFast u + denFast (u-(2*d+3)) + denFast (u-(2*d+4)) + denFast (u-(2*d+5))) -
      (denFast (u-(d+1)) + denFast (u-(d+2)) + denFast (u-(d+3)))
def cutFast (d u r : ℕ) : ℕ :=
  if d < r then 0 else cumFast (d-r) u
def kFast (d l u o r : ℕ) : ℕ :=
  (cumFast d u + cutFast d (o - 3*r) r) - (cumFast d o + cutFast d l r)
def originalK (s j : ℕ) : ℕ :=
  let o := 4650 - (s+j)
  let r := (4649-s)/4+1
  (125576826 + cutFast 1650 (o-3*r) r) -
    (denFast o + cutFast 1650 (1650-j) r)
def certifiedSaving (s j : ℕ) (p : Powers) : ℕ :=
  let a := p.value
  let b := p.top
  let c := p.cubic
  if 1650 < a+b+3*c || 550 < b+c || j+1 < c || 4649 < s+a+4*c then 0 else
  let d := 1650-(a+b+3*c)
  let l := 1650-(j+3*b+2*c)
  let u := 1651-3*(b+c)
  let o := 4650-(s+j+2*b+3*c)
  let r := min d ((4649-(s+a+4*c))/4)+1
  min 30000000 (kFast d l u o r) - originalK s j
private theorem twice_half (n : ℤ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  have h : (2 : ℤ) ∣ n * (n - 1) := by
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ n) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ n - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem denFast_correct (n : ℕ) :
    (denFast n : ℤ) = denominator ((n : ℤ) - 1) := by
  cases n with
  | zero => decide
  | succ n =>
    rw [denFast, ite_eq_right (by simp), Nat.succ_sub_one]
    push_cast
    rw [show (n : ℤ) + 1 - 1 = n by omega, denominator, ite_eq_right (by omega)]
    let q := (n : ℤ) / 6
    let r := (n : ℤ) % 6
    change (q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1)) / 2 =
      1 + r*(r+1)/2 + q*(22+7*r+r*(r-1)/2) +
        (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2)
    have h := twice_half (r+1)
    rw [show (r+1)*(r+1-1) = r*(r+1) by ring] at h
    have heq : q * (q * (12*q+21+6*r) + 11+r*(7+r)) + 2+r*(r+1) =
        2 * (1 + r*(r+1)/2 + q*(22+7*r+r*(r-1)/2) +
          (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2)) := by
      linear_combination -h - q * twice_half r - (57+6*r) * twice_half q
    rw [heq]
    omega
private theorem denFast_sub (n k : ℕ) :
    (denFast (n - k) : ℤ) = denominator ((n : ℤ) - 1 - k) := by
  rw [denFast_correct]
  by_cases h : k ≤ n
  · rw [Int.ofNat_sub h]
    congr 1
    omega
  · have hz : n - k = 0 := by omega
    simp [hz, denominator, show (n : ℤ) - 1 - k < 0 by omega]
private theorem cumulative_nonneg (d : ℕ) (u : ℤ) : 0 ≤ cumulative (d : ℤ) u := by
  by_cases h : u < 0
  · simp [cumulative, h]
  · have hm := cumulative_mono d (show (-1 : ℤ) ≤ u by omega)
    simpa [cumulative] using hm
private theorem cumFast_correct (d u : ℕ) :
    (cumFast d u : ℤ) = cumulative (d : ℤ) ((u : ℤ) - 1) := by
  by_cases h0 : u = 0
  · subst u
    simp [cumFast, denFast, cumulative]
  let n := min u (3*d+1)
  have hv : min ((u : ℤ) - 1) (3 * d) = (n : ℤ) - 1 := by
    simp only [n, min_def]
    split <;> split <;> omega
  have hd0 : ¬ (d : ℤ) < 0 := by omega
  have hu0 : ¬ (u : ℤ) - 1 < 0 := by omega
  rw [cumFast]
  by_cases h : u ≤ d+1
  · rw [ite_eq_left h, denFast_correct]
    have hn : n = u := min_eq_left (by omega)
    have hz (z : ℤ) (hz : z < 0) : denominator z = 0 := by simp [denominator, hz]
    simp (disch := omega) only [cumulative, hd0, hu0, decide_false, Bool.false_or,
      Bool.false_eq_true, ite_false, hv, hn, hz, sub_zero, add_zero]
  · rw [ite_eq_right h]
    let pos := denFast n + denFast (n-(2*d+3)) + denFast (n-(2*d+4)) + denFast (n-(2*d+5))
    let neg := denFast (n-(d+1)) + denFast (n-(d+2)) + denFast (n-(d+3))
    change ((pos - neg : ℕ) : ℤ) = _
    have hn : n ≤ 3*d+1 := min_le_right _ _
    have hlast : denominator ((n : ℤ) - 1 - 3*d - 6) = 0 := by
      simp [denominator, show (n : ℤ) - 1 - 3*d - 6 < 0 by omega]
    have he : (pos : ℤ) - neg = cumulative d ((u : ℤ) - 1) := by
      simp only [pos, neg, Nat.cast_add, denFast_sub, Nat.cast_mul, Nat.cast_ofNat]
      rw [denFast_correct]
      simp only [cumulative, hd0, hu0, decide_false, Bool.false_or, Bool.false_eq_true,
        ite_false, hv, hlast, sub_zero]
      ring_nf
    have hpos : 0 ≤ (pos : ℤ) - neg := he ▸ cumulative_nonneg d _
    rwa [← Int.toNat_sub, Int.toNat_of_nonneg hpos]
private theorem cumFast_clipped (d : ℕ) (u : ℤ) :
    (cumFast d u.toNat : ℤ) = cumulative d (u - 1) := by
  rw [cumFast_correct]
  by_cases h : 0 ≤ u
  · rw [Int.toNat_of_nonneg h]
  · simp [Int.toNat_of_nonpos (by omega : u ≤ 0), cumulative, show u - 1 < 0 by omega]
private theorem cutFast_correct (d r : ℕ) (u : ℤ) :
    (cutFast d u.toNat r : ℤ) = cumulative ((d : ℤ) - r) (u - 1) := by
  unfold cutFast
  by_cases h : d < r
  · simp [h, cumulative, show (d : ℤ) - r < 0 by omega]
  · rw [ite_eq_right h, cumFast_clipped, Int.ofNat_sub (by omega : r ≤ d)]
private def balance (F : Flag) : ℤ := F.order - 1 - F.lower + F.degree
private theorem capped_eq (d u f : ℤ) (hf : 0 ≤ f) (hu : u ≤ 3*f) :
    cappedCount d u f = cumulative d u := by
  simp [cappedCount, not_lt.mpr hf, cumulative, show u - 3*(f+1) < 0 by omega]
private theorem kernel_formula (F : Flag) (hd : 0 ≤ F.degree) (hu : 0 ≤ F.upper)
    (hc : 0 ≤ F.cap) (hcap : F.upper ≤ 3*F.cap) (hl : F.lower - 1 ≤ F.upper)
    (hb : 0 ≤ balance F) :
    let r := min F.degree (balance F / 4) + 1
    kernelLower F =
      cumulative F.degree F.upper + cumulative (F.degree - r) (F.order - 1 - 3*r) -
        (cumulative F.degree (F.order - 1) + cumulative (F.degree - r) (F.lower - 1)) := by
  unfold kernelLower oldCount targetCount
  simp only [not_lt.mpr hd, not_lt.mpr hu, not_lt.mpr hc, decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_right hl]
  have hb' : ¬ F.order - 1 - F.lower + F.degree < 0 := not_lt.mpr hb
  simp only [hb', ite_false]
  rw [capped_eq _ _ _ hc hcap, capped_eq _ _ _ hc (hl.trans hcap)]
  simp only [balance]
  ring
private theorem kFast_correct (F : Flag) (d u r : ℕ) (hd : F.degree = d)
    (hu : F.upper = (u : ℤ) - 1) (hu0 : 0 ≤ F.upper) (hc : 0 ≤ F.cap)
    (hcap : F.upper ≤ 3*F.cap) (hl : F.lower - 1 ≤ F.upper) (hb : 0 ≤ balance F)
    (hr : (r : ℤ) = min F.degree (balance F / 4) + 1) :
    kFast d F.lower.toNat u F.order.toNat r = (kernelLower F).toNat := by
  rw [kernel_formula F (by omega) hu0 hc hcap hl hb, ← hr, hd, hu]
  unfold kFast
  rw [← Int.toNat_sub]
  push_cast
  rw [cumFast_correct, cumFast_clipped, cutFast_correct]
  have ht : F.order.toNat - 3*r = (F.order - 3*(r : ℤ)).toNat := by omega
  rw [ht, cutFast_correct]
  rw [show F.order - 3*(r : ℤ) - 1 = F.order - 1 - 3*r by ring]
private def fullFlag (s j : ℕ) : Flag := ⟨1650, 1650 - j, 1650, 550, 4650 - s - j⟩
private theorem originalK_correct (s j : ℕ) (_hs : 2008 ≤ s) (hsj : s+j ≤ 3419)
    (hdiag : 3000 ≤ s+j) (hj : j ≤ 1062) :
    originalK s j = (kernelLower (fullFlag s j)).toNat := by
  let r := (4649-s)/4+1
  have h := kFast_correct (fullFlag s j) 1650 1651 r rfl rfl (by change 0 ≤ (1650 : ℤ); decide)
    (by change 0 ≤ (550 : ℤ); decide) (by change (1650 : ℤ) ≤ 3*550; decide) (by simp [fullFlag]; omega) (by simp [balance, fullFlag]; omega) (by
      simp only [r, fullFlag, balance, Nat.cast_add, Nat.cast_one, Int.natCast_ediv, Nat.cast_ofNat,
        Int.ofNat_sub (show s ≤ 4649 by omega)]
      have hmin : min (1650 : ℤ) ((4649 - (s : ℤ)) / 4) = (4649 - (s : ℤ)) / 4 :=
        min_eq_right (by omega)
      rw [show (4650 : ℤ) - s - j - 1 - (1650 - j) + 1650 = 4649 - s by ring, hmin])
  rw [← h]
  have hl : (fullFlag s j).lower.toNat = 1650-j := by simp [fullFlag]
  have ho : (fullFlag s j).order.toNat = 4650-(s+j) := by simp [fullFlag]; omega
  have hd : cumFast 1650 (4650-(s+j)) = denFast (4650-(s+j)) := by
    rw [cumFast, ite_eq_left (by omega)]
  simp only [originalK, kFast, hl, ho, hd, r, show cumFast 1650 1651 = 125576826 by decide]
private theorem full_enough (s j : ℕ) (hj : 322 ≤ j) :
    30000000 ≤ oldCount (fullFlag s j) := by
  simp only [oldCount, fullFlag, min_eq_right (show (1650 : ℤ) - j - 1 ≤ 1650 by omega)]
  rw [capped_eq _ _ _ (by decide) (by decide),
    capped_eq _ _ _ (by decide) (by omega)]
  have hm := cumulative_mono 1650 (show (1650 : ℤ) - j - 1 ≤ 1327 by omega)
  change cumulative (1650 : ℤ) (1650 - j - 1) ≤ cumulative (1650 : ℤ) 1327 at hm
  have hn : (30000000 : ℤ) ≤ cumulative 1650 1650 - cumulative 1650 1327 := by decide
  omega
private theorem saving_arithmetic (full k k' : ℤ) (hf : 30000000 ≤ full) :
    min 30000000 k'.toNat - k.toNat ≤
      (full - max 0 k).toNat - (full - max 0 (max k k')).toNat := by
  let m := min 30000000 k'.toNat
  have hm₁ : (m : ℤ) ≤ 30000000 := by exact_mod_cast (min_le_left 30000000 k'.toNat)
  have hm₂ : (m : ℤ) ≤ (k'.toNat : ℤ) := by exact_mod_cast (min_le_right 30000000 k'.toNat)
  have hm₃ : (m : ℤ) ≤ max 0 (max k k') := by
    rw [Int.toNat_eq_max, max_comm k' 0] at hm₂
    exact hm₂.trans (max_le_max_left _ (le_max_right _ _))
  have h₁ : full - (k.toNat : ℤ) ≤ ((full - max 0 k).toNat : ℤ) := by
    rw [Int.toNat_eq_max k, max_comm k 0]
    exact Int.self_le_toNat _
  have h₂ : ((full - max 0 (max k k')).toNat : ℤ) ≤ full - (m : ℤ) := by
    rw [Int.toNat_eq_max]
    exact max_le (sub_le_sub_left hm₃ _) (by omega)
  change m - k.toNat ≤ _
  omega
theorem certifiedSaving_le (i : BlockIndex) (p : Powers) (hi : w2.Contains i) :
    certifiedSaving i.1.val i.2.val p ≤ savings i p := by
  have hdata := hi
  obtain ⟨hs, _, hj, hj', hdiag, hdiag'⟩ := hdata
  change 2008 ≤ i.1.val at hs
  change 322 ≤ i.2.val at hj
  change i.2.val ≤ 1062 at hj'
  change 3000 ≤ i.1.val + i.2.val at hdiag
  change i.1.val + i.2.val ≤ 3419 at hdiag'
  let s := i.1.val
  let j := i.2.val
  let a := p.value
  let b := p.top
  let c := p.cubic
  change 2008 ≤ s at hs
  change 322 ≤ j at hj
  change j ≤ 1062 at hj'
  change 3000 ≤ s+j at hdiag
  change s+j ≤ 3419 at hdiag'
  rw [← discounted_eq i p hi]
  change certifiedSaving s j p ≤ discounted s j p
  unfold certifiedSaving
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i hg
    change ¬ (1650 < a+b+3*c || 550 < b+c || j+1 < c || 4649 < s+a+4*c) = true at hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hg
    obtain ⟨⟨⟨hd, hc⟩, hl⟩, hb⟩ := hg
    let F := shifted (fullFlag s j) p
    let d := 1650-(a+b+3*c)
    let u := 1651-3*(b+c)
    let r := min d ((4649-(s+a+4*c))/4)+1
    have hd' : F.degree = d := by
      change (1650 : ℤ) - (a+b+3*c) = ((1650-(a+b+3*c) : ℕ) : ℤ)
      push_cast [Int.ofNat_sub hd]
      rfl
    have hu' : F.upper = (u : ℤ) - 1 := by
      change (1650 : ℤ) - (3*b+3*c) = ((1651-3*(b+c) : ℕ) : ℤ) - 1
      rw [Int.ofNat_sub (by omega : 3*(b+c) ≤ 1651)]
      push_cast
      ring
    have hb' : balance F = 4649 - ((s : ℤ)+a+4*c) := by
      simp only [balance, F, shifted, fullFlag, a, c]
      ring
    have hr' : (r : ℤ) = min F.degree (balance F / 4) + 1 := by
      rw [hd', hb']
      simp only [r, Nat.cast_add, Nat.cast_one, Nat.cast_min, Int.natCast_ediv, Nat.cast_ofNat,
        Int.ofNat_sub hb, Nat.cast_mul]
    have hk := kFast_correct F d u r hd' hu'
      (by change 0 ≤ (1650 : ℤ) - (3*b+3*c); omega)
      (by change 0 ≤ (550 : ℤ) - (b+c); omega)
      (by change (1650 : ℤ) - (3*b+3*c) ≤ 3*(550-(b+c)); omega)
      (by change (1650 : ℤ) - j - (3*b+2*c) - 1 ≤ 1650 - (3*b+3*c); omega)
      (by rw [hb']; omega) hr'
    have hL : F.lower.toNat = 1650-(j+3*b+2*c) := by
      change ((1650 : ℤ) - j - (3*b+2*c)).toNat = _
      omega
    have hO : F.order.toNat = 4650-(s+j+2*b+3*c) := by
      change ((4650 : ℤ) - s - j - (2*b+3*c)).toNat = _
      omega
    change min 30000000 (kFast d _ u _ r) - originalK s j ≤ _
    rw [originalK_correct _ _ hs hdiag' hdiag hj', ← hL, ← hO, hk]
    exact saving_arithmetic _ _ _ (full_enough s j hj)
end K1_13_2_3_5
end
