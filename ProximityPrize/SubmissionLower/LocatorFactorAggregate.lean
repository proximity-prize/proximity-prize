import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D

/- Flag inequalities only. The first flag always records actual factor
   degrees; padding changes only its two tail supports. -/
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095

set_option maxRecDepth 2048
set_option maxHeartbeats 300000

def middle (p : FlagDegree) : ℕ := p.yz + p.all
def total (p : FlagDegree) : ℕ := p.zOnly + p.yz + p.all
def Below (p q : FlagDegree) : Prop :=
  p.all ≤ q.all ∧ middle p ≤ middle q ∧ total p ≤ total q

def cap (t y s : ℕ) : FlagDegree := ⟨t - y, y - s, s⟩

theorem cap_cumulative (t y s : ℕ) (hsy : s ≤ y) (hyt : y ≤ t) :
    (cap t y s).all = s ∧ middle (cap t y s) = y ∧ total (cap t y s) = t := by
  dsimp [cap, middle, total]
  omega

/- This expansion has no subtraction. It proves monotonicity for cumulative
   flags, not the stronger and generally unavailable coordinatewise order. -/
theorem mixed_expansion (p q r : FlagDegree) :
    flagMixed p q r =
      (q.all * r.all + q.yz * r.all + q.all * r.yz) * total p +
      (q.zOnly * r.all + q.all * r.zOnly) * middle p +
      (q.yz * r.yz + q.zOnly * r.yz + q.yz * r.zOnly) * p.all := by
  simp only [flagMixed, middle, total]
  ring

theorem mixed_mono_first {p P : FlagDegree} (h : Below p P) (q r : FlagDegree) :
    flagMixed p q r ≤ flagMixed P q r := by
  rw [mixed_expansion p q r, mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)

theorem mixed_mono_second (p : FlagDegree) {q Q : FlagDegree}
    (h : Below q Q) (r : FlagDegree) : flagMixed p q r ≤ flagMixed p Q r := by
  calc
    flagMixed p q r = flagMixed q p r := by unfold flagMixed; ring
    _ ≤ flagMixed Q p r := mixed_mono_first h p r
    _ = flagMixed p Q r := by unfold flagMixed; ring

theorem mixed_mono_third (p q : FlagDegree) {r R : FlagDegree}
    (h : Below r R) : flagMixed p q r ≤ flagMixed p q R := by
  calc
    flagMixed p q r = flagMixed r q p := by unfold flagMixed; ring
    _ ≤ flagMixed R q p := mixed_mono_first h q p
    _ = flagMixed p q R := by unfold flagMixed; ring

theorem mixed_mono_tails (p : FlagDegree) {q Q r R : FlagDegree}
    (hq : Below q Q) (hr : Below r R) : flagMixed p q r ≤ flagMixed p Q R :=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)

theorem sum_mixed_le {I : Type*} [Fintype I]
    (p : I → FlagDegree) (P q r : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, flagMixed (p i) q r) ≤ flagMixed P q r := by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)

def padS (p : FlagDegree) : ℕ := max p.all 2
def padY (p : FlagDegree) : ℕ := max (middle p) (padS p + 1)
def padT (p : FlagDegree) : ℕ := max (total p) (padY p)

def paddedTail (p : FlagDegree) (d : ℕ) : FlagDegree :=
  ⟨2 * (padT p - padY p) * d,
    1 + 2 * (padY p - padS p) * d,
    2 * (padS p - 1) * d⟩

/- Only the tails are padded: the first flag is always p itself. -/
def paddedCost (d e : ℕ) (p : FlagDegree) : ℕ :=
  flagMixed p (paddedTail p d) (paddedTail p e)

theorem paddedTail_cumulative (p : FlagDegree) (d : ℕ) :
    (paddedTail p d).all = 2 * (padS p - 1) * d ∧
    middle (paddedTail p d) = 1 + 2 * (padY p - 1) * d ∧
    total (paddedTail p d) = 1 + 2 * (padT p - 1) * d := by
  have hs : 1 ≤ padS p := by
    have h : 2 ≤ padS p := le_max_right _ _
    omega
  have hy : padS p + 1 ≤ padY p := le_max_right _ _
  have ht : padY p ≤ padT p := le_max_right _ _
  have hyadd : padY p - padS p + (padS p - 1) = padY p - 1 := by omega
  have htadd : padT p - padY p + (padY p - padS p) + (padS p - 1) =
      padT p - 1 := by omega
  refine ⟨rfl, ?_, ?_⟩
  · change (1 + 2 * (padY p - padS p) * d) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padY p - padS p + (padS p - 1)) * d := by ring
      _ = _ := by rw [hyadd]
  · change (2 * (padT p - padY p) * d +
      (1 + 2 * (padY p - padS p) * d)) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padT p - padY p + (padY p - padS p) +
        (padS p - 1)) * d := by ring
      _ = _ := by rw [htadd]

theorem padding_mono {p q : FlagDegree} (h : Below p q) :
    padS p ≤ padS q ∧ padY p ≤ padY q ∧ padT p ≤ padT q := by
  have hs : padS p ≤ padS q := max_le_max h.1 (Nat.le_refl 2)
  have hy : padY p ≤ padY q := max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht : padT p ≤ padT q := max_le_max h.2.2 hy
  exact ⟨hs, hy, ht⟩

theorem paddedTail_mono (d : ℕ) {p q : FlagDegree} (h : Below p q) :
    Below (paddedTail p d) (paddedTail q d) := by
  have hp := paddedTail_cumulative p d
  have hq := paddedTail_cumulative q d
  have hc := padding_mono h
  have hm {a b : ℕ} (hab : a ≤ b) : 2 * (a - 1) * d ≤ 2 * (b - 1) * d :=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  exact ⟨hm hc.1, Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩

theorem paddedCost_mono (d e : ℕ) {p q : FlagDegree} (h : Below p q) :
    paddedCost d e p ≤ paddedCost d e q := by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))

/- General merging lemma, including S=1 and Y=S padding. The only budgets
   are the cumulative sums of the actual, unpadded first flags. -/
theorem merge_padded_costs {I : Type*} [Fintype I]
    (d e : ℕ) (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, paddedCost d e (p i)) ≤ paddedCost d e P := by
  classical
  have hi (i : I) : Below (p i) P := by
    exact ⟨(Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hy,
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ht⟩
  calc
    (∑ i, paddedCost d e (p i)) ≤
        ∑ i, flagMixed (p i) (paddedTail P d) (paddedTail P e) :=
      Finset.sum_le_sum (fun i _ =>
        mixed_mono_tails (p i) (paddedTail_mono d (hi i)) (paddedTail_mono e (hi i)))
    _ ≤ paddedCost d e P := sum_mixed_le p P _ _ hs hy ht

theorem paddedTail_cap (t y s d : ℕ)
    (hs : 2 ≤ s) (hy : s + 1 ≤ y) (ht : y ≤ t) :
    paddedTail (cap t y s) d =
      ⟨2 * (t - y) * d, 1 + 2 * (y - s) * d, 2 * (s - 1) * d⟩ := by
  have hc := cap_cumulative t y s (by omega) ht
  have hps : padS (cap t y s) = s := by
    change max s 2 = s
    exact max_eq_left hs
  have hpy : padY (cap t y s) = y := by
    unfold padY
    rw [hc.2.1, hps, max_eq_left hy]
  have hpt : padT (cap t y s) = t := by
    unfold padT
    rw [hc.2.2, hpy, max_eq_left ht]
  simp only [paddedTail, hps, hpy, hpt]


private abbrev bound6744 : ℕ := 250000000000000000

theorem middle_le_total (p : FlagDegree) : middle p ≤ total p := by
  dsimp [middle, total]
  omega

theorem all_le_total (p : FlagDegree) : p.all ≤ total p := by
  dsimp [total]
  omega

theorem below_cap_of_bounds (p : FlagDegree) (t y s : ℕ)
    (hsy : s ≤ y) (hyt : y ≤ t)
    (hs : p.all ≤ s) (hy : middle p ≤ y) (ht : total p ≤ t) :
    Below p (cap t y s) := by
  have hc := cap_cumulative t y s hsy hyt
  unfold Below
  rw [hc.1, hc.2.1, hc.2.2]
  exact ⟨hs, hy, ht⟩

private theorem below_total_flag (p : FlagDegree) :
    Below p ⟨0, 0, total p⟩ := by
  exact ⟨all_le_total p, by simpa [middle] using middle_le_total p, by simp [total]⟩

private theorem pad_relations (p : FlagDegree) :
    2 ≤ padS p ∧ padS p + 1 ≤ padY p ∧ padY p ≤ padT p := by
  exact ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

private theorem flag_eq {p q : FlagDegree}
    (hz : p.zOnly = q.zOnly) (hy : p.yz = q.yz) (hs : p.all = q.all) : p = q := by
  cases p
  cases q
  simp_all

def exactTail6744 (p : FlagDegree) : FlagDegree :=
  cap (1 + 2 * (padT p - 1) * 131072)
    (1 + 2 * (padY p - 1) * 131072) ((2 * padS p - 1) * 131072)

def hybridTail6744 (p : FlagDegree) : FlagDegree :=
  cap (80202 + (2 * padT p - 3) * 65537)
    (80202 + (2 * padY p - 3) * 65537) ((2 * padS p - 1) * 65537)

def movingFiber6744 (p : FlagDegree) : FlagDegree :=
  cap (padT p + 1) (padY p + 1) (padS p + 1)

def movingCut6744 (p : FlagDegree) : FlagDegree :=
  cap (131074 * padT p - 1) (131074 * padY p - 1) (131074 * padS p - 1)

theorem exactTail6744_coordinates (p : FlagDegree) :
    exactTail6744 p = ⟨2 * (padT p - padY p) * 131072,
      1 + (2 * (padY p - padS p - 1) + 1) * 131072,
      (2 * (padS p - 2) + 3) * 131072⟩ := by
  have hp := pad_relations p
  apply flag_eq
  · change (1 + 2 * (padT p - 1) * 131072) -
        (1 + 2 * (padY p - 1) * 131072) =
          2 * (padT p - padY p) * 131072
    rw [Nat.add_sub_add_left]
    calc
      2 * (padT p - 1) * 131072 - 2 * (padY p - 1) * 131072 =
          ((padT p - 1) - (padY p - 1)) * (2 * 131072) := by
            rw [Nat.mul_sub_right_distrib]
            ring
      _ = (padT p - padY p) * (2 * 131072) := by
        congr 1
        omega
      _ = 2 * (padT p - padY p) * 131072 := by ring
  · change (1 + 2 * (padY p - 1) * 131072) -
        ((2 * padS p - 1) * 131072) =
          1 + (2 * (padY p - padS p - 1) + 1) * 131072
    have hcoef : 2 * (padY p - 1) =
        (2 * (padY p - padS p - 1) + 1) + (2 * padS p - 1) := by
      omega
    rw [hcoef]
    have hdist : ((2 * (padY p - padS p - 1) + 1) +
        (2 * padS p - 1)) * 131072 =
        (2 * (padY p - padS p - 1) + 1) * 131072 +
          (2 * padS p - 1) * 131072 := by ring
    rw [hdist]
    omega
  · change (2 * padS p - 1) * 131072 =
        (2 * (padS p - 2) + 3) * 131072
    congr 1
    omega

theorem hybridTail6744_coordinates (p : FlagDegree) :
    hybridTail6744 p = ⟨(padT p - padY p) * 131074,
      80202 + 2 * (padY p - padS p - 1) * 65537,
      (2 * (padS p - 2) + 3) * 65537⟩ := by
  have hp := pad_relations p
  apply flag_eq
  · change (80202 + (2 * padT p - 3) * 65537) -
        (80202 + (2 * padY p - 3) * 65537) =
          (padT p - padY p) * 131074
    rw [Nat.add_sub_add_left]
    have hcoef : 2 * padT p - 3 =
        2 * (padT p - padY p) + (2 * padY p - 3) := by
      omega
    rw [hcoef]
    have hdist : (2 * (padT p - padY p) + (2 * padY p - 3)) * 65537 =
        2 * (padT p - padY p) * 65537 + (2 * padY p - 3) * 65537 := by ring
    rw [hdist, Nat.add_sub_cancel]
    ring
  · change (80202 + (2 * padY p - 3) * 65537) -
        ((2 * padS p - 1) * 65537) =
          80202 + 2 * (padY p - padS p - 1) * 65537
    have hcoef : 2 * padY p - 3 =
        2 * (padY p - padS p - 1) + (2 * padS p - 1) := by
      omega
    rw [hcoef]
    have hdist : (2 * (padY p - padS p - 1) + (2 * padS p - 1)) * 65537 =
        2 * (padY p - padS p - 1) * 65537 +
          (2 * padS p - 1) * 65537 := by ring
    rw [hdist]
    omega
  · change (2 * padS p - 1) * 65537 =
        (2 * (padS p - 2) + 3) * 65537
    congr 1
    omega

theorem movingFiber6744_coordinates (p : FlagDegree) :
    movingFiber6744 p = ⟨padT p - padY p,
      padY p - padS p, padS p + 1⟩ := by
  have hp := pad_relations p
  apply flag_eq
  · change (padT p + 1) - (padY p + 1) = padT p - padY p
    omega
  · change (padY p + 1) - (padS p + 1) = padY p - padS p
    omega
  · change padS p + 1 = padS p + 1
    rfl

theorem movingCut6744_coordinates (p : FlagDegree) :
    movingCut6744 p = ⟨131074 * (padT p - padY p),
      131074 * (padY p - padS p), 131074 * padS p - 1⟩ := by
  have hp := pad_relations p
  apply flag_eq
  · change (131074 * padT p - 1) - (131074 * padY p - 1) =
        131074 * (padT p - padY p)
    omega
  · change (131074 * padY p - 1) - (131074 * padS p - 1) =
        131074 * (padY p - padS p)
    omega
  · change 131074 * padS p - 1 = 131074 * padS p - 1
    rfl

def hybridCostAt6744 (p q : FlagDegree) : ℕ :=
  flagMixed p (exactTail6744 q) (hybridTail6744 q) +
    131072 * flagMixed p (movingFiber6744 q) (movingCut6744 q)

def hybridCost6744 (p : FlagDegree) : ℕ := hybridCostAt6744 p p

private theorem cap_mono {t y s t' y' s' : ℕ}
    (hsy : s ≤ y) (hyt : y ≤ t) (hSY : s' ≤ y') (hYT : y' ≤ t')
    (hs : s ≤ s') (hy : y ≤ y') (ht : t ≤ t') :
    Below (cap t y s) (cap t' y' s') := by
  have hc := cap_cumulative t y s hsy hyt
  have hC := cap_cumulative t' y' s' hSY hYT
  unfold Below
  rw [hc.1, hc.2.1, hc.2.2, hC.1, hC.2.1, hC.2.2]
  exact ⟨hs, hy, ht⟩

private theorem pad_cap_values (t y s : ℕ) (hs : 2 ≤ s)
    (hy : s + 1 ≤ y) (ht : y ≤ t) :
    padS (cap t y s) = s ∧ padY (cap t y s) = y ∧ padT (cap t y s) = t := by
  have hc := cap_cumulative t y s (by omega) ht
  have hps : padS (cap t y s) = s := by
    change max s 2 = s
    exact max_eq_left hs
  have hpy : padY (cap t y s) = y := by
    unfold padY
    rw [hc.2.1, hps, max_eq_left hy]
  have hpt : padT (cap t y s) = t := by
    unfold padT
    rw [hc.2.2, hpy, max_eq_left ht]
  exact ⟨hps, hpy, hpt⟩

private theorem exactTail6744_mono {p q : FlagDegree} (h : Below p q) :
    Below (exactTail6744 p) (exactTail6744 q) := by
  have hp := pad_relations p
  have hq := pad_relations q
  have hm := padding_mono h
  unfold exactTail6744
  apply cap_mono <;> omega

private theorem hybridTail6744_mono {p q : FlagDegree} (h : Below p q) :
    Below (hybridTail6744 p) (hybridTail6744 q) := by
  have hp := pad_relations p
  have hq := pad_relations q
  have hm := padding_mono h
  unfold hybridTail6744
  apply cap_mono <;> omega

private theorem movingFiber6744_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingFiber6744 p) (movingFiber6744 q) := by
  have hp := pad_relations p
  have hq := pad_relations q
  have hm := padding_mono h
  unfold movingFiber6744
  apply cap_mono <;> omega

private theorem movingCut6744_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingCut6744 p) (movingCut6744 q) := by
  have hp := pad_relations p
  have hq := pad_relations q
  have hm := padding_mono h
  unfold movingCut6744
  apply cap_mono <;> omega

private theorem hybridCostAt6744_mono_tails (p : FlagDegree) {q Q : FlagDegree}
    (h : Below q Q) : hybridCostAt6744 p q ≤ hybridCostAt6744 p Q := by
  unfold hybridCostAt6744
  exact Nat.add_le_add
    (mixed_mono_tails p (exactTail6744_mono h) (hybridTail6744_mono h))
    (Nat.mul_le_mul_left 131072
      (mixed_mono_tails p (movingFiber6744_mono h) (movingCut6744_mono h)))

private theorem hybridCostAt6744_mono_first {p P q : FlagDegree} (h : Below p P) :
    hybridCostAt6744 p q ≤ hybridCostAt6744 P q := by
  unfold hybridCostAt6744
  exact Nat.add_le_add (mixed_mono_first h _ _)
    (Nat.mul_le_mul_left 131072 (mixed_mono_first h _ _))

theorem hybridCost6744_mono {p q : FlagDegree} (h : Below p q) :
    hybridCost6744 p ≤ hybridCost6744 q :=
  (hybridCostAt6744_mono_tails p h).trans (hybridCostAt6744_mono_first h)

theorem sum_hybridCostAt6744_le {I : Type*} [Fintype I]
    (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, hybridCostAt6744 (p i) P) ≤ hybridCost6744 P := by
  classical
  unfold hybridCost6744 hybridCostAt6744
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (sum_mixed_le p P _ _ hs hy ht)
    (Nat.mul_le_mul_left 131072 (sum_mixed_le p P _ _ hs hy ht))

private def diagonalRate6744 (u s : ℕ) : ℕ :=
  hybridCostAt6744 ⟨0, 0, 1⟩ (cap u u s)

private theorem cost_le_diagonal_rate6744 (p : FlagDegree) (u s : ℕ)
    (h : Below p (cap u u s)) :
    hybridCost6744 p ≤ diagonalRate6744 u s * total p := by
  calc
    _ ≤ hybridCostAt6744 p (cap u u s) := hybridCostAt6744_mono_tails p h
    _ ≤ hybridCostAt6744 ⟨0, 0, total p⟩ (cap u u s) :=
      hybridCostAt6744_mono_first (below_total_flag p)
    _ = diagonalRate6744 u s * total p := by
      simp only [hybridCostAt6744, diagonalRate6744, flagMixed]
      ring

private theorem scale_rate6744 {c t k : ℕ} (hc : c ≤ k * t)
    (hk : 1510 * k ≤ bound6744) : 1510 * c ≤ bound6744 * t := by
  calc
    1510 * c ≤ 1510 * (k * t) := Nat.mul_le_mul_left 1510 hc
    _ = (1510 * k) * t := by ring
    _ ≤ bound6744 * t := Nat.mul_le_mul_right t hk

private theorem diagonal_rate6744 (p : FlagDegree) (u s : ℕ)
    (h : Below p (cap u u s)) (hk : 1510 * diagonalRate6744 u s ≤ bound6744) :
    1510 * hybridCost6744 p ≤ bound6744 * total p :=
  scale_rate6744 (cost_le_diagonal_rate6744 p u s h) hk

private theorem affine62 (t : ℕ) (ht : 62 ≤ t) :
    hybridCost6744 (cap t 62 9) + 5243128745360666 = 157377134395427 * t := by
  have hsub : t - 62 + 62 = t := Nat.sub_add_cancel ht
  have hp := pad_cap_values t 62 9 (by decide) (by decide) ht
  simp only [hybridCost6744, hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744]
  rw [hp.1, hp.2.1, hp.2.2]
  simp only [cap, flagMixed]
  ring_nf
  omega

private theorem affine58 (t : ℕ) (ht : 58 ≤ t) :
    hybridCost6744 (cap t 58 10) + 5089003506746360 = 161319074463783 * t := by
  have hsub : t - 58 + 58 = t := Nat.sub_add_cancel ht
  have hp := pad_cap_values t 58 10 (by decide) (by decide) ht
  simp only [hybridCost6744, hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744]
  rw [hp.1, hp.2.1, hp.2.2]
  simp only [cap, flagMixed]
  ring_nf
  omega

private theorem affine54 (t : ℕ) (ht : 54 ≤ t) :
    hybridCost6744 (cap t 54 11) + 4837165365889754 = 162477833257003 * t := by
  have hsub : t - 54 + 54 = t := Nat.sub_add_cancel ht
  have hp := pad_cap_values t 54 11 (by decide) (by decide) ht
  simp only [hybridCost6744, hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744]
  rw [hp.1, hp.2.1, hp.2.2]
  simp only [cap, flagMixed]
  ring_nf
  omega

private theorem affine51 (t : ℕ) (ht : 51 ≤ t) :
    hybridCost6744 (cap t 51 12) + 4687814379917760 = 164529958617135 * t := by
  have hsub : t - 51 + 51 = t := Nat.sub_add_cancel ht
  have hp := pad_cap_values t 51 12 (by decide) (by decide) ht
  simp only [hybridCost6744, hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744]
  rw [hp.1, hp.2.1, hp.2.2]
  simp only [cap, flagMixed]
  ring_nf
  omega

private theorem affine46 (t : ℕ) (ht : 46 ≤ t) :
    hybridCost6744 (cap t 46 13) + 4098487941863594 = 156445807018035 * t := by
  have hsub : t - 46 + 46 = t := Nat.sub_add_cancel ht
  have hp := pad_cap_values t 46 13 (by decide) (by decide) ht
  simp only [hybridCost6744, hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744]
  rw [hp.1, hp.2.1, hp.2.2]
  simp only [cap, flagMixed]
  ring_nf
  omega

private theorem rate_of_affine6744 {t c top alpha deficit : ℕ}
    (ht : t ≤ 1510) (hc : c + deficit = alpha * t)
    (hTop : top + deficit = alpha * 1510) (hbound : top ≤ bound6744) :
    1510 * c ≤ bound6744 * t := by
  have hscaled : 1510 * c + deficit * t ≤ top * t + deficit * t := by
    calc
      _ ≤ 1510 * c + deficit * 1510 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left deficit ht) _
      _ = (c + deficit) * 1510 := by ring
      _ = (alpha * t) * 1510 := by rw [hc]
      _ = (alpha * 1510) * t := by ring
      _ = (top + deficit) * t := by rw [← hTop]
      _ = top * t + deficit * t := by ring
  exact (Nat.le_of_add_le_add_right hscaled).trans
    (Nat.mul_le_mul_right t hbound)

private theorem large_rate62 (t : ℕ) (hlo : 62 ≤ t) (hhi : t ≤ 1510) :
    1510 * hybridCost6744 (cap t 62 9) ≤ bound6744 * t :=
  rate_of_affine6744 hhi (affine62 t hlo) (affine62 1510 (by decide)) (by decide)

private theorem large_rate58 (t : ℕ) (hlo : 58 ≤ t) (hhi : t ≤ 1510) :
    1510 * hybridCost6744 (cap t 58 10) ≤ bound6744 * t :=
  rate_of_affine6744 hhi (affine58 t hlo) (affine58 1510 (by decide)) (by decide)

private theorem large_rate54 (t : ℕ) (hlo : 54 ≤ t) (hhi : t ≤ 1510) :
    1510 * hybridCost6744 (cap t 54 11) ≤ bound6744 * t :=
  rate_of_affine6744 hhi (affine54 t hlo) (affine54 1510 (by decide)) (by decide)

private theorem large_rate51 (t : ℕ) (hlo : 51 ≤ t) (hhi : t ≤ 1510) :
    1510 * hybridCost6744 (cap t 51 12) ≤ bound6744 * t :=
  rate_of_affine6744 hhi (affine51 t hlo) (affine51 1510 (by decide)) (by decide)

private theorem large_rate46 (t : ℕ) (hlo : 46 ≤ t) (hhi : t ≤ 1510) :
    1510 * hybridCost6744 (cap t 46 13) ≤ bound6744 * t :=
  rate_of_affine6744 hhi (affine46 t hlo) (affine46 1510 (by decide)) (by decide)

private theorem middle_formula62 (p : FlagDegree) :
    hybridCostAt6744 p (cap 62 62 9) =
      52028337225745 * total p + 143166297684402 * p.all := by
  norm_num [hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744, padT, padY, padS, cap, total, middle, flagMixed]
  ring

private theorem middle_formula58 (p : FlagDegree) :
    hybridCostAt6744 p (cap 58 58 10) =
      53355052335123 * total p + 117290977671592 * p.all := by
  norm_num [hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744, padT, padY, padS, cap, total, middle, flagMixed]
  ring

private theorem middle_formula54 (p : FlagDegree) :
    hybridCostAt6744 p (cap 54 54 11) =
      53754040352789 * total p + 93992677357982 * p.all := by
  norm_num [hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744, padT, padY, padS, cap, total, middle, flagMixed]
  ring

private theorem middle_formula51 (p : FlagDegree) :
    hybridCostAt6744 p (cap 51 51 12) =
      54445090471959 * total p + 77209491290518 * p.all := by
  norm_num [hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744, padT, padY, padS, cap, total, middle, flagMixed]
  ring

private theorem middle_formula46 (p : FlagDegree) :
    hybridCostAt6744 p (cap 46 46 13) =
      51768835112985 * total p + 55127135828362 * p.all := by
  norm_num [hybridCostAt6744, exactTail6744, hybridTail6744,
    movingFiber6744, movingCut6744, padT, padY, padS, cap, total, middle, flagMixed]
  ring

private theorem middle_cost_le6744 (p : FlagDegree) (u s a b : ℕ)
    (h : Below p (cap u u s))
    (heq : hybridCostAt6744 p (cap u u s) = a * total p + b * p.all) :
    hybridCost6744 p ≤ a * total p + b * s := by
  exact (hybridCostAt6744_mono_tails p h).trans
    (heq.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_left b h.1) _))

private theorem middle_rate62 (t : ℕ) (ht : 12 ≤ t) :
    1510 * (52028337225745 * t + 143166297684402 * 9) ≤ bound6744 * t := by
  unfold bound6744
  omega

private theorem middle_rate58 (t : ℕ) (ht : 11 ≤ t) :
    1510 * (53355052335123 * t + 117290977671592 * 10) ≤ bound6744 * t := by
  unfold bound6744
  omega

private theorem middle_rate54 (t : ℕ) (ht : 11 ≤ t) :
    1510 * (53754040352789 * t + 93992677357982 * 11) ≤ bound6744 * t := by
  unfold bound6744
  omega

private theorem middle_rate51 (t : ℕ) (ht : 12 ≤ t) :
    1510 * (54445090471959 * t + 77209491290518 * 12) ≤ bound6744 * t := by
  unfold bound6744
  omega

private theorem middle_rate46 (t : ℕ) (ht : 13 ≤ t) :
    1510 * (51768835112985 * t + 55127135828362 * 13) ≤ bound6744 * t := by
  unfold bound6744
  omega

theorem rate_bound_6744 (p : FlagDegree)
    (hs : p.all ≤ 13) (hy : middle p ≤ 62) (ht : total p ≤ 1510)
    (h10 : p.all = 10 → middle p ≤ 58)
    (h11 : p.all = 11 → middle p ≤ 54)
    (h12 : p.all = 12 → middle p ≤ 51)
    (h13 : p.all = 13 → middle p ≤ 46) :
    1510 * hybridCost6744 p ≤ bound6744 * total p := by
  have hn := middle_le_total p
  have ha := all_le_total p
  by_cases hsmall : p.all ≤ 9
  · by_cases ht11 : total p ≤ 11
    · exact diagonal_rate6744 p 12 10
        (below_cap_of_bounds p 12 12 10 (by decide) (by decide)
          (by omega) ((hn.trans ht11).trans (by decide))
          (ht11.trans (by decide))) (by decide)
    · by_cases ht61 : total p ≤ 62
      · have hc := middle_cost_le6744 p 62 9 52028337225745 143166297684402
          (below_cap_of_bounds p 62 62 9 (by decide) (by decide) hsmall hy ht61)
          (middle_formula62 p)
        exact (Nat.mul_le_mul_left 1510 hc).trans (middle_rate62 _ (by omega))
      · have hlo : 62 ≤ total p := by omega
        have hb := below_cap_of_bounds p (total p) 62 9 (by decide) hlo
          hsmall hy (le_refl _)
        exact (Nat.mul_le_mul_left 1510 (hybridCost6744_mono hb)).trans
          (large_rate62 _ hlo ht)
  · have hcases : p.all = 10 ∨ p.all = 11 ∨ p.all = 12 ∨ p.all = 13 := by omega
    rcases hcases with hr | hr | hr | hr
    · have hy57 := h10 hr
      by_cases ht10 : total p ≤ 10
      · exact diagonal_rate6744 p 12 10
          (below_cap_of_bounds p 12 12 10 (by decide) (by decide)
            (by omega) ((hn.trans ht10).trans (by decide))
            (ht10.trans (by decide))) (by decide)
      · by_cases ht57 : total p ≤ 58
        · have hc := middle_cost_le6744 p 58 10 53355052335123 117290977671592
            (below_cap_of_bounds p 58 58 10 (by decide) (by decide)
              (by omega) hy57 ht57) (middle_formula58 p)
          exact (Nat.mul_le_mul_left 1510 hc).trans (middle_rate58 _ (by omega))
        · have hlo : 58 ≤ total p := by omega
          have hb := below_cap_of_bounds p (total p) 58 10 (by decide) hlo
            (by omega) hy57 (le_refl _)
          exact (Nat.mul_le_mul_left 1510 (hybridCost6744_mono hb)).trans
            (large_rate58 _ hlo ht)
    · have hy53 := h11 hr
      by_cases ht53 : total p ≤ 54
      · have hc := middle_cost_le6744 p 54 11 53754040352789 93992677357982
          (below_cap_of_bounds p 54 54 11 (by decide) (by decide)
            (by omega) hy53 ht53) (middle_formula54 p)
        exact (Nat.mul_le_mul_left 1510 hc).trans (middle_rate54 _ (by omega))
      · have hlo : 54 ≤ total p := by omega
        have hb := below_cap_of_bounds p (total p) 54 11 (by decide) hlo
          (by omega) hy53 (le_refl _)
        exact (Nat.mul_le_mul_left 1510 (hybridCost6744_mono hb)).trans
          (large_rate54 _ hlo ht)
    · have hy50 := h12 hr
      by_cases ht50 : total p ≤ 51
      · have hc := middle_cost_le6744 p 51 12 54445090471959 77209491290518
          (below_cap_of_bounds p 51 51 12 (by decide) (by decide)
            (by omega) hy50 ht50) (middle_formula51 p)
        exact (Nat.mul_le_mul_left 1510 hc).trans (middle_rate51 _ (by omega))
      · have hlo : 51 ≤ total p := by omega
        have hb := below_cap_of_bounds p (total p) 51 12 (by decide) hlo
          (by omega) hy50 (le_refl _)
        exact (Nat.mul_le_mul_left 1510 (hybridCost6744_mono hb)).trans
          (large_rate51 _ hlo ht)
    · have hy45 := h13 hr
      by_cases ht45 : total p ≤ 46
      · have hc := middle_cost_le6744 p 46 13 51768835112985 55127135828362
          (below_cap_of_bounds p 46 46 13 (by decide) (by decide)
            (by omega) hy45 ht45) (middle_formula46 p)
        exact (Nat.mul_le_mul_left 1510 hc).trans (middle_rate46 _ (by omega))
      · have hlo : 46 ≤ total p := by omega
        have hb := below_cap_of_bounds p (total p) 46 13 (by decide) hlo
          (by omega) hy45 (le_refl _)
        exact (Nat.mul_le_mul_left 1510 (hybridCost6744_mono hb)).trans
          (large_rate46 _ hlo ht)

theorem aggregate_6744 {I : Type*} [Fintype I] (p : I → FlagDegree)
    (hs : ∀ i, (p i).all ≤ 13)
    (hy : ∀ i, middle (p i) ≤ 62)
    (htsum : (∑ i, total (p i)) ≤ 1510)
    (h10 : ∀ i, (p i).all = 10 → middle (p i) ≤ 58)
    (h11 : ∀ i, (p i).all = 11 → middle (p i) ≤ 54)
    (h12 : ∀ i, (p i).all = 12 → middle (p i) ≤ 51)
    (h13 : ∀ i, (p i).all = 13 → middle (p i) ≤ 46) :
    (∑ i, hybridCost6744 (p i)) ≤ bound6744 := by
  classical
  have hti (i : I) : total (p i) ≤ 1510 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans htsum
  have hscaled : 1510 * (∑ i, hybridCost6744 (p i)) ≤ 1510 * bound6744 := by
    calc
      _ = ∑ i, 1510 * hybridCost6744 (p i) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, bound6744 * total (p i) :=
        Finset.sum_le_sum (fun i _ => rate_bound_6744 (p i)
          (hs i) (hy i) (hti i) (h10 i) (h11 i) (h12 i) (h13 i))
      _ = bound6744 * (∑ i, total (p i)) := by rw [Finset.mul_sum]
      _ ≤ bound6744 * 1510 := Nat.mul_le_mul_left _ htsum
      _ = 1510 * bound6744 := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

end ProximityPrize.SubmissionLower.LocatorFactorAggregate
