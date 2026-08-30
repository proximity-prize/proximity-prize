import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D

/- Local, uncompiled research draft. This module proves only inequalities
   between explicit natural-number flag costs. It does not assert a seed
   counting theorem, the regular-colon exclusion, or a ProtocolClaim. -/
namespace ProximityPrize.SubmissionLower.FactorAggregate
open scoped BigOperators
open RCN095

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

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

/- Write a=T-56. These are small polynomial expressions with no truncated
   subtraction. Their differences certify both alternatives for every a. -/
def targetCost (a d e : ℕ) : ℕ :=
  flagMixed ⟨a + 3, 41, 12⟩
    ⟨2 * (a + 3) * d, 1 + 82 * d, 22 * d⟩
    ⟨2 * (a + 3) * e, 1 + 82 * e, 22 * e⟩

def lowSlopeCost (a d e : ℕ) : ℕ :=
  flagMixed ⟨a, 45, 11⟩
    ⟨2 * a * d, 1 + 90 * d, 20 * d⟩
    ⟨2 * a * e, 1 + 90 * e, 20 * e⟩

def splitEnvelope (a d e : ℕ) : ℕ :=
  flagMixed ⟨a, 44, 12⟩
    ⟨2 * a * d, 1 + 88 * d, 20 * d⟩
    ⟨2 * a * e, 1 + 88 * e, 20 * e⟩

theorem targetCost_eq_padded (a d e : ℕ) :
    paddedCost d e (cap (a + 56) 53 12) = targetCost a d e := by
  unfold paddedCost
  rw [paddedTail_cap (a + 56) 53 12 d (by omega) (by omega) (by omega),
    paddedTail_cap (a + 56) 53 12 e (by omega) (by omega) (by omega)]
  have ha : a + 56 - 53 = a + 3 := by omega
  norm_num [targetCost, cap, ha]

theorem lowSlopeCost_eq_padded (a d e : ℕ) :
    paddedCost d e (cap (a + 56) 56 11) = lowSlopeCost a d e := by
  unfold paddedCost
  rw [paddedTail_cap (a + 56) 56 11 d (by omega) (by omega) (by omega),
    paddedTail_cap (a + 56) 56 11 e (by omega) (by omega) (by omega)]
  norm_num [lowSlopeCost, cap]

theorem splitEnvelope_eq_padded (a d e : ℕ) :
    flagMixed (cap (a + 56) 56 12)
      (paddedTail (cap (a + 55) 55 11) d)
      (paddedTail (cap (a + 55) 55 11) e) = splitEnvelope a d e := by
  rw [paddedTail_cap (a + 55) 55 11 d (by omega) (by omega) (by omega),
    paddedTail_cap (a + 55) 55 11 e (by omega) (by omega) (by omega)]
  norm_num [splitEnvelope, cap]

theorem split_gap (a d e : ℕ) :
    targetCost a d e = splitEnvelope a d e +
      ((68 * d * e + 2 * (d + e)) * a + 23192 * d * e + 112 * (d + e)) := by
  unfold targetCost splitEnvelope flagMixed
  ring

theorem low_slope_gap (a d e : ℕ) :
    targetCost a d e = lowSlopeCost a d e +
      ((252 * d * e + 4 * (d + e)) * a + 22540 * d * e + 178 * (d + e) + 1) := by
  unfold targetCost lowSlopeCost flagMixed
  ring

theorem splitEnvelope_le (a d e : ℕ) : splitEnvelope a d e ≤ targetCost a d e := by
  rw [split_gap]
  exact Nat.le_add_right _ _

theorem lowSlopeCost_le (a d e : ℕ) : lowSlopeCost a d e ≤ targetCost a d e := by
  rw [low_slope_gap]
  exact Nat.le_add_right _ _

theorem individual_strict_of_nontrivial {I : Type*} [Fintype I] [Nontrivial I]
    (f : I → ℕ) (B : ℕ) (hpos : ∀ i, 1 ≤ f i) (hsum : (∑ i, f i) ≤ B)
    (i : I) : f i + 1 ≤ B := by
  classical
  obtain ⟨j, hji⟩ := exists_ne i
  have hpair : f i + f j ≤ ∑ k, f k := by
    have h : (∑ k ∈ ({i, j} : Finset I), f k) ≤ ∑ k, f k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simpa [hji, Ne.symm hji] using h
  have hj := hpos j
  omega

/- With at least two positive-slope factors, each factor leaves at least
   one unit in ALL three cumulative degree budgets. This avoids enumeration. -/
theorem multi_factor_envelope {I : Type*} [Fintype I] [Nontrivial I]
    (a d e : ℕ) (p : I → FlagDegree) (hpos : ∀ i, 1 ≤ (p i).all)
    (hs : (∑ i, (p i).all) ≤ 12)
    (hy : (∑ i, middle (p i)) ≤ 56)
    (ht : (∑ i, total (p i)) ≤ a + 56) :
    (∑ i, paddedCost d e (p i)) ≤ splitEnvelope a d e := by
  classical
  have hpy (i : I) : 1 ≤ middle (p i) := by
    have h := hpos i
    dsimp [middle]
    omega
  have hpt (i : I) : 1 ≤ total (p i) := by
    have h := hpos i
    dsimp [total]
    omega
  have small := cap_cumulative (a + 55) 55 11 (by omega) (by omega)
  have large := cap_cumulative (a + 56) 56 12 (by omega) (by omega)
  have hi (i : I) : Below (p i) (cap (a + 55) 55 11) := by
    have hsi := individual_strict_of_nontrivial (fun i => (p i).all) 12 hpos hs i
    have hyi := individual_strict_of_nontrivial (fun i => middle (p i)) 56 hpy hy i
    have hti := individual_strict_of_nontrivial (fun i => total (p i)) (a + 56) hpt ht i
    unfold Below
    rw [small.1, small.2.1, small.2.2]
    omega
  calc
    (∑ i, paddedCost d e (p i)) ≤
        ∑ i, flagMixed (p i)
          (paddedTail (cap (a + 55) 55 11) d)
          (paddedTail (cap (a + 55) 55 11) e) :=
      Finset.sum_le_sum (fun i _ =>
        mixed_mono_tails (p i) (paddedTail_mono d (hi i)) (paddedTail_mono e (hi i)))
    _ ≤ flagMixed (cap (a + 56) 56 12)
        (paddedTail (cap (a + 55) 55 11) d)
        (paddedTail (cap (a + 55) 55 11) e) :=
      sum_mixed_le p _ _ _
        (by simpa only [large.1] using hs)
        (by simpa only [large.2.1] using hy)
        (by simpa only [large.2.2] using ht)
    _ = splitEnvelope a d e := splitEnvelope_eq_padded a d e

theorem individual_cost_le {I : Type*} [Fintype I]
    (a d e : ℕ) (p : I → FlagDegree)
    (hs : (∑ i, (p i).all) ≤ 12)
    (hy : (∑ i, middle (p i)) ≤ 56)
    (ht : (∑ i, total (p i)) ≤ a + 56)
    (hfull : ∀ i, (p i).all = 12 → middle (p i) ≤ 53) (i : I) :
    paddedCost d e (p i) ≤ targetCost a d e := by
  classical
  have hsi : (p i).all ≤ 12 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs
  have hyi : middle (p i) ≤ 56 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hy
  have hti : total (p i) ≤ a + 56 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ht
  by_cases h12 : (p i).all = 12
  · have hc := cap_cumulative (a + 56) 53 12 (by omega) (by omega)
    have hi : Below (p i) (cap (a + 56) 53 12) := by
      unfold Below
      rw [hc.1, hc.2.1, hc.2.2]
      exact ⟨hsi, hfull i h12, hti⟩
    calc
      paddedCost d e (p i) ≤ paddedCost d e (cap (a + 56) 53 12) :=
        paddedCost_mono d e hi
      _ = targetCost a d e := targetCost_eq_padded a d e
  · have hc := cap_cumulative (a + 56) 56 11 (by omega) (by omega)
    have hi : Below (p i) (cap (a + 56) 56 11) := by
      unfold Below
      rw [hc.1, hc.2.1, hc.2.2]
      exact ⟨by omega, hyi, hti⟩
    calc
      paddedCost d e (p i) ≤ paddedCost d e (cap (a + 56) 56 11) :=
        paddedCost_mono d e hi
      _ = lowSlopeCost a d e := lowSlopeCost_eq_padded a d e
      _ ≤ targetCost a d e := lowSlopeCost_le a d e

/- Main arithmetic statement. Index precisely the original base-field
   positive-slope factors with nonempty regular seed sets. The regular-colon
   theorem must separately discharge hfull; no independent seed count is
   hidden in this statement. Geometric components retain their parent's tails. -/
theorem aggregate_bound {I : Type*} [Fintype I]
    (a d e : ℕ) (p : I → FlagDegree) (hpos : ∀ i, 1 ≤ (p i).all)
    (hs : (∑ i, (p i).all) ≤ 12)
    (hy : (∑ i, middle (p i)) ≤ 56)
    (ht : (∑ i, total (p i)) ≤ a + 56)
    (hfull : ∀ i, (p i).all = 12 → middle (p i) ≤ 53) :
    (∑ i, paddedCost d e (p i)) ≤ targetCost a d e := by
  classical
  rcases subsingleton_or_nontrivial I with hI | hI
  · letI : Subsingleton I := hI
    by_cases hne : (Finset.univ : Finset I).Nonempty
    · obtain ⟨i, _⟩ := hne
      have hu : (Finset.univ : Finset I) = {i} := by
        ext j
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim j i
      rw [hu, Finset.sum_singleton]
      exact individual_cost_le a d e p hs hy ht hfull i
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact Nat.zero_le _
  · letI : Nontrivial I := hI
    exact (multi_factor_envelope a d e p hpos hs hy ht).trans (splitEnvelope_le a d e)

theorem aggregate_caps_bound {I : Type*} [Fintype I]
    (T d e : ℕ) (hT : 56 ≤ T) (p : I → FlagDegree) (hpos : ∀ i, 1 ≤ (p i).all)
    (hs : (∑ i, (p i).all) ≤ 12)
    (hy : (∑ i, middle (p i)) ≤ 56)
    (ht : (∑ i, total (p i)) ≤ T)
    (hfull : ∀ i, (p i).all = 12 → middle (p i) ≤ 53) :
    (∑ i, paddedCost d e (p i)) ≤ paddedCost d e (cap T 53 12) := by
  have hT' : T = (T - 56) + 56 := by omega
  have hb := aggregate_bound (T - 56) d e p hpos hs hy (by omega) hfull
  rw [hT', targetCost_eq_padded]
  exact hb

theorem candidate_caps :
    targetCost 1224 131072 131073 = 272657752062485740 ∧
    targetCost 1226 131072 131073 = 273093849213101384 ∧
    splitEnvelope 1224 131072 131073 = 270829387044149996 ∧
    splitEnvelope 1226 131072 131073 = 271263147713682244 := by
  norm_num [targetCost, splitEnvelope, flagMixed]

end ProximityPrize.SubmissionLower.FactorAggregate
