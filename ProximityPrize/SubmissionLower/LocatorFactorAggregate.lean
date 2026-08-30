import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D


namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000

def middle (p:FlagDegree):ℕ:=p.yz+p.all
def total (p:FlagDegree):ℕ:=p.zOnly+p.yz+p.all
def Below (p q:FlagDegree):Prop:=
  p.all≤q.all ∧ middle p≤middle q ∧ total p≤total q

def cap (t y s:ℕ):FlagDegree:=⟨t - y,y - s,s⟩

theorem cap_cumulative (t y s:ℕ) (hsy:s≤y) (hyt:y≤t):
    (cap t y s).all=s ∧ middle (cap t y s)=y ∧ total (cap t y s)=t:=by
  dsimp [cap,middle,total]
  omega


theorem mixed_expansion (p q r:FlagDegree):
    flagMixed p q r=
      (q.all*r.all+q.yz*r.all+q.all*r.yz)*total p+
      (q.zOnly*r.all+q.all*r.zOnly)*middle p+
      (q.yz*r.yz+q.zOnly*r.yz+q.yz*r.zOnly)*p.all:=by
  simp only [flagMixed,middle,total]
  ring

theorem mixed_mono_first {p P:FlagDegree} (h:Below p P) (q r:FlagDegree):
    flagMixed p q r≤flagMixed P q r:=by
  rw [mixed_expansion p q r,mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)

theorem mixed_mono_second (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r≤flagMixed p Q r:=by
  calc
    flagMixed p q r=flagMixed q p r:=by unfold flagMixed; ring
    _≤flagMixed Q p r:=mixed_mono_first h p r
    _=flagMixed p Q r:=by unfold flagMixed; ring

theorem mixed_mono_third (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r≤flagMixed p q R:=by
  calc
    flagMixed p q r=flagMixed r q p:=by unfold flagMixed; ring
    _≤flagMixed R q p:=mixed_mono_first h q p
    _=flagMixed p q R:=by unfold flagMixed; ring

theorem mixed_mono_tails (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r≤flagMixed p Q R:=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)

theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i,(p i).all)≤P.all)
    (hy:(∑ i,middle (p i))≤middle P)
    (ht:(∑ i,total (p i))≤total P):
    (∑ i,flagMixed (p i) q r)≤flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _=>mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)

def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p+1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)

def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree:=
  ⟨2*(padT p - padY p)*d,
    1+2*(padY p - padS p)*d,
    2*(padS p - 1)*d⟩


def paddedCost (d e:ℕ) (p:FlagDegree):ℕ:=
  flagMixed p (paddedTail p d) (paddedTail p e)

theorem paddedTail_cumulative (p:FlagDegree) (d:ℕ):
    (paddedTail p d).all=2*(padS p - 1)*d ∧
    middle (paddedTail p d)=1+2*(padY p - 1)*d ∧
    total (paddedTail p d)=1+2*(padT p - 1)*d:=by
  have hs:1≤padS p:=by
    have h:2≤padS p:=le_max_right _ _
    omega
  have hy:padS p+1≤padY p:=le_max_right _ _
  have ht:padY p≤padT p:=le_max_right _ _
  have hyadd:padY p - padS p+(padS p - 1)=padY p - 1:=by omega
  have htadd:padT p - padY p+(padY p - padS p)+(padS p - 1)=
      padT p - 1:=by omega
  refine ⟨rfl,?_,?_⟩
  · change (1+2*(padY p - padS p)*d)+2*(padS p - 1)*d=_
    calc
      _=1+2*(padY p - padS p+(padS p - 1))*d:=by ring
      _=_:=by rw [hyadd]
  · change (2*(padT p - padY p)*d+
      (1+2*(padY p - padS p)*d))+2*(padS p - 1)*d=_
    calc
      _=1+2*(padT p - padY p+(padY p - padS p)+
        (padS p - 1))*d:=by ring
      _=_:=by rw [htadd]

theorem padding_mono {p q:FlagDegree} (h:Below p q):
    padS p≤padS q ∧ padY p≤padY q ∧ padT p≤padT q:=by
  have hs:padS p≤padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p≤padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p≤padT q:=max_le_max h.2.2 hy
  exact ⟨hs,hy,ht⟩

theorem paddedTail_mono (d:ℕ) {p q:FlagDegree} (h:Below p q):
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=paddedTail_cumulative p d
  have hq:=paddedTail_cumulative q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a≤b):2*(a - 1)*d≤2*(b - 1)*d:=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  exact ⟨hm hc.1,Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩

theorem paddedCost_mono (d e:ℕ) {p q:FlagDegree} (h:Below p q):
    paddedCost d e p≤paddedCost d e q:=by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))


theorem merge_padded_costs {I:Type*} [Fintype I]
    (d e:ℕ) (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i,(p i).all)≤P.all)
    (hy:(∑ i,middle (p i))≤middle P)
    (ht:(∑ i,total (p i))≤total P):
    (∑ i,paddedCost d e (p i))≤paddedCost d e P:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  have hi (i:I):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hs,
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hy,
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans ht⟩
  calc
    (∑ i,paddedCost d e (p i))≤
        ∑ i,flagMixed (p i) (paddedTail P d) (paddedTail P e):=
      Finset.sum_le_sum (fun i _=>
        mixed_mono_tails (p i) (paddedTail_mono d (hi i)) (paddedTail_mono e (hi i)))
    _≤paddedCost d e P:=sum_mixed_le p P _ _ hs hy ht

theorem middle_le_total (p:FlagDegree):middle p≤total p:=by
  dsimp [middle,total]
  omega

theorem below_cap_of_bounds (p:FlagDegree) (t y s:ℕ)
    (hsy:s≤y) (hyt:y≤t)
    (hs:p.all≤s) (hy:middle p≤y) (ht:total p≤t):
    Below p (cap t y s):=by
  have hc:=cap_cumulative t y s hsy hyt
  unfold Below
  rw [hc.1,hc.2.1,hc.2.2]
  exact ⟨hs,hy,ht⟩

private abbrev bound80191 : ℕ := 271263904445294429

private theorem cap_self (p : FlagDegree) :
    cap (total p) (middle p) p.all = p := by
  rcases p with ⟨z, y, s⟩
  simp only [cap, total, middle]
  congr <;> omega

private def remainder (t y s : ℕ) : FlagDegree :=
  cap (1469 - t)
    (min (60 - y) (1469 - t))
    (min (13 - s) (min (60 - y) (1469 - t)))

private def pairCost (t y s : ℕ) : ℕ :=
  paddedCost 131072 131073 (cap t y s) +
    paddedCost 131072 131073 (remainder t y s)

private theorem low_rate_table :
    ∀ (t y s : ℕ), t ≤ 1469 → y ≤ 60 → 1 ≤ s → s ≤ 8 →
      s ≤ y → y ≤ t →
      1469 * paddedCost 131072 131073 (cap t y s) ≤ bound80191 * t := by
  intro t y s ht hy hs hS hsy hyt
  interval_cases s <;> interval_cases y <;>
    norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
      total, middle, flagMixed] at * <;> omega

private theorem cap_below_cap (t y s tt yy ss : ℕ)
    (hsy : s ≤ y) (hyt : y ≤ t) (hSY : ss ≤ yy) (hYT : yy ≤ tt)
    (hs : s ≤ ss) (hy : y ≤ yy) (ht : t ≤ tt) :
    Below (cap t y s) (cap tt yy ss) := by
  have hc := cap_cumulative t y s hsy hyt
  exact below_cap_of_bounds (cap t y s) tt yy ss hSY hYT
    (by simpa only [hc.1] using hs)
    (by simpa only [hc.2.1] using hy)
    (by simpa only [hc.2.2] using ht)

private theorem remainder_below_cap (t y s tt yy ss : ℕ)
    (hSY : ss ≤ yy) (hYT : yy ≤ tt)
    (hs : min (13 - s) (min (60 - y) (1469 - t)) ≤ ss)
    (hy : min (60 - y) (1469 - t) ≤ yy)
    (ht : 1469 - t ≤ tt) : Below (remainder t y s) (cap tt yy ss) := by
  have hc := cap_cumulative (1469 - t)
    (min (60 - y) (1469 - t))
    (min (13 - s) (min (60 - y) (1469 - t)))
    (min_le_right _ _) (min_le_right _ _)
  apply below_cap_of_bounds (remainder t y s) tt yy ss hSY hYT
  · simpa only [remainder, hc.1] using hs
  · simpa only [remainder, hc.2.1] using hy
  · simpa only [remainder, hc.2.2] using ht

private theorem pairCost_le_caps (t y s tt yy ss uu vv rr : ℕ)
    (hleft : Below (cap t y s) (cap tt yy ss))
    (hright : Below (remainder t y s) (cap uu vv rr)) :
    pairCost t y s ≤ paddedCost 131072 131073 (cap tt yy ss) +
      paddedCost 131072 131073 (cap uu vv rr) := by
  exact Nat.add_le_add (paddedCost_mono 131072 131073 hleft)
    (paddedCost_mono 131072 131073 hright)

private theorem pair9_cond (t y : ℕ) (ht : t ≤ 1252)
    (hylo : 60 ≤ y) (hyhi : y ≤ 60) (hyt : y ≤ t) :
    pairCost t y 9 ≤ bound80191 := by
  interval_cases y
  unfold pairCost remainder
  rw [min_eq_left (by omega)]
  norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
    total, middle, flagMixed] at *
  omega

private theorem pair10_cond (t y : ℕ) (ht : t ≤ 1406)
    (hylo : 40 ≤ y) (hyhi : y ≤ 56) (hyt : y ≤ t) :
    pairCost t y 10 ≤ bound80191 := by
  interval_cases y
  all_goals
    unfold pairCost remainder
    rw [min_eq_left (by omega)]
    norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
      total, middle, flagMixed] at *
    omega

private theorem pair11_cond (t y : ℕ) (ht : t ≤ 1407)
    (hylo : 36 ≤ y) (hyhi : y ≤ 52) (hyt : y ≤ t) :
    pairCost t y 11 ≤ bound80191 := by
  interval_cases y
  all_goals
    unfold pairCost remainder
    rw [min_eq_left (by omega)]
    norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
      total, middle, flagMixed] at *
    omega

private theorem pair12_cond (t y : ℕ) (ht : t ≤ 1405)
    (hylo : 32 ≤ y) (hyhi : y ≤ 48) (hyt : y ≤ t) :
    pairCost t y 12 ≤ bound80191 := by
  interval_cases y
  all_goals
    unfold pairCost remainder
    rw [min_eq_left (by omega)]
    norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
      total, middle, flagMixed] at *
    omega

private theorem pair13_cond (t y : ℕ) (ht : t ≤ 1408)
    (hylo : 27 ≤ y) (hyhi : y ≤ 44) (hyt : y ≤ t) :
    pairCost t y 13 ≤ bound80191 := by
  interval_cases y
  all_goals
    unfold pairCost remainder
    rw [min_eq_left (by omega)]
    norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
      total, middle, flagMixed] at *
    omega

private theorem pair9_mid (t y : ℕ) (htlo : 59 ≤ t) (hthi : t ≤ 1418)
    (hylo : 9 ≤ y) (hyhi : y ≤ 59) (hyt : y ≤ t) :
    pairCost t y 9 ≤ bound80191 := by
  interval_cases y
  all_goals
    unfold pairCost remainder
    rw [min_eq_left (by omega)]
    norm_num [paddedCost, paddedTail, padT, padY, padS, cap,
      total, middle, flagMixed] at *
    omega

private theorem pair9_low (t y : ℕ) (ht : t ≤ 1469)
    (hylo : 9 ≤ y) (hyhi : y ≤ 59) (hyt : y ≤ t) :
    pairCost t y 9 ≤ bound80191 := by
  by_cases ht59 : 59 ≤ t
  · by_cases ht1418 : t ≤ 1418
    · exact pair9_mid t y ht59 ht1418 hylo hyhi hyt
    · have hle := pairCost_le_caps t y 9 1469 59 9 50 50 4
        (cap_below_cap t y 9 1469 59 9 (by omega) hyt (by omega)
          (by omega) (by omega) hyhi ht)
        (remainder_below_cap t y 9 50 50 4 (by omega) (by omega)
          (by omega) (by omega) (by omega))
      exact hle.trans (by
        norm_num [bound80191, paddedCost, paddedTail, padT, padY, padS,
          cap, total, middle, flagMixed])
  · have hle := pairCost_le_caps t y 9 59 59 9 1460 51 4
      (cap_below_cap t y 9 59 59 9 (by omega) hyt (by omega)
        (by omega) (by omega) (by omega) (by omega))
      (remainder_below_cap t y 9 1460 51 4 (by omega) (by omega)
        (by omega) (by omega) (by omega))
    exact hle.trans (by
      norm_num [bound80191, paddedCost, paddedTail, padT, padY, padS,
        cap, total, middle, flagMixed])

private theorem pair10_low (t y : ℕ) (ht : t ≤ 1469)
    (hylo : 10 ≤ y) (hyhi : y ≤ 39) (hyt : y ≤ t) :
    pairCost t y 10 ≤ bound80191 := by
  have hle := pairCost_le_caps t y 10 1469 39 10 1459 50 3
    (cap_below_cap t y 10 1469 39 10 (by omega) hyt (by omega)
      (by omega) (by omega) hyhi ht)
    (remainder_below_cap t y 10 1459 50 3 (by omega) (by omega)
      (by omega) (by omega) (by omega))
  exact hle.trans (by
    norm_num [bound80191, paddedCost, paddedTail, padT, padY, padS,
      cap, total, middle, flagMixed])

private theorem pair11_low (t y : ℕ) (ht : t ≤ 1469)
    (hylo : 11 ≤ y) (hyhi : y ≤ 35) (hyt : y ≤ t) :
    pairCost t y 11 ≤ bound80191 := by
  have hle := pairCost_le_caps t y 11 1469 35 11 1458 49 2
    (cap_below_cap t y 11 1469 35 11 (by omega) hyt (by omega)
      (by omega) (by omega) hyhi ht)
    (remainder_below_cap t y 11 1458 49 2 (by omega) (by omega)
      (by omega) (by omega) (by omega))
  exact hle.trans (by
    norm_num [bound80191, paddedCost, paddedTail, padT, padY, padS,
      cap, total, middle, flagMixed])

private theorem pair12_low (t y : ℕ) (ht : t ≤ 1469)
    (hylo : 12 ≤ y) (hyhi : y ≤ 31) (hyt : y ≤ t) :
    pairCost t y 12 ≤ bound80191 := by
  have hle := pairCost_le_caps t y 12 1469 31 12 1457 48 1
    (cap_below_cap t y 12 1469 31 12 (by omega) hyt (by omega)
      (by omega) (by omega) hyhi ht)
    (remainder_below_cap t y 12 1457 48 1 (by omega) (by omega)
      (by omega) (by omega) (by omega))
  exact hle.trans (by
    norm_num [bound80191, paddedCost, paddedTail, padT, padY, padS,
      cap, total, middle, flagMixed])

private theorem pair13_low (t y : ℕ) (ht : t ≤ 1469)
    (hylo : 13 ≤ y) (hyhi : y ≤ 26) (hyt : y ≤ t) :
    pairCost t y 13 ≤ bound80191 := by
  have hle := pairCost_le_caps t y 13 1469 26 13 1456 47 0
    (cap_below_cap t y 13 1469 26 13 (by omega) hyt (by omega)
      (by omega) (by omega) hyhi ht)
    (remainder_below_cap t y 13 1456 47 0 (by omega) (by omega)
      (by omega) (by omega) (by omega))
  exact hle.trans (by
    norm_num [bound80191, paddedCost, paddedTail, padT, padY, padS,
      cap, total, middle, flagMixed])

private theorem high_pair_table (t y s : ℕ)
    (ht : t ≤ 1469) (hy : y ≤ 60) (hS : s ≤ 13)
    (hs : 9 ≤ s) (hsy : s ≤ y) (hyt : y ≤ t)
    (hy10 : s = 10 → y ≤ 56)
    (hy11 : s = 11 → y ≤ 52)
    (hy12 : s = 12 → y ≤ 48)
    (hy13 : s = 13 → y ≤ 44)
    (ht9 : s = 9 → 60 ≤ y → t ≤ 1252)
    (ht10 : s = 10 → 40 ≤ y → t ≤ 1406)
    (ht11 : s = 11 → 36 ≤ y → t ≤ 1407)
    (ht12 : s = 12 → 32 ≤ y → t ≤ 1405)
    (ht13 : s = 13 → 27 ≤ y → t ≤ 1408) :
    pairCost t y s ≤ bound80191 := by
  interval_cases s
  · by_cases h : 60 ≤ y
    · exact pair9_cond t y (ht9 rfl h) h hy hyt
    · exact pair9_low t y ht hsy (by omega) hyt
  · by_cases h : 40 ≤ y
    · exact pair10_cond t y (ht10 rfl h) h (hy10 rfl) hyt
    · exact pair10_low t y ht hsy (by omega) hyt
  · by_cases h : 36 ≤ y
    · exact pair11_cond t y (ht11 rfl h) h (hy11 rfl) hyt
    · exact pair11_low t y ht hsy (by omega) hyt
  · by_cases h : 32 ≤ y
    · exact pair12_cond t y (ht12 rfl h) h (hy12 rfl) hyt
    · exact pair12_low t y ht hsy (by omega) hyt
  · by_cases h : 27 ≤ y
    · exact pair13_cond t y (ht13 rfl h) h (hy13 rfl) hyt
    · exact pair13_low t y ht hsy (by omega) hyt

private theorem low_rate (p : FlagDegree)
    (hpos : 0 < p.all) (hs : p.all ≤ 8)
    (hy : middle p ≤ 60) (ht : total p ≤ 1469) :
    1469 * paddedCost 131072 131073 p ≤ bound80191 * total p := by
  have hsy : p.all ≤ middle p := by simp only [middle]; omega
  have h := low_rate_table (total p) (middle p) p.all
    ht hy hpos hs hsy (middle_le_total p)
  simpa only [cap_self] using h

private theorem merge_padded_costs_finset {I : Type*} [DecidableEq I]
    (S : Finset I) (d e : ℕ) (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i ∈ S, (p i).all) ≤ P.all)
    (hy : (∑ i ∈ S, middle (p i)) ≤ middle P)
    (ht : (∑ i ∈ S, total (p i)) ≤ total P) :
    (∑ i ∈ S, paddedCost d e (p i)) ≤ paddedCost d e P := by
  let q : S → FlagDegree := fun i ↦ p i.1
  have hs' : (∑ i, (q i).all) ≤ P.all := by
    simpa only [q, Finset.sum_subtype S (fun _ ↦ Iff.rfl)] using hs
  have hy' : (∑ i, middle (q i)) ≤ middle P := by
    simpa only [q, Finset.sum_subtype S (fun _ ↦ Iff.rfl)] using hy
  have ht' : (∑ i, total (q i)) ≤ total P := by
    simpa only [q, Finset.sum_subtype S (fun _ ↦ Iff.rfl)] using ht
  have h := merge_padded_costs d e q P hs' hy' ht'
  simpa only [q, Finset.sum_subtype S (fun _ ↦ Iff.rfl)] using h

/-- Exact row-80191 aggregation for the conditioned factor caps. -/
theorem aggregate_80191 {I : Type*} [Fintype I]
    (p : I → FlagDegree)
    (hpos : ∀ i, 0 < (p i).all)
    (hsum : (∑ i, (p i).all) ≤ 13)
    (hysum : (∑ i, middle (p i)) ≤ 60)
    (htsum : (∑ i, total (p i)) ≤ 1469)
    (hy10 : ∀ i, (p i).all = 10 → middle (p i) ≤ 56)
    (hy11 : ∀ i, (p i).all = 11 → middle (p i) ≤ 52)
    (hy12 : ∀ i, (p i).all = 12 → middle (p i) ≤ 48)
    (hy13 : ∀ i, (p i).all = 13 → middle (p i) ≤ 44)
    (ht9 : ∀ i, (p i).all = 9 → 60 ≤ middle (p i) →
      total (p i) ≤ 1252)
    (ht10 : ∀ i, (p i).all = 10 → 40 ≤ middle (p i) →
      total (p i) ≤ 1406)
    (ht11 : ∀ i, (p i).all = 11 → 36 ≤ middle (p i) →
      total (p i) ≤ 1407)
    (ht12 : ∀ i, (p i).all = 12 → 32 ≤ middle (p i) →
      total (p i) ≤ 1405)
    (ht13 : ∀ i, (p i).all = 13 → 27 ≤ middle (p i) →
      total (p i) ≤ 1408) :
    (∑ i, paddedCost 131072 131073 (p i)) ≤ bound80191 := by
  letI : DecidableEq I := Classical.decEq I
  have hs (i : I) : (p i).all ≤ 13 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans hsum
  have hy (i : I) : middle (p i) ≤ 60 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans hysum
  have ht (i : I) : total (p i) ≤ 1469 :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans htsum
  by_cases hex : ∃ i, 9 ≤ (p i).all
  · rcases hex with ⟨i, hi⟩
    let S : Finset I := (Finset.univ : Finset I).erase i
    have hmem : i ∈ (Finset.univ : Finset I) := Finset.mem_univ i
    have hsdecomp : (∑ j ∈ S, (p j).all) + (p i).all =
        ∑ j, (p j).all := by
      simpa only [S] using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j ↦ (p j).all) hmem
    have hydecomp : (∑ j ∈ S, middle (p j)) + middle (p i) =
        ∑ j, middle (p j) := by
      simpa only [S] using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j ↦ middle (p j)) hmem
    have htdecomp : (∑ j ∈ S, total (p j)) + total (p i) =
        ∑ j, total (p j) := by
      simpa only [S] using Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j ↦ total (p j)) hmem
    have htrest : (∑ j ∈ S, total (p j)) ≤
        1469 - total (p i) := by omega
    have hyrest0 : (∑ j ∈ S, middle (p j)) ≤
        60 - middle (p i) := by omega
    have hsrest0 : (∑ j ∈ S, (p j).all) ≤
        13 - (p i).all := by omega
    have hslemiddle : (∑ j ∈ S, (p j).all) ≤
        ∑ j ∈ S, middle (p j) :=
      Finset.sum_le_sum (fun j _ ↦ by simp only [middle]; omega)
    have hymidtotal : (∑ j ∈ S, middle (p j)) ≤
        ∑ j ∈ S, total (p j) :=
      Finset.sum_le_sum (fun j _ ↦ middle_le_total (p j))
    have hyrest : (∑ j ∈ S, middle (p j)) ≤
        min (60 - middle (p i)) (1469 - total (p i)) :=
      le_min hyrest0 (hymidtotal.trans htrest)
    have hsrest : (∑ j ∈ S, (p j).all) ≤
        min (13 - (p i).all)
          (min (60 - middle (p i)) (1469 - total (p i))) :=
      le_min hsrest0 (hslemiddle.trans hyrest)
    have hcap := cap_cumulative
      (1469 - total (p i))
      (min (60 - middle (p i)) (1469 - total (p i)))
      (min (13 - (p i).all)
        (min (60 - middle (p i)) (1469 - total (p i))))
      (min_le_right _ _) (min_le_right _ _)
    have hrest := merge_padded_costs_finset S 131072 131073 p
      (remainder (total (p i)) (middle (p i)) (p i).all)
      (by simpa only [remainder, hcap.1] using hsrest)
      (by simpa only [remainder, hcap.2.1] using hyrest)
      (by simpa only [remainder, hcap.2.2] using htrest)
    have hpair := high_pair_table (total (p i)) (middle (p i)) (p i).all
      (ht i) (hy i) (hs i) hi (by simp only [middle]; omega)
      (middle_le_total (p i)) (hy10 i) (hy11 i) (hy12 i) (hy13 i)
      (ht9 i) (ht10 i) (ht11 i) (ht12 i) (ht13 i)
    change paddedCost 131072 131073
        (cap (total (p i)) (middle (p i)) (p i).all) +
          paddedCost 131072 131073
            (remainder (total (p i)) (middle (p i)) (p i).all) ≤
        bound80191 at hpair
    rw [cap_self] at hpair
    have hcostdecomp :
        (∑ j, paddedCost 131072 131073 (p j)) =
          (∑ j ∈ S, paddedCost 131072 131073 (p j)) +
            paddedCost 131072 131073 (p i) := by
      simpa only [S] using (Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j ↦ paddedCost 131072 131073 (p j)) hmem).symm
    rw [hcostdecomp]
    omega
  · have hrate (i : I) :
        1469 * paddedCost 131072 131073 (p i) ≤
          bound80191 * total (p i) :=
      low_rate (p i) (hpos i) (by
        have hnot : ¬ 9 ≤ (p i).all := fun h ↦ hex ⟨i, h⟩
        omega) (hy i) (ht i)
    have hscaled :
        1469 * (∑ i, paddedCost 131072 131073 (p i)) ≤
          1469 * bound80191 := by
      calc
        _ = ∑ i, 1469 * paddedCost 131072 131073 (p i) := by
          rw [Finset.mul_sum]
        _ ≤ ∑ i, bound80191 * total (p i) :=
          Finset.sum_le_sum (fun i _ ↦ hrate i)
        _ = bound80191 * (∑ i, total (p i)) := by rw [Finset.mul_sum]
        _ ≤ bound80191 * 1469 := Nat.mul_le_mul_left bound80191 htsum
        _ = 1469 * bound80191 := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by decide)

theorem bound80191_is_attained :
    paddedCost 131072 131073 (cap 1407 52 11) +
      paddedCost 131072 131073 (cap 62 8 2) = bound80191 := by
  decide

end ProximityPrize.SubmissionLower.LocatorFactorAggregate
