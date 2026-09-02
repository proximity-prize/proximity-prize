import ProximityPrize.SubmissionLower.LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorFactorReplacement
open scoped BigOperators
open RCN095 LocatorFactorAggregate
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def remainingCap (T YS S:ℕ) (p:FlagDegree):FlagDegree :=
  cap (T - total p) (min (YS - middle p) (T - total p))
    (min (S - p.all) (min (YS - middle p) (T - total p)))
def remainingCost (T YS S d e:ℕ) (p:FlagDegree):ℕ :=
  if (remainingCap T YS S p).all = 0 then 0
  else paddedCost d e (remainingCap T YS S p)
def cellCost (T YS S d e:ℕ) (p:FlagDegree) (q:ℕ):ℕ :=
  min (paddedCost d e p) q + remainingCost T YS S d e p
def Bad (T d e bound:ℕ) (p:FlagDegree):Prop :=
  bound * total p < T * paddedCost d e p
theorem remainingCap_cumulative (T YS S:ℕ) (p:FlagDegree) :
    (remainingCap T YS S p).all =
        min (S - p.all) (min (YS - middle p) (T - total p)) ∧
      middle (remainingCap T YS S p) = min (YS - middle p) (T - total p) ∧
      total (remainingCap T YS S p) = T - total p:=by
  exact cap_cumulative _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _)
theorem sum_erase_le_sub {I:Type*} [Fintype I] [DecidableEq I]
    (f:I → ℕ) (B:ℕ) (h:(∑ i, f i) ≤ B) (i:I) :
    (∑ j ∈ Finset.univ.erase i, f j) ≤ B - f i:=by
  have heq:=Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  omega
theorem remaining_cumulative {I:Type*} [Fintype I] [DecidableEq I]
    (p:I → FlagDegree) (T YS S:ℕ) (i:I)
    (hs:(∑ j, (p j).all) ≤ S)
    (hy:(∑ j, middle (p j)) ≤ YS)
    (ht:(∑ j, total (p j)) ≤ T) :
    (∑ j ∈ Finset.univ.erase i, (p j).all) ≤ (remainingCap T YS S (p i)).all ∧
      (∑ j ∈ Finset.univ.erase i, middle (p j)) ≤ middle (remainingCap T YS S (p i)) ∧
      (∑ j ∈ Finset.univ.erase i, total (p j)) ≤ total (remainingCap T YS S (p i)):=by
  have hrs:=sum_erase_le_sub (fun j => (p j).all) S hs i
  have hys:=sum_erase_le_sub (fun j => middle (p j)) YS hy i
  have hts:=sum_erase_le_sub (fun j => total (p j)) T ht i
  have hry:(∑ j ∈ Finset.univ.erase i, (p j).all) ≤
      ∑ j ∈ Finset.univ.erase i, middle (p j) :=
    Finset.sum_le_sum (fun j _ => all_le_middle (p j))
  have hyt:(∑ j ∈ Finset.univ.erase i, middle (p j)) ≤
      ∑ j ∈ Finset.univ.erase i, total (p j) :=
    Finset.sum_le_sum (fun j _ => middle_le_total (p j))
  have hc:=remainingCap_cumulative T YS S (p i)
  rw [hc.1, hc.2.1, hc.2.2]
  exact ⟨le_min hrs (le_min (hry.trans hys) ((hry.trans hyt).trans hts)),
    le_min hys (hyt.trans hts), hts⟩
theorem sum_others_le_remainingCost {I:Type*} [Fintype I] [DecidableEq I]
    (p:I → FlagDegree) (count:I → ℕ) (T YS S d e:ℕ) (i:I)
    (hs:(∑ j, (p j).all) ≤ S)
    (hy:(∑ j, middle (p j)) ≤ YS)
    (ht:(∑ j, total (p j)) ≤ T)
    (hstage:∀ j, count j ≤ paddedCost d e (p j))
    (hzero:∀ j, (p j).all = 0 → count j = 0) :
    (∑ j ∈ Finset.univ.erase i, count j) ≤ remainingCost T YS S d e (p i):=by
  have hc:=remaining_cumulative p T YS S i hs hy ht
  by_cases hz:(remainingCap T YS S (p i)).all = 0
  · rw [remainingCost, if_pos hz]
    have hrs:(∑ j ∈ Finset.univ.erase i, (p j).all) ≤ 0:=by
      simpa only [hz] using hc.1
    have hcount:(∑ j ∈ Finset.univ.erase i, count j) = 0:=by
      apply Finset.sum_eq_zero
      intro j hj
      apply hzero j
      have hji:(p j).all ≤ ∑ k ∈ Finset.univ.erase i, (p k).all :=
        Finset.single_le_sum (f:=fun k => (p k).all)
          (fun k _ => Nat.zero_le (p k).all) hj
      omega
    exact hcount.le
  · rw [remainingCost, if_neg hz]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, paddedCost d e (p j) :=
        Finset.sum_le_sum (fun j _ => hstage j)
      _ ≤ paddedCost d e (remainingCap T YS S (p i)) :=
        merge_padded_costs_finset (Finset.univ.erase i) d e p _ hc.1 hc.2.1 hc.2.2
theorem sum_le_cellCost {I:Type*} [Fintype I] [DecidableEq I]
    (p:I → FlagDegree) (count:I → ℕ) (T YS S d e:ℕ) (i:I) (q:ℕ)
    (hs:(∑ j, (p j).all) ≤ S)
    (hy:(∑ j, middle (p j)) ≤ YS)
    (ht:(∑ j, total (p j)) ≤ T)
    (hstage:∀ j, count j ≤ paddedCost d e (p j))
    (hzero:∀ j, (p j).all = 0 → count j = 0)
    (hrepl:count i ≤ q) :
    (∑ j, count j) ≤ cellCost T YS S d e (p i) q:=by
  have hi:=le_min (hstage i) hrepl
  have hr:=sum_others_le_remainingCost p count T YS S d e i hs hy ht hstage hzero
  calc
    _ = count i + ∑ j ∈ Finset.univ.erase i, count j :=
      (Finset.add_sum_erase Finset.univ count (Finset.mem_univ i)).symm
    _ ≤ min (paddedCost d e (p i)) q + remainingCost T YS S d e (p i) :=
      Nat.add_le_add hi hr
    _ = cellCost T YS S d e (p i) q:=rfl
theorem high_unique {I:Type*} [Fintype I] [DecidableEq I] (p:I → FlagDegree)
    (hs:(∑ i, (p i).all) ≤ 14) {i j:I}
    (hi:8 ≤ (p i).all) (hj:8 ≤ (p j).all):i = j:=by
  by_contra hne
  have hjmem:j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩
  have hrest:=sum_erase_le_sub (fun k => (p k).all) 14 hs i
  have hjrest:(p j).all ≤ ∑ k ∈ Finset.univ.erase i, (p k).all :=
    Finset.single_le_sum (f:=fun k => (p k).all)
      (fun k _ => Nat.zero_le (p k).all) hjmem
  omega
theorem aggregate_of_rate_and_cells {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T YS S d e lowR bound:ℕ)
    (hT:0 < T)
    (hs:(∑ i, (p i).all) ≤ S)
    (hy:(∑ i, middle (p i)) ≤ YS)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ paddedCost d e (p i))
    (hzero:∀ i, (p i).all = 0 → count i = 0)
    (hrate:∀ i, (p i).all ≤ lowR → T * paddedCost d e (p i) ≤ bound * total (p i))
    (hrepl:∀ i, lowR < (p i).all → count i ≤ q i)
    (hcell:∀ i, lowR < (p i).all → cellCost T YS S d e (p i) (q i) ≤ bound) :
    (∑ i, count i) ≤ bound:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  by_cases hh:∃ i, lowR < (p i).all
  · obtain ⟨i, hi⟩:=hh
    exact (sum_le_cellCost p count T YS S d e i (q i) hs hy ht hstage hzero
      (hrepl i hi)).trans (hcell i hi)
  · have hlo (i:I):(p i).all ≤ lowR:=by
      have hn:¬ lowR < (p i).all:=fun hi => hh ⟨i, hi⟩
      omega
    have hscaled:T * (∑ i, count i) ≤ T * bound:=by
      calc
        _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
        _ ≤ ∑ i, T * paddedCost d e (p i) :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left T (hstage i))
        _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hrate i (hlo i))
        _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
        _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
        _ = T * bound:=by ring
    exact Nat.le_of_mul_le_mul_left hscaled hT
theorem aggregate_of_bad_cells {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T YS S d e bound:ℕ)
    (hT:0 < T)
    (hs:(∑ i, (p i).all) ≤ S)
    (hy:(∑ i, middle (p i)) ≤ YS)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ paddedCost d e (p i))
    (hzero:∀ i, (p i).all = 0 → count i = 0)
    (hrepl:∀ i, Bad T d e bound (p i) → count i ≤ q i)
    (hcell:∀ i, Bad T d e bound (p i) →
      cellCost T YS S d e (p i) (q i) ≤ bound) :
    (∑ i, count i) ≤ bound:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  by_cases hh:∃ i, Bad T d e bound (p i)
  · obtain ⟨i, hi⟩:=hh
    exact (sum_le_cellCost p count T YS S d e i (q i) hs hy ht hstage hzero
      (hrepl i hi)).trans (hcell i hi)
  · have hrate (i:I):T * paddedCost d e (p i) ≤ bound * total (p i):=by
      have hn:¬ Bad T d e bound (p i):=fun hi => hh ⟨i, hi⟩
      dsimp only [Bad] at hn
      omega
    have hscaled:T * (∑ i, count i) ≤ T * bound:=by
      calc
        _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
        _ ≤ ∑ i, T * paddedCost d e (p i) :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left T (hstage i))
        _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hrate i)
        _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
        _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
        _ = T * bound:=by ring
    exact Nat.le_of_mul_le_mul_left hscaled hT
theorem aggregate_of_rate_replacements {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T d e bound:ℕ)
    (hT:0 < T)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ paddedCost d e (p i))
    (hrepl:∀ i, Bad T d e bound (p i) → count i ≤ q i)
    (hqrate:∀ i, Bad T d e bound (p i) →
      T * q i ≤ bound * total (p i)) :
    (∑ i, count i) ≤ bound:=by
  have hone (i:I):T * count i ≤ bound * total (p i):=by
    by_cases hbad:Bad T d e bound (p i)
    · exact (Nat.mul_le_mul_left T (hrepl i hbad)).trans (hqrate i hbad)
    · have hordinary:T * paddedCost d e (p i) ≤ bound * total (p i):=by
        unfold Bad at hbad
        omega
      exact (Nat.mul_le_mul_left T (hstage i)).trans hordinary
  have hscaled:T * (∑ i, count i) ≤ T * bound:=by
    calc
      _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
      _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hone i)
      _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
      _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
      _ = T * bound:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled hT
theorem aggregate_6751 {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ)
    (hs:(∑ i, (p i).all) ≤ 14)
    (hy:(∑ i, middle (p i)) ≤ 64)
    (ht:(∑ i, total (p i)) ≤ 1698)
    (hstage:∀ i, count i ≤ paddedCost 131072 131073 (p i))
    (hzero:∀ i, (p i).all = 0 → count i = 0)
    (hrepl:∀ i, 8 ≤ (p i).all → count i ≤ q i)
    (hcell:∀ i, 8 ≤ (p i).all →
      cellCost 1698 64 14 131072 131073 (p i) (q i) ≤ 266000000000000000) :
    (∑ i, count i) ≤ 266000000000000000:=by
  classical
  refine aggregate_of_rate_and_cells p count q 1698 64 14 131072 131073 7
    266000000000000000 (by decide) hs hy ht hstage hzero ?_ ?_ ?_
  · intro i hi
    have hyi:middle (p i) ≤ 64 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hy
    have hti:total (p i) ≤ 1698 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ht
    exact (rate_bound_6751_low (p i) hi hyi hti).trans
      (Nat.mul_le_mul_right (total (p i))
        (by decide:261420997282933785 ≤ 266000000000000000))
  · intro i hi
    exact hrepl i (by omega)
  · intro i hi
    exact hcell i (by omega)
/-- Ordinary-route badness for an arbitrary ordinary cost function. -/
def BadCost (T:ℕ) (cost:FlagDegree → ℕ) (bound:ℕ) (p:FlagDegree):Prop :=
  bound * total p < T * cost p
theorem aggregate_of_rate_replacements_cost {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T:ℕ) (cost:FlagDegree → ℕ) (bound:ℕ)
    (hT:0 < T)
    (ht:(∑ i, total (p i)) ≤ T)
    (hstage:∀ i, count i ≤ cost (p i))
    (hrepl:∀ i, BadCost T cost bound (p i) → count i ≤ q i)
    (hqrate:∀ i, BadCost T cost bound (p i) →
      T * q i ≤ bound * total (p i)) :
    (∑ i, count i) ≤ bound:=by
  have hone (i:I):T * count i ≤ bound * total (p i):=by
    by_cases hbad:BadCost T cost bound (p i)
    · exact (Nat.mul_le_mul_left T (hrepl i hbad)).trans (hqrate i hbad)
    · have hordinary:T * cost (p i) ≤ bound * total (p i):=by
        unfold BadCost at hbad
        omega
      exact (Nat.mul_le_mul_left T (hstage i)).trans hordinary
  have hscaled:T * (∑ i, count i) ≤ T * bound:=by
    calc
      _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
      _ ≤ ∑ i, bound * total (p i):=Finset.sum_le_sum (fun i _ => hone i)
      _ = bound * (∑ i, total (p i)):=by rw [Finset.mul_sum]
      _ ≤ bound * T:=Nat.mul_le_mul_left bound ht
      _ = T * bound:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled hT

/-- Ordinary-route badness charged against an arbitrary nonnegative weight. -/
def BadCostW (T:ℕ) (cost:FlagDegree → ℕ) (bound:ℕ) (wgt:FlagDegree → ℕ)
    (p:FlagDegree):Prop :=
  bound * wgt p < T * cost p

theorem badCostW_total (T:ℕ) (cost:FlagDegree → ℕ) (bound:ℕ) (p:FlagDegree) :
    BadCostW T cost bound total p ↔ BadCost T cost bound p:=Iff.rfl

/-- Weighted charging.  This is the ordinary rate-replacement aggregation with
each factor charged against `wgt` rather than only its total degree. -/
theorem aggregate_of_rate_replacements_weighted {I:Type*} [Fintype I]
    (p:I → FlagDegree) (count q:I → ℕ) (T:ℕ) (cost wgt:FlagDegree → ℕ) (bound:ℕ)
    (hT:0 < T)
    (hw:(∑ i, wgt (p i)) ≤ T)
    (hstage:∀ i, count i ≤ cost (p i))
    (hrepl:∀ i, BadCostW T cost bound wgt (p i) → count i ≤ q i)
    (hqrate:∀ i, BadCostW T cost bound wgt (p i) →
      T * q i ≤ bound * wgt (p i)) :
    (∑ i, count i) ≤ bound:=by
  have hone (i:I):T * count i ≤ bound * wgt (p i):=by
    by_cases hbad:BadCostW T cost bound wgt (p i)
    · exact (Nat.mul_le_mul_left T (hrepl i hbad)).trans (hqrate i hbad)
    · have hordinary:T * cost (p i) ≤ bound * wgt (p i):=by
        unfold BadCostW at hbad
        omega
      exact (Nat.mul_le_mul_left T (hstage i)).trans hordinary
  have hscaled:T * (∑ i, count i) ≤ T * bound:=by
    calc
      _ = ∑ i, T * count i:=by rw [Finset.mul_sum]
      _ ≤ ∑ i, bound * wgt (p i):=Finset.sum_le_sum (fun i _ => hone i)
      _ = bound * (∑ i, wgt (p i)):=by rw [Finset.mul_sum]
      _ ≤ bound * T:=Nat.mul_le_mul_left bound hw
      _ = T * bound:=by ring
  exact Nat.le_of_mul_le_mul_left hscaled hT

end ProximityPrize.SubmissionLower.LocatorFactorReplacement
