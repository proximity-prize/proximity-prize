import ProximityPrize.SubmissionLower.BoundaryTailBase
import ProximityPrize.SubmissionLower.BoundaryTailRouting

/-! Arithmetic receipt interface for the 6805 base. The numerical certificate
retains the ordinary zero-z Bellman table and a strict carrier floor. No
geometric provider is assumed: each factor uses BoundaryTailBase.cap. -/
namespace ProximityPrize.SubmissionLower.BoundaryTailBaseOracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open LocatorOrdinaryZConvex (two_discreteConvex_endpoint)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section

def cost (r v z : ℕ) : ℕ := BoundaryTailOrdinary.rawCost (rawFlag r v z)

/-- Pure arithmetic shape needed to concentrate the z coordinate. The low
branch is the checked old padded cost; the high branch is affine in z. -/
structure Shape : Prop where
  mono : ∀ r v, Monotone (cost r v)
  convex : ∀ r v z, 1 ≤ r →
    2 * cost r v (z+1) ≤ cost r v z + cost r v (z+2)

theorem exists_z_carrier
    (cost : ℕ → ℕ → ℕ → ℕ)
    (hmono : ∀ r v, Monotone (cost r v))
    (hconvex : ∀ r v z, 1 ≤ r →
      2 * cost r v (z+1) ≤ cost r v z + cost r v (z+2))
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (r v z : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i) (hne : s.Nonempty) :
    ∃ c ∈ s,
      (∑ i ∈ s, cost (r i) (v i) (z i)) ≤
        cost (r c) (v c) (∑ i ∈ s, z i) +
          ∑ i ∈ s.erase c, cost (r i) (v i) 0 := by
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      by_cases hs : s = ∅
      · subst s
        refine ⟨a, by simp, ?_⟩
        simp
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨c, hc, hbound⟩ := ih (fun i hi => hr i (by simp [hi])) hsne
        have hra : 1 ≤ r a := hr a (by simp)
        have hrc : 1 ≤ r c := hr c (by simp [hc])
        have hpair := two_discreteConvex_endpoint
          (cost (r a) (v a)) (cost (r c) (v c))
          (hmono (r a) (v a)) (hmono (r c) (v c))
          (fun n => hconvex (r a) (v a) n hra)
          (fun n => hconvex (r c) (v c) n hrc)
          (z a) (∑ i ∈ s, z i)
        have hpre :
            (∑ i ∈ insert a s, cost (r i) (v i) (z i)) ≤
              cost (r a) (v a) (z a) +
                (cost (r c) (v c) (∑ i ∈ s, z i) +
                  ∑ i ∈ s.erase c, cost (r i) (v i) 0) := by
          rw [Finset.sum_insert ha]
          exact Nat.add_le_add_left hbound _
        by_cases hend :
            cost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                cost (r c) (v c) 0 ≤
              cost (r a) (v a) 0 +
                cost (r c) (v c) (z a + ∑ i ∈ s, z i)
        · refine ⟨c, by simp [hc], ?_⟩
          have htwo :
              cost (r a) (v a) (z a) +
                  cost (r c) (v c) (∑ i ∈ s, z i) ≤
                cost (r a) (v a) 0 +
                  cost (r c) (v c) (z a + ∑ i ∈ s, z i) := by
            exact hpair.trans (by simpa [max_eq_right hend])
          calc
            (∑ i ∈ insert a s, cost (r i) (v i) (z i)) ≤
                cost (r a) (v a) (z a) +
                  (cost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, cost (r i) (v i) 0) := hpre
            _ ≤ (cost (r a) (v a) 0 +
                  cost (r c) (v c) (z a + ∑ i ∈ s, z i)) +
                    ∑ i ∈ s.erase c, cost (r i) (v i) 0 := by omega
            _ = cost (r c) (v c) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase c,
                    cost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
              have hac : a ≠ c := fun h => ha (h ▸ hc)
              rw [Finset.erase_insert_of_ne hac, Finset.sum_insert]
              · ac_rfl
              · exact fun h => ha (Finset.mem_of_mem_erase h)
        · refine ⟨a, by simp, ?_⟩
          have hreverse :
              cost (r c) (v c) (z a + ∑ i ∈ s, z i) +
                  cost (r a) (v a) 0 ≤
                cost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  cost (r c) (v c) 0 := by
            omega
          have htwo :
              cost (r a) (v a) (z a) +
                  cost (r c) (v c) (∑ i ∈ s, z i) ≤
                cost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  cost (r c) (v c) 0 := by
            exact hpair.trans (by
              rw [max_eq_left]
              simpa [Nat.add_comm] using hreverse)
          have hzeros :
              cost (r c) (v c) 0 +
                  ∑ i ∈ s.erase c, cost (r i) (v i) 0 =
                ∑ i ∈ s, cost (r i) (v i) 0 := by
            simpa only [Nat.add_comm] using
              (Finset.sum_erase_add s
                (fun i => cost (r i) (v i) 0) hc)
          calc
            (∑ i ∈ insert a s, cost (r i) (v i) (z i)) ≤
                cost (r a) (v a) (z a) +
                  (cost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, cost (r i) (v i) 0) := hpre
            _ ≤ (cost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  cost (r c) (v c) 0) +
                    ∑ i ∈ s.erase c, cost (r i) (v i) 0 := by omega
            _ = cost (r a) (v a) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase a,
                    cost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha, Finset.erase_insert ha]
              rw [← hzeros]
              ac_rfl

/-- The Bellman check has only four bounded indices. The `fits` alternative
excludes a nonempty residual family with zero total slope. -/
def ZeroRows (zero : ℕ → ℕ → ℕ) : Prop :=
  ∀ R V r v, 1 ≤ r → r ≤ R → v ≤ V → R ≤ 31 → R+V ≤ 142 →
    (r < R ∨ v = V) → cost r v 0 + zero (R-r) (V-v) ≤ zero R V

def StrictRows (zero : ℕ → ℕ → ℕ) (split : FlagDegree → ℕ) : Prop :=
  ∀ R V r v z, 1 ≤ r → r < R → v ≤ V → R ≤ 31 → R+V ≤ 142 →
    R+V+z ≤ 7501 → cost r v z + zero (R-r) (V-v) ≤ split (rawFlag R V z)

theorem sum_zero_le (zero : ℕ → ℕ → ℕ) (hrows : ZeroRows zero)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (r v : ι → ℕ)
    (hpositive : ∀ i ∈ s, 1 ≤ r i)
    (hrCap : (∑ i ∈ s, r i) ≤ 31)
    (hrvCap : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 142) :
    (∑ i ∈ s, cost (r i) (v i) 0) ≤ zero (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hra : 1 ≤ r a := hpositive a (by simp)
      have hRInsert : r a + (∑ i ∈ s, r i) ≤ 31 := by
        simpa only [Finset.sum_insert ha] using hrCap
      have hRVInsert :
          (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ 142 := by
        rw [Finset.sum_insert ha, Finset.sum_insert ha] at hrvCap
        omega
      have ihBound := ih
        (fun i hi ↦ hpositive i (Finset.mem_insert_of_mem hi))
        (by omega) (by omega)
      have hfits : r a < r a + (∑ i ∈ s, r i) ∨
          v a = v a + (∑ i ∈ s, v i) := by
        by_cases hs : s.Nonempty
        · obtain ⟨i, hi⟩ := hs
          have hri := hpositive i (Finset.mem_insert_of_mem hi)
          have hriSum : r i ≤ ∑ j ∈ s, r j :=
            Finset.single_le_sum (f := fun j ↦ r j)
              (fun _ _ ↦ Nat.zero_le _) hi
          left
          omega
        · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
          subst s
          simp
      have hcandidate := hrows
        (r a + ∑ i ∈ s, r i) (v a + ∑ i ∈ s, v i)
        (r a) (v a) hra (by omega) (by omega) hRInsert hRVInsert hfits
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Nat.add_le_add_left ihBound _).trans (by
        simpa only [Nat.add_sub_cancel_left] using hcandidate)

theorem sum_count_le (shape : Shape) (zero : ℕ → ℕ → ℕ)
    (hzeroRows : ZeroRows zero) (single split : FlagDegree → ℕ)
    (hsplit : StrictRows zero split)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree) (count : ι → ℕ)
    (hpositive : ∀ i ∈ s, 1 ≤ (p i).all)
    (hrCap : (sumFlag s p).all ≤ 31) (hyCap : middle (sumFlag s p) ≤ 142)
    (htCap : total (sumFlag s p) ≤ 7501)
    (hold : ∀ i ∈ s, count i ≤ cost (p i).all (p i).yz (p i).zOnly)
    (hnew : ∀ i ∈ s, count i ≤ single (p i)) :
    (∑ i ∈ s, count i) ≤ max (single (sumFlag s p)) (split (sumFlag s p)) := by
  classical
  have hcount := Finset.sum_le_sum hold
  by_cases hs : s.Nonempty
  · obtain ⟨c,hc,hconcentrate⟩ := exists_z_carrier cost shape.mono shape.convex s
      (fun i => (p i).all) (fun i => (p i).yz) (fun i => (p i).zOnly) hpositive hs
    by_cases hrest : (s.erase c).Nonempty
    ·
      have hzero := sum_zero_le zero hzeroRows (s.erase c)
        (fun i ↦ (p i).all) (fun i ↦ (p i).yz)
        (fun i hi ↦ hpositive i (Finset.mem_of_mem_erase hi))
        (by
          have hsub : s.erase c ⊆ s := Finset.erase_subset c s
          have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).all)
          exact hle.trans hrCap)
        (by
          have hsub : s.erase c ⊆ s := Finset.erase_subset c s
          have hrle := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).all)
          have hvle := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).yz)
          have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 142 := by
            rw [sumFlag_middle] at hyCap
            simp only [middle, Finset.sum_add_distrib] at hyCap
            omega
          omega)
      have hcR : (p c).all ≤ ∑ i ∈ s, (p i).all := by
        exact Finset.single_le_sum (f := fun i ↦ (p i).all)
          (fun _ _ ↦ Nat.zero_le _) hc
      have hcV : (p c).yz ≤ ∑ i ∈ s, (p i).yz := by
        exact Finset.single_le_sum (f := fun i ↦ (p i).yz)
          (fun _ _ ↦ Nat.zero_le _) hc
      have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 142 := by
        rw [sumFlag_middle] at hyCap
        simp only [middle, Finset.sum_add_distrib] at hyCap
        omega
      have htotal : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) +
          (∑ i ∈ s, (p i).zOnly) ≤ 7501 := by
        rw [sumFlag_total] at htCap
        simp only [total, middle, Finset.sum_add_distrib] at htCap
        omega
      have hrErase := Finset.sum_erase_add s (fun i ↦ (p i).all) hc
      have hvErase := Finset.sum_erase_add s (fun i ↦ (p i).yz) hc
      have hstrict : (p c).all < ∑ i ∈ s, (p i).all := by
        obtain ⟨i,hi⟩ := hrest
        have hiS := Finset.mem_of_mem_erase hi
        have hri := hpositive i hiS
        have hiSum : (p i).all ≤ ∑ j ∈ s.erase c, (p j).all :=
          Finset.single_le_sum (f := fun j => (p j).all) (fun _ _ => Nat.zero_le _) hi
        omega
      have hcandidate := hsplit
        (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
        (p c).all (p c).yz (∑ i ∈ s, (p i).zOnly)
        (hpositive c hc) hstrict hcV hrCap hmiddle htotal
      have hzero' :
          (∑ i ∈ s.erase c,
              cost (p i).all (p i).yz 0) ≤
            zero
              ((∑ i ∈ s, (p i).all) - (p c).all)
              ((∑ i ∈ s, (p i).yz) - (p c).yz) := by
        simpa only [show (∑ i ∈ s, (p i).all) - (p c).all =
            ∑ i ∈ s.erase c, (p i).all by omega,
          show (∑ i ∈ s, (p i).yz) - (p c).yz =
            ∑ i ∈ s.erase c, (p i).yz by omega] using hzero
      have hflagEq : sumFlag s p = rawFlag (∑ i ∈ s, (p i).all)
          (∑ i ∈ s, (p i).yz) (∑ i ∈ s, (p i).zOnly) := rfl
      have hb := hconcentrate.trans ((Nat.add_le_add_left hzero' _).trans hcandidate)
      rw [←hflagEq] at hb
      exact (hcount.trans hb).trans (le_max_right _ _)
    · have he : s.erase c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrest
      have hsEq : s = {c} := by rw [←Finset.insert_erase hc,he]; rfl
      rw [hsEq]
      simpa only [Finset.sum_singleton,sumFlag,Finset.sum_singleton] using
        (hnew c hc).trans (le_max_left (single (p c)) (split (p c)))
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

/-- Compact numerical facts required of the generated rows. All fields are
inequalities in natural numbers; no algebraic counting provider is assumed.
The last field retains the strict aggregate floor even when a profile improves
the singleton row. -/
structure Receipt (zero : ℕ → ℕ → ℕ) (split base : FlagDegree → ℕ) : Prop where
  shape : Shape
  zeroRows : ZeroRows zero
  strictRows : StrictRows zero split
  singleton : ∀ p : FlagDegree, 1 ≤ p.all → p.all ≤ 31 →
    middle p ≤ 142 → total p ≤ 7501 →
    BoundaryTailOrdinary.rawCost p ≤ base p ∨
      (BoundaryTailBase.Active p ∧
        BoundaryTailRefinedCap.profile p.all p.yz p.zOnly ≤ base p)
  floor : ∀ p : FlagDegree, 1 ≤ p.all → p.all ≤ 31 →
    middle p ≤ 142 → total p ≤ 7501 → split p ≤ base p

theorem Receipt.single_le {zero : ℕ → ℕ → ℕ} {split base : FlagDegree → ℕ}
    (receipt : Receipt zero split base) (p : FlagDegree)
    (hpos : 1 ≤ p.all) (hr : p.all ≤ 31) (hy : middle p ≤ 142)
    (ht : total p ≤ 7501) : BoundaryTailBase.cap p ≤ base p := by
  rcases receipt.singleton p hpos hr hy ht with hraw | ⟨hactive,hprofile⟩
  · exact (BoundaryTailBase.cap_le_raw p).trans hraw
  · exact (BoundaryTailBase.cap_le_profile p hactive).trans hprofile

theorem Receipt.sum_count_le {zero : ℕ → ℕ → ℕ} {split base : FlagDegree → ℕ}
    (receipt : Receipt zero split base)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree) (count : ι → ℕ)
    (hpositive : ∀ i ∈ s, 1 ≤ (p i).all)
    (hrCap : (sumFlag s p).all ≤ 31) (hyCap : middle (sumFlag s p) ≤ 142)
    (htCap : total (sumFlag s p) ≤ 7501)
    (hnew : ∀ i ∈ s, count i ≤ BoundaryTailBase.cap (p i)) :
    (∑ i ∈ s, count i) ≤ base (sumFlag s p) := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi⟩ := hs
    have hpos : 1 ≤ (sumFlag s p).all :=
      (hpositive i hi).trans
        (Finset.single_le_sum (f := fun j => (p j).all)
          (fun _ _ => Nat.zero_le _) hi)
    have hraw : ∀ i ∈ s, count i ≤ cost (p i).all (p i).yz (p i).zOnly := by
      intro i hi
      have h := (hnew i hi).trans (BoundaryTailBase.cap_le_raw (p i))
      simpa only [cost, rawFlag] using h
    exact (BoundaryTailBaseOracle.sum_count_le receipt.shape zero receipt.zeroRows BoundaryTailBase.cap split
      receipt.strictRows s p count hpositive hrCap hyCap htCap hraw hnew).trans
      (max_le (receipt.single_le (sumFlag s p) hpos hrCap hyCap htCap)
        (receipt.floor (sumFlag s p) hpos hrCap hyCap htCap))
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end
end ProximityPrize.SubmissionLower.BoundaryTailBaseOracle

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseSemantics
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN095 RCN130 RCN140 RCN238 RCN266 RCN275 LocatorFactorAggregate
open LocatorBatchProductRoute
open LocatorPhase6800Oracle (sumFlag)
open LocatorBatchPhase6800 (regularAggregateFlag)
open Lower80801.BatchPhase
set_option autoImplicit false
noncomputable section
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

/-- The base step consumes the actual per-factor cap already established by
BoundaryTailBase.regular_factor_count (or its carrier specialization). Its
remaining assumptions are precisely the generated arithmetic receipts. -/
theorem stateLocalRegularBoundOn_of_base
    {zero : ℕ → ℕ → ℕ} {split base : FlagDegree → ℕ}
    (receipt : BoundaryTailBaseOracle.Receipt zero split base)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hsingle : ∀ F ∈ ambient, (regularSeeds H selected Gamma F).card ≤
      BoundaryTailBase.cap (regularCumulativeFlag H F)) :
    StateLocalRegularBoundOn H selected Gamma ambient base := by
  classical
  intro A hAambient hs hy ht
  exact receipt.sum_count_le A (regularCumulativeFlag H)
    (fun F => (regularSeeds H selected Gamma F).card)
    (fun F _ => Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
    hs hy ht (fun F hF => hsingle F (hAambient hF))

end
end ProximityPrize.SubmissionLower.Lower80801.PhaseSemantics
