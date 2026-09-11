import ProximityPrize.SubmissionLower.Part.G001_04
section Compact_PackedLocatorTail
section PackedLocator_LocatorPhase6800Audit
namespace ProximityPrize.SubmissionLower.LocatorPhase6800Audit
open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxRecDepth 100000


/-- Finite arithmetic checked for one aggregate row and one candidate
carrier.  Every generated row has one or two useful affine segments. -/
def CandidateRowCheck (rows : Array BaseRow) (R V r v : ℕ) : Prop :=
  let q := lookupBaseRow rows R V
  let zero := baseZeroCap rows (R - r) (V - v)
  LocatorOrdinaryZConvex.rawCost r v 0 + zero ≤ q.z0 ∧
  LocatorOrdinaryZConvex.rawCost r v 1 + zero ≤ q.z1 ∧
  LocatorOrdinaryZConvex.rawCost r v 2 + zero ≤ q.z2 ∧
  match q.segments with
  | [s] =>
      s.start = 3 ∧ candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
        candidateSlope r v ≤ s.slope
  | [s₁, s₂] =>
      s₁.start = 3 ∧ s₁.start < s₂.start ∧
        candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
        candidateLine rows R V r v (s₂.start - 1) ≤
          s₁.evalAt (s₂.start - 1) ∧
        candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
        candidateSlope r v ≤ s₂.slope
  | _ => False

instance (rows : Array BaseRow) (R V r v : ℕ) :
    Decidable (CandidateRowCheck rows R V r v) := by
  unfold CandidateRowCheck
  dsimp only
  generalize hq : lookupBaseRow rows R V = q
  cases hs : q.segments with
  | nil =>
      simp only [hs]
      infer_instance
  | cons s tail =>
      cases ht : tail with
      | nil =>
          simp only [hs, ht]
          infer_instance
      | cons s₂ rest =>
          cases hu : rest with
          | nil =>
              simp only [hs, ht, hu]
              infer_instance
          | cons s₃ rest₃ =>
              simp only [hs, ht, hu]
              infer_instance

/-- One finite `R` layer of the carrier-row checker. -/
def CandidateRCheck (rows : Array BaseRow) (R : ℕ) : Prop :=
  ∀ V ∈ List.range (136 - R),
    ∀ r ∈ List.range (R + 1), 1 ≤ r →
      ∀ v ∈ List.range (V + 1), (r < R ∨ v = V) →
        CandidateRowCheck rows R V r v

instance (rows : Array BaseRow) (R : ℕ) : Decidable (CandidateRCheck rows R) := by
  unfold CandidateRCheck
  infer_instance

/-- Complete finite base-table checker.  Its executable domain has only the
2.443-million aggregate/carrier splits, not a `z` grid. -/
def BaseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R → CandidateRCheck rows R

instance (rows : Array BaseRow) : Decidable (BaseCandidateChecks rows) := by
  unfold BaseCandidateChecks
  infer_instance

theorem candidateRowCheck_sound
    (rows : Array BaseRow) (R V r v z : ℕ) (hr : 1 ≤ r)
    (hcheck : CandidateRowCheck rows R V r v) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z) := by
  let q := lookupBaseRow rows R V
  change LocatorOrdinaryZConvex.rawCost r v z +
      baseZeroCap rows (R - r) (V - v) ≤ q.evalAt z
  change
    LocatorOrdinaryZConvex.rawCost r v 0 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z0 ∧
      LocatorOrdinaryZConvex.rawCost r v 1 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z1 ∧
      LocatorOrdinaryZConvex.rawCost r v 2 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z2 ∧
      (match q.segments with
      | [s] =>
          s.start = 3 ∧
            candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
            candidateSlope r v ≤ s.slope
      | [s₁, s₂] =>
          s₁.start = 3 ∧ s₁.start < s₂.start ∧
            candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
            candidateLine rows R V r v (s₂.start - 1) ≤
              s₁.evalAt (s₂.start - 1) ∧
            candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
            candidateSlope r v ≤ s₂.slope
      | _ => False) at hcheck
  rcases hcheck with ⟨hzero, hone, htwo, hsegmentsSound⟩
  by_cases hz0 : z = 0
  · subst z
    simpa [BaseRow.evalAt] using hzero
  by_cases hz1 : z = 1
  · subst z
    simpa [BaseRow.evalAt] using hone
  by_cases hz2 : z = 2
  · subst z
    simpa [BaseRow.evalAt] using htwo
  have hz3 : 3 ≤ z := by omega
  rw [carrierCost_eq_candidateLine rows R V r v z hr hz3]
  cases hsegments : q.segments with
  | nil =>
      simp only [hsegments] at hsegmentsSound
  | cons s₁ tail =>
      cases htail : tail with
      | nil =>
          have hsound :
              s₁.start = 3 ∧
                candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
                candidateSlope r v ≤ s₁.slope := by
            simpa only [hsegments, htail] using hsegmentsSound
          rcases hsound with ⟨hs₁Start, hlineStart, hslope⟩
          have hline := candidateLine_le_segment_of_start_and_slope
            rows R V r v z s₁ (by omega) (by omega) hlineStart hslope
          have heval : q.evalAt z = s₁.evalAt z := by
            simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail,
              hz0, hz1, hz2]
          rw [heval]
          exact hline
      | cons s₂ rest =>
          cases hrest : rest with
          | nil =>
              have hsound :
                  s₁.start = 3 ∧ s₁.start < s₂.start ∧
                    candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
                    candidateLine rows R V r v (s₂.start - 1) ≤
                      s₁.evalAt (s₂.start - 1) ∧
                    candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
                    candidateSlope r v ≤ s₂.slope := by
                simpa only [hsegments, htail, hrest] using hsegmentsSound
              rcases hsound with
                ⟨hs₁Start, hs₁₂, hlineStart, hlineFinish,
                  hlineSecond, hslopeSecond⟩
              by_cases hs₂z : s₂.start ≤ z
              · have hline := candidateLine_le_segment_of_start_and_slope
                  rows R V r v z s₂ (by omega) hs₂z hlineSecond
                    hslopeSecond
                have heval : q.evalAt z = s₂.evalAt z := by
                  simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail, hrest,
                    hz0, hz1, hz2, hs₂z]
                rw [heval]
                exact hline
              · have hzf : z ≤ s₂.start - 1 := by omega
                have hline := candidateLine_le_segment_between
                  rows R V r v z (s₂.start - 1) s₁
                    (by omega) (by omega) hzf hlineStart hlineFinish
                have heval : q.evalAt z = s₁.evalAt z := by
                  simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail, hrest,
                    hz0, hz1, hz2, hs₂z]
                rw [heval]
                exact hline
          | cons s₃ rest₃ =>
              simp only [hsegments, htail, hrest] at hsegmentsSound

theorem baseCandidatesSound_of_checks
    (rows : Array BaseRow) (hchecks : BaseCandidateChecks rows) :
    BaseCandidatesSound rows := by
  intro R V r v z hr hrR hvV hR hRV hfits htotal
  have hRpos : 1 ≤ R := hr.trans hrR
  have hRcheck := hchecks R (List.mem_range.mpr (by omega)) hRpos
  have hVcheck := hRcheck V (List.mem_range.mpr (by omega))
  have hrcheck := hVcheck r (List.mem_range.mpr (by omega)) hr
  have hcheck := hrcheck v (List.mem_range.mpr (by omega)) hfits
  exact candidateRowCheck_sound rows R V r v z hr hcheck

theorem ordinaryCostOf_eq_rawCost (p : FlagDegree) :
    LocatorHybridCost.ordinaryCostOf p =
      LocatorOrdinaryZConvex.rawCost p.all p.yz p.zOnly := by
  cases p
  rfl

/-- The `z = 0` part of `BaseCandidatesSound` is exactly the Bellman
inequality needed to aggregate an arbitrary finite zero-`z` family. -/
theorem sum_rawCost_zero_le_baseZeroCap
    (rows : Array BaseRow) (hrows : BaseCandidatesSound rows)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (r v : ι → ℕ)
    (hpositive : ∀ i ∈ s, 1 ≤ r i)
    (hrCap : (∑ i ∈ s, r i) ≤ 29)
    (hrvCap : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 135) :
    (∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) ≤
      baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseZeroCap]
  | @insert a s ha ih =>
      have hra : 1 ≤ r a := hpositive a (by simp)
      have hRInsert : r a + (∑ i ∈ s, r i) ≤ 29 := by
        simpa only [Finset.sum_insert ha] using hrCap
      have hRVInsert :
          (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ 135 := by
        rw [Finset.sum_insert ha, Finset.sum_insert ha] at hrvCap
        omega
      have hsR : (∑ i ∈ s, r i) ≤ 29 := by
        omega
      have hsRV : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 135 := by
        omega
      have ihBound := ih
        (fun i hi ↦ hpositive i (Finset.mem_insert_of_mem hi)) hsR hsRV
      have hfits : r a < r a + (∑ i ∈ s, r i) ∨
          v a = v a + (∑ i ∈ s, v i) := by
        by_cases hs : s.Nonempty
        · obtain ⟨i, hi⟩ := hs
          have hri : 1 ≤ r i :=
            hpositive i (Finset.mem_insert_of_mem hi)
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
        (r a) (v a) 0 hra (by omega) (by omega)
        hRInsert hRVInsert hfits
        (by omega)
      have hposSum : 1 ≤ r a + ∑ i ∈ s, r i := by omega
      calc
        (∑ i ∈ insert a s,
            LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) =
            LocatorOrdinaryZConvex.rawCost (r a) (v a) 0 +
              ∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
        _ ≤ LocatorOrdinaryZConvex.rawCost (r a) (v a) 0 +
              baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) :=
            Nat.add_le_add_left ihBound _
        _ ≤ baseTableCap rows
              (rawFlag (r a + ∑ i ∈ s, r i)
                (v a + ∑ i ∈ s, v i) 0) := by
            simpa only [Nat.add_sub_cancel_left] using hcandidate
        _ = baseZeroCap rows (∑ i ∈ insert a s, r i)
              (∑ i ∈ insert a s, v i) := by
            simp only [Finset.sum_insert ha, baseZeroCap,
              if_neg (Nat.ne_of_gt hposSum)]

/-- A checked carrier table gives the genuinely state-local base oracle.  The
proof first concentrates all `z` on one factor, bounds the remaining zero-`z`
family by the same Bellman table, and finally applies that carrier's row. -/
theorem stateLocalBaseOracleSound_of_candidates
    (rows : Array BaseRow) (hrows : BaseCandidatesSound rows) :
    StateLocalBaseOracleSound (baseTableCap rows) := by
  intro ι inst s p hpositive hrCap hyCap htCap
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨c, hc, hconcentrate⟩ :=
      LocatorOrdinaryConcentration.exists_z_carrier s
        (fun i ↦ (p i).all) (fun i ↦ (p i).yz) (fun i ↦ (p i).zOnly)
        hpositive hs
    have hzero := sum_rawCost_zero_le_baseZeroCap rows hrows (s.erase c)
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
        have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 135 := by
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
    have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 135 := by
      rw [sumFlag_middle] at hyCap
      simp only [middle, Finset.sum_add_distrib] at hyCap
      omega
    have htotal : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) +
        (∑ i ∈ s, (p i).zOnly) ≤ 6677 := by
      rw [sumFlag_total] at htCap
      simp only [total, middle, Finset.sum_add_distrib] at htCap
      omega
    have hrErase := Finset.sum_erase_add s (fun i ↦ (p i).all) hc
    have hvErase := Finset.sum_erase_add s (fun i ↦ (p i).yz) hc
    have hfits :
        (p c).all < ∑ i ∈ s, (p i).all ∨
          (p c).yz = ∑ i ∈ s, (p i).yz := by
      by_cases hrest : (s.erase c).Nonempty
      · obtain ⟨i, hi⟩ := hrest
        have hiS : i ∈ s := Finset.mem_of_mem_erase hi
        have hri : 1 ≤ (p i).all := hpositive i hiS
        have hriSum : (p i).all ≤ ∑ j ∈ s.erase c, (p j).all :=
          Finset.single_le_sum (f := fun j ↦ (p j).all)
            (fun _ _ ↦ Nat.zero_le _) hi
        left
        omega
      · have hrest0 : s.erase c = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hrest
        right
        rw [hrest0] at hvErase
        simp only [Finset.sum_empty] at hvErase
        omega
    have hcandidate := hrows
      (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
      (p c).all (p c).yz (∑ i ∈ s, (p i).zOnly)
      (hpositive c hc) hcR hcV hrCap hmiddle hfits htotal
    have hzero' :
        (∑ i ∈ s.erase c,
            LocatorOrdinaryZConvex.rawCost (p i).all (p i).yz 0) ≤
          baseZeroCap rows
            ((∑ i ∈ s, (p i).all) - (p c).all)
            ((∑ i ∈ s, (p i).yz) - (p c).yz) := by
      simpa only [show (∑ i ∈ s, (p i).all) - (p c).all =
          ∑ i ∈ s.erase c, (p i).all by omega,
        show (∑ i ∈ s, (p i).yz) - (p c).yz =
          ∑ i ∈ s.erase c, (p i).yz by omega] using hzero
    have hcostEq :
        (∑ i ∈ s, LocatorHybridCost.ordinaryCostOf (p i)) =
          ∑ i ∈ s, LocatorOrdinaryZConvex.rawCost
            (p i).all (p i).yz (p i).zOnly := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ordinaryCostOf_eq_rawCost (p i)
    have hflagEq : sumFlag s p =
        rawFlag (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
          (∑ i ∈ s, (p i).zOnly) := rfl
    rw [hcostEq, hflagEq]
    exact hconcentrate.trans ((Nat.add_le_add_left hzero' _).trans hcandidate)
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end ProximityPrize.SubmissionLower.LocatorPhase6800Audit
end PackedLocator_LocatorPhase6800Audit

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchPowerRoute. -/
section PackedLocator_LocatorBatchPowerRoute

/-!
# Counting consumer for shared regular-product power routes

`LocatorBatchProductRoute` selects the first strict post-projection factor
subset.  This file turns that algebraic stage into the helper bounds used by
the numerical phase recursion.  Source-specific gaps and receipt arithmetic
remain parameters here and are instantiated in the phase bridge.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute
  LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The exact cell box of a regular factor.  With this box `stageCost` is the
actual unequal-pair charge after the displayed number of source quotients. -/
def exactRouteBox {H : P4} (F : RegularIndex H) : PowerRouteBox where
  tLo := wt residualTotalWeights F.1
  tHi := wt residualTotalWeights F.1
  yLo := wt residualYSWeights F.1
  yHi := wt residualYSWeights F.1
  rLo := wt residualSWeights F.1
  rHi := wt residualSWeights F.1

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- Multiplying the low terminal quotient by the removed batch power returns
an original source row in the derivative-contact box. -/
theorem reconstruct_mem_low_of_batch_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (P J : P4)
    (heq : P ^ j * J = reconstruct K D 131071 L S v.1)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) J <
      Dlow - j * wt (contactWeights 131071) P) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have hmul := wt_mul_le (contactWeights 131071) (P ^ j) J
  have hp := wt_pow_le (contactWeights 131071) P j
  omega

/-- Convert a selected batch exit into per-factor helper charges.  The
consumer retains the complementary product in every helper, so no internal
collision locus is charged. -/
theorem counts_of_batchExitStage
    (D L S m YS delta fuel : ℕ)
    (hD : 0 < D) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181363 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (A : Finset (RegularIndex H))
    (q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4)
    (hproduct : ∀ v,
      reconstruct K D 131071 L S v.1 = regularProduct H A * q v)
    (hexit : HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) (regularProduct H A))
      131071 delta
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) H A q)
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgates : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let P := regularProduct H A
  change HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) P) 131071 delta
      (L - wt residualTotalWeights P) (YS - wt residualYSWeights P)
      (S - wt residualSWeights P) H A q at hexit
  obtain ⟨e, U, v, J, hUA, hv, hJ, heq, hbox, havoid⟩ := hexit
  let j := e.val + 1
  have hj : 1 ≤ j := by simp only [j]; omega
  have hjle : j ≤ fuel := by simp only [j]; omega
  have hjchar : j < 2130706433 := hjle.trans_lt hfuelChar
  have heqOriginal : P ^ j * J =
      reconstruct K D 131071 L S v.1 := by
    calc
      P ^ j * J = P * (P ^ e.val * J) := by
        simp only [j, pow_succ']
        ring
      _ = P * q v := by rw [heq]
      _ = reconstruct K D 131071 L S v.1 := (hproduct v).symm
  change J ∈ nestedCoefficientBox K
      (D - delta - wt (contactWeights 131071) P - e.val * delta -
        e.val * wt (contactWeights 131071) P) 131071
      (L - wt residualTotalWeights P - e.val * wt residualTotalWeights P)
      (YS - wt residualYSWeights P - e.val * wt residualYSWeights P)
      (S - wt residualSWeights P - e.val * wt residualSWeights P) at hbox
  have hweights := nested_mem_weights hbox hJ
  have hJT : wt residualTotalWeights J ≤
      L - j * wt residualTotalWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.1
  have hJY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.1
  have hJS : wt residualSWeights J ≤
      S - j * wt residualSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.2.1
  have hJcontact : wt (contactWeights 131071) J <
      D - j * delta - j * wt (contactWeights 131071) P := by
    have hc := hweights.2.2.2
    simp only [j, Nat.sub_sub, Nat.add_mul, one_mul] at hc ⊢
    omega
  have hlow : reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K (D - j * delta) 131071 L S :=
    reconstruct_mem_low_of_batch_power u0 u1 v P J heqOriginal hD
      (hlowpos j hj hjle) hJcontact
  have hPT : j * wt residualTotalWeights P ≤ L :=
    (Nat.mul_le_mul_right (wt residualTotalWeights P) hjle).trans hfeasible.1
  have hPY : j * wt residualYSWeights P ≤ YS :=
    (Nat.mul_le_mul_right (wt residualYSWeights P) hjle).trans hfeasible.2.1
  have hPS : j * wt residualSWeights P ≤ S :=
    (Nat.mul_le_mul_right (wt residualSWeights P) hjle).trans hfeasible.2.2
  refine ⟨U, hUA, ?_⟩
  intro F hFU
  have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFU)
  have hQbounds := liftedHelper_residual_bounds H A F hFA L YS S j J hJ
    hJT hJY hJS hPT hPY hPS
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma QF = 0 := by
    exact batch_helper_zero_on_regularSeeds j D (D - j * delta) 131071
      L S m 181363 2130706433
      (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
      IRSProfile.domain u0 u1 H A F hFA selected Gamma v J hj hjchar
      (by decide) hdegree hagreement (hcapacity j hj hjle) hlow
      heqOriginal
  have hstage := regularSeeds_count_le_stageCost L YS S
    (exactRouteBox F) j u0 u1 H selected Gamma hdegree hagreement hno F
    (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
    (degreeZ_le_totalWeight F.1) QF
    (by simpa only [exactRouteBox] using hQbounds.1)
    (by simpa only [exactRouteBox] using hQbounds.2.1)
    (by simpa only [exactRouteBox] using hQbounds.2.2)
    hrel (by simpa only [exactRouteBox] using hgates F hFA j hj hjle)
    hQzero
  exact hstage.trans (hcharge F hFA j hj hjle)

/-- A complete algebraic step for one fresh source.  Stage zero uses the
existing divisor-or-helper switch.  If the entire batch product divides the
source, it is removed once and the shared product-power selector finds a
later strict exit.  `hcharge` is the sole interface to the additive numerical
potential used by a phase receipt. -/
theorem exists_strict_helper_split_of_batch_source
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181363)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181363 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hband : powerBandBudget delta
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hwidth :
          D - wt (contactWeights 131071) (regularProduct H A) ≤
            (D - delta -
              wt (contactWeights 131071) (regularProduct H A)) + delta := by
        omega
      have hsource : powerBandBudget delta
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hband.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudget_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) hwidth q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))


/-! ## Contact-thinned consumer (lever S1): the band hypothesis is the thin budget. -/


theorem exists_strict_helper_split_of_batch_source_thin
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181363)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181363 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) delta
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hDlow :
          D - delta - wt (contactWeights 131071) (regularProduct H A) =
            (D - wt (contactWeights 131071) (regularProduct H A)) - delta := by
        omega
      have hsource : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (D - wt (contactWeights 131071) (regularProduct H A)) delta
          (wt (contactWeights 131071) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hbandThin.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudgetThin_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) (by decide) hDlow q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))


end

end ProximityPrize.SubmissionLower.LocatorBatchPowerRoute
end PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic. -/
section PackedLocator_LocatorFastKernelArithmetic

/-!
# Kernel-cheap arithmetic for large locator sources

The contact-rank bound is definitionally a sum of nested `Finset.range` sums.
For the larger replacement sources, evaluating that definition directly would
expand hundreds of millions of summands.  This file closes each rectangular
block symbolically and leaves only one primitive recursion over the contact
rows.  It also provides a primitive-recursive evaluator for coefficient
counts after the weighted cutoff has removed the long zero tail.
-/

namespace ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RCN302
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Number of entries in a rectangular block, weighted by the descending
affine function `L + 1 - offset - i - j`. -/
def rectangularCount (ni nj offset L : ℕ) : ℕ :=
  ni * nj * (L + 1 - offset) -
    (nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2))

private theorem pairIndexSum (ni nj : ℕ) :
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
      nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
  calc
    (∑ i ∈ Finset.range ni, ∑ j ∈ Finset.range nj, (i + j)) =
        ∑ i ∈ Finset.range ni,
          (nj * i + nj * (nj - 1) / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    _ = nj * (ni * (ni - 1) / 2) + ni * (nj * (nj - 1) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

theorem rectangularSum_eq_rectangularCount (ni nj offset L : ℕ)
    (hbound : offset + (ni - 1) + (nj - 1) ≤ L) :
    (∑ i ∈ Finset.range ni,
      ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) =
      rectangularCount ni nj offset L := by
  have hpoint : ∀ i ∈ Finset.range ni, ∀ j ∈ Finset.range nj,
      (L + 1 - offset - i - j) + (i + j) = L + 1 - offset := by
    intro i hi j hj
    have hil : i ≤ ni - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hjl : j ≤ nj - 1 := by
      have := Finset.mem_range.mp hj
      omega
    omega
  have hadd :
      (∑ i ∈ Finset.range ni,
        ∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
          (∑ i ∈ Finset.range ni,
            ∑ j ∈ Finset.range nj, (i + j)) =
        ni * nj * (L + 1 - offset) := by
    calc
      _ = ∑ i ∈ Finset.range ni,
          ((∑ j ∈ Finset.range nj, (L + 1 - offset - i - j)) +
            ∑ j ∈ Finset.range nj, (i + j)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ Finset.range ni,
          ∑ j ∈ Finset.range nj,
            ((L + 1 - offset - i - j) + (i + j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_add_distrib.symm
      _ = ∑ i ∈ Finset.range ni,
          ∑ _j ∈ Finset.range nj, (L + 1 - offset) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i hi j hj
      _ = ni * nj * (L + 1 - offset) := by
          simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
          ring
  rw [pairIndexSum] at hadd
  unfold rectangularCount
  omega

theorem blockInputCount_eq_rectangularCount (M L s : ℕ)
    (hbound : M + s ≤ L) :
    blockInputCount M L s = rectangularCount (M + 1) (s + 1) 0 L := by
  simpa only [blockInputCount, Nat.zero_add, Nat.sub_zero] using
    rectangularSum_eq_rectangularCount (M + 1) (s + 1) 0 L (by omega)

theorem blockKernelLowerBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    blockKernelLowerBound M L s h =
      rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL : h ≤ L := by omega
      have hshape : M - h + (s - h) ≤ L - h := by omega
      have heq : blockKernelLowerBound M L s h =
          blockInputCount (M - h) (L - h) (s - h) := by
        have hMr : M + 1 - h = M - h + 1 := by omega
        have hsr : s + 1 - h = s - h + 1 := by omega
        have hLr : L + 1 - h = L - h + 1 := by omega
        unfold blockKernelLowerBound blockInputCount
        rw [hMr, hsr, hLr]
      rw [heq, blockInputCount_eq_rectangularCount _ _ _ hshape]
      have hMr : M + 1 - h = M - h + 1 := by omega
      have hsr : s + 1 - h = s - h + 1 := by omega
      have hLr : L + 1 - h = L - h + 1 := by omega
      unfold rectangularCount
      rw [hMr, hsr, hLr]
      simp only [Nat.sub_zero]
    · have hz : s + 1 - h = 0 := by omega
      simp [blockKernelLowerBound, rectangularCount, hz]
  · have hz : M + 1 - h = 0 := by omega
    simp [blockKernelLowerBound, rectangularCount, hz]

theorem contactRankBound_eq_rectangularCount (M L s h : ℕ)
    (hbound : M + s ≤ L) :
    contactRankBound M L s h =
      rectangularCount (M + 1) (s + 1) 0 L -
        rectangularCount (M + 1 - h) (s + 1 - h) h L := by
  unfold contactRankBound
  rw [blockInputCount_eq_rectangularCount M L s hbound,
    blockKernelLowerBound_eq_rectangularCount M L s h hbound]

/-- The same local rank as `RCN119.localRankBound`, but every rectangular
block is closed and the sole remaining sum uses primitive recursion. -/
def fastLocalRankBound (m L s : ℕ) : ℕ :=
  kernelSumRange (fun r =>
    let M := min r L
    let h := min (r + 1) (m - r)
    rectangularCount (M + 1) (s + 1) 0 L -
      rectangularCount (M + 1 - h) (s + 1 - h) h L) m

theorem localRankBound_eq_fastLocalRankBound (m L s : ℕ)
    (hshape : m + s ≤ L + 1) :
    localRankBound m L s = fastLocalRankBound m L s := by
  unfold localRankBound fastLocalRankBound
  rw [kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r < m := Finset.mem_range.mp hr
  have hb : min r L + s ≤ L := by
    have hm : min r L ≤ r := Nat.min_le_left _ _
    omega
  exact contactRankBound_eq_rectangularCount
    (min r L) L s (min (r + 1) (m - r)) hb

/-- Coefficient count with the weighted zero tail removed and both finite sums
represented by primitive recursion. -/
def fastCoefficientCount (D w L s cutoff : ℕ) : ℕ :=
  kernelSumRange (fun i =>
    kernelSumRange (fun j =>
      (L + 1 - i - j) * (D - w * i - (w - 1) * j)) (s + 1)) cutoff


/-! The primitive evaluator above is already much cheaper than the original
nested `Finset` computation, but it still performs `cutoff * (s + 1)` steps.
The inner summand is quadratic, so the following evaluator closes each row and
performs only `cutoff` primitive steps. -/

private def triangularCount (n : ℕ) : ℕ := n * (n - 1) / 2

private def squareCount (n : ℕ) : ℕ :=
  n * (n - 1) * (2 * n - 1) / 6





/-- Closed value of `sum_{j<N} (A-j)*(B-c*j)` when neither subtraction
truncates on that range. -/
private def quadraticDescendingCount (A B c N : ℕ) : ℕ :=
  N * (A * B) + c * squareCount N -
    (A * c + B) * triangularCount N



/-- Closed form for one coefficient-count row.  `J` is the last index before
either descending factor becomes truncated, so all later terms are zero. -/
def closedCoefficientRow (D w L s i : ℕ) : ℕ :=
  let A := L + 1 - i
  let B := D - w * i
  let c := w - 1
  let J := min s (min (L - i) (B / c))
  quadraticDescendingCount A B c (J + 1)


/-- Coefficient count with a closed inner row and one primitive outer sum. -/
def fastClosedCoefficientCount (D w L s cutoff : ℕ) : ℕ :=
  kernelSumRange (closedCoefficientRow D w L s) cutoff


/-! ## Constant-time coefficient count in the one-residue regime

For the large power sources used by the 6800 locator, write `D = q*w+r`.
Their entire slope range satisfies `r+s <= w`.  Hence, in slope row `j`,
the nonzero weighted columns are exactly `0,...,q-j`.  Reflecting those
columns and summing the resulting quadratic gives a linear combination of
`choose (q+1-j) 1`, `choose (q+1-j) 2`, and `choose (q+1-j) 3`.
The hockey-stick identity then closes the remaining slope sum.  Numerical
evaluation below uses descending factorials, so its cost depends only on the
fixed indices `2,3,4`, rather than on `q` or `s`.
-/

private theorem two_mul_choose_two_add (n : ℕ) :
    2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        2 * (n + n.choose 2) + (n + 1) =
            (2 * n.choose 2 + n) + (2 * n + 1) := by ring
        _ = n * n + (2 * n + 1) := by rw [ih]
        _ = (n + 1) * (n + 1) := by ring

private theorem kernelSumRange_square_eq_choose (n : ℕ) :
    kernelSumRange (fun i => i * i) n =
      2 * n.choose 3 + n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [kernelSumRange_succ, ih, Nat.choose_succ_succ,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      rw [← two_mul_choose_two_add n]
      ring

private theorem finset_sum_range_square_eq_choose (n : ℕ) :
    (∑ i ∈ Finset.range n, i * i) =
      2 * n.choose 3 + n.choose 2 := by
  rw [← kernelSumRange_eq, kernelSumRange_square_eq_choose]

private theorem sum_increasingProduct_eq_choose (U C w N : ℕ) :
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
      N * (U * C) + (U * w + C) * N.choose 2 +
        w * (2 * N.choose 3 + N.choose 2) := by
  calc
    (∑ h ∈ Finset.range N, (U + h) * (C + w * h)) =
        ∑ h ∈ Finset.range N,
          (U * C + (U * w + C) * h + w * (h * h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = N * (U * C) + (U * w + C) * N.choose 2 +
          w * (2 * N.choose 3 + N.choose 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_id,
        finset_sum_range_square_eq_choose, ← Nat.choose_two_right]

private theorem three_mul_choose_three_add_two_mul_choose_two (n : ℕ) :
    3 * n.choose 3 + 2 * n.choose 2 = n * n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      calc
        3 * (n.choose 2 + n.choose 3) +
              2 * (n + n.choose 2) =
            (3 * n.choose 3 + 2 * n.choose 2) +
              (2 * n.choose 2 + n) + (n.choose 2 + n) := by ring
        _ = n * n.choose 2 + n * n + (n.choose 2 + n) := by
          rw [ih, two_mul_choose_two_add]
        _ = (n + 1) * (n + n.choose 2) := by ring

private theorem oneResidueRow_algebra
    (U C w r j q N wm T V : ℕ)
    (hC : C = r + j) (hN : N + j = q + 1) (hw : wm + 2 = w)
    (hsq : 2 * T + N = N * N)
    (hcub : 3 * V + 2 * T = N * T) :
    N * (U * C) + (U * w + C) * T + w * (2 * V + T) =
      U * (r + q) * N +
        (U * wm + r + q + (wm + 1)) * T +
          (2 * wm + 1) * V := by
  have hCz : (C : ℤ) = (r : ℤ) + j := by exact_mod_cast hC
  have hNz : (N : ℤ) + j = (q : ℤ) + 1 := by exact_mod_cast hN
  have hwz : (wm : ℤ) + 2 = w := by exact_mod_cast hw
  have hsqz : 2 * (T : ℤ) + N = N * N := by exact_mod_cast hsq
  have hcubz : 3 * (V : ℤ) + 2 * T = N * T := by exact_mod_cast hcub
  have hqz : (q : ℤ) = N + j - 1 := by linarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [hCz, ← hwz, hqz]
  linear_combination (U : ℤ) * hsqz + hcubz

/-- The three binomial coefficients of one slope row after reflecting its
weighted columns. -/
private def oneResidueCoefficientRow (q r w L j : ℕ) : ℕ :=
  let U := L + 1 - q
  let N := q + 1 - j
  U * (r + q) * N.choose 1 +
    (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
      (2 * (w - 2) + 1) * N.choose 3

private theorem coefficientColumn_eq_oneResidueCoefficientRow
    (q r w L j : ℕ) (hw : 2 ≤ w) (hj : j ≤ q)
    (hL : q ≤ L) (hres : r + j ≤ w) :
    (∑ i ∈ Finset.range (q + 1),
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) =
      oneResidueCoefficientRow q r w L j := by
  let N := q + 1 - j
  let U := L + 1 - q
  let C := r + j
  have hNpos : 0 < N := by simp only [N]; omega
  have hNq : N ≤ q + 1 := by simp only [N]; omega
  have hsubset : Finset.range N ⊆ Finset.range (q + 1) :=
    Finset.range_mono hNq
  have htrim :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ i ∈ Finset.range (q + 1),
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j) := by
    apply Finset.sum_subset hsubset
    intro i hi hinot
    have hiq : i ≤ q := by
      have := Finset.mem_range.mp hi
      omega
    have hiN : N ≤ i := by
      by_contra hni
      exact hinot (Finset.mem_range.mpr (by omega))
    have hij : q + 1 ≤ i + j := by simp only [N] at hiN; omega
    have hr : r ≤ w - j := by omega
    have hmul : w * (q + 1) ≤ w * (i + j) :=
      Nat.mul_le_mul_left w hij
    have hwj : w * j - j = (w - 1) * j := by
      symm
      rw [Nat.sub_mul]
      simp only [Nat.one_mul]
    have hweight : q * w + r ≤ w * i + (w - 1) * j := by
      calc
        q * w + r ≤ q * w + (w - j) := Nat.add_le_add_left hr _
        _ = w * (q + 1) - j := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
          omega
        _ ≤ w * (i + j) - j := Nat.sub_le_sub_right hmul j
        _ = w * i + (w - 1) * j := by
          have hjwj : j ≤ w * j :=
            Nat.le_mul_of_pos_left j (by omega)
          rw [Nat.mul_add, Nat.add_sub_assoc hjwj, hwj]
    have hz : q * w + r - w * i - (w - 1) * j = 0 := by
      rw [Nat.sub_sub]
      exact Nat.sub_eq_zero_of_le hweight
    simp only [hz, Nat.mul_zero]
  have hreflect :
      (∑ i ∈ Finset.range N,
        (L + 1 - i - j) *
          (q * w + r - w * i - (w - 1) * j)) =
      ∑ h ∈ Finset.range N, (U + h) * (C + w * h) := by
    rw [← Finset.sum_range_reflect (fun i =>
      (L + 1 - i - j) *
        (q * w + r - w * i - (w - 1) * j)) N]
    apply Finset.sum_congr rfl
    intro h hh
    have hhN : h < N := Finset.mem_range.mp hh
    have hidx : N - 1 - h = q - j - h := by
      simp only [N]
      omega
    have hqsplit : q = (q - j - h) + j + h := by omega
    have hwj : w * j = (w - 1) * j + j := by
      have hw' : w - 1 + 1 = w := by omega
      calc
        w * j = (w - 1 + 1) * j := by rw [hw']
        _ = (w - 1) * j + j := by ring
    have htotal :
        q * w + r = w * (q - j - h) + (w - 1) * j +
          (r + j + w * h) := by
      calc
        q * w + r = ((q - j - h) + j + h) * w + r := by rw [← hqsplit]
        _ = w * (q - j - h) + w * j + w * h + r := by ring
        _ = w * (q - j - h) + (w - 1) * j +
            (r + j + w * h) := by rw [hwj]; ring
    have hfirst : L + 1 - (N - 1 - h) - j = U + h := by
      simp only [N, U]
      omega
    have hsecond :
        q * w + r - w * (N - 1 - h) - (w - 1) * j =
          C + w * h := by
      rw [hidx]
      simp only [C]
      omega
    rw [hfirst, hsecond]
  have hsum := sum_increasingProduct_eq_choose U C w N
  have hNj : N + j = q + 1 := by simp only [N]; omega
  have hwsub : w - 2 + 2 = w := by omega
  have hsq := two_mul_choose_two_add N
  have hcub := three_mul_choose_three_add_two_mul_choose_two N
  rw [← htrim, hreflect, hsum]
  change N * (U * C) + (U * w + C) * N.choose 2 +
      w * (2 * N.choose 3 + N.choose 2) =
    U * (r + q) * N.choose 1 +
      (U * (w - 2) + r + q + ((w - 2) + 1)) * N.choose 2 +
        (2 * (w - 2) + 1) * N.choose 3
  simp only [Nat.choose_one_right]
  exact oneResidueRow_algebra
    (U := U) (C := C) (w := w) (r := r) (j := j) (q := q)
    (N := N) (wm := w - 2) (T := N.choose 2) (V := N.choose 3)
    (by rfl) hNj hwsub hsq hcub

private theorem sum_range_choose_descending_add (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) +
        (N - s).choose (k + 1) = (N + 1).choose (k + 1) := by
  induction s with
  | zero =>
      simp only [Nat.sub_zero, Finset.range_one, Finset.sum_singleton]
      exact (Nat.choose_succ_succ' N k).symm
  | succ s ih =>
      have hs' : s ≤ N := by omega
      rw [Finset.sum_range_succ]
      have hold := ih hs'
      have hpred : N - s = (N - (s + 1)) + 1 := by omega
      have hp := Nat.choose_succ_succ' (N - (s + 1)) k
      rw [← hpred] at hp
      omega

private theorem sum_range_choose_descending (N s k : ℕ)
    (hs : s ≤ N) :
    (∑ j ∈ Finset.range (s + 1), (N - j).choose k) =
      (N + 1).choose (k + 1) - (N - s).choose (k + 1) := by
  have h := sum_range_choose_descending_add N s k hs
  omega

/-- `Nat.choose` evaluated through a descending factorial.  In this file it
is used only at indices at most four, so closed source receipts do not recurse
through a thousand Pascal rows. -/
def smallChoose (n k : ℕ) : ℕ :=
  n.descFactorial k / Nat.factorial k

private theorem choose_eq_smallChoose (n k : ℕ) :
    n.choose k = smallChoose n k := by
  simpa only [smallChoose] using
    Nat.choose_eq_descFactorial_div_factorial n k

/-- Constant-time coefficient count for `D=q*w+r` when the complete slope
range remains in the first residue regime. -/
def oneResidueCoefficientCount (q r w L s : ℕ) : ℕ :=
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  c1 * (smallChoose (q + 2) 2 - smallChoose (q + 1 - s) 2) +
    c2 * (smallChoose (q + 2) 3 - smallChoose (q + 1 - s) 3) +
      c3 * (smallChoose (q + 2) 4 - smallChoose (q + 1 - s) 4)

theorem coefficientCount_eq_oneResidueCoefficientCount
    (q r w L s : ℕ) (hw : 2 ≤ w) (hsq : s ≤ q)
    (hL : q ≤ L) (hres : r + s ≤ w) :
    coefficientCount (q * w + r) w L s =
      oneResidueCoefficientCount q r w L s := by
  have hcutoff : q + 1 ≤ L + 1 := by omega
  have hweight : q * w + r ≤ w * (q + 1) := by
    have hrw : r ≤ w := by omega
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w q]
    omega
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (q * w + r) w L s (q + 1) hcutoff hweight]
  rw [Finset.sum_comm]
  have hrows :
      (∑ j ∈ Finset.range (s + 1),
        ∑ i ∈ Finset.range (q + 1),
          (L + 1 - i - j) *
            (q * w + r - w * i - (w - 1) * j)) =
      ∑ j ∈ Finset.range (s + 1),
        oneResidueCoefficientRow q r w L j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hj
      omega
    exact coefficientColumn_eq_oneResidueCoefficientRow q r w L j hw
      (hjs.trans hsq) hL ((Nat.add_le_add_left hjs r).trans hres)
  rw [hrows]
  let U := L + 1 - q
  let c1 := U * (r + q)
  let c2 := U * (w - 2) + r + q + ((w - 2) + 1)
  let c3 := 2 * (w - 2) + 1
  have h1 := sum_range_choose_descending (q + 1) s 1 (by omega)
  have h2 := sum_range_choose_descending (q + 1) s 2 (by omega)
  have h3 := sum_range_choose_descending (q + 1) s 3 (by omega)
  unfold oneResidueCoefficientRow
  change (∑ j ∈ Finset.range (s + 1),
      (c1 * (q + 1 - j).choose 1 +
        c2 * (q + 1 - j).choose 2 +
          c3 * (q + 1 - j).choose 3)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
  unfold oneResidueCoefficientCount
  rw [← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose,
    ← choose_eq_smallChoose, ← choose_eq_smallChoose]

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

/-- A numerical nullity receipt for any source profile gives the dimension
needed by the arbitrary-power route, uniformly in the two received words. -/
theorem challengeConstraintKernel_finrank_lower_bound_of_numeric
    (D L s m gap : ℕ) (u0 u1 : I → K)
    (hnumeric : gap ≤ coefficientCount D 131071 L s -
      262144 * localRankBound m L s) :
    gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L s m
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    (K := K) D 131071 L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hnumeric.trans hlo'

end ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic
end PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Parameters. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Coefficient. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankA. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankB. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankC. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankD. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankE. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankF. -/


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower
end Compact_PackedLocatorTail
