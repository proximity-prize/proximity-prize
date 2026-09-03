import ProximityPrize.SubmissionLower.LocatorPhase6800Audit
import ProximityPrize.SubmissionLower.LocatorPhase6800BaseDirectData

/-!
# Base-table soundness over direct `(R,V)` lookup

The dummy array parameter lets this module reuse the already-audited proof
text exactly.  Its local lookup ignores the array; all closed computations
therefore reduce only the selected `rowRR V` branch.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseDirectAudit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

def lookupBaseRow (_rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  LocatorPhase6800BaseDirectData.lookup r v

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def baseZeroCap (rows : Array BaseRow) (r v : ℕ) : ℕ :=
  if r = 0 then 0 else baseTableCap rows (rawFlag r v 0)

/-- The sole semantic arithmetic condition required of the compact base
table.  It is finite on the benchmark box.  For every possible carrier
`(r,v)`, the row for the aggregate `(R,V)` dominates that carrier with all
remaining factors charged to the zero-`z` table. -/
def BaseCandidatesSound (rows : Array BaseRow) : Prop :=
  ∀ R V r v z,
    1 ≤ r → r ≤ R → v ≤ V → R ≤ 28 → R + V ≤ 127 →
    (r < R ∨ v = V) → R + V + z ≤ 5964 →
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z)

/-- Slope of the carrier's affine ordinary-cost tail, valid from `z = 3`. -/
def candidateSlope (r v : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 4 -
    LocatorOrdinaryZConvex.rawCost r v 3

/-- Carrier line after adding the exact zero-`z` residual-table value. -/
def candidateLine (rows : Array BaseRow) (R V r v z : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 3 +
    baseZeroCap rows (R - r) (V - v) + candidateSlope r v * (z - 3)

theorem carrierCost_eq_candidateLine
    (rows : Array BaseRow) (R V r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) =
      candidateLine rows R V r v z := by
  rw [LocatorOrdinaryZConvex.rawCost_affine_from_three r v z hr hz]
  unfold candidateLine candidateSlope
  omega

theorem candidateLine_shift
    (rows : Array BaseRow) (R V r v start z : ℕ)
    (hstart : 3 ≤ start) (hz : start ≤ z) :
    candidateLine rows R V r v z =
      candidateLine rows R V r v start + candidateSlope r v * (z - start) := by
  unfold candidateLine
  have hsplit : z - 3 = (start - 3) + (z - start) := by omega
  rw [hsplit, Nat.mul_add]
  omega

/-- Two affine natural-number functions ordered at the left endpoint remain
ordered when the lower function has no larger slope. -/
theorem affine_le_of_start_and_slope
    (a A m M d : ℕ) (ha : a ≤ A) (hm : m ≤ M) :
    a + m * d ≤ A + M * d := by
  exact Nat.add_le_add ha (Nat.mul_le_mul_right d hm)

/-- Endpoint domination suffices on a finite interval even when the candidate
line has the larger slope. -/
theorem affine_le_between
    (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A)
    (hend : a + m * finish ≤ A + M * finish) :
    a + m * d ≤ A + M * d := by
  by_cases hm : m ≤ M
  · exact affine_le_of_start_and_slope a A m M d hstart hm
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M + (m - M) = m := Nat.add_sub_of_le hMm
    have hdeltaFinish : a + (m - M) * finish ≤ A := by
      rw [← hdecomp, Nat.add_mul] at hend
      omega
    have hdelta : (m - M) * d ≤ (m - M) * finish :=
      Nat.mul_le_mul_left (m - M) hd
    rw [← hdecomp, Nat.add_mul]
    omega

theorem candidateLine_le_segment_of_start_and_slope
    (rows : Array BaseRow) (R V r v z : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hslope : candidateSlope r v ≤ s.slope) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  unfold BaseSegment.evalAt
  exact affine_le_of_start_and_slope _ _ _ _ _ hstart hslope

theorem candidateLine_le_segment_between
    (rows : Array BaseRow) (R V r v z finish : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z) (hzf : z ≤ finish)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hfinish : candidateLine rows R V r v finish ≤ s.evalAt finish) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  have hsf : s.start ≤ finish := hsz.trans hzf
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  rw [candidateLine_shift rows R V r v s.start finish hs3 hsf] at hfinish
  unfold BaseSegment.evalAt at hfinish ⊢
  apply affine_le_between _ _ _ _ _ _
  · exact Nat.sub_le_sub_right hzf s.start
  · exact hstart
  · exact hfinish

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
  ∀ V ∈ List.range (128 - R),
    ∀ r ∈ List.range (R + 1), 1 ≤ r →
      ∀ v ∈ List.range (V + 1), (r < R ∨ v = V) →
        CandidateRowCheck rows R V r v

instance (rows : Array BaseRow) (R : ℕ) : Decidable (CandidateRCheck rows R) := by
  unfold CandidateRCheck
  infer_instance

/-- Complete finite base-table checker.  Its executable domain has only the
2.443-million aggregate/carrier splits, not a `z` grid. -/
def BaseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R ∈ List.range 29, 1 ≤ R → CandidateRCheck rows R

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
    (hrCap : (∑ i ∈ s, r i) ≤ 28)
    (hrvCap : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 127) :
    (∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) ≤
      baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseZeroCap]
  | @insert a s ha ih =>
      have hra : 1 ≤ r a := hpositive a (by simp)
      have hRInsert : r a + (∑ i ∈ s, r i) ≤ 28 := by
        simpa only [Finset.sum_insert ha] using hrCap
      have hRVInsert :
          (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ 127 := by
        rw [Finset.sum_insert ha, Finset.sum_insert ha] at hrvCap
        omega
      have hsR : (∑ i ∈ s, r i) ≤ 28 := by
        omega
      have hsRV : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 127 := by
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
        have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 127 := by
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
    have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 127 := by
      rw [sumFlag_middle] at hyCap
      simp only [middle, Finset.sum_add_distrib] at hyCap
      omega
    have htotal : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) +
        (∑ i ∈ s, (p i).zOnly) ≤ 5964 := by
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

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseDirectAudit
