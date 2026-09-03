import ProximityPrize.SubmissionLower.LocatorPhase6802BaseDirectData

/-!
# Compact certificates for the sparse base checker

All executable checks in this module use literal cached costs.  The generic
lemmas transfer those checks to `rawCost` through the separately checked
carrier-cost receipt.  There is no metaprogramming in the submission source.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhaseBaseSparseCoreC2

open LocatorPhase6802Oracle LocatorOrdinaryZConvexC2
open LocatorPhaseBaseC2 LocatorPhaseBaseSparseBridgeC2

set_option autoImplicit false
set_option maxRecDepth 100000

structure Costs where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

abbrev CarrierCorrect (_r _v : ℕ) : Prop := True

def carrierCosts (r v : ℕ) : Costs :=
  ⟨rawCost r v 0, rawCost r v 1, rawCost r v 2,
    rawCost r v 3, rawCost r v 4⟩

/-- The affine continuation encoded by the five cached carrier values. -/
def costAt (c : Costs) (z : ℕ) : ℕ :=
  if z = 0 then c.c0
  else if z = 1 then c.c1
  else if z = 2 then c.c2
  else c.c3 + (c.c4 - c.c3) * (z - 3)

theorem costAt_eq_rawCost (r v z : ℕ) (hr : 1 ≤ r)
    (_hc : CarrierCorrect r v) :
    costAt (carrierCosts r v) z = rawCost r v z := by
  by_cases hz0 : z = 0
  · subst z
    simp [costAt, carrierCosts]
  by_cases hz1 : z = 1
  · subst z
    simp [costAt, carrierCosts]
  by_cases hz2 : z = 2
  · subst z
    simp [costAt, carrierCosts]
  have hz3 : 3 ≤ z := by omega
  rw [rawCost_affine_from_three r v z hr hz3]
  simp [costAt, carrierCosts, hz0, hz1, hz2]

/-- Coefficientwise order of two cached affine cost curves. -/
def CurveLE (a b : Costs) : Prop :=
  a.c0 ≤ b.c0 ∧ a.c1 ≤ b.c1 ∧ a.c2 ≤ b.c2 ∧ a.c3 ≤ b.c3 ∧
    a.c4 - a.c3 ≤ b.c4 - b.c3

instance (a b : Costs) : Decidable (CurveLE a b) := by
  unfold CurveLE
  infer_instance

theorem costAt_le_of_curveLE (a b : Costs)
    (h : CurveLE a b) (z : ℕ) : costAt a z ≤ costAt b z := by
  rcases h with ⟨h0, h1, h2, h3, hs⟩
  by_cases hz0 : z = 0
  · simpa [costAt, hz0] using h0
  by_cases hz1 : z = 1
  · simpa [costAt, hz0, hz1] using h1
  by_cases hz2 : z = 2
  · simpa [costAt, hz0, hz1, hz2] using h2
  simp only [costAt, hz0, hz1, hz2, if_false]
  exact Nat.add_le_add h3 (Nat.mul_le_mul_right (z - 3) hs)

/-- Coefficientwise midpoint convexity of three cached affine curves. -/
def CurveConvex (a b c : Costs) : Prop :=
  2 * b.c0 ≤ a.c0 + c.c0 ∧
  2 * b.c1 ≤ a.c1 + c.c1 ∧
  2 * b.c2 ≤ a.c2 + c.c2 ∧
  2 * b.c3 ≤ a.c3 + c.c3 ∧
  2 * (b.c4 - b.c3) ≤ (a.c4 - a.c3) + (c.c4 - c.c3)

instance (a b c : Costs) : Decidable (CurveConvex a b c) := by
  unfold CurveConvex
  infer_instance

theorem costAt_convex_of_curveConvex (a b c : Costs)
    (h : CurveConvex a b c) (z : ℕ) :
    2 * costAt b z ≤ costAt a z + costAt c z := by
  rcases h with ⟨h0, h1, h2, h3, hs⟩
  by_cases hz0 : z = 0
  · simpa [costAt, hz0] using h0
  by_cases hz1 : z = 1
  · simpa [costAt, hz0, hz1] using h1
  by_cases hz2 : z = 2
  · simpa [costAt, hz0, hz1, hz2] using h2
  simp only [costAt, hz0, hz1, hz2, if_false]
  have hsm := Nat.mul_le_mul_right (z - 3) hs
  calc
    2 * (b.c3 + (b.c4 - b.c3) * (z - 3)) =
        2 * b.c3 + 2 * (b.c4 - b.c3) * (z - 3) := by ring
    _ ≤ (a.c3 + c.c3) +
        ((a.c4 - a.c3) + (c.c4 - c.c3)) * (z - 3) :=
      Nat.add_le_add h3 hsm
    _ = (a.c3 + (a.c4 - a.c3) * (z - 3)) +
        (c.c3 + (c.c4 - c.c3) * (z - 3)) := by ring

/-- Exact direct base-table zero value.  Bounded shape hypotheses ensure that
the default branch of the total lookup is never observed. -/
def zeroDirect (r v : ℕ) : ℕ :=
  if r = 0 then 0 else (LocatorPhase6802BaseDirectData.lookup r v).z0

theorem zeroDirect_eq_baseZeroCap (r v : ℕ) :
    zeroDirect r v =
      baseZeroCap LocatorPhase6802BaseDirectData.lookup r v := by
  unfold zeroDirect LocatorPhaseBaseC2.baseZeroCap
    LocatorPhaseBaseC2.baseTableCap
    LocatorPhaseBaseC2.lookupBaseRow
  simp only [rawFlag, BaseRow.evalAt, if_pos]

def cachedSlope (r v : ℕ) : ℕ :=
  let c := carrierCosts r v
  c.c4 - c.c3

def cachedLine (R V r v z : ℕ) : ℕ :=
  (carrierCosts r v).c3 + zeroDirect (R - r) (V - v) +
    cachedSlope r v * (z - 3)

/-- Cached form of `CandidateRowCheck`; every arithmetic leaf is a direct
literal lookup. -/
def CachedCandidateRowCheck (R V r v : ℕ) : Prop :=
  let q := LocatorPhase6802BaseDirectData.lookup R V
  let c := carrierCosts r v
  let zero := zeroDirect (R - r) (V - v)
  c.c0 + zero ≤ q.z0 ∧
  c.c1 + zero ≤ q.z1 ∧
  c.c2 + zero ≤ q.z2 ∧
  match q.segments with
  | [s] =>
      s.start = 3 ∧ cachedLine R V r v s.start ≤ s.valueAtStart ∧
        cachedSlope r v ≤ s.slope
  | [s₁, s₂] =>
      s₁.start = 3 ∧ s₁.start < s₂.start ∧
        cachedLine R V r v s₁.start ≤ s₁.valueAtStart ∧
        cachedLine R V r v (s₂.start - 1) ≤ s₁.evalAt (s₂.start - 1) ∧
        cachedLine R V r v s₂.start ≤ s₂.valueAtStart ∧
        cachedSlope r v ≤ s₂.slope
  | _ => False

instance (R V r v : ℕ) : Decidable (CachedCandidateRowCheck R V r v) := by
  unfold CachedCandidateRowCheck
  dsimp only
  generalize hq : LocatorPhase6802BaseDirectData.lookup R V = q
  cases hs : q.segments with
  | nil => simp only [hs]; infer_instance
  | cons s tail =>
      cases ht : tail with
      | nil => simp only [hs, ht]; infer_instance
      | cons s₂ rest =>
          cases hu : rest with
          | nil => simp only [hs, ht, hu]; infer_instance
          | cons s₃ rest₃ => simp only [hs, ht, hu]; infer_instance

theorem candidateRowCheck_of_cached
    (R V r v : ℕ) (_hc : CarrierCorrect r v)
    (h : CachedCandidateRowCheck R V r v) :
    CandidateRowCheck LocatorPhase6802BaseDirectData.lookup R V r v := by
  unfold CachedCandidateRowCheck at h
  unfold CandidateRowCheck
  dsimp only
  simp only [LocatorPhaseBaseC2.lookupBaseRow,
    zeroDirect_eq_baseZeroCap] at h ⊢
  unfold cachedLine cachedSlope at h
  unfold candidateLine candidateSlope
  dsimp only [carrierCosts] at h ⊢
  exact h

def rBoundaryValues (R : ℕ) : List ℕ := [R, 1, R - 1]
def vBoundaryValues (V : ℕ) : List ℕ := [0, 1, 2, V - 2, V - 1, V]

theorem mem_rBoundaryValues (R r : ℕ) (h : RBoundary R r) :
    r ∈ rBoundaryValues R := by
  rcases h with h | h | h
  · simp [rBoundaryValues, h]
  · simp [rBoundaryValues, h]
  · simp [rBoundaryValues]
    omega

theorem mem_vBoundaryValues (V v : ℕ) (hv : v ≤ V)
    (h : VBoundary V v) : v ∈ vBoundaryValues V := by
  simp only [vBoundaryValues, List.mem_cons, List.mem_singleton]
  rcases h with h | h <;> omega

/-- At most thirteen useful carrier checks for a fixed aggregate cell. -/
def CachedSparseCell (R V : ℕ) : Prop :=
  ∀ r ∈ rBoundaryValues R, ∀ v ∈ vBoundaryValues V,
    1 ≤ r → r ≤ R → v ≤ V → (r < R ∨ v = V) →
      CachedCandidateRowCheck R V r v

instance (R V : ℕ) : Decidable (CachedSparseCell R V) := by
  unfold CachedSparseCell
  infer_instance

def CachedSparseLayer (R : ℕ) : Prop :=
  ∀ V ∈ List.range (133 - R), CachedSparseCell R V

instance (R : ℕ) : Decidable (CachedSparseLayer R) := by
  unfold CachedSparseLayer
  infer_instance

def CachedSparseAll : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R → CachedSparseLayer R

instance : Decidable CachedSparseAll := by
  unfold CachedSparseAll
  infer_instance

/-- Literal shape checks rooted at one positive carrier coordinate. -/
def CachedShapeCell (r v : ℕ) : Prop :=
  (r + 1 ≤ 29 → r + 1 + v ≤ 132 →
    CurveLE (carrierCosts r v) (carrierCosts (r + 1) v) ∧
      zeroDirect r v ≤ zeroDirect (r + 1) v) ∧
  (r + 2 ≤ 29 → r + 2 + v ≤ 132 →
    CurveConvex (carrierCosts r v) (carrierCosts (r + 1) v)
        (carrierCosts (r + 2) v) ∧
      2 * zeroDirect (r + 1) v ≤ zeroDirect r v + zeroDirect (r + 2) v) ∧
  (2 ≤ v → r + (v + 1) ≤ 132 →
    CurveLE (carrierCosts r v) (carrierCosts r (v + 1)) ∧
      zeroDirect r v ≤ zeroDirect r (v + 1)) ∧
  (2 ≤ v → r + (v + 2) ≤ 132 →
    CurveConvex (carrierCosts r v) (carrierCosts r (v + 1))
        (carrierCosts r (v + 2)) ∧
      2 * zeroDirect r (v + 1) ≤ zeroDirect r v + zeroDirect r (v + 2))

instance (r v : ℕ) : Decidable (CachedShapeCell r v) := by
  unfold CachedShapeCell
  infer_instance

def CachedShapeLayer (r : ℕ) : Prop :=
  ∀ v ∈ List.range (133 - r), CachedShapeCell r v

instance (r : ℕ) : Decidable (CachedShapeLayer r) := by
  unfold CachedShapeLayer
  infer_instance

def CachedShapeAll : Prop :=
  ∀ r ∈ List.range 30, 1 ≤ r → CachedShapeLayer r

instance : Decidable CachedShapeAll := by
  unfold CachedShapeAll
  infer_instance

theorem correct_in_box (r v : ℕ) (_hr : 1 ≤ r) (_hr29 : r ≤ 29)
    (_hrv : r + v ≤ 132) : CarrierCorrect r v := by
  trivial

theorem coordinateShape_of_cached (h : CachedShapeAll) :
    CoordinateShape zeroDirect := by
  constructor
  · intro v z n hn28 hnv
    have cell := h (n + 1) (List.mem_range.mpr (by omega)) (by omega)
      v (List.mem_range.mpr (by omega))
    have hcurve := (cell.1 (by omega) (by omega)).1
    rw [← costAt_eq_rawCost (n + 1) v z (by omega)
      (correct_in_box (n + 1) v (by omega) (by omega) (by omega)),
      ← costAt_eq_rawCost (n + 2) v z (by omega)
      (correct_in_box (n + 2) v (by omega) (by omega) (by omega))]
    exact costAt_le_of_curveLE _ _ hcurve z
  · intro v z n hn28 hnv
    have cell := h (n + 1) (List.mem_range.mpr (by omega)) (by omega)
      v (List.mem_range.mpr (by omega))
    have hcurve := (cell.2.1 (by omega) (by omega)).1
    rw [← costAt_eq_rawCost (n + 1) v z (by omega)
      (correct_in_box (n + 1) v (by omega) (by omega) (by omega)),
      ← costAt_eq_rawCost (n + 2) v z (by omega)
      (correct_in_box (n + 2) v (by omega) (by omega) (by omega)),
      ← costAt_eq_rawCost (n + 3) v z (by omega)
      (correct_in_box (n + 3) v (by omega) (by omega) (by omega))]
    exact costAt_convex_of_curveConvex _ _ _ hcurve z
  · intro v n hn28 hnv
    have cell := h (n + 1) (List.mem_range.mpr (by omega)) (by omega)
      v (List.mem_range.mpr (by omega))
    exact (cell.1 (by omega) (by omega)).2
  · intro v n hn28 hnv
    have cell := h (n + 1) (List.mem_range.mpr (by omega)) (by omega)
      v (List.mem_range.mpr (by omega))
    exact (cell.2.1 (by omega) (by omega)).2
  · intro r z n hr hr28 hrv
    have cell := h r (List.mem_range.mpr (by omega)) hr
      (n + 2) (List.mem_range.mpr (by omega))
    have hcurve := (cell.2.2.1 (by omega) (by omega)).1
    rw [← costAt_eq_rawCost r (n + 2) z hr
      (correct_in_box r (n + 2) hr hr28 (by omega)),
      ← costAt_eq_rawCost r (n + 3) z hr
      (correct_in_box r (n + 3) hr hr28 (by omega))]
    exact costAt_le_of_curveLE _ _ hcurve z
  · intro r z n hr hr28 hrv
    have cell := h r (List.mem_range.mpr (by omega)) hr
      (n + 2) (List.mem_range.mpr (by omega))
    have hcurve := (cell.2.2.2 (by omega) (by omega)).1
    rw [← costAt_eq_rawCost r (n + 2) z hr
      (correct_in_box r (n + 2) hr hr28 (by omega)),
      ← costAt_eq_rawCost r (n + 3) z hr
      (correct_in_box r (n + 3) hr hr28 (by omega)),
      ← costAt_eq_rawCost r (n + 4) z hr
      (correct_in_box r (n + 4) hr hr28 (by omega))]
    exact costAt_convex_of_curveConvex _ _ _ hcurve z
  · intro r n hr hr28 hrv
    have cell := h r (List.mem_range.mpr (by omega)) hr
      (n + 2) (List.mem_range.mpr (by omega))
    exact (cell.2.2.1 (by omega) (by omega)).2
  · intro r n hr hr28 hrv
    have cell := h r (List.mem_range.mpr (by omega)) hr
      (n + 2) (List.mem_range.mpr (by omega))
    exact (cell.2.2.2 (by omega) (by omega)).2

theorem sparseCandidateChecks_of_cached
    (h : CachedSparseAll) :
    SparseCandidateChecks LocatorPhase6802BaseDirectData.lookup := by
  intro R V r v hr hrR hvV hR29 hRV hcandidate hRb hVb
  have layer := h R (List.mem_range.mpr (by omega)) (by omega)
  have cell := layer V (List.mem_range.mpr (by omega))
  apply candidateRowCheck_of_cached R V r v
  · exact correct_in_box r v hr (by omega) (by omega)
  · exact cell r (mem_rBoundaryValues R r hRb)
      v (mem_vBoundaryValues V v hvV hVb) hr hrR hvV hcandidate

theorem baseCandidatesSound_of_cached
    (hshape : CachedShapeAll) (hsparse : CachedSparseAll) :
    BaseCandidatesSound LocatorPhase6802BaseDirectData.lookup := by
  exact baseCandidatesSound_of_sparse LocatorPhase6802BaseDirectData.lookup zeroDirect
    (coordinateShape_of_cached hshape)
    (fun r v _ _ => zeroDirect_eq_baseZeroCap r v)
    (sparseCandidateChecks_of_cached hsparse)

end ProximityPrize.SubmissionLower.LocatorPhaseBaseSparseCoreC2
