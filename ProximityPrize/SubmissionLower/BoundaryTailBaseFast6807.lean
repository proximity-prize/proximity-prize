import ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData6807

/-! Exact shared row certificates and balanced lookup for finite base checks.
The soundness theorems return the original receipt propositions. -/
namespace ProximityPrize.SubmissionLower.BoundaryTailBaseFast6807
open BoundaryTailBaseChecksCore6807 BoundaryTailBaseChecksData6807
open LocatorPhase6800Oracle SecondJetRowIntervals
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

structure Cut where
  stop : ℕ
  loValue : ℕ
  hiValue : ℕ

structure Row where
  z0 : ℕ
  z1 : ℕ
  z2 : ℕ
  cuts : List Cut

def PlanValid (q : BaseRow) (finish : ℕ) : ℕ → List Cut → Prop
  | lo, [] => lo = finish
  | lo, cut::cuts => lo < cut.stop ∧ cut.stop ≤ finish ∧ 3 ≤ lo ∧
      BaseCell q lo (cut.stop-1) ∧ cut.loValue ≤ q.evalAt lo ∧
      cut.hiValue ≤ q.evalAt (cut.stop-1) ∧ PlanValid q finish cut.stop cuts

instance (q : BaseRow) (finish lo : ℕ) (cuts : List Cut) :
    Decidable (PlanValid q finish lo cuts) := by
  induction cuts generalizing lo with
  | nil => simp only [PlanValid]; infer_instance
  | cons cut cuts ih => simp only [PlanValid]; infer_instance

def Bounds (c : Carrier) (offset : ℕ) : ℕ → List Cut → Prop
  | _, [] => True
  | lo, cut::cuts =>
      c.c3+(c.c4-c.c3)*(lo-3)+offset ≤ cut.loValue ∧
      c.c3+(c.c4-c.c3)*(cut.stop-1-3)+offset ≤ cut.hiValue ∧
      Bounds c offset cut.stop cuts

instance (c : Carrier) (offset lo : ℕ) (cuts : List Cut) :
    Decidable (Bounds c offset lo cuts) := by
  induction cuts generalizing lo with
  | nil => simp only [Bounds]; infer_instance
  | cons cut cuts ih => simp only [Bounds]; infer_instance

theorem plan_sound (q : BaseRow) (finish lo : ℕ) (cuts : List Cut)
    (c : Carrier) (offset : ℕ)
    (hplan : PlanValid q finish lo cuts) (hbound : Bounds c offset lo cuts) :
    LineRuns q (fun z => c.eval z+offset) finish lo (cuts.map Cut.stop) := by
  induction cuts generalizing lo with
  | nil => exact hplan
  | cons cut cuts ih =>
    rcases hplan with ⟨hstop,hfinish,hlo,hcell,h0,h1,hrest⟩
    rcases hbound with ⟨hb0,hb1,hbrest⟩
    refine ⟨hstop,hfinish,hlo,hcell,?_,?_,ih cut.stop hrest hbrest⟩
    · simpa only [Carrier.eval,if_neg (show lo ≠ 0 by omega),
        if_neg (show lo ≠ 1 by omega),if_neg (show lo ≠ 2 by omega)]
        using hb0.trans h0
    · simpa only [Carrier.eval,if_neg (show cut.stop-1 ≠ 0 by omega),
        if_neg (show cut.stop-1 ≠ 1 by omega),
        if_neg (show cut.stop-1 ≠ 2 by omega)] using hb1.trans h1

def Valid (row : Row) (R V : ℕ) : Prop :=
  let q := BoundaryTailStrictData6807.lookup R V
  row.z0 ≤ q.z0 ∧ row.z1 ≤ q.z1 ∧ row.z2 ≤ q.z2 ∧
    row.cuts.map Cut.stop = stopsFor q (7785-R-V) ∧
    PlanValid q (7785-R-V) 3 row.cuts

instance (row : Row) (R V : ℕ) : Decidable (Valid row R V) := by
  unfold Valid; infer_instance

def Check (row : Row) (c : Carrier) (offset : ℕ) : Prop :=
  c.c0+offset ≤ row.z0 ∧ c.c1+offset ≤ row.z1 ∧ c.c2+offset ≤ row.z2 ∧
    Bounds c offset 3 row.cuts

instance (row : Row) (c : Carrier) (offset : ℕ) : Decidable (Check row c offset) := by
  unfold Check; infer_instance

theorem check_sound (row : Row) (R V r v : ℕ) (c : Carrier)
    (hvalid : Valid row R V)
    (hc : Check row c (BoundaryTailStrictData6807.zero (R-r) (V-v))) :
    StrictCheck c R V r v := by
  rcases hvalid with ⟨h0,h1,h2,hstops,hplan⟩
  rcases hc with ⟨hc0,hc1,hc2,hbounds⟩
  refine ⟨hc0.trans h0,hc1.trans h1,hc2.trans h2,?_⟩
  have hh := plan_sound (BoundaryTailStrictData6807.lookup R V) (7785-R-V)
    3 row.cuts c (BoundaryTailStrictData6807.zero (R-r) (V-v)) hplan hbounds
  rw [hstops] at hh
  exact hh

def fastCarriers := carriers
def fastZero := BoundaryTailStrictData6807.zero

def ZeroAtFast (R V : ℕ) : Prop :=
  ∀ r ∈ List.range (R+1), ∀ v ∈ List.range (V+1),
    1 ≤ r → (r < R ∨ v=V) →
      (fastCarriers r v).c0+fastZero (R-r) (V-v) ≤ fastZero R V

instance (R V : ℕ) : Decidable (ZeroAtFast R V) := by
  unfold ZeroAtFast; infer_instance

theorem fastCarriers_eq (R V : ℕ) : fastCarriers R V = carriers R V := rfl
theorem fastZero_eq (R V : ℕ) : fastZero R V = BoundaryTailStrictData6807.zero R V := rfl

theorem zeroAtFast_sound (R V : ℕ) (h : ZeroAtFast R V) : ZeroCheckAt R V := by
  intro r hr v hv hrpos hfit
  simpa only [fastCarriers_eq, fastZero_eq] using h r hr v hv hrpos hfit

def StrictAtFast (row : Row) (R V : ℕ) : Prop :=
  ∀ r ∈ List.range R, ∀ v ∈ List.range (V+1), 1 ≤ r →
    Check row (fastCarriers r v) (fastZero (R-r) (V-v))

instance (row : Row) (R V : ℕ) : Decidable (StrictAtFast row R V) := by
  unfold StrictAtFast; infer_instance

theorem strictAtFast_sound (row : Row) (R V : ℕ)
    (hvalid : Valid row R V) (h : StrictAtFast row R V) : StrictCheckAt R V := by
  intro r hr v hv hrpos
  apply check_sound row R V r v (carriers r v) hvalid
  simpa only [fastCarriers_eq, fastZero_eq] using h r hr v hv hrpos

/-- The strict receipt handles every proper split; only these two scalar
    comparisons are needed to obtain the zero receipt. -/
def ZeroCertificate (row : Row) (R V : ℕ) : Prop :=
  row.z0 ≤ fastZero R V ∧
    (fastCarriers R V).c0 + fastZero 0 0 ≤ fastZero R V

instance (row : Row) (R V : ℕ) : Decidable (ZeroCertificate row R V) := by
  unfold ZeroCertificate
  infer_instance

theorem zeroAtFast_of_strict (row : Row) (R V : ℕ)
    (hstrict : StrictAtFast row R V) (hzero : ZeroCertificate row R V) :
    ZeroAtFast R V := by
  intro r hr v hv hpos hfit
  by_cases hlt : r < R
  · exact ((hstrict r (List.mem_range.mpr hlt) v hv hpos).1).trans hzero.1
  · have hrle : r < R + 1 := List.mem_range.mp hr
    have heq : r = R := by omega
    have hvEq : v = V := hfit.resolve_left hlt
    subst r
    subst v
    simpa only [Nat.sub_self] using hzero.2

/-- Join adjacent certificate blocks without repeating case-split proofs. -/
theorem range_join {P : ℕ → Prop} (start n m : ℕ)
    (hl : ∀ i ∈ List.range n, P (start + i))
    (hr : ∀ i ∈ List.range m, P (start + n + i)) :
    ∀ i ∈ List.range (n + m), P (start + i) := by
  intro i hi
  have hi' := List.mem_range.mp hi
  by_cases h : i < n
  · exact hl i (List.mem_range.mpr h)
  · have hh := hr (i - n) (List.mem_range.mpr (by omega))
    simpa only [show start + n + (i - n) = start + i by omega] using hh

end ProximityPrize.SubmissionLower.BoundaryTailBaseFast6807

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseFastData6807
open BoundaryTailBaseFast6807 BoundaryTailBaseChecksCore6807
open LocatorPhase6800Oracle SecondJetRowIntervals

/-- Derive endpoint values from the existing row instead of duplicating its data. -/
def cuts (q : BaseRow) : ℕ → List ℕ → List Cut
  | _, [] => []
  | start, stop :: rest =>
      ⟨stop, q.evalAt start, q.evalAt (stop - 1)⟩ :: cuts q stop rest

def row (R V : ℕ) : Row :=
  let q := BoundaryTailStrictData6807.lookup R V
  ⟨q.z0, q.z1, q.z2, cuts q 3 (stopsFor q (7785 - R - V))⟩

end ProximityPrize.SubmissionLower.BoundaryTailBaseFastData6807
