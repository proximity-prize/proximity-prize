import ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData

/-! Exact shared row certificates and balanced lookup for finite base checks.
The soundness theorems return the original receipt propositions. -/
namespace ProximityPrize.SubmissionLower.BoundaryTailBaseFast
open BoundaryTailBaseChecksCore BoundaryTailBaseChecksData
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
  let q := BoundaryTailStrictData.lookup R V
  row.z0 ≤ q.z0 ∧ row.z1 ≤ q.z1 ∧ row.z2 ≤ q.z2 ∧
    row.cuts.map Cut.stop = stopsFor q (7502-R-V) ∧
    PlanValid q (7502-R-V) 3 row.cuts

instance (row : Row) (R V : ℕ) : Decidable (Valid row R V) := by
  unfold Valid; infer_instance

def Check (row : Row) (c : Carrier) (offset : ℕ) : Prop :=
  c.c0+offset ≤ row.z0 ∧ c.c1+offset ≤ row.z1 ∧ c.c2+offset ≤ row.z2 ∧
    Bounds c offset 3 row.cuts

instance (row : Row) (c : Carrier) (offset : ℕ) : Decidable (Check row c offset) := by
  unfold Check; infer_instance

theorem check_sound (row : Row) (R V r v : ℕ) (c : Carrier)
    (hvalid : Valid row R V)
    (hc : Check row c (BoundaryTailStrictData.zero (R-r) (V-v))) :
    StrictCheck c R V r v := by
  rcases hvalid with ⟨h0,h1,h2,hstops,hplan⟩
  rcases hc with ⟨hc0,hc1,hc2,hbounds⟩
  refine ⟨hc0.trans h0,hc1.trans h1,hc2.trans h2,?_⟩
  have hh := plan_sound (BoundaryTailStrictData.lookup R V) (7502-R-V)
    3 row.cuts c (BoundaryTailStrictData.zero (R-r) (V-v)) hplan hbounds
  rw [hstops] at hh
  exact hh

def fastCarriers (R V : ℕ) : Carrier :=
  if R < 32 then (if R < 15 then (if R < 7 then (if R < 3 then (if R < 1 then (⟨0,0,0,0,0⟩) else (if R < 2 then (costs1 V) else (costs2 V))) else (if R < 5 then (if R < 4 then (costs3 V) else (costs4 V)) else (if R < 6 then (costs5 V) else (costs6 V)))) else (if R < 11 then (if R < 9 then (if R < 8 then (costs7 V) else (costs8 V)) else (if R < 10 then (costs9 V) else (costs10 V))) else (if R < 13 then (if R < 12 then (costs11 V) else (costs12 V)) else (if R < 14 then (costs13 V) else (costs14 V))))) else (if R < 23 then (if R < 19 then (if R < 17 then (if R < 16 then (costs15 V) else (costs16 V)) else (if R < 18 then (costs17 V) else (costs18 V))) else (if R < 21 then (if R < 20 then (costs19 V) else (costs20 V)) else (if R < 22 then (costs21 V) else (costs22 V)))) else (if R < 27 then (if R < 25 then (if R < 24 then (costs23 V) else (costs24 V)) else (if R < 26 then (costs25 V) else (costs26 V))) else (if R < 29 then (if R < 28 then (costs27 V) else (costs28 V)) else (if R < 30 then (costs29 V) else (if R < 31 then (costs30 V) else (costs31 V))))))) else (⟨0,0,0,0,0⟩)

def fastZero (R V : ℕ) : ℕ :=
  if R < 32 then (if R < 15 then (if R < 7 then (if R < 3 then (if R < 1 then (0) else (if R < 2 then (BoundaryTailStrictData.zeroRow1 V) else (BoundaryTailStrictData.zeroRow2 V))) else (if R < 5 then (if R < 4 then (BoundaryTailStrictData.zeroRow3 V) else (BoundaryTailStrictData.zeroRow4 V)) else (if R < 6 then (BoundaryTailStrictData.zeroRow5 V) else (BoundaryTailStrictData.zeroRow6 V)))) else (if R < 11 then (if R < 9 then (if R < 8 then (BoundaryTailStrictData.zeroRow7 V) else (BoundaryTailStrictData.zeroRow8 V)) else (if R < 10 then (BoundaryTailStrictData.zeroRow9 V) else (BoundaryTailStrictData.zeroRow10 V))) else (if R < 13 then (if R < 12 then (BoundaryTailStrictData.zeroRow11 V) else (BoundaryTailStrictData.zeroRow12 V)) else (if R < 14 then (BoundaryTailStrictData.zeroRow13 V) else (BoundaryTailStrictData.zeroRow14 V))))) else (if R < 23 then (if R < 19 then (if R < 17 then (if R < 16 then (BoundaryTailStrictData.zeroRow15 V) else (BoundaryTailStrictData.zeroRow16 V)) else (if R < 18 then (BoundaryTailStrictData.zeroRow17 V) else (BoundaryTailStrictData.zeroRow18 V))) else (if R < 21 then (if R < 20 then (BoundaryTailStrictData.zeroRow19 V) else (BoundaryTailStrictData.zeroRow20 V)) else (if R < 22 then (BoundaryTailStrictData.zeroRow21 V) else (BoundaryTailStrictData.zeroRow22 V)))) else (if R < 27 then (if R < 25 then (if R < 24 then (BoundaryTailStrictData.zeroRow23 V) else (BoundaryTailStrictData.zeroRow24 V)) else (if R < 26 then (BoundaryTailStrictData.zeroRow25 V) else (BoundaryTailStrictData.zeroRow26 V))) else (if R < 29 then (if R < 28 then (BoundaryTailStrictData.zeroRow27 V) else (BoundaryTailStrictData.zeroRow28 V)) else (if R < 30 then (BoundaryTailStrictData.zeroRow29 V) else (if R < 31 then (BoundaryTailStrictData.zeroRow30 V) else (BoundaryTailStrictData.zeroRow31 V))))))) else (0)

def ZeroAtFast (R V : ℕ) : Prop :=
  ∀ r ∈ List.range (R+1), ∀ v ∈ List.range (V+1),
    1 ≤ r → (r < R ∨ v=V) →
      (fastCarriers r v).c0+fastZero (R-r) (V-v) ≤ fastZero R V

instance (R V : ℕ) : Decidable (ZeroAtFast R V) := by
  unfold ZeroAtFast; infer_instance

theorem fastCarriers_eq (R V : ℕ) : fastCarriers R V = carriers R V := by
  by_cases hR : R ≤ 31
  · interval_cases R <;> rfl
  · have hge : 32 ≤ R := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    simp only [fastCarriers, if_neg (show ¬32+j < 32 by omega)]
    rw [Nat.add_comm 32 j]
    rfl

theorem fastZero_eq (R V : ℕ) : fastZero R V = BoundaryTailStrictData.zero R V := by
  by_cases hR : R ≤ 31
  · interval_cases R <;> rfl
  · have hge : 32 ≤ R := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    simp only [fastZero, if_neg (show ¬32+j < 32 by omega)]
    rw [Nat.add_comm 32 j]
    rfl

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

end ProximityPrize.SubmissionLower.BoundaryTailBaseFast
