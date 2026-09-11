import ProximityPrize.SubmissionLower.BoundaryTailBaseFast
import ProximityPrize.SubmissionLower.ConvexEndpoint

namespace ProximityPrize.SubmissionLower.BoundaryTailStrictConvex
open BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxHeartbeats 1000000

def scalar (c : Carrier) (j z : ℕ) : ℕ :=
  match j with
  | 0 => c.c0
  | 1 => c.c1
  | 2 => c.c2
  | _ => c.c3 + (c.c4-c.c3)*z

def Step (a b c : Carrier) : Prop :=
  2*b.c0 ≤ a.c0+c.c0 ∧ 2*b.c1 ≤ a.c1+c.c1 ∧
  2*b.c2 ≤ a.c2+c.c2 ∧ 2*b.c3 ≤ a.c3+c.c3 ∧
  2*(b.c4-b.c3) ≤ (a.c4-a.c3)+(c.c4-c.c3)

instance (a b c : Carrier) : Decidable (Step a b c) := by
  unfold Step; infer_instance

theorem Step.scalar {a b c : Carrier} (h : Step a b c) (j z : ℕ) :
    2*scalar b j z ≤ scalar a j z+scalar c j z := by
  rcases h with ⟨h0,h1,h2,h3,hs⟩
  rcases j with _ | _ | _ | j
  · exact h0
  · exact h1
  · exact h2
  · change 2*(b.c3+(b.c4-b.c3)*z) ≤
      (a.c3+(a.c4-a.c3)*z)+(c.c3+(c.c4-c.c3)*z)
    have hm := Nat.mul_le_mul_right z hs
    nlinarith

-- One reusable curvature receipt per data row; no parent rectangle sweep.
def Curvature (r : ℕ) : Prop :=
  ∀ v ∈ List.range (143-r), 1 ≤ v → v+2+r ≤ 142 →
    Step (fastCarriers r v) (fastCarriers r (v+1)) (fastCarriers r (v+2)) ∧
    2*fastZero r (v+1) ≤ fastZero r v+fastZero r (v+2)

instance (r : ℕ) : Decidable (Curvature r) := by
  unfold Curvature; infer_instance

theorem curve_step (r v : ℕ) (h : Curvature r) (hv : 1 ≤ v)
    (hfit : v+2+r ≤ 142) :
    Step (fastCarriers r v) (fastCarriers r (v+1)) (fastCarriers r (v+2)) ∧
    2*fastZero r (v+1) ≤ fastZero r v+fastZero r (v+2) :=
  h v (List.mem_range.mpr (by omega)) hv hfit

theorem split_step (R V r j z i : ℕ) (hfit : R+V ≤ 142)
    (hr : r ≤ R) (hc : Curvature r) (hz : Curvature (R-r))
    (hi : 1 ≤ i) (hiV : i+2 ≤ V-1) :
    2*(scalar (fastCarriers r (i+1)) j z+fastZero (R-r) (V-(i+1))) ≤
      (scalar (fastCarriers r i) j z+fastZero (R-r) (V-i))+
      (scalar (fastCarriers r (i+2)) j z+fastZero (R-r) (V-(i+2))) := by
  have hcs := (curve_step r i hc hi (by omega)).1.scalar j z
  have hzs := (curve_step (R-r) (V-(i+2)) hz (by omega) (by omega)).2
  have e1 : V-(i+2)+1 = V-(i+1) := by omega
  have e2 : V-(i+2)+2 = V-i := by omega
  rw [e1,e2] at hzs
  omega

theorem bounds_of_scalar (a b c : Carrier) (oa ob oc lo : ℕ) (cuts : List Cut)
    (h : ∀ j z, scalar b j z+ob ≤ max (scalar a j z+oa) (scalar c j z+oc))
    (ha : Bounds a oa lo cuts) (hc : Bounds c oc lo cuts) : Bounds b ob lo cuts := by
  induction cuts generalizing lo with
  | nil => trivial
  | cons cut cuts ih =>
    rcases ha with ⟨ha0,ha1,hat⟩
    rcases hc with ⟨hc0,hc1,hct⟩
    exact ⟨(h 3 (lo-3)).trans (max_le ha0 hc0),
      (h 3 (cut.stop-1-3)).trans (max_le ha1 hc1), ih cut.stop hat hct⟩

theorem check_of_scalar (row : Row) (a b c : Carrier) (oa ob oc : ℕ)
    (h : ∀ j z, scalar b j z+ob ≤ max (scalar a j z+oa) (scalar c j z+oc))
    (ha : Check row a oa) (hc : Check row c oc) : Check row b ob := by
  rcases ha with ⟨ha0,ha1,ha2,hat⟩
  rcases hc with ⟨hc0,hc1,hc2,hct⟩
  exact ⟨(h 0 0).trans (max_le ha0 hc0), (h 1 0).trans (max_le ha1 hc1),
    (h 2 0).trans (max_le ha2 hc2), bounds_of_scalar a b c oa ob oc 3 row.cuts h hat hct⟩

-- Four positions also cover the exceptional curvature at either head.
def Endpoints (row : Row) (R V : ℕ) : Prop :=
  ∀ r ∈ List.range R, 1 ≤ r →
    ∀ v ∈ [0, min 1 V, V-1, V], Check row (fastCarriers r v) (fastZero (R-r) (V-v))

instance (row : Row) (R V : ℕ) : Decidable (Endpoints row R V) := by
  unfold Endpoints; infer_instance

theorem endpoints_sound (row : Row) (R V : ℕ) (hfit : R+V ≤ 142)
    (hcurves : ∀ r ∈ List.range 32, 1 ≤ r → Curvature r)
    (hR : R ≤ 31) (h : Endpoints row R V) : StrictAtFast row R V := by
  intro r hr v hv hrpos
  have hrR := List.mem_range.mp hr
  have hvV := List.mem_range.mp hv
  by_cases h0 : v = 0
  · subst v; exact h r hr hrpos 0 (by simp)
  by_cases hV : v = V
  · subst v; exact h r hr hrpos V (by simp)
  apply check_of_scalar row (fastCarriers r 1) (fastCarriers r v)
    (fastCarriers r (V-1)) (fastZero (R-r) (V-1)) (fastZero (R-r) (V-v))
    (fastZero (R-r) (V-(V-1)))
  · intro j z
    exact ConvexEndpoint.bound
      (fun k => scalar (fastCarriers r k) j z+fastZero (R-r) (V-k))
      1 (V-1) v (by omega) (by omega)
      (fun i hi hiV => split_step R V r j z i hfit (by omega)
        (hcurves r (List.mem_range.mpr (by omega)) hrpos)
        (hcurves (R-r) (List.mem_range.mpr (by omega)) (by omega)) hi hiV)
  · exact h r hr hrpos 1 (by simp [Nat.min_eq_left (show 1 ≤ V by omega)])
  · exact h r hr hrpos (V-1) (by simp)

end ProximityPrize.SubmissionLower.BoundaryTailStrictConvex
