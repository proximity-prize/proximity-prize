import ProximityPrize.SubmissionLower.FinalBaseCheck6815
import ProximityPrize.SubmissionLower.FinalRemovalAlgebra6815
namespace ProximityPrize.SubmissionLower.FinalPayment6815
open FinalCurves6815 FinalPrefixCheck6815 FinalPrefixSound6815 FinalRemovalAlgebra6815
open FinalPrefixRowsCheck6815 FinalBaseCheck6815
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def src (j : ℕ) := (Lower80899.TenPhase.sound j).source
def cost (j r v z : ℕ) := ExactInitialCharge6815.cost (src j).totalCap (src j).middleCap
  (src j).slopeCap r (r+v) (r+v+z)
def Payment (j r v z cap : ℕ) : Prop :=
  ∀ q u x, q<r → u≤v → x≤z → (q=0 → u=0 ∧ x=0) →
    (1≤q → x<cut q u j) →
    FinalLedgerData6815.cap q u x+cost j (r-q) (v-u) (z-x)≤cap

def fastCut (r v j : ℕ) := threshold (SingletonCertificate6815.thresholds (FinalLookup6815.single r v)) j
def fastPrefix (r v j : ℕ) := coeff (FinalLookup6815.pref r v) j
def fastSeen (r v k : ℕ) := present (FinalLookup6815.pref r v) k

theorem fastCut_eq (r v j : ℕ) (hr : 1≤r) (hR : r≤39) : fastCut r v j=cut r v j := by
  unfold fastCut cut
  rw [FinalLookup6815.single_eq r v hr hR]

theorem fastPrefix_eq (r v j : ℕ) (hR : r≤39) : fastPrefix r v j=prefixCap r v j := by
  unfold fastPrefix prefixCap
  by_cases h : r=0
  · subst r; rfl
  · rw [FinalLookup6815.pref_eq r v (by omega) hR]

theorem fastSeen_eq (r v k : ℕ) (hR : r≤39) : fastSeen r v k=seen r v k := by
  unfold fastSeen seen
  by_cases h : r=0
  · subst r; rfl
  · rw [FinalLookup6815.pref_eq r v (by omega) hR]

theorem affine_add_removed (p : Potential) (r v z q u x : ℕ) (hq : q≤r) (hu : u≤v) (hx : x≤z) :
    affine p q u x+affine p (r-q) (v-u) (z-x)=affine p r v z := by
  unfold affine
  calc
    _=p.totalCoeff*(q+u+x+((r-q)+(v-u)+(z-x)))+
      p.middleCoeff*(q+u+((r-q)+(v-u)))+p.slopeCoeff*(q+(r-q)) := by ring
    _=_ := by
      rw [show q+u+x+((r-q)+(v-u)+(z-x))=r+v+z by omega,
        show q+u+((r-q)+(v-u))=r+v by omega,show q+(r-q)=r by omega]

theorem cost_phase (j r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    cost (sourceIndex j) r v z≤affine (phase j) r v z := by
  have h := cost_phase_le j r v z hr hR hy ht
  simpa only [cost,src,phase_source] using h

theorem phase_payment (j r v z cap : ℕ) (hj : j<8) (hr : 1≤r) (hR : r≤39)
    (hy : r+v≤182) (ht : r+v+z≤11192)
    (hbudget : affine (phase j) r v z+prefixCap (r-1) v j≤cap) :
    Payment (sourceIndex j) r v z cap := by
  intro q u x hq hu hx hzero hcut
  by_cases hq0 : q=0
  · obtain ⟨rfl,rfl⟩ := hzero hq0
    subst q
    have h := cost_phase j r v z hr hR hy ht
    simpa only [FinalLedgerData6815.cap,FinalLedgerData6815.row,FinalCurves6815.eval,
      FinalCurves6815.evalFrom,Nat.sub_zero,Nat.zero_add] using h.trans (Nat.le_add_right _ _ |>.trans hbudget)
  · have hq1 : 1≤q := by omega
    have hc := phase_prefix q u x j hq1 (by omega) (by omega) (by omega) hj (hcut hq1)
    have hp := prefix_mono j q u (r-1) v (by omega) (by omega) hu (by omega) (by omega)
    have hm := cost_phase j (r-q) (v-u) (z-x) (by omega) (by omega) (by omega) (by omega)
    have he := affine_add_removed (phase j) r v z q u x (by omega) hu hx
    omega

theorem terminal_payment (r v z cap : ℕ) (hr : 1≤r) (hR : r≤39)
    (hy : r+v≤182) (ht : r+v+z≤11192)
    (hbudget : ∀ k, k<5 → (k=0 ∨ (seen (r-1) v k=true ∧ floorR k<r ∧ floorY k<r+v ∧ floorT k<r+v+z)) →
      affine (terminal k) r v z+prefixCap (r-1) v (k+8)≤cap) :
    Payment 5 r v z cap := by
  intro q u x hq hu hx hzero hcut
  by_cases hq0 : q=0
  · obtain ⟨rfl,rfl⟩ := hzero hq0
    subst q
    have hc := cost_terminal_le 0 r (r+v) (r+v+z) (by decide) hr hR hy ht
    have hb := hbudget 0 (by decide) (Or.inl rfl)
    change cost 5 r v z≤affine (terminal 0) r v z at hc
    simpa only [FinalLedgerData6815.cap,FinalLedgerData6815.row,FinalCurves6815.eval,
      FinalCurves6815.evalFrom,Nat.sub_zero,Nat.zero_add] using hc.trans (Nat.le_add_right _ _ |>.trans hb)
  · have hq1 : 1≤q := by omega
    let k := classify q u x
    have hk : k<5 := class_lt_five _ _ _
    have hc := terminal_prefix q u x hq1 (by omega) (by omega) (by omega) (hcut hq1)
    have hs := seen_mono k q u (r-1) v hk (by omega) hu (by omega) (by omega) hc.2
    have hp := prefix_mono (k+8) q u (r-1) v (by omega) (by omega) hu (by omega) (by omega)
    have hf := class_interval q u x (by omega)
    change (floorR k≤q ∧ floorY k≤q+u) ∧ lower k q u≤x ∧ _ at hf
    have htFloor : floorT k≤q+u+x := by have h := hf.2.1; unfold lower at h; omega
    have hm := cost_terminal_le k (r-q) ((r-q)+(v-u)) ((r-q)+(v-u)+(z-x)) hk
      (by omega) (by omega) (by omega) (by omega)
    change cost 5 (r-q) (v-u) (z-x)≤affine (terminal k) (r-q) (v-u) (z-x) at hm
    have he := affine_add_removed (terminal k) r v z q u x (by omega) hu hx
    have hb := hbudget k hk (Or.inr ⟨hs,by omega,by omega,by omega⟩)
    dsimp only [k] at hp hm he hb
    omega

end ProximityPrize.SubmissionLower.FinalPayment6815
