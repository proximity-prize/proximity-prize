import ProximityPrize.SubmissionLower.FinalPrefixData6815
namespace ProximityPrize.SubmissionLower.FinalPrefixSound6815
open FinalPrefixCheck6815 FinalPrefixRowsCheck6815
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def prefixCap (r v j : ℕ) := coeff (FinalPrefixData6815.row r v) j
def seen (r v k : ℕ) := present (FinalPrefixData6815.row r v) k
def cut (r v j : ℕ) := threshold (SingletonCertificate6815.thresholds (SingletonData6815.row r v)) j

theorem curve_valid (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) :
    FinalCurves6815.validFrom (11193-r-v) 0 (FinalLedgerData6815.row r v)=true := by
  have h := FinalLedgerData6815.checked r v hr hR hy
  simp only [FinalLedgerChecks6815.checkRow,Bool.and_eq_true] at h
  exact h.1

theorem prefix_mono (j r v R V : ℕ) (hj : j<13) (hr : r≤R) (hv : v≤V)
    (hR : R≤39) (hy : R+V≤182) : prefixCap r v j≤prefixCap R V j := by
  apply rectangle_mono (fun r v => prefixCap r v j) 39 182 _ _ r v R V hr hv hR hy
  · intro q u hq hu
    have h := (coeff_mono (q+1) u _ _ _ _ _
      (FinalPrefixData6815.checked (q+1) u (by omega) hq hu) j hj).1
    simpa only [prefixCap,Nat.add_sub_cancel] using h
  · intro q u hq hu
    by_cases h0 : q=0
    · subst q; rfl
    have h := (coeff_mono q (u+1) _ _ _ _ _
      (FinalPrefixData6815.checked q (u+1) (by omega) hq (by omega)) j hj).2
    simpa only [prefixCap,Nat.add_sub_cancel,show ¬u+1=0 by omega,if_false] using h

theorem seen_mono (k r v R V : ℕ) (hk : k<5) (hr : r≤R) (hv : v≤V)
    (hR : R≤39) (hy : R+V≤182) (hseen : seen r v k=true) : seen R V k=true := by
  let f := fun r v => if seen r v k then (1:ℕ) else 0
  have bool_le (a b : Bool) (h : a=true → b=true) :
      (if a then (1:ℕ) else 0)≤(if b then 1 else 0) := by
    cases ha : a <;> cases hb : b <;> simp_all
  have hm : f r v≤f R V := by
    apply rectangle_mono f 39 182 _ _ r v R V hr hv hR hy
    · intro q u hq hu
      apply bool_le
      have h := (present_mono (q+1) u _ _ _ _ _
        (FinalPrefixData6815.checked (q+1) u (by omega) hq hu) k hk).1
      simpa only [seen,Nat.add_sub_cancel] using h
    · intro q u hq hu
      by_cases h0 : q=0
      · subst q; rfl
      apply bool_le
      have h := (present_mono q (u+1) _ _ _ _ _
        (FinalPrefixData6815.checked q (u+1) (by omega) hq (by omega)) k hk).2
      simpa only [seen,Nat.add_sub_cancel,show ¬u+1=0 by omega,if_false] using h
  dsimp only [f] at hm
  rw [hseen] at hm
  cases h : seen R V k <;> simp_all

theorem phase_prefix (r v z j : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182)
    (hz : r+v+z≤11192) (hj : j<8) (hcut : z<cut r v (sourceIndex j)) :
    FinalLedgerData6815.cap r v z≤affine (phase j) r v z+prefixCap r v j := by
  exact phaseCheck_sound r v _ _ j (11193-r-v) z _ (curve_valid r v hr hR hy)
    (phase_check _ _ _ _ _ _ _ (FinalPrefixData6815.checked r v hr hR hy) j hj) (by omega) hcut

theorem terminal_prefix (r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182)
    (hz : r+v+z≤11192) (hcut : z<cut r v 5) :
    FinalLedgerData6815.cap r v z≤affine (terminal (classify r v z)) r v z+
      prefixCap r v (classify r v z+8) ∧ seen r v (classify r v z)=true := by
  exact classCheck_sound r v _ _ (classify r v z) z _ _ (curve_valid r v hr hR hy)
    (class_check _ _ _ _ _ _ _ (FinalPrefixData6815.checked r v hr hR hy) _ (class_lt_five _ _ _))
    rfl (by omega) hcut

end ProximityPrize.SubmissionLower.FinalPrefixSound6815
