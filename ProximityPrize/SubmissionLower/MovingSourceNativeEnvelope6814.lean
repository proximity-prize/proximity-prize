import ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814

/-! Exact nonlinear unique-owner arithmetic for just two retained profiles.
This is a checked-cell ledger bound; it is not a global score claim. -/
namespace ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN095 SecondJetRelaxedFlag

def copies3 (m : ℕ) : ℕ := (m+2)/m
def copies7 (m : ℕ) : ℕ := (m+6)/m
def capS (m : ℕ) : ℕ := min (14/copies3 m) (24/copies7 m)
def capB (m : ℕ) : ℕ := min (31/copies3 m) (53/copies7 m)
def capU (m : ℕ) : ℕ := min (98/copies3 m) (177/copies7 m)
def capT (m : ℕ) : ℕ := min (995/copies3 m) (3429/copies7 m)
def nativeFlag (m s : ℕ) : FlagDegree := budgetFlag (capB m) (capU m) (capT m) m s
def parentFlag : FlagDegree := ⟨3504,45,12⟩
def coefficientZ3 : ℕ := 4*131072*(131074*3504)+3*65539*(131073*3504)
def coefficientU3 : ℕ := 4*131072*(131074*45-131072)+3*65539*(131073*45)
def coefficientA3 : ℕ := 4*131072*(131074*11)+3*65539*(131073*12-1)

def scaledMain (m s : ℕ) : ℕ := 3*126275387074424400*m+
  coefficientZ3*flagMixed parentFlag unitZFlag (nativeFlag m s)+
  coefficientU3*flagMixed parentFlag unitYZFlag (nativeFlag m s)+
  coefficientA3*flagMixed parentFlag unitAllFlag (nativeFlag m s)

theorem copies3_le (m e : ℕ) (hm : 0<m) (h : 3≤e*m) : copies3 m≤e := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hm).mpr
  nlinarith

theorem copies7_le (m e : ℕ) (hm : 0<m) (h : 7≤e*m) : copies7 m≤e := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hm).mpr
  nlinarith

theorem copies3_pos (m : ℕ) (hm : 0<m) : 0<copies3 m := by
  change 0<(m+2)/m
  exact Nat.div_pos (by omega) hm

theorem copies7_pos (m : ℕ) (hm : 0<m) : 0<copies7 m := by
  change 0<(m+6)/m
  exact Nat.div_pos (by omega) hm

theorem budget_caps (m : ℕ) : capB m≤capU m ∧ capU m≤capT m := by
  constructor
  · exact min_le_min (Nat.div_le_div_right (by omega)) (Nat.div_le_div_right (by omega))
  · exact min_le_min (Nat.div_le_div_right (by omega)) (Nat.div_le_div_right (by omega))

/-- 15x15 guarded small-Nat cases; no polynomial spaces or rational
arithmetic are evaluated. The valid set contains 73 nonlinear envelopes. -/
theorem finite_native_receipt : ∀ m s : Fin 15,
    0<m.val → 2≤s.val → m.val≤s.val → s.val≤capS m.val → 2*s.val≤capB m.val →
    4*scaledMain m.val s.val≤3*1036142808586141401*m.val := by
  decide +kernel

theorem nonlinear_native_main_fits (m s : ℕ)
    (hm : 0<m) (hs : 2≤s) (hms : m≤s) (hcap : s≤capS m) (hB : 2*s≤capB m) :
    scaledMain m s<3*272069082261391681*m := by
  have hs14 : s≤14 := by
    have h3 := copies3_pos m hm
    have h := hcap.trans (min_le_left (14/copies3 m) (24/copies7 m))
    have hd := Nat.div_le_self 14 (copies3 m)
    omega
  have hh := finite_native_receipt ⟨m,by omega⟩ ⟨s,by omega⟩ hm hs hms hcap hB
  change 4*scaledMain m s≤3*1036142808586141401*m at hh
  nlinarith

/-- The linear case was tested, not silently included in the receipt. -/
theorem linear_native_does_not_fit :
    3*272069082261391681<scaledMain 1 1 := by decide +kernel

#print axioms nonlinear_native_main_fits
#print axioms linear_native_does_not_fit
end ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
