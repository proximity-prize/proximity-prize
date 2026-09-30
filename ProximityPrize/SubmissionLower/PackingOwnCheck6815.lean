import ProximityPrize.SubmissionLower.PackingData6815
import ProximityPrize.SubmissionLower.SingletonData6815
namespace ProximityPrize.SubmissionLower.PackingOwnCheck6815
open PackingSemantics6815 PackingData6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def fullCheck (r v : ℕ) (curve : List FinalCurves6815.Piece) : Bool := allN (fun j =>
  affineCheck (full_slope j) (lookup (full_own j) r v) curve) 8
def lightCheck (r v : ℕ) (curve : List FinalCurves6815.Piece) : Bool := allN (fun j =>
  affineCheck (light_slope j) (lookup (light_own j) r v) curve) 14
def localCheck (r v : ℕ) (curve : List FinalCurves6815.Piece) : Bool := fullCheck r v curve &&
  (if r<10 ∧ v≤70 then lightCheck r v curve else true)
def rowCheck (r v : ℕ) : Bool := localCheck r v (SingletonData6815.curve r v)

theorem curve_valid (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) :
    FinalCurves6815.validFrom (11193-r-v) 0 (SingletonData6815.curve r v)=true := by
  have h := check_curve r v _ (SingletonData6815.checked r v hr hR hy)
  simp only [SingletonCurveChecks6815.check,Bool.and_eq_true] at h
  exact h.1.1

theorem full_sound (r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (hz : r+v+z≤11192)
    (h : rowCheck r v=true) (j : ℕ) (hj : j<8) :
    SingletonData6815.cap r v z≤full_slope j*z+lookup (full_own j) r v := by
  simp only [rowCheck,localCheck,Bool.and_eq_true] at h
  exact affineCheck_sound _ _ (11193-r-v) _ (curve_valid r v hr hR hy)
    (allN_sound _ 8 h.1 j hj) z (by omega)

theorem light_sound (r v z : ℕ) (hr : 1≤r) (hR : r<10) (hv : v≤70) (hz : r+v+z≤11192)
    (h : rowCheck r v=true) (j : ℕ) (hj : j<14) :
    SingletonData6815.cap r v z≤light_slope j*z+lookup (light_own j) r v := by
  simp only [rowCheck,localCheck,Bool.and_eq_true,if_pos (show r<10 ∧ v≤70 from ⟨hR,hv⟩)] at h
  exact affineCheck_sound _ _ (11193-r-v) _ (curve_valid r v hr (by omega) (by omega))
    (allN_sound _ 14 h.2 j hj) z (by omega)

end ProximityPrize.SubmissionLower.PackingOwnCheck6815
