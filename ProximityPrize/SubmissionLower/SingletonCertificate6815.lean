import ProximityPrize.SubmissionLower.SingletonCurveGeometry6815
import ProximityPrize.SubmissionLower.FinalThreshold6815
namespace ProximityPrize.SubmissionLower.SingletonCertificate6815
open FinalCurves6815 SingletonCurveChecks6815 FinalThreshold6815
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

structure Header where
  cut : ℕ
  runs : List Lower80899.CompressedBand.Run
  deriving Inhabited

def decodeRuns : ℕ → ℕ → List Lower80899.CompressedBand.Run
  | 0, _ => []
  | n+1, code => ⟨code%16384,code/16384%16⟩ :: decodeRuns n (code/262144)

def decodeHeaders : ℕ → ℕ → List Header
  | 0, _ => []
  | n+1, code =>
    let count := code/16384%16
    ⟨code%16384,decodeRuns count (code/262144)⟩ ::
      decodeHeaders n (code/(262144*262144^count))

structure Row where
  curve : List Piece
  choices : List Piece
  headers : Array Header
  deriving Inhabited

def thresholds (d : Row) : Array ℕ := d.headers.map Header.cut

def allN (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => allN p n && p n

theorem allN_sound (p : ℕ → Bool) (n : ℕ) (h : allN p n=true) :
    ∀ j, j<n → p j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allN,Bool.and_eq_true] at h
    intro j hj
    by_cases he : j=n
    · simpa only [he] using h.2
    · exact ih h.1 j (by omega)

def thresholdCheck (r v : ℕ) (d : Row) (j : ℕ) : Bool :=
  thresholdK (Lower80899.TenPhase.sound j).source r v
    (MovingFiberSingleCore6815.thresholdAt (thresholds d) j)
    ((d.headers[j]?).getD default).runs

def check (r v : ℕ) (d : Row) : Bool :=
  allN (thresholdCheck r v d) 7 && SingletonCurveChecks6815.check r v (thresholds d) d.curve d.choices

theorem check_thresholds (r v : ℕ) (d : Row) (h : check r v d=true) :
    ∀ j, j<7 → Lower80899.ThresholdFast.FastSourceThresholdSufficient
      (Lower80899.TenPhase.sound j).source r v (MovingFiberSingleCore6815.thresholdAt (thresholds d) j) := by
  simp only [check,Bool.and_eq_true] at h
  intro j hj
  exact thresholdK_sound _ _ _ _ _ (allN_sound _ 7 h.1 j hj)

theorem check_curve (r v : ℕ) (d : Row) (h : check r v d=true) :
    SingletonCurveChecks6815.check r v (thresholds d) d.curve d.choices=true := by
  simp only [check,Bool.and_eq_true] at h
  exact h.2

end ProximityPrize.SubmissionLower.SingletonCertificate6815
