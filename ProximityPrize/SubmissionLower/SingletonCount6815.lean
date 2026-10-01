import ProximityPrize.SubmissionLower.SingletonData6815
import ProximityPrize.SubmissionLower.MergedInfra6815_28
import ProximityPrize.SubmissionLower.MergedInfra6815_48
import ProximityPrize.SubmissionLower.MergedInfra6815_13
import ProximityPrize.SubmissionLower.MergedInfra6815_0
namespace ProximityPrize.SubmissionLower.SingletonCount6815
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorFactorAggregate LocatorPhase6800Oracle LocatorBatchPhase6800
open Lower80899.Oracle Lower80899.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181245 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i)=u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex Q) (hr : (regularCumulativeFlag Q F).all≤39)
    (hy : middle (regularCumulativeFlag Q F)≤182) (ht : total (regularCumulativeFlag Q F)≤11192)
 :
    (regularSeeds Q selected Gamma F).card≤SingletonData6815.cap
      (regularCumulativeFlag Q F).all (regularCumulativeFlag Q F).yz (regularCumulativeFlag Q F).zOnly := by
  let p := regularCumulativeFlag Q F
  have hr1 : 1≤p.all := regularCumulativeFlag_positive Q F
  have hY : p.all+p.yz≤182 := by simpa only [p,middle,Nat.add_comm] using hy
  have hc := SingletonData6815.checked p.all p.yz hr1 hr hY
  exact SingletonCurveGeometry6815.count_of_curve D P hDlow hDchar Q hQ hbox
    selected Gamma u0 u1 hdegree hagreement hno F hr hy ht
    (SingletonCertificate6815.thresholds (SingletonData6815.row p.all p.yz))
    (SingletonData6815.row p.all p.yz).curve (SingletonData6815.row p.all p.yz).choices
    (SingletonCertificate6815.check_curve _ _ _ hc)
    (SingletonCertificate6815.check_thresholds _ _ _ hc)

end
end ProximityPrize.SubmissionLower.SingletonCount6815
