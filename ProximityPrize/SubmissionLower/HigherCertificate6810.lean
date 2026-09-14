import ProximityPrize.SubmissionLower.HigherClosure6810
import ProximityPrize.SubmissionLower.HigherFiniteCertificate6810
namespace ProximityPrize.SubmissionLower.HigherCertificate6810
open RCN095 LocatorFactorAggregate
open HigherFiniteCertificate6810 Lower80850
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private theorem ledger_transfer (a b c d e f : ℕ) (hc : c=e) (hd : d=f)
    (h : a+b+e+f+18000000000000+(1872396431124186+160822954741488) ≤ 274736416276891560) :
    a+b+c+d+18000000000000+1872396431124186+39*4123665506192 ≤ 274736416276891560 := by
  omega

theorem ledgerReceipt : Assembly.LedgerReceiptSound PhaseSemantics.phaseCap Closure.ledgerBudget := by
  constructor
  · decide +kernel
  · intro r v z hr hR hY hT
    have h := LedgerAudit.RunsValid.sound (PhaseData.rowContext r v) (LedgerData.lookup r v)
      0 z (ledger_all r v hr hR hY) (Nat.zero_le _) (by change z < 8866-(r+v); omega)
    change PhaseRows.capBefore (PhaseData.rowContext r v) 10 z +
      Initial.initialAComplement (LocatorPhase6800Oracle.rawFlag r v z) +
      r * AsymmetricChainPolynomial80850.unit (r+v) (r+v+z) r +
      (37-r) * AsymmetricChainPolynomial80850.unit (164-(r+v)) (38980-(r+v+z)) (37-r) +
      18000000000000 + (1872396431124186+160822954741488) ≤ 274736416276891560 at h
    change PhaseRows.capBefore (PhaseData.rowContext r v) 10 z +
      Initial.initialAComplement (LocatorPhase6800Oracle.rawFlag r v z) +
      r * AsymmetricChainPolynomial80850.unit (v+r) (z+v+r) r +
      (37-r) * AsymmetricChainPolynomial80850.unit (164-(v+r)) (38980-(z+v+r)) (37-r) +
      18000000000000 + 1872396431124186 + 39*4123665506192 ≤ 274736416276891560
    have hu : AsymmetricChainPolynomial80850.unit (v+r) (z+v+r) r =
        AsymmetricChainPolynomial80850.unit (r+v) (r+v+z) r :=
      congrArg₂ (fun y t => AsymmetricChainPolynomial80850.unit y t r)
        (show v+r = r+v by omega) (show z+v+r = r+v+z by omega)
    have hv : AsymmetricChainPolynomial80850.unit (164-(v+r)) (38980-(z+v+r)) (37-r) =
        AsymmetricChainPolynomial80850.unit (164-(r+v)) (38980-(r+v+z)) (37-r) :=
      congrArg₂ (fun y t => AsymmetricChainPolynomial80850.unit (164-y) (38980-t) (37-r))
        (show v+r = r+v by omega) (show z+v+r = r+v+z by omega)
    exact ledger_transfer _ _ _ _ _ _ (congrArg (fun u => r*u) hu)
      (congrArg (fun u => (37-r)*u) hv) h

theorem protocolClaim : ProximityPrize.Benchmark.ProtocolClaim 6810 10348847 33554432 :=
  Closure.protocolClaim6810 baseReceipt prefixReceipt thresholdReceipt runsReceipt ledgerReceipt

#print axioms protocolClaim
end ProximityPrize.SubmissionLower.HigherCertificate6810
