import ProximityPrize.SubmissionLower.R6966ProofNearCases
import ProximityPrize.SubmissionLower.R6966ProofNearTerminal
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalCount
import ProximityPrize.SubmissionLower.R6966ProofHeightTarget
import ProximityPrize.SubmissionLower.Low6966Endpoint

set_option Elab.async false

namespace Research6966.Endpoint6966
open ProximityPrize.Benchmark
open K1 (K)

theorem transition {u deleted} (M:P1.ModelAt 33677 u deleted) {Γ:Finset K}
    (F:P1.FamilyAt 179769 M Γ) (low:2330≤M.overhead) (high:M.overhead≤2499) :
    Γ.card≤274790602290452470 := by
  classical
  have lo:2330≤M.overhead.toNat:=by omega
  have hi:M.overhead.toNat≤2499:=by omega
  obtain ⟨D,⟨Crt⟩,regular,residues⟩:=Lower6960.FarPoleChart.of_family M F
  obtain ⟨C⟩:=NearCases.exists_cover F Crt lo hi regular residues
  obtain ⟨included,covered,marks⟩:=C.remaining
  exact covered.trans (NearTerminal.count F Crt lo hi C.main C.rescue C.index C.invoice
    rfl rfl C.main_ok.degreeCap C.rescue_ok.degreeCap included marks)

theorem high : Front6966.c7 := by
  intro u deleted M Γ F lo hi
  change 2330≤M.overhead at lo
  change M.overhead≤33677 at hi
  by_cases early:M.overhead≤2499
  · exact transition M F lo early
  · have far : 2500≤M.overhead := by omega
    exact FarTerminalCount.count M F far hi

theorem protocol : ProtocolClaim 6966 ProtocolProfile.p ProtocolProfile.q :=
  HeightTarget.of_height_counts LowProfile6966.low_6966 high

#print axioms transition
#print axioms high
#print axioms protocol
end Research6966.Endpoint6966
