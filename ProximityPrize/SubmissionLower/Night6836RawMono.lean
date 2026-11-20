/- Apache-2.0. Monotonicity of the physical raw invoice across a total-degree bin. -/
import ProximityPrize.SubmissionLower.K6833TerminalPrices
namespace ProximityPrize.SubmissionLower.Raw6836
open RCN095 K6833Residual
set_option maxHeartbeats 1000000
def rowRaw (r e z:ℕ) :=
  rawChargeWithCorrections TailCorrections.original ((⟨r,r+e,r+e+z⟩:Envelope).pad 0) (⟨z,e,r⟩:FlagDegree)
private def pointwise (p q:FlagDegree) : Prop := p.zOnly≤q.zOnly ∧ p.yz≤q.yz ∧ p.all≤q.all
private theorem mixed_mono {p q r p' q' r' :FlagDegree} (hp:pointwise p p') (hq:pointwise q q') (hr:pointwise r r') :
    flagMixed p q r ≤ flagMixed p' q' r' := by
  obtain ⟨pp,pm,ps⟩ := hp; obtain ⟨qp,qm,qs⟩ := hq; obtain ⟨rp,rm,rs⟩ := hr
  unfold flagMixed
  gcongr
theorem raw_mono_z (r e:ℕ) {z hi:ℕ} (h:z≤hi) : rowRaw r e z ≤ rowRaw r e hi := by
  let f (v:ℕ) := ((⟨r,r+e,r+e+v⟩:Envelope).pad 0)
  have dm : (f z).total-(f z).middle ≤ (f hi).total-(f hi).middle := by
    simp only [f,Envelope.pad]
    omega
  have coords : pointwise (⟨z,e,r⟩:FlagDegree) ⟨hi,e,r⟩ := ⟨h,le_rfl,le_rfl⟩
  have fst : pointwise (firstTail (f z)) (firstTail (f hi)) :=
    ⟨Nat.mul_le_mul_left _ dm,le_rfl,le_rfl⟩
  have nrm : pointwise (normalTail 0 (f z)) (normalTail 0 (f hi)) :=
    ⟨Nat.mul_le_mul_left _ dm,le_rfl,le_rfl⟩
  have mov : pointwise (movingFiber (f z)) (movingFiber (f hi)) := ⟨dm,le_rfl,le_rfl⟩
  have ord : pointwise (ordinaryMovingTail (f z)) (ordinaryMovingTail (f hi)) :=
    ⟨Nat.mul_le_mul_left _ dm,le_rfl,le_rfl⟩
  exact Nat.add_le_add (mixed_mono coords fst nrm) (Nat.mul_le_mul_left 65539 (mixed_mono coords mov ord))
end ProximityPrize.SubmissionLower.Raw6836
#print axioms ProximityPrize.SubmissionLower.Raw6836.raw_mono_z
