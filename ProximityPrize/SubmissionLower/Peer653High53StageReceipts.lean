import ProximityPrize.SubmissionLower.Peer653High53StageLeaf01Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf01Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf02Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf02Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf03Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf03Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf04Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf04Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf05Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf05Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf06Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf06Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf07Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf07Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf08Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf08Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf09Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf09Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf10Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf10Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf11Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf11Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf12Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf12Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf13Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf13Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf14Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf14Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf15Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf15Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf16Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf16Moving
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf17Free
import ProximityPrize.SubmissionLower.Peer653High53StageLeaf17Moving

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false
set_option autoImplicit true

namespace Peer653High53Stages

open Peer653High53
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free)
    (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false

private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine cons receipt1Free receipt1Moving ?_
    refine cons receipt2Free receipt2Moving ?_
    refine cons receipt3Free receipt3Moving ?_
    refine cons receipt4Free receipt4Moving ?_
    refine cons receipt5Free receipt5Moving ?_
    refine cons receipt6Free receipt6Moving ?_
    refine cons receipt7Free receipt7Moving ?_
    refine cons receipt8Free receipt8Moving ?_
    refine cons receipt9Free receipt9Moving ?_
    refine cons receipt10Free receipt10Moving ?_
    refine cons receipt11Free receipt11Moving ?_
    refine cons receipt12Free receipt12Moving ?_
    refine cons receipt13Free receipt13Moving ?_
    refine cons receipt14Free receipt14Moving ?_
    refine cons receipt15Free receipt15Moving ?_
    refine cons receipt16Free receipt16Moving ?_
    refine cons receipt17Free receipt17Moving ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

#print axioms stage_bounds
end Peer653High53Stages
