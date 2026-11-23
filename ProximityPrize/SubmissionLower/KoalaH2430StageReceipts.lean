import ProximityPrize.SubmissionLower.KoalaH2430StageReceipt1
import ProximityPrize.SubmissionLower.KoalaH2430StageReceipt2
import ProximityPrize.SubmissionLower.KoalaH2430StageReceipt3
import ProximityPrize.SubmissionLower.KoalaH2430StageReceipt4
import ProximityPrize.SubmissionLower.KoalaH2430StageReceipt5
import ProximityPrize.SubmissionLower.KoalaH2430StageReceipt6

set_option autoImplicit false

namespace KoalaH2430Stages
open HighCore82258 (stages Stage start)
open HighCore82258Stages (BankCertificate)

private def Checks (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate 2430 s.reserve 0 s.free ∧ BankCertificate 2430 s.reserve 1 s.moving

private theorem cons {s : Stage} {ss : List Stage}
    (hf : BankCertificate 2430 s.reserve 0 s.free)
    (hm : BankCertificate 2430 s.reserve 1 s.moving)
    (ht : Checks ss) : Checks (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

theorem certificates : ∀ s ∈ stages .h2430,
    BankCertificate (start .h2430) s.reserve 0 s.free ∧
    BankCertificate (start .h2430) s.reserve 1 s.moving := by
  change Checks KoalaH2430Banks.stages
  unfold KoalaH2430Banks.stages
  refine cons stage00_0 stage00_1 ?_
  refine cons stage01_0 stage01_1 ?_
  refine cons stage02_0 stage02_1 ?_
  refine cons stage03_0 stage03_1 ?_
  refine cons stage04_0 stage04_1 ?_
  refine cons stage05_0 stage05_1 ?_
  refine cons stage06_0 stage06_1 ?_
  refine cons stage07_0 stage07_1 ?_
  refine cons stage08_0 stage08_1 ?_
  refine cons stage09_0 stage09_1 ?_
  refine cons stage10_0 stage10_1 ?_
  refine cons stage11_0 stage11_1 ?_
  refine cons stage12_0 stage12_1 ?_
  refine cons stage13_0 stage13_1 ?_
  refine cons stage14_0 stage14_1 ?_
  refine cons stage15_0 stage15_1 ?_
  refine cons stage16_0 stage16_1 ?_
  refine cons stage17_0 stage17_1 ?_
  refine cons stage18_0 stage18_1 ?_
  refine cons stage19_0 stage19_1 ?_
  refine cons stage20_0 stage20_1 ?_
  refine cons stage21_0 stage21_1 ?_
  exact fun _ hs => (List.not_mem_nil hs).elim

#print axioms certificates
end KoalaH2430Stages
