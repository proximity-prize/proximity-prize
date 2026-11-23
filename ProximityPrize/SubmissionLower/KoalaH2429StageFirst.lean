import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2429Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2429Stages
open HighCore82258Stages
open KoalaH2429Banks

local notation "rank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage00_cert :
    BankCertificate 2429 stage00.reserve 0 stage00.free ∧
      BankCertificate 2429 stage00.reserve 1 stage00.moving :=
  ⟨(rank! 98,113046,0x103db5fe64,0x907bd3a118), (rank! 579,395932,0x706286f841d8,0x52d03680e2df18)⟩

end KoalaH2429Stages
