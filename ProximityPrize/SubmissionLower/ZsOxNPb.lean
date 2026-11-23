import ProximityPrize.SubmissionLower.Ztdy5wb
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace qXrbKzb
open P5_7_2 (fO)
open qoK3iCb (BandWitness)
open q5oHm3d (ProjectionCheck)
open scoped qoK3iCb
private abbrev b:fO:=⟨10,by decide⟩
private def data :ℕ:=0x41424211a753cd4a39424211f89fd1993940f207bc1c3c2a414002000f3a769651c002000bf07084397873ddd516ac98394242138f1c4d5e3940f20832817e1139400200107ddce6498002000cf31e9c4982420f395a6b5a4982420fdd3d00a64140f2071f11d9a941400e00689c2a3a518002000c914016414242119588251441424211eb77fef63940f207b84c2ee941402200fb30bf0951c02200c50724194982420e983929f84982420f4fb5f3954140f206f5d9c3ae498002000d15cc6d620002000a398ac1498b4a4cb940ce06418b4a4fd387778b4144ba23c0f8232c59c0aa03c6d556167240aa02f6bce24851f8735b4e8fee3c49b8736f7fe6ac9c4197a2a98eef059349800a003fd5e66f62003200f91f788b59f873351c23edf051f8734e26f553614997a29fd8fddd9a6a003200f330211682c00a0025f9adfe49b87368d83faebd498b4a4bdcbc1839498352173db9e415620352107cb165b482c3520cf1a82a2349b8736ab0c644e849b8737cececd4c051c032012193ae527a803200d0e45ea19b003200a4b05d7d6238731be660c17359cb4a3e6e19093462035210979ffe179303520b9c50b8a7bbc35209156e858c62387320b76c44ec59f8733c59d3dc9459c3521214b8017282c3520c9e4e4859ab80aa01f91b270d7283520e1bffc6d26a43520fb7ad3eb08283520d0931ce8cbbc352091a1a0631ecc352071df56f0b
private theorem w:BandWitness b:=witnesses!
private theorem proj:ProjectionCheck b 11 13 (asb (entry data 5 11 4)) :=
  .inr ⟨7,by decide,stage_of_ordinate_bound checked! checked! checked!⟩
theorem dx1 :y8 b 5:=grid_of_tests (data :=data) w (by
  intro o t
  by_cases h:o.val=11∧t.val = 4
  · have ho:o=⟨11,by decide⟩:=Fin.ext h.1
    have ht:t=⟨4,by decide⟩:=Fin.ext h.2
    subst o
    subst t
    exact az proj
  · fin_cases o <;> fin_cases t <;>
      (first | exact (h (by decide)).elim | exact az (.inl checked!)))
end qXrbKzb
