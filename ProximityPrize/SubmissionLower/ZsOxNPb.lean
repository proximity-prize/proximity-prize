import ProximityPrize.SubmissionLower.Ztdy5wb
set_option Elab.async false
section
set_option autoImplicit true
namespace qoK3iCb
open P5_7_2 (fO)
private def wB (b:fO) :Bool:=(List.range 52).all fun i=>scalarCheck b (i+3) (extra b (i+3)) (copies b (i+3))
private theorem wit_of {b:fO} (h:wB b=true) :BandWitness b:=
 witness_of_checks fun i=>List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qXrbKzb
open P5_7_2 (fO Ls)
open q7F2qKe
open qB9xHGe (ng)
open qoK3iCb (BandWitness graphRate scalarSlope uq)
open q5oHm3d
open TD (GM bCb)
open cu (Shape)
private def restB (b:fO) (o j w:ℕ) :Bool:=
 decide (graphRate 55≤asb w) && decide (0≤ rowHeight b w) &&
 decide (graphRate (rowLimit w+1)≤asb w) && rateTests b (asb w) (rowHeight b w) (rowLimit w) &&
 (List.finRange 4).all fun k=>decide (asb w*SS b j 0 k+rowHeight b w*SS b j 1 k≤ng b o j k)
private theorem rest_of {b:fO} {o j w:ℕ} (hp:ProjectionCheck b o j (asb w)) (h:restB b o j w=true) :
  RowTests b o j w := by
 unfold restB at h
 rw [Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true] at h
 obtain ⟨⟨⟨⟨h2,h3⟩,h4⟩,h5⟩,h6⟩:=h
 exact ⟨hp,of_decide_eq_true h2,of_decide_eq_true h3,of_decide_eq_true h4,h5,
  fun k=>of_decide_eq_true (List.all_eq_true.mp h6 k (List.mem_finRange k))⟩
private def gridX (b:fO) (n data:ℕ) :Bool:=
 (List.range 13).all fun o=>(List.range n).all fun t=>(o==11 && t==4) ||
  (decide (project (aHp b (t+9)) (clip b o (t+9))≤asb (entry data n o t)) && restB b o (t+9) (entry data n o t))
private theorem gridX_of {b:fO} {n data:ℕ} (h:gridX b n data=true) (o:Fin 13) (t:Fin n)
  (hx:¬(o.val=11∧t.val=4)) :RowTests b o (t.val+9) (entry data n o t) := by
 have h1:=List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) t.val (List.mem_range.mpr t.isLt)
 rw [Bool.or_eq_true,Bool.and_eq_true,Bool.and_eq_true,beq_iff_eq,beq_iff_eq] at h1
 obtain ⟨hp,hr⟩:=h1.resolve_left hx
 exact rest_of (Or.inl (of_decide_eq_true hp)) hr
end qXrbKzb
end
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
private theorem w:BandWitness b:=qoK3iCb.wit_of (by decide +kernel)
private theorem proj:ProjectionCheck b 11 13 (asb (entry data 5 11 4)) :=
  .inr ⟨7,by decide,stage_of_ordinate_bound (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
theorem dx1 :y8 b 5:=grid_of_tests (data :=data) w (by
  intro o t
  by_cases h:o.val=11∧t.val = 4
  · have ho:o=⟨11,by decide⟩:=Fin.ext h.1
    have ht:t=⟨4,by decide⟩:=Fin.ext h.2
    subst o
    subst t
    exact qXrbKzb.rest_of proj (by decide +kernel)
  · exact qXrbKzb.gridX_of (by decide +kernel) o t h)
end qXrbKzb
