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
private def rowB (b:fO) (o j w:ℕ) :Bool:=
 decide (project (aHp b j) (clip b o j)≤asb w) && decide (graphRate 55≤asb w) && decide (0≤ rowHeight b w) &&
 decide (graphRate (rowLimit w+1)≤asb w) && rateTests b (asb w) (rowHeight b w) (rowLimit w) &&
 (List.finRange 4).all fun k=>decide (asb w*SS b j 0 k+rowHeight b w*SS b j 1 k≤ng b o j k)
private theorem row_of {b:fO} {o j w:ℕ} (h:rowB b o j w=true) :RowTests b o j w := by
 unfold rowB at h
 rw [Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true] at h
 obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩:=h
 exact ⟨Or.inl (of_decide_eq_true h1),of_decide_eq_true h2,of_decide_eq_true h3,of_decide_eq_true h4,h5,
  fun k=>of_decide_eq_true (List.all_eq_true.mp h6 k (List.mem_finRange k))⟩
private def gridB (b:fO) (n data:ℕ) :Bool:=
 (List.range 13).all fun o=>(List.range n).all fun t=>rowB b o (t+9) (entry data n o t)
private theorem grid_of {b:fO} {n data:ℕ} (h:gridB b n data=true) :
  ∀ (o:Fin 13) (t:Fin n),RowTests b o (t.val+9) (entry data n o t):= fun o t=>
 row_of (List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) t.val (List.mem_range.mpr t.isLt))
end qXrbKzb
end
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace qXrbKzb
open P5_7_2 (fO)
open qoK3iCb (BandWitness)

open scoped qoK3iCb
private abbrev b:fO:=⟨11,by decide⟩
private def data :ℕ:=0x498002000daccb56394242130a864f984140f206edf122a641806202c1d0e89659c002000b62c6aa414002000ee76b94390242141ce4f86c4140f20746e80f6541406202de321b1951c00a003ad9687059c002000b79bee941424211283341444980f2065199c11d498062028fe82eb651c00a0039e1a197498002000d61d51039424212cbfab2cc4180f206d9adbef5498032015027c35d62000a003478c4b859c002000ae7b7c841424210a99128e44980f206288b457f51c00a003beb06f76a4002000950bdf051c002000bc40a524142421166a023d84980f20665d3e5be620032010614f4327a800a0028f4b23e5a002200b6c4d2674142421087d6a3ac49901267f765502751c0aa03f48d849a6a4002000941d9f96a400200095de3384982420f5664847051c0f205ba97a7dc6a403200e360182a8b000a00235b3cc859c02200c0ac2b66414242110877159051835214cfd82b146a43520f7cfe9fb08ac0aa026c79771659c02200bff824004980aa04a15f09fc6203521158d90cad8283520cfb74084fa340aa020a6b37787a8022008f64013251c0aa03f239f0847243520eb0b3937f9b43520ae0f0fc71c400aa01b213a80a724022009275bdf84980aa044b17cb186a03520ff922aa828b03520bd136281eb3c0aa01d72712f88ac022007e6e121c6a4022009e77de589300aa024da0cbeac400aa01b448524efd40220043f4aacc
private theorem w:BandWitness b:=qoK3iCb.wit_of (by decide +kernel)
theorem dx2 :y8 b 5:=grid_of_tests (data :=data) w (qXrbKzb.grid_of (by decide +kernel))
end qXrbKzb
