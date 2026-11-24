import ProximityPrize.SubmissionLower.ZEe4bHc
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
section
set_option autoImplicit true
namespace qVu1nGe
open P5_7_2 (fO)
open q7F2qKe
open qB9xHGe (ng upperGlobal)
open q5oHm3d
open qoK3iCb (BandWitness graphRate rateAt scalarSlope uq)
open TD (bCb)
private def bandB (b:fO) (n:ℕ) :Bool:=
 (List.range n).all fun o=>(List.range 4).all fun i=>paidCheck b o (afterFree b+1+i) && ratesCheck b o (afterFree b+1+i)
private theorem band_h {b:fO} {n:ℕ} (h:bandB b n=true) :
  ∀ (o:Fin n) (i:Fin 4),paidCheck b o (afterFree b+1+i)=true∧ratesCheck b o (afterFree b+1+i)=true:= fun o i=> by
 have h1:=List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) i.val (List.mem_range.mpr i.isLt)
 rwa [Bool.and_eq_true] at h1
end qVu1nGe
end
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
section
set_option autoImplicit true
namespace qVu1nGe
open qoK3iCb
private abbrev b0:P5_7_2.fO:=⟨0,by decide⟩
private theorem w0:BandWitness b0:=qoK3iCb.wit_of (by decide +kernel)
theorem r0:BandRows b0 :=
  band_of_checks (n:=13) w0 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
private abbrev b1 :P5_7_2.fO:=⟨1,by decide⟩
private theorem w1 :BandWitness b1 :=qoK3iCb.wit_of (by decide +kernel)
theorem r1 :BandRows b1 :=
  band_of_checks (n:=14) w1 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
private abbrev b2 :P5_7_2.fO:=⟨2,by decide⟩
private theorem w2 :BandWitness b2 :=qoK3iCb.wit_of (by decide +kernel)
theorem r2 :BandRows b2 :=
  band_of_checks (n:=14) w2 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
end qVu1nGe
end
section
set_option autoImplicit true
namespace qVu1nGe
open qoK3iCb
private abbrev b3:P5_7_2.fO:=⟨3,by decide⟩
private theorem w3:BandWitness b3:=qoK3iCb.wit_of (by decide +kernel)
theorem r3:BandRows b3 :=
  band_of_checks (n:=14) w3 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
private abbrev b4 :P5_7_2.fO:=⟨4,by decide⟩
private theorem w4 :BandWitness b4 :=qoK3iCb.wit_of (by decide +kernel)
theorem r4 :BandRows b4 :=
  band_of_checks (n:=14) w4 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
end qVu1nGe
end
section
set_option autoImplicit true
namespace qVu1nGe
open qoK3iCb
private abbrev b5:P5_7_2.fO:=⟨5,by decide⟩
private theorem w5:BandWitness b5:=qoK3iCb.wit_of (by decide +kernel)
theorem r5:BandRows b5 :=
  band_of_checks (n:=14) w5 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
private abbrev b6:P5_7_2.fO:=⟨6,by decide⟩
private theorem w6:BandWitness b6:=qoK3iCb.wit_of (by decide +kernel)
theorem r6:BandRows b6 :=
  band_of_checks (n:=14) w6 (by decide) (by decide) (qVu1nGe.band_h (by decide +kernel))
end qVu1nGe
end
section
set_option autoImplicit true
namespace qXrbKzb
open P5_7_2 (fO)
open qoK3iCb (BandWitness)

open scoped qoK3iCb
private abbrev b:fO:=⟨7,by decide⟩
private def data :ℕ:=0x3100f2091e7e9bd239400200118938d4498002000deb93ca3100f209a689d48c39400200111878b4498002000d99ba0c3940f2081ef26cd539400200112f17d7498002000d9947b92900f20a6d752df431000200125967e8418002000e9e33313957a2c5d7348fc83943521b033f5bd049835215600ab82b3903521d7b32a00e4983521708f93bcc59c35212548564f63944ba25bcf0617a41400a004943ca1451c0320121d09d3b498032015319c58a59c0320118514a3e72403200dddc48dc3943521a7c41746a51c352148635b2886203521058d3229149802200ea84b3aa62002200b199091a7a83520dd8933b8a620352118993f7047243520e86501c509303520b7e5f9eea59c352123336f0427243520ecd061e208b00aa0258b651a57a83520d6d5b182a9b03520b0cd46c68c4035208bfdc4171
private theorem w:BandWitness b:=qoK3iCb.wit_of (by decide +kernel)
theorem band7:y8 b 3:=grid_of_tests (data :=data) w (qXrbKzb.grid_of (by decide +kernel))
end qXrbKzb
end
