import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x8698951b025424b8100180271036f4c0ae928904bd600b2d163c80326c99c162980328760e700e64bab0667600e1f80e53041100181d51803e8cb7c441236f98085160112a01590050ee5e02579804abc545c0164cfd00a7a0014218d1f0061553402e680055eda49c01a4b9d00cba0016bd812f0070bfb403768005fa2b4dc01e023d00efa0
local notation "q!" k:arg n:arg=>block 327 71 (288+8*k) n=unpack (d >>> (90*k))
private theorem tE {x y:qKlO94b.Totals} (h:(x.r.beq y.r&&x.m.beq y.m&&x.e.beq y.e)=true) :x=y:= by
 simp only [Bool.and_eq_true] at h
 cases x; cases y; simp only [qKlO94b.Totals.mk.injEq]
 exact ⟨Nat.eq_of_beq_eq_true h.1.1,Nat.eq_of_beq_eq_true h.1.2,Nat.eq_of_beq_eq_true h.2⟩
set_option quotPrecheck false in
local notation "qk!"=>tE (by decide +kernel)
private theorem b0:q! 0 8:=qk!
private theorem b1 :q! 1 8:=qk!
private theorem b2 :q! 2 8:=qk!
private theorem b3:q! 3 8:=qk!
private theorem b4 :q! 4 8:=qk!
private theorem b5:q! 5 8:=qk!
private theorem b6:q! 6 8:=qk!
private theorem b7:q! 7 8:=qk!
private theorem b8:q! 8 8:=qk!
private theorem b9:q! 9 8:=qk!
private theorem b10 :q! 10 8:=qk!
private theorem b11 :q! 11 8:=qk!
theorem p4_4 :block 327 71 288 96=sumPacked d 12 :=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (b11)))))))))))
end qKlO94b
