import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x2073ed9f00bd2934076680082db269c030209d01eba0020ef61af00c393b407f6800847a36dc031973d020fa00214525bf00c8de3408868008590071c032c5dd0233a00217be6e920cd06728915f408634b437833a6632255fc02198e396e0cfd0788991f0086818b7f8342dc92270fc021a4d3e8e0d1599089edf00869cbec783470ef2283fc
local notation "q!" k:arg n:arg=>block 327 71 (96+8*k) n=unpack (d >>> (90*k))
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
theorem p4_2 :block 327 71 96 96=sumPacked d 12 :=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (b11)))))))))))
end qKlO94b
