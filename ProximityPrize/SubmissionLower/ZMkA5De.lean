import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x21a83f3ae0d201a88a29f0086a26e0f83487d5228efc021a8ad8ce0d228c08a45f007f575e88031b1b4826e7701bbb25b200ad26620878e005eea8d080250a5c81cff8013d45052007bd002060ee004020b388019068481397800c5638f2004d07a203c4e0022f9d20800da62c80aaf800540df920020cd42019ae000775e888002e954802478
local notation "q!" k:arg n:arg=>block 327 71 (0+8*k) n=unpack (d >>> (90*k))
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
theorem p4_1 :block 327 71 0 96=sumPacked d 12 :=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (b11)))))))))))
end qKlO94b
