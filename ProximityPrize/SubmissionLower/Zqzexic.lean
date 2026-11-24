import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x84f530000425e000320000d2cc2200069b5c005080008818f340044cce003520003fba54d00208c880198800194f225400d164600a72000915e751004c410003e080030b4f730019f89901592000f83928d0086d17407288004c0719c002a2635024b200168fd67100ccb5480b7040067d346a803c4d4c03774001cf1c3fa01137c30104d0007e21f52804cd4cc04af40021c04d9a0150ba30152d0008e8213a805aec4c05e74
local notation "q!" k:arg n:arg=>block 171 38 (128+8*k) n=unpack (d >>> (90*k))
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
private theorem b12 :q! 12 8:=qk!
private theorem b13:q! 13 8:=qk!
private theorem b14 :q! 14 7:=qk!
theorem p2_2 :block 171 38 128 119=sumPacked d 15:=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (join b11 (join b12 (join b13 (b14))))))))))))))
end qKlO94b
