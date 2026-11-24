import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x18fdc53f007f0a34040680067f6851c02170dd0113a001ae9194f008c34b404968006f04155c024977d0137a001c863d5f00983f34052680074e6659c027761d015ba001ddbf16f00a329b405b680079b875dc02a0cbd017fa001ef0f57f00acf43406468007d95461c02c5b5d01a3a001fcc098f00b59eb406d68008097d65c02e61fd01c7a0
local notation "q!" k:arg n:arg=>block 327 71 (192+8*k) n=unpack (d >>> (90*k))
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
theorem p4_3:block 327 71 192 96=sumPacked d 12 :=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (b11)))))))))))
end qKlO94b
