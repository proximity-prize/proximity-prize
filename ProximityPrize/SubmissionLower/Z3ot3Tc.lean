import ProximityPrize.SubmissionLower.Zytxfqb
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace qKlO94b
private def d:=0x2530733a018438301a0d00099dda22806693cc071f400277cb4da01adf6301eed000a11ea0a806fcb4c085740028df927a01cdf43023cd000a52f0f2807692cc098f4002993742c01e42ccc28aa800a6f1eb1807acbce0ab600029cf763601ef5bf82c88000a758d69807c5b2e0b6e00029d7a91601f221782e680009ad45e2c07338d20ac7b001d8bee98015fcf9020eb00052bb5e6003d916405c2c000c44a498009213900dab0001135566000cce640132c
local notation "q!" k:arg n:arg=>block 171 38 (0+8*k) n=unpack (d >>> (90*k))
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
private theorem b14 :q! 14 8:=qk!
private theorem b15:q! 15 8:=qk!
theorem p2_1 :block 171 38 0 128=sumPacked d 16:=join b0 (join b1 (join b2 (join b3 (join b4 (join b5 (join b6 (join b7 (join b8 (join b9 (join b10 (join b11 (join b12 (join b13 (join b14 (b15)))))))))))))))
end qKlO94b
