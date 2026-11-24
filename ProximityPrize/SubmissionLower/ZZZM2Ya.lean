import ProximityPrize.SubmissionLower.ZMoN2Pa
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 50000
set_option maxRecDepth 256
namespace P6_6_8_3
open aR (Shape ceilDiv)


open P6_6
open private eB eJ eT from ProximityPrize.SubmissionLower.ZhZv6fd


open private L g den upperNum from ProximityPrize.SubmissionLower.Zsx1Iye
private def zeroUpper (B J:ℕ) :ℕ :=
  let H :=J*B
  ceilDiv (4*L*P6.t*(B*B^2+H^2)) g+B*B+H^2+B
private theorem ceiling_mono {a b d:ℕ} (h:a≤b) :ceilDiv a d≤ ceilDiv b d :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h d) 1)
private def positiveRates (A:Shape) :Shape :=
  let f := fun x=>ceilDiv (upperNum A x).toNat den
  ⟨f eB+zeroUpper A.b A.j,f eB+f eJ+ceilDiv (f eT) 3,0⟩
private theorem zero_le {r A:Shape} (hs :JetShape r) (ht:0< r.t) (hb:r.b≤A.b)
    (hj:r.j≤A.j) :
    (let u:=r.b - r.t
     let c:=(r.j-3*r.t)/2
     let h:=max u ((2*c - 1)*u - c^2)
     ceilDiv (4*L*P6.t*(r.b*u^2+h^2)) g+r.b*u+h^2+u)≤zeroUpper A.b A.j:= by
  let u:=r.b - r.t
  let c:=(r.j-3*r.t)/2
  have hu:u≤ r.b:=Nat.sub_le _ _
  have hc:2*c - 1≤ r.j:= by dsimp [c]; omega
  have h1 :1≤ r.j:= by have :=hs.2.1; omega
  have hG:max u ((2*c - 1)*u - c^2)≤A.j*A.b :=
    (max_le ((hu.trans (by simpa only [one_mul] using Nat.mul_le_mul_right r.b h1)))
      ((Nat.sub_le _ _).trans (Nat.mul_le_mul hc hu))).trans (Nat.mul_le_mul hj hb)
  have hU:=hu.trans hb
  change ceilDiv (4*L*P6.t*(r.b*u^2+(max u ((2*c - 1)*u - c^2))^2)) g +
    r.b*u+(max u ((2*c - 1)*u - c^2))^2+u≤_
  unfold zeroUpper
  apply Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ (Nat.mul_le_mul hb hU))
    (Nat.pow_le_pow_left hG 2)) hU
  exact ceiling_mono (Nat.mul_le_mul_left _
    (Nat.add_le_add (Nat.mul_le_mul hb (Nat.pow_le_pow_left hU 2)) (Nat.pow_le_pow_left hG 2)))
end P6_6_8_3
