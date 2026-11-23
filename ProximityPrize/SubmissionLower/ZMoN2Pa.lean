import ProximityPrize.SubmissionLower.Zsx1Iye
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 50000
set_option maxRecDepth 256
namespace P6_6_8_3
open aR (Shape ceilDiv)


open P6_6
open private Linear eB eJ eT bvc from ProximityPrize.SubmissionLower.ZhZv6fd
open private cEr from ProximityPrize.SubmissionLower.E6
open private den upperNum upper_linear from ProximityPrize.SubmissionLower.Zsx1Iye
private theorem enough_round (n d:ℕ) (hd:0<d) :n≤d*ceilDiv n d:= by
  unfold ceilDiv
  have hm:=Nat.mod_lt (n+d - 1) hd
  have he :=Nat.mod_add_div (n+d - 1) d
  omega
private theorem top_pay {r :Shape} {m:ℕ} (h:3*r.t≤ r.j) :
    m*r.t≤ ceilDiv m 3*r.j:= by
  calc
    m*r.t≤(3*ceilDiv m 3)*r.t:=Nat.mul_le_mul_right _ (enough_round _ _ (by decide))
    _=ceilDiv m 3*(3*r.t) := by ac_rfl
    _≤ ceilDiv m 3*r.j:=Nat.mul_le_mul_left _ h
private theorem round_linear (f :Shape→ℤ) (hf :Linear f) (d:ℕ) (hd:0<d)
    (x :Shape) :
    ceilDiv (f x).toNat d ≤
      x.b*ceilDiv (f eB).toNat d + x.j*ceilDiv (f eJ).toNat d +
      x.t*ceilDiv (f eT).toNat d:= by
  apply cEr
  let m:= fun e=>ceilDiv (f e).toNat d
  have h (e :Shape) :f e≤(d:ℤ)*(m e :ℤ) :=bvc _ hd
  have he :f x≤((d*(x.b*m eB + x.j*m eJ + x.t*m eT) :ℕ) :ℤ) := calc
    _=(x.b:ℤ)*f eB+(x.j:ℤ)*f eJ+(x.t:ℤ)*f eT:=hf x
    _≤(x.b:ℤ)*((d:ℤ)*(m eB:ℤ)) +
        (x.j:ℤ)*((d:ℤ)*(m eJ:ℤ)) +
        (x.t:ℤ)*((d:ℤ)*(m eT:ℤ)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h _) (Int.natCast_nonneg x.b))
        (mul_le_mul_of_nonneg_left (h _) (Int.natCast_nonneg x.j)))
        (mul_le_mul_of_nonneg_left (h _) (Int.natCast_nonneg x.t))
    _ = _:= by
      simp only [Nat.cast_add,Nat.cast_mul]
      ring
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat he
private theorem linear_pay (A x :Shape) :
    ceilDiv (upperNum A x).toNat den ≤
      x.b*ceilDiv (upperNum A eB).toNat den +
      x.j*ceilDiv (upperNum A eJ).toNat den +
      x.t*ceilDiv (upperNum A eT).toNat den :=
  round_linear (upperNum A) (upper_linear A) den (by decide) x
end P6_6_8_3
