import ProximityPrize.SubmissionLower.ZK7Ye0a
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 650000
namespace qQ9yWTb

private theorem convex_fee {u v R b c d entry a z cap:ℚ}
    (hu:0< u) (hv :0≤v) (hvu:v≤u) (hd:0<d)
    (ha :a≤R*(u-v)) (hz :d*z≤10*(c*v+b)^2)
    (hf :d*(R*u+entry)+10*b^2≤d*cap)
    (hl:d*entry+10*(c*u+b)^2≤d*cap) :a+z+entry≤ cap:= by
  have huv :=sub_nonneg.mpr hvu
  apply le_of_mul_le_mul_left _ (mul_pos hu hd)
  calc
    (u*d)*(a+z+entry)=u*(d*a+d*z+d*entry) := by ring
    _≤u*(d*(R*(u-v))+10*(c*v+b)^2+d*entry) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha hd.le) hz) le_rfl) hu.le
    _≤(u-v)*(d*(R*u+entry)+10*b^2)+v*(d*entry+10*(c*u+b)^2) := by
      rw [show (u-v)*(d*(R*u+entry)+10*b^2)+v*(d*entry+10*(c*u+b)^2) =
          u*(d*(R*(u-v))+10*(c*v+b)^2+d*entry)+10*c^2*u*v*(u-v) by ring]
      exact le_add_of_nonneg_right (by positivity)
    _≤(u-v)*(d*cap)+v*(d*cap) :=
      add_le_add (mul_le_mul_of_nonneg_left hf huv) (mul_le_mul_of_nonneg_left hl hv)
    _=(u*d)*cap:= by ring
end qQ9yWTb
