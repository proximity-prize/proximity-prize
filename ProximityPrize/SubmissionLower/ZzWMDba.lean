import ProximityPrize.SubmissionLower.ZogIzOe
set_option Elab.async false
open _root_ renaming add_le_add→aU,le_rfl→c9,mul_le_mul_of_nonneg_left→nX,mul_le_mul_of_nonneg_right→lJ
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace q9NbxKa
noncomputable section









open Finset
open scoped Classical
private theorem mix {a a₀ r b m H T s E :ℚ} (h₀:a₀≤a) (hr :a< r)
    (hH :0≤H) (hE :0≤E) (direct :T≤ r*m) (other :T≤a₀*m+s*H+E)
    (rate :s*(r-a)/(r-a₀)≤b) :T≤a*m+b*H+E := by
  let θ:=(r-a)/(r-a₀)
  have hden:0< r-a₀:=sub_pos.mpr (h₀.trans_lt hr)
  have hθ:0≤θ:=div_nonneg (sub_nonneg.mpr hr.le) hden.le
  have hθ₁:θ≤1 :=(div_le_one hden).mpr (sub_le_sub_left h₀ r)
  have hcancel:θ*(r-a₀)=r-a :=div_mul_cancel₀ _ hden.ne'
  have hslope : (1-θ)*r+θ*a₀=a := by linarith only [hcancel]
  have hrate :s*θ≤b:= by simpa only [θ,mul_div_assoc] using rate
  calc
    T=(1-θ)*T+θ*T:= by ring
    _≤(1-θ)*(r*m)+θ*(a₀*m+s*H+E) :=
      aU (nX direct (sub_nonneg.mpr hθ₁))
        (nX other hθ)
    _=a*m+(s*θ)*H+θ*E := by rw [← hslope]; ring
    _≤_:=aU (aU c9 (lJ hrate hH))
      (by simpa only [one_mul] using lJ hθ₁ hE)
private theorem mix_zero {a r b m H T s E :ℚ} (ha :0≤a) (hr :a< r)
  (hH :0≤H) (hE :0≤E) (direct :T≤ r*m) (other :T≤ s*H+E)
  (rate : (1-a/r)*s≤b) :T≤a*m+b*H+E := by
 have he : (r-a)/r=1-a/r := by rw [sub_div,div_self (ha.trans_lt hr).ne']
 apply mix ha hr hH hE direct (by simpa only [zero_mul,zero_add] using other)
 calc
  _=s*((r-a)/r) := by rw [sub_zero,mul_div_assoc]
  _=(1-a/r)*s := by rw [he,mul_comm]
  _≤b:=rate
private theorem ePj:YY.c2 :=
 aBb.of_children czq.proof bzX.proof
end
end q9NbxKa
