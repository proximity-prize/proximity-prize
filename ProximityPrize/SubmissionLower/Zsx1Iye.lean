import ProximityPrize.SubmissionLower.Zsr715c
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 50000
set_option maxRecDepth 256
namespace P6_6_8_3
open aR (Shape)


open P6_6
open private Linear lin_add lin_mul_l lin_mul_r lin_b lin_pair lin_curve lin_mixed from ProximityPrize.SubmissionLower.ZhZv6fd


private abbrev L:=bf
private abbrev g:=mV
private abbrev den:=32*g
private def upperNum (A x :Shape) :ℤ :=
  let P:=m6
  let E :=curve32 A x P
  (g:ℤ)*pair32 false A x P +
    32*((P6.t:ℤ)+2*g)*x.b*P.b*(weightedChart (L+1) A).b +
    (2+2*(A.t:ℤ))*E A+E (joinBody A P) +
    g*wP x P A A+64*(g:ℤ)*gZ*x.b*P.b
private theorem upper_linear (A:Shape) :Linear (upperNum A) := by
  let P:=m6
  have h0:Linear (fun x=>(g:ℤ)*pair32 false A x P) :=
    lin_mul_l (lin_pair false A P)
  have h1 :Linear (fun x=>32*((P6.t:ℤ)+2*g)*x.b*P.b *
      (weightedChart (L+1) A).b) :=
    lin_mul_r (lin_mul_r (lin_mul_l lin_b))
  have h2 :Linear (fun x=>(2+2*(A.t:ℤ))*curve32 A x P A) :=
    lin_mul_l (lin_curve A P A)
  have h3:=lin_curve A P (joinBody A P)
  have h4 :Linear (fun x=>(g:ℤ)*wP x P A A) :=
    lin_mul_l (lin_mixed P A A)
  have h5:Linear (fun x=>64*(g:ℤ)*gZ*x.b*P.b) :=
    lin_mul_r (lin_mul_l lin_b)
  exact lin_add (lin_add (lin_add (lin_add (lin_add h0 h1) h2) h3) h4) h5
end P6_6_8_3
