import ProximityPrize.SubmissionLower.R6966ProofRegularPhysicalChart

set_option Elab.async false

namespace Research6966.PhysicalSeparant
open Polynomial
open K1_14_1 (jetConstant)
open K1_14_1_4 (doubleMap)
open RegularPhysicalChart (transform)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 450000
variable {R S:Type*} [CommRing R] [CommRing S]

def value (f:R→+*S) (y v:S) : R[X][X]→+*S:=eval₂RingHom (eval₂RingHom f y) v

private theorem natural (f:R→+*S) (a b u d:R) (y v:S) :
    (value f y v).comp (transform a b u d)=value f (f a*y+f b) (f a*v+f u*y+f d) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro c;simp [value,transform,K1_14_1_4.substitute,jetConstant]
    · simp [value,transform,K1_14_1_4.substitute,jetConstant,RegularPhysicalChart.yVar,RegularPhysicalChart.vVar]
  · simp [value,transform,K1_14_1_4.substitute,jetConstant,RegularPhysicalChart.yVar,RegularPhysicalChart.vVar]

private theorem linear_value (f:R→+*S) (y v:S) (P:R[X][X]) (deg:P.natDegree≤1) :
    value f y v P=(P.coeff 1).eval₂ f y*v+(P.coeff 0).eval₂ f y := by
  have eq:=congrArg (value f y v) (eq_X_add_C_of_natDegree_le_one deg)
  simpa only [value,coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,eval₂_X] using eq

theorem compare (f:R→+*S) (a b u d c:R) (P Q:R[X][X]) (p:P.natDegree≤1) (q:Q.natDegree≤1)
    (eq:transform a b u d P=jetConstant c*Q) (y:S) :
    f a*(P.coeff 1).eval₂ f (f a*y+f b)=f c*(Q.coeff 1).eval₂ f y := by
  have atV (v:S) : (P.coeff 1).eval₂ f (f a*y+f b)*(f a*v+f u*y+f d)+(P.coeff 0).eval₂ f (f a*y+f b)=
      f c*((Q.coeff 1).eval₂ f y*v+(Q.coeff 0).eval₂ f y) := by
    rw [←linear_value f _ _ P p,←linear_value f _ _ Q q]
    have input:=RingHom.congr_fun (natural f a b u d y v) P
    rw [←input,RingHom.comp_apply,eq,map_mul]
    simp [value,jetConstant]
  have one:=atV 1;have zero:=atV 0
  linear_combination one-zero

theorem nonzero_iff [IsDomain S] (f:R→+*S) (a b u d c:R) (ua:IsUnit a) (uc:IsUnit c)
    (P Q:R[X][X]) (p:P.natDegree≤1) (q:Q.natDegree≤1)
    (eq:transform a b u d P=jetConstant c*Q) (y:S) :
    (Q.coeff 1).eval₂ f y≠0 ↔ (P.coeff 1).eval₂ f (f a*y+f b)≠0 := by
  have both:=compare f a b u d c P Q p q eq y
  have left: f a≠0:=(ua.map f).ne_zero
  have right:f c≠0:=(uc.map f).ne_zero
  have identical: (f c*(Q.coeff 1).eval₂ f y=0) ↔
      (f a*(P.coeff 1).eval₂ f (f a*y+f b)=0) := by rw [both]
  exact not_congr (by simpa only [mul_eq_zero,or_iff_right right,or_iff_right left] using identical)

end
end Research6966.PhysicalSeparant
