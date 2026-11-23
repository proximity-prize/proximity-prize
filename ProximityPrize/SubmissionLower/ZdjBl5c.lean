import ProximityPrize.SubmissionLower.ZXiQNLd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qh06gse
noncomputable section
open Polynomial
open P5 (K)

open qaySLPd (pe RS)
open cu (L FX aZ Jet kr j9 qD)
open DP (Source U4)
open private bjE.alC dGu ady from ProximityPrize.SubmissionLower.Z
private theorem lift_base :lift=bjE.alC:= by
  apply Polynomial.ringHom_ext
  · intro q
    change lift (C q)=bjE.alC (C q)
    rw [bIr,bjE.alC,coe_eval₂RingHom,eval₂_C]
    rfl
  · rw [cXC]
    simp [bjE.alC,uk.center]
abbrev fibreMap (S:K[X]) :Jet →+* aZ :=
  eval₂RingHom (evalRingHom (MvPolynomial.C (kr S))) (MvPolynomial.C (kr S.derivative))
theorem fibre_mark (f :Jet) (S:K[X]) (z :K) :
    qD z (RS f S)=cu.rD f z S:= by
  change qD z (fibreMap S f)=XY.vf z S f
  have h: (qD z).comp (fibreMap S)=XY.vf z S:= by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext <;> simp [ XY.vf,fibreMap,qD]
    · simp [ XY.vf,fibreMap,qD]
  exact RingHom.congr_fun h _
private abbrev rawFibre (S:K[X]) :Source →+* pe[X] :=
  eval₂RingHom (evalRingHom ((j9 S).map MvPolynomial.C))
    ((j9 S.derivative).map MvPolynomial.C)
private theorem lift_raw (P:Source) (S:K[X]) :
    lift (rawFibre S P)=fibreMap S (U4 P) := by
  have hpol (T:L[X]) :lift (T.map MvPolynomial.C)=MvPolynomial.C (algebraMap L[X] FX T) := by
    have h:lift.comp (mapRingHom (MvPolynomial.C:L →+* pe)) =
        (MvPolynomial.C:FX →+* aZ).comp (algebraMap L[X] FX) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [bIr,uk.wZ,uk.gA]
      · simp [cXC,uk.center]
    exact RingHom.congr_fun h _
  rw [← RingHom.comp_apply]
  have h:lift.comp (rawFibre S)=(fibreMap S).comp (ady bjE.alC) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        simp [ady,lift_base]
      · simp [ady,hpol,kr]
    · simp [ady,hpol,kr]
  rw [h,RingHom.comp_apply,← dGu]
end
end qh06gse
