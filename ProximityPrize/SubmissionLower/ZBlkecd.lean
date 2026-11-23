import ProximityPrize.SubmissionLower.Z5cOcra
import ProximityPrize.SubmissionLower.ZR3mCBd
import ProximityPrize.SubmissionLower.ZULJdud
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qVHIGFe
noncomputable section
open Polynomial TrivSqZeroExt
open cu (L FX)
open P5_7_7 (phys)
open qNu3xvc (physicalDerivative seedDerivative)
open private aug aug_eval dualLift lift_on aug_lift from ProximityPrize.SubmissionLower.ZR3mCBd
open private chain chain₂ from ProximityPrize.SubmissionLower.Z5cOcra
private abbrev T:=TrivSqZeroExt FX FX
private def c:L →+* FX:=phys.comp Polynomial.C
private theorem ev :eval₂RingHom c (phys Polynomial.X)=phys := by
 apply Polynomial.ringHom_ext
 · intro a
   exact eval₂_C _ _
 · exact eval₂_X _ _
private def f :L[X] →+* T :=
 eval₂RingHom ((inlHom FX FX).comp c) (inl (phys Polynomial.X)+inr 1)
private theorem hf : (aug FX).comp f=(RingHom.id FX).comp (algebraMap L[X] FX) := by
 rw [f,aug_eval,RingHom.id_comp]
 change eval₂RingHom ((aug FX).comp ((inlHom FX FX).comp c)) (phys Polynomial.X)=phys
 have hc: (aug FX).comp ((inlHom FX FX).comp c)=c:= by
  ext a
  rfl
 rw [hc,ev]
private def g:FX →+* T:=dualLift f (RingHom.id FX) hf
private theorem gfst (a :FX) : (g a).fst=a :=
 RingHom.congr_fun (aug_lift f (RingHom.id FX) hf) a
private theorem gphys (a :L[X]) :g (phys a)=f a :=
 lift_on f (RingHom.id FX) hf a
local instance :Algebra ℤ FX:=Ring.toIntAlgebra FX
private def D:Derivation ℤ FX FX :=
 { toFun:= fun a=>(g a).snd
   map_add' := fun a b=> by simp
   map_smul' := fun n a=> by simp
   map_one_eq_zero' := by change (g 1).snd=0; simp
   leibniz' := fun a b=> by
    change (g (a*b)).snd=a•(g b).snd+b•(g a).snd
    simp [gfst,mul_comm] }
private theorem Dc (a :L) :D (c a)=0:= by
 change (g (phys (Polynomial.C a))).snd=0
 rw [gphys]
 simp [f]
private theorem Dx :D (phys Polynomial.X)=1 := by
 change (g (phys Polynomial.X)).snd = 1
 rw [gphys]
 simp [f]
private theorem Dpoly (a :L[X]) :D (phys a)=phys a.derivative := by
 have h:=chain D c (phys Polynomial.X) a
 rw [← coe_eval₂RingHom,ev,Dx,mul_one] at h
 simpa [Polynomial.sum_def,Dc,← coe_eval₂RingHom,ev] using h
theorem section_jet (F:L[X][X]) (P Q:L[X])
   (h:F.eval₂ phys (phys P/phys Q)=0)
   (hs :F.derivative.eval₂ phys (phys P/phys Q)≠0) :
   -(physicalDerivative F).eval₂ phys (phys P/phys Q) /
     F.derivative.eval₂ phys (phys P/phys Q) =
     phys (P.derivative*Q-P*Q.derivative)/phys Q^2 := by
 let y :=phys P/phys Q
 have hd:=chain₂ (0:Derivation L L L) D c
   (fun a=> by simp [Dc]) (phys Polynomial.X) y F
 dsimp only at hd
 rw [ev,h,map_zero,Dx,mul_one,
   show seedDerivative (0:Derivation L L L) F=0 by
     simp [seedDerivative,Polynomial.sum_def],eval₂_zero,zero_add] at hd
 have hy :D y=phys (P.derivative*Q-P*Q.derivative)/phys Q^2 := by
   rw [show y=phys P/phys Q from rfl,D.leibniz_div,Dpoly,Dpoly]
   simp only [smul_eq_mul,map_sub,map_mul,div_eq_mul_inv,inv_pow]
   ring
 apply (div_eq_iff hs).2
 rw [← hy,mul_comm]
 exact (eq_neg_of_add_eq_zero_right hd.symm).symm
end
end qVHIGFe
end
