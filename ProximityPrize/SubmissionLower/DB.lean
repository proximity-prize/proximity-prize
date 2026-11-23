import Mathlib.Algebra.Order.Sub.Prod
import ProximityPrize.SubmissionLower.AY
set_option Elab.async false
set_option autoImplicit true
section
namespace ak0
noncomputable section
open Polynomial Finset
open uk
open cu (aZ Equation)

open vq (Dx)
abbrev pO:aZ →+* aQ:=algebraMap aZ aQ
def splitting (q:Equation) :IntermediateField aQ HR :=
 IntermediateField.adjoin aQ ((ek q).rootSet HR)
abbrev Y6 (q:Equation) := ↥(splitting q)
def aTH :aZ →+ aZ :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
theorem adg (s :aZ) (m:Fin 2 →₀ ℕ) :
 (aTH s).coeff m=Dx (s.coeff m) :=rfl
end
end ak0
end
section
namespace ak0
noncomputable section
open Polynomial Finset
open uk
open cu (Equation)
instance splittingField (q:Equation) : (ek q).IsSplittingField aQ (Y6 q) :=
 IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
end
end ak0
end
section
namespace aZF
noncomputable section
open Polynomial
open cu (L FX aZ)
open vq (Dx)
open uk (pe center gA wZ)
open ak0 (aTH adg)
open private ar4 a7v from ProximityPrize.SubmissionLower.ZFFuWqa


private theorem cxs (f :L[X]) :
  Dx (algebraMap L[X] FX f)=algebraMap L[X] FX f.derivative := by
 change (ar4 (algebraMap L[X] FX f)).snd= _
 rw [a7v]
 rfl
private theorem bQO (a :L) :Dx (gA a)=0:= by
 change Dx (algebraMap L[X] FX (C a))=0
 rw [cxs,derivative_C,map_zero]
private theorem aYE :Dx center=1 := by
 unfold center
 rw [cxs,derivative_X,map_one]
private def bx0 {A:Type*} [CommRing A] {source target :Algebra ℤ A}
  (d : @Derivation ℤ A A inferInstance inferInstance inferInstance source
    inferInstance inferInstance) :
  @Derivation ℤ A A inferInstance inferInstance inferInstance target
    inferInstance inferInstance :=
 Subsingleton.elim source target ▸ d
private theorem bia {A:Type*} [CommRing A]
  {source target :Algebra ℤ A}
  (d : @Derivation ℤ A A inferInstance inferInstance inferInstance source
    inferInstance inferInstance) (a :A) :
  bx0 (target :=target) d a=d a := by
 have h:source=target :=Subsingleton.elim _ _
 subst target
 rfl
private theorem bXz (a :FX) :aTH (MvPolynomial.C a :aZ)=MvPolynomial.C (Dx a) := by
 classical
 apply MvPolynomial.ext
 intro m
 by_cases h:0=m <;>
  simp only [adg,MvPolynomial.coeff_C,h,ite_true,ite_false,map_zero]
private theorem bXA (s :pe) :aTH (wZ s)=0:= by
 apply MvPolynomial.ext
 intro m
 simp only [adg,wZ,MvPolynomial.coeff_map,bQO,
  AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
end
end aZF
end
section
namespace Qv
noncomputable section

open yW (cO)
open cu (FX Equation)
open vq (flatten D6)
def lX (f :Equation) :Equation :=
 MvPolynomial.optionEquivLeft FX (Fin 2) (D6 (flatten f))
def S4 (δ:Equation→Equation) (P:cO) :cO :=
 P.sum fun k q=>Polynomial.monomial k (δ q)
end
end Qv
end
section
namespace Qv
noncomputable section
open cu (FX aZ Equation vm)

open yW (cO)

open scoped BigOperators


private def Bounded (P:cO) (v s :ℕ) :Prop :=
 P.natDegree≤v ∧ ∀ j,vm (P.coeff j) s
private theorem dcC (s :ℕ) :vm 0 s := by
 intro i
 simp
private theorem coT (x :FX) :vm (Polynomial.C (MvPolynomial.C x)) 0:= by
 intro i
 by_cases hi:i=0
 · simp [hi]
 · simp [Polynomial.coeff_C_of_ne_zero hi]
private theorem dcA {A B:Equation} {a b:ℕ}
  (hA:vm A a) (hB:vm B b) :vm (A*B) (a+b) := by
 intro i
 rw [Polynomial.coeff_mul]
 apply MvPolynomial.totalDegree_finsetSum_le
 intro j _
 exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hA j.1) (hB j.2))
private theorem Bounded.C {P:Equation} {s :ℕ} (hP:vm P s) :
   Bounded (Polynomial.C P) 0 s := by
 refine ⟨(Polynomial.natDegree_C _).le,fun j => ?_⟩
 by_cases hj:j=0
 · subst j
   simpa only [Polynomial.coeff_C_zero] using hP
 · rw [Polynomial.coeff_C_of_ne_zero hj]
   exact dcC s
private theorem Bounded.add {P Q:cO} {v s :ℕ}
   (hP:Bounded P v s) (hQ:Bounded Q v s) :Bounded (P+Q) v s := by
 refine ⟨?_,fun j i => ?_⟩
 · simpa only [max_self] using Polynomial.natDegree_add_le_of_le hP.1 hQ.1
 · rw [Polynomial.coeff_add,Polynomial.coeff_add]
   exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hP.2 j i) (hQ.2 j i))
private theorem Bounded.derivative {P:cO} {v s :ℕ} (hP:Bounded P v s) :
  Bounded P.derivative (v-1) s := by
 refine ⟨(Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right hP.1 _),
  fun j => ?_⟩
 rw [Polynomial.coeff_derivative]
 rw [← map_natCast (Polynomial.C:aZ →+* Equation),← map_natCast (MvPolynomial.C:FX →+* aZ)]
 simpa only [Nat.add_zero,map_add,map_one] using dcA (hP.2 (j+1)) (coT (j+1))
end
end Qv
end
section
namespace anl
noncomputable section
open uk (Input j7 Factors)
open yW (cO jU rP uf)



abbrev Graph (J:Input) (B:j7 J) (D:Factors J B) :=
 cO ⧸ rP J B D
def a6l (J:Input) (B:j7 J) (D:Factors J B) :Graph J B D :=
 Ideal.Quotient.mk _ (jU*uf J B)
abbrev Overlap (J:Input) (B:j7 J) (D:Factors J B) :=
 Localization.Away (a6l J B D)
def finite (J:Input) (B:j7 J) (D:Factors J B) :cO →+* Overlap J B D :=
 (algebraMap (Graph J B D) (Overlap J B D)).comp (Ideal.Quotient.mk _)
end
end anl
end
section
namespace bSg
noncomputable section
open cu (FX Equation)

open vq (Dx aG6)

open Qv (lX)
local notation "unwrap" => MvPolynomial.optionEquivLeft FX (Fin 2)
private theorem aMW (p:Equation) (i:ℕ) (m:Fin 2 →₀ ℕ) :
  ((lX p).coeff i).coeff m=Dx ((p.coeff i).coeff m) := by
 rw [lX,MvPolynomial.optionEquivLeft_coeff_coeff,aG6,
  ← MvPolynomial.optionEquivLeft_coeff_coeff FX,AlgEquiv.apply_symm_apply]
end
end bSg
end
section
namespace dnV
noncomputable section






private def cLc {A R:Type*} [CommRing A] [CommRing R]
  (ev :A →+* R) (d:A →+ A)
  (hd : ∀ a b,d (a*b)=a*d b+d a*b) :A →+* DualNumber R where
 toFun a :=(ev a,ev (d a))
 map_zero' := by apply TrivSqZeroExt.ext <;> simp
 map_one' := by
  have h:=hd 1 1
  simp only [mul_one,one_mul] at h
  have h1 :d 1=0:=(add_eq_left.mp h.symm)
  apply TrivSqZeroExt.ext <;> simp [h1]
 map_add' a b:= by
  apply TrivSqZeroExt.ext
  · exact map_add ev a b
  · change ev (d (a+b))=ev (d a)+ev (d b)
    rw [map_add,map_add]
 map_mul' a b:= by
  apply TrivSqZeroExt.ext
  · exact map_mul ev a b
  · change ev (d (a*b))=ev a*ev (d b)+ev (d a)*ev b
    rw [hd,map_add,map_mul,map_mul]
end
end dnV
end
