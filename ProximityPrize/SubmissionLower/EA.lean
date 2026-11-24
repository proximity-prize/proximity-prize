import ProximityPrize.SubmissionLower.ZUCbske
set_option Elab.async false
set_option maxHeartbeats 900000
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace WQ
noncomputable section
open Polynomial Finset



open yW (cO)
open Ke
def Chart (J:Input) (B:j7 J) :=Localization.Away (uf J B)
instance aho (J:Input) (B:j7 J) :CommRing (Chart J B) :=
 inferInstanceAs (CommRing (Localization.Away (uf J B)))
instance adp (J:Input) (B:j7 J) :Algebra cO (Chart J B) :=
 inferInstanceAs (Algebra cO (Localization.Away (uf J B)))
instance dH5 (J:Input) (B:j7 J) :
  IsLocalization.Away (uf J B) (Chart J B) :=
 inferInstanceAs (IsLocalization.Away (uf J B) (Localization.Away (uf J B)))
end
end WQ
end
section
namespace WQ
noncomputable section
open Polynomial
open Ke


variable {J:Input} {B:j7 J}
def aWF {R:Type*} [CommRing R] (P:Ideal R) (δ:Derivation ℤ R R)
    (h : ∀ z∈P,δ z∈P) :Derivation ℤ (R ⧸ P) (R ⧸ P) where
  toLinearMap:=(P.restrictScalars ℤ).liftQ
    ((Ideal.Quotient.mk P).toAddMonoidHom.toIntLinearMap.comp δ.toLinearMap)
    (fun z hz=>LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (h z hz)))
  map_one_eq_zero' := by
    change Ideal.Quotient.mk P (δ 1)=0
    simp
  leibniz' := by
    intro u v
    obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective u
    obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective v
    let q:=Ideal.Quotient.mk P
    change q (δ (a*b))=q a*q (δ b)+q b*q (δ a)
    rw [δ.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul]
@[simp] theorem bKW {R:Type*} [CommRing R] (P:Ideal R) (δ:Derivation ℤ R R)
   (h : ∀ z∈P,δ z∈P) (a :R) :
   aWF P δ h (Ideal.Quotient.mk P a)=Ideal.Quotient.mk P (δ a) :=rfl
end
end WQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace WQ
noncomputable section
open Polynomial
open cu (qD jz)
open uk (gA zU wZ)
open Ke
private theorem cXQ (z :P2.K) :
   (qD z).comp wZ=gA.comp (zU z) := by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp [qD,wZ,zU]
 · intro i
   fin_cases i <;> simp [qD,wZ,zU,gA,jz]
end
end WQ
end
