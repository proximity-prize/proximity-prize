import ProximityPrize.SubmissionLower.CE
import ProximityPrize.SubmissionLower.ZaQt7ib
set_option Elab.async false
set_option autoImplicit true
namespace NU
noncomputable section



open dN (GeoField)

open B8 (lS MH aC0 i9)

open agM (Vw bJv)
open MvPolynomial (affineHilbertPolynomial monomialMap eq_affineHilbertPolynomial_of_eval_eq)
open scoped BigOperators Pointwise
private theorem bEc (hcount:c3) (B:lS)
    (hB : ∀ i,agJ (B i)) (t:Fin 5→ℕ) :
    (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField (D0 B t)) ⊥)).coeff 5 =
      azm (Vw B t) := by
  obtain ⟨H,_,hcoeff,hH⟩:=hcount (Vw B t) (cru B hB t)
  have heq :H=affineHilbertPolynomial
      (Ideal.comap (monomialMap GeoField (D0 B t)) ⊥) := by
    apply eq_affineHilbertPolynomial_of_eval_eq (N₀:=0)
    intro n _
    rw [bJv _ (byT B t),c3l B hB t n]
    exact hH n
  rwa [← heq]
private theorem cKY (hcut:c1) (hcycle :c2) :aYC:= by
  intro B hB P I i hP hi hd D hD hprop ι S C w hinj hcomp
  let:=hP
  have hr :IsLeftRegular (Ideal.Quotient.mk P D) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
  have hdle :MH P (I.card+1) :=le_of_eq hd
  exact (hcycle B hB (i9 P D) I (aC0 hr hdle) S C w hinj
    (fun a ha=>⟨(hcomp a ha).minimal,(hcomp a ha).length_le⟩)).trans
    (hcut B hB P I i hi hdle D hD hr)
end
end NU
