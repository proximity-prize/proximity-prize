import ProximityPrize.SubmissionLower.DdZvFuy6d
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.DdAE
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Function.iterate_succ_apply' → zLk, MvPolynomial.aeval_X → zTw, MvPolynomial.eval₂Hom → zOD, MvPolynomial.map → zDK, MvPolynomial.pderiv → zWe, MvPolynomial.pderiv_mul → zGW
section
set_option autoImplicit true
namespace qC8CERb
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative gR
open aR (ao embed af jet cK Z8)
open i4 (K N)

open P5_8_3 (rows)




private abbrev weight (i:Fin 3) :ℕ:=N - i.val
abbrev coeffForm:=MvPolynomial.optionEquivRight ao (Fin 3)
theorem specialize (Q:DifferentialPolynomial ao 2) (S:(Polynomial ao)) :
  cK (coeffForm Q) S=differentialSpecialization Q S:= by
 let x :Option (Fin 3)→(Polynomial ao) := fun
  | none=>Polynomial.X
  | some i=>jet S i
 have h:=MvPolynomial.aeval_map_optionEquivRight (R:=ao) x Q
 rw [show x none=Polynomial.X from rfl,
  show (fun j=>x (some j))=jet S from rfl,Polynomial.aeval_X_left] at h
 rw [show (AlgHom.id ao (Polynomial ao)).toRingHom=RingHom.id ((Polynomial ao)) from rfl,
  MvPolynomial.map_id,MvPolynomial.aeval_eq_eval] at h
 refine h.trans (AlgHom.congr_fun ?_ Q)
 apply MvPolynomial.algHom_ext
 intro v
 rw [differentialSpecializationHom,zTw,zTw]
 cases v <;> rfl
theorem Yw {w T R} (hR:R∈rows w T) :
    ∀ e∈(coeffForm (zDK embed R)).support,
      ((coeffForm (zDK embed R)).coeff e).natDegree +
        e.sum (fun i k=>weight i*k)≤T:= by
  let P:=coeffForm (zDK embed R)
  intro e he
  have hw:R∈MvPolynomial.restrictWeightedDegree (differentialWeight N) T:=hR.1.2
  have h:=MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp hw
  let j:=(P.coeff e).natDegree
  have hc: (P.coeff e).coeff j≠0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)
  rw [MvPolynomial.optionEquivRight_coeff_coeff] at hc
  have hs :e.optionElim j∈R.support :=
    MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr hc)
  have hb:=(Finset.sup_le_iff.mp h) _ hs
  change (e.optionElim j).weight (differentialWeight N)≤T at hb
  rw [show differentialWeight (d:=2) N=fun v=>v.elim 1 weight from by
    funext v; cases v <;> rfl,Finsupp.weight_optionElim,one_mul] at hb
  simpa only [Finsupp.weight_apply,smul_eq_mul,Nat.mul_comm] using hb
private theorem shift_partial (i:Fin 3) (P:af 3) (S:(Polynomial ao)) :
   Z8 (zWe i P) S=zWe i (Z8 P S) := by
 classical
 let g:=zOD MvPolynomial.C
   (fun j:Fin 3=>MvPolynomial.X j+MvPolynomial.C (jet S j))
 change g (zWe i P)=zWe i (g P)
 induction P using MvPolynomial.induction_on with
 | C c=>simp [g]
 | add P Q hP hQ=>simp [hP,hQ]
 | mul_X P j hP =>
   rw [zGW,map_add,map_mul,map_mul,hP,map_mul,zGW]
   by_cases hj:j=i
   · subst j
     simp [g]
   · simp [g,MvPolynomial.pderiv_X_of_ne hj]
theorem shift_jetDerivative (Q:DifferentialPolynomial K 2) (S:(Polynomial ao))
    (i:Fin 3) (r :ℕ) :
    Z8 (coeffForm (zDK embed (jetDerivative Q i r))) S =
      (zWe i)^[r] (Z8 (coeffForm (zDK embed Q)) S) := by
  induction r with
  | zero=>rfl
  | succ r ih =>
    rw [jetDerivative_succ,map_separant,zLk]
    have he (F:DifferentialPolynomial ao 2) :
        coeffForm (separant F i)=zWe i (coeffForm F) := by
      apply coeffForm.symm.injective
      rw [MvPolynomial.optionEquivRight_symm_pderiv,AlgEquiv.symm_apply_apply,
        AlgEquiv.symm_apply_apply]
      rfl
    rw [he,shift_partial,ih]
theorem coeff_iterate_zero (i:Fin 3) (P:af 3) {D:ℕ}
   (h : ∀ e :Fin 3 →₀ ℕ,e.degree<D→P.coeff e=0)
   (r :ℕ) (e :Fin 3 →₀ ℕ) (he :e.degree+r<D) :
   ((zWe i)^[r] P).coeff e=0:= by
 induction r generalizing e with
 | zero=>exact h e (by simpa using he)
 | succ r ih =>
   rw [zLk,MvPolynomial.coeff_pderiv,ih,zero_mul]
   rw [map_add,Finsupp.degree_single]
   omega
theorem atJet_eq_const (P:af 3) (S:(Polynomial ao)) :
  cK P S=(Z8 P S).coeff 0:= by
 let g:Fin 3→af 3:= fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i)
 change (MvPolynomial.eval (jet S)) P =
  (MvPolynomial.constantCoeff.comp (zOD MvPolynomial.C g)) P
 congr 1
 ext <;> simp [g]
end
end qC8CERb
end
section
set_option autoImplicit true
namespace qfaXGOd
noncomputable section
open i4 (Jet)

open P5_8_3 (symbolBand)
open Finset
open P5_8_6 (row box_formula)
private def S5:Jet ≃ (Fin 3 →₀ ℕ) where
 toFun j:=Finsupp.equivFunOnFinite.symm ![j.a,j.b,j.c]
 invFun u:=⟨u 2,u 1,u 0⟩
 left_inv := by rintro ⟨c,b,a⟩; rfl
 right_inv := by intro u; ext i; fin_cases i <;> rfl
private def tuples (B J C:ℕ) :Finset Jet :=
 (range (C+1)).sigma fun c =>
   (range (J+1-2*c)).sigma fun b=>range (B+1-(c+b))
private theorem exponent_set (B J C:ℕ) :
   (↑((tuples B J C).map S5.toEmbedding) :Set (Fin 3 →₀ ℕ)) =
     {u | u.degree≤B∧u.weight Fin.val≤J∧u (Fin.last 2)≤C} := by
 ext u
 obtain ⟨⟨c,b,a⟩,rfl⟩:=S5.surjective u
 rw [Finset.mem_coe,mem_map_equiv,Equiv.symm_apply_apply]
 simp only [tuples,mem_sigma,mem_range,Set.mem_ofPred_eq,Finsupp.degree_eq_sum,
   Finsupp.weight_eq_sum,Fin.sum_univ_three]
 change (c<C+1∧b<J+1-2*c∧a<B+1-(c+b)) ↔
   a+b+c≤B∧a*0+b*1+c*2≤J∧c≤C
 omega
theorem proof :P5_8_3.c7:= by
 rintro ⟨B,J,C⟩
 rw [symbolBand,← exponent_set,MvPolynomial.finrank_restrictSupport_finset,card_map,
  box_formula]
 simp only [tuples,card_sigma,card_range,row,le_refl]
end
end qfaXGOd
end
