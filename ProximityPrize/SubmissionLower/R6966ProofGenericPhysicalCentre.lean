import ProximityPrize.SubmissionLower.R6966ProofQuadraticWeight
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.GenericPhysicalCentre
open Polynomial
open scoped Polynomial nonZeroDivisors Differential
noncomputable section
variable {K:Type*} [Field K]

abbrev Frac (K:Type*) [Field K] := FractionRing K[X]
private abbrev Dual (R:Type*) := TrivSqZeroExt R R

private def jetPoly : K[X]→+*Dual (Frac K) where
  toFun P := (algebraMap K[X] (Frac K) P,algebraMap K[X] (Frac K) P.derivative)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' P Q := by
    apply TrivSqZeroExt.ext
    · exact map_add _ _ _
    · change algebraMap K[X] (Frac K) (P+Q).derivative=_
      rw [map_add,map_add];rfl
  map_mul' P Q := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change algebraMap K[X] (Frac K) (P*Q).derivative=
        algebraMap _ _ P*algebraMap _ _ Q.derivative+algebraMap _ _ P.derivative*algebraMap _ _ Q
      rw [derivative_mul,map_add,map_mul,map_mul,add_comm]

private def jetFrac : Frac K→+*Dual (Frac K) :=
  IsLocalization.lift (M:=nonZeroDivisors K[X]) (g:=jetPoly) (fun d=>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (show IsUnit (algebraMap K[X] (Frac K) d.val) from
      ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (Frac K))).mpr (nonZeroDivisors.ne_zero d.property)).isUnit))
-- A rational function at the generic physical centre has its original value
-- in the first coordinate and its ordinary derivative in the second.
private theorem jet_poly (P:K[X]) : jetFrac (algebraMap K[X] (Frac K) P)=jetPoly P :=
  IsLocalization.lift_eq _ _

private theorem jet_value (x:Frac K) : (jetFrac x).fst=x := by
  let fst: Dual (Frac K)→+*Frac K:=(TrivSqZeroExt.fstHom (Frac K) (Frac K) (Frac K)).toRingHom
  have eq:fst.comp jetFrac=RingHom.id _ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors K[X])
    apply RingHom.ext
    intro P
    change (jetFrac (algebraMap K[X] (Frac K) P)).fst=_
    rw [jet_poly];rfl
  exact RingHom.congr_fun eq x

private def ofJet {R:Type*} [CommRing R] (jet:R→+*Dual R) (fst:∀ x:R,(jet x).fst=x) : Differential R where
  deriv:=Derivation.mk' (((TrivSqZeroExt.sndHom (R:=R) (M:=R)).toAddMonoidHom.comp
    jet.toAddMonoidHom).toIntLinearMap) (by
      intro x y
      change (jet (x*y)).snd=x*(jet y).snd+y*(jet x).snd
      rw [map_mul]
      change (jet x).fst*(jet y).snd+(jet x).snd*(jet y).fst=_
      rw [fst,fst,mul_comm (jet x).snd y])

@[instance_reducible] def physical (K:Type*) [Field K] : Differential (Frac K) :=
  ofJet jetFrac jet_value

attribute [local instance] physical

theorem physical_poly (P:K[X]) : Differential.deriv (algebraMap K[X] (Frac K) P) =
    algebraMap K[X] (Frac K) P.derivative := by
  change (jetFrac (algebraMap K[X] (Frac K) P)).snd=_
  rw [jet_poly];rfl

theorem physical_iterate (P:K[X]) (j:ℕ) : Differential.deriv^[j] (algebraMap K[X] (Frac K) P)=
    algebraMap K[X] (Frac K) (Polynomial.derivative^[j] P) := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [Function.iterate_succ_apply',ih,physical_poly,Function.iterate_succ_apply']

section Coefficients
variable {F σ:Type*} [CommRing F] [Differential F]

private def onCoeffs (P:MvPolynomial σ F) : MvPolynomial σ F :=
  AddMonoidAlgebra.ofCoeff (P.coeff.mapRange Differential.deriv (map_zero _))

private theorem onCoeffs_coeff (P:MvPolynomial σ F) (e:σ→₀ℕ) :
    (onCoeffs P).coeff e = Differential.deriv (P.coeff e) := rfl

@[instance_reducible] def seeds (σ F:Type*) [CommRing F] [Differential F] : Differential (MvPolynomial σ F) where
  deriv:=Derivation.mk' (({
    toFun:=onCoeffs
    map_zero' := by ext e;simp only [onCoeffs_coeff,MvPolynomial.coeff_zero,Finsupp.zero_apply,map_zero]
    map_add' := by intro P Q;ext e;simp only [onCoeffs_coeff,MvPolynomial.coeff_add,map_add]
    } : MvPolynomial σ F →+ MvPolynomial σ F).toIntLinearMap) (by
      intro P Q
      classical
      ext e
      change (onCoeffs (P*Q)).coeff e=((P*onCoeffs Q)+(Q*onCoeffs P)).coeff e
      rw [mul_comm Q (onCoeffs P)]
      simp only [onCoeffs_coeff,MvPolynomial.coeff_add,MvPolynomial.coeff_mul,map_sum,Derivation.leibniz,
        smul_eq_mul,Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro ab _
      exact mul_comm _ _)

attribute [local instance] seeds

theorem deriv_coeff (P:MvPolynomial σ F) (e:σ→₀ℕ) :
    (Differential.deriv P).coeff e = Differential.deriv (P.coeff e) := rfl

private theorem deriv_C_seed (c:F) : Differential.deriv (MvPolynomial.C c : MvPolynomial σ F)=
    MvPolynomial.C (Differential.deriv c) := by
  classical
  ext e
  rw [deriv_coeff]
  by_cases eq:0=e <;> simp [MvPolynomial.coeff_C,eq]

private theorem deriv_X_seed (i:σ) : Differential.deriv (MvPolynomial.X i:MvPolynomial σ F)=0 := by
  classical
  ext e
  rw [deriv_coeff]
  by_cases eq:Finsupp.single i 1=e <;> simp [MvPolynomial.coeff_X,eq]

theorem deriv_eval (p:σ→F) (fixed:∀i,Differential.deriv (p i)=0) (P:MvPolynomial σ F) :
    Differential.deriv (MvPolynomial.eval p P)=MvPolynomial.eval p (Differential.deriv P) := by
  induction P using MvPolynomial.induction_on with
  | C c=>simp [deriv_C_seed]
  | add P Q hp hq=>simp [hp,hq]
  | mul_X P i hp=>simp [Derivation.leibniz,smul_eq_mul,hp,deriv_X_seed,fixed,mul_comm]

theorem deriv_axis (P:MvPolynomial σ F) (i:σ) :
    (Differential.deriv P).degreeOf i≤P.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  apply MvPolynomial.le_degreeOf_of_mem_support
  apply MvPolynomial.mem_support_iff.mpr
  intro zero
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [deriv_coeff,zero,map_zero])

#print axioms deriv_axis
#print axioms deriv_eval
end Coefficients
#print axioms physical_iterate
end
end Research6966.GenericPhysicalCentre
