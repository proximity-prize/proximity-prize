import ProximityPrize.SubmissionLower.R6960BranchCollisions
import Mathlib.RingTheory.AdjoinRoot
import ArkLib.Data.Polynomial.FractionFieldResultant

noncomputable section
set_option Elab.async false
namespace Lower6960.MarkedRoot
open Polynomial Finset
open scoped Polynomial
variable {K : Type} [Field K] [DecidableEq K]

/-- The cofactor, scaled to equal one at the word, is the projector onto its
sheet. It is zero on the complementary factor and is nonconstant. -/
theorem sheet {F : (Polynomial K)} (degree : 2≤F.natDegree) (y : K) (root : F.eval y=0)
    (simple : F.derivative.eval y≠0) :
    ∃ H Q : (Polynomial K),F=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      let e:=AdjoinRoot.mk F H
      e^2=e ∧ e≠0 ∧ e≠1 := by
  have fn : F≠0 := by intro eq; simp [eq] at degree
  obtain ⟨Q,eq⟩ := dvd_iff_isRoot.mpr root
  have qn : Q≠0 := fun h=>fn (by rw [eq,h,mul_zero])
  have qdeg : F.natDegree=1+Q.natDegree := by
    rw [eq,natDegree_mul (X_sub_C_ne_zero _) qn,natDegree_X_sub_C]
  have qy : Q.eval y≠0 := by
    rw [eq,derivative_mul] at simple
    simpa using simple
  let H:=C (Q.eval y)⁻¹*Q
  have value : H.eval y=1 := by simp [H,qy]
  have hd : H.natDegree=Q.natDegree := natDegree_C_mul (inv_ne_zero qy)
  have hn : H≠0 := by intro h; simp [h] at value
  have div : Polynomial.X-C y∣H-1 := dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot,value])
  obtain ⟨G,fac⟩ := div
  have rel : F∣H*(H-1) := by
    refine ⟨C (Q.eval y)⁻¹*G,?_⟩
    rw [fac,eq]; unfold H; ring
  let e:=AdjoinRoot.mk F H
  have idemp : e^2=e := by
    have zero := AdjoinRoot.mk_eq_zero.mpr rel
    rw [map_mul,map_sub,map_one] at zero
    change e*(e-1)=0 at zero
    linear_combination zero
  refine ⟨H,Q,eq,value,dvd_mul_left ..,idemp,?_,?_⟩
  · intro zero
    have h := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp zero) hn
    omega
  · intro one
    have zero : AdjoinRoot.mk F (H-1)=0 := by rw [map_sub,map_one,one,sub_self]
    have dv := AdjoinRoot.mk_eq_zero.mp zero
    by_cases h : H-1=0
    · have he := sub_eq_zero.mp h
      rw [he,natDegree_one] at hd; omega
    · have hle := natDegree_le_of_dvd dv h
      have upper := natDegree_sub_le H 1
      rw [natDegree_one,_root_.max_zero] at upper; omega

/-- Specialization to a marked scalar preserves the full ordinate degree
and produces a genuine sheet except at the roots of one bounded polynomial. -/
theorem good_marks (F : Polynomial (Polynomial K)) (p : ℕ) [CharP (FractionRing (Polynomial K)) p]
    (ir : Irreducible F) (large : 2≤F.natDegree) (tame : F.natDegree<p)
    (v : ℕ) (seed : ∀j,(F.coeff j).natDegree≤v)
    (T : Finset K) (word : K→K) (root : ∀z∈T,(F.map (evalRingHom z)).eval (word z)=0) :
    ∃ bad ⊆ T, bad.card≤(2*F.natDegree-1)*v ∧
      ∀ z∈T, z∉bad → let f:=F.map (evalRingHom z)
        f.natDegree=F.natDegree ∧ f.Separable ∧
        ∃ H Q : (Polynomial K), f=(Polynomial.X-C (word z))*Q ∧ H.eval (word z)=1 ∧ Q∣H ∧
          let e:=AdjoinRoot.mk f H
          e^2=e ∧ e≠0 ∧ e≠1 := by
  classical
  let R:=F.resultant F.derivative F.natDegree (F.natDegree-1)
  have rn : R≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField F
    (BranchCollisions.tame_separable p ir.squarefree tame)
  have deg := natDegree_resultant_le_of_coeff_natDegree_le F F.derivative F.natDegree
    (F.natDegree-1) v v seed (fun j=>by
      rw [coeff_derivative,mul_comm,show ((j:(Polynomial K))+1)=C ((j:K)+1) by simp]
      exact (natDegree_C_mul_le _ _).trans (seed _))
  let bad:=T.filter fun z=>R.eval z=0
  have incl : bad⊆R.roots.toFinset := fun z hz => Multiset.mem_toFinset.mpr
    ((mem_roots rn).mpr (mem_filter.mp hz).2)
  refine ⟨bad,filter_subset _ _,?_,?_⟩
  · refine ((card_le_card incl).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))).trans ?_
    exact deg.trans_eq (by rw [←Nat.add_mul]; congr 1; omega)
  · intro z hz keep
    have unit : (evalRingHom z) R≠0 := fun h=>keep (mem_filter.mpr ⟨hz,h⟩)
    have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
      le_rfl unit
    have sep := separable_map_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
      le_rfl (by omega) unit
    exact ⟨full,sep,sheet (full ▸ large) (word z) (root z hz)
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
        le_rfl (by omega) unit (word z) (root z hz))⟩

#print axioms good_marks
end Lower6960.MarkedRoot
