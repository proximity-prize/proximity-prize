import ProximityPrize.SubmissionLower.R6960PrefixReceipt
import ProximityPrize.SubmissionLower.R6960FreeSource6960
import ProximityPrize.SubmissionLower.Fast069

noncomputable section
set_option Elab.async false
namespace Lower6960.MainPrefixSource
open Polynomial
open K1_14 (Jet L liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (jetMarkHom toJet)
open HelperSource (helperBank helperCutoff)
open DifferentialContact (Native)
open PrefixRows (Prepared rescueDegrees)
open FreeSource (bank cutoff reserve)
open K1_14_2_6_2 (seedIndex)
open K1_14_2_4_2 (factorial_ne_zero)
open K1_14_2_2_3 (shiftedWord)
open K1_14_2_6_2 (seed_iter coordDeriv)

/-- The helper provides eleven orders before taking its stage-dependent power. -/
def copies (i : Fin 17) := (reserve i+11)/11

/-- Convert mixed ordinary contact at a mark to the divided seed derivative
used by the introductory cover. Its factorial is a unit in the mark field. -/
theorem hasse_at_mark {z : K1.K} {S : (Polynomial K1.K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r+1) P)
    (j : Fin 2) (a : ℕ) (within : a≤r) (small : a<K1.p) :
    K1_14.jetAt (K1_14.seedHasse j a P) z S=0 := by
  have rep (n : ℕ) : toJet (shiftedWord P (List.replicate n j)) =
      (coordDeriv (seedIndex j))^[n] (toJet P) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ,shiftedWord,Function.iterate_succ_apply',←ih]
      simpa using (seed_iter j 1 (shiftedWord P (List.replicate n j))).symm
  have van := RingHom.mem_ker.mp (contact (List.replicate a j) (by simpa using Nat.lt_succ_of_le within))
  rw [rep,seed_iter,map_nsmul,nsmul_eq_mul,K1_14_2.eval_toJet] at van
  exact (mul_eq_zero.mp van).resolve_left (factorial_ne_zero small)

/-- Source and contact for every main stage. The same free rows, helper, and
possible exceptional factor work for every mark and every agreement witness. -/
theorem rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2339≤h) (hi : h≤33561) :
    ∃ (P : Fin 17→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ rescueDegrees out.exception) ∧
      (∀ i,P i∈evaluated Crt word (bank i).shape (cutoff h i)) ∧
      ∀ (_noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
        (z : K1.K) (S : (Polynomial K1.K)), MarkResidues D z S →
        (liftPoly S).natDegree ≤ 131071+h →
        ∀ hits : Finset K1.I, 179827≤hits.card →
        (∀ i ∈ hits,(liftPoly S).eval (nodeL i)=word i) →
        toJet out.exception∉RingHom.ker (jetMarkHom z S) →
        ∀ i, Native (RingHom.ker (jetMarkHom z S)) (reserve i+1) (out.free i) ∧
          Native (RingHom.ker (jetMarkHom z S)) (reserve i+1) (out.helper^(copies i)) := by
  choose P inside nz using FreeSource.free_rows Crt word lo hi
  obtain ⟨out,kind⟩ := PrefixRows.prepare_6960 P (fun i=>(bank i).shape) copies nz
    (fun i=>evaluated_shape Crt word (inside i)) Crt word lo hi
  refine ⟨P,out,kind,inside,?_⟩
  intro noPole z S residues degree hits many agree regular i
  apply PrefixRows.native_at_6960 Crt word lo hi out i (cutoff h i) (reserve i) (inside i)
  · exact FreeSource.cutoff_fit lo hi i
  · unfold copies
    omega
  all_goals assumption

#print axioms rows
#print axioms hasse_at_mark
end Lower6960.MainPrefixSource
