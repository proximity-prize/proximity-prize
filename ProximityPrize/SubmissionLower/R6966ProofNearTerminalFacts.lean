import ProximityPrize.SubmissionLower.R6966ProofNearBook
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowNative
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofSpreadInterval

set_option Elab.async false

namespace Research6966.NearTerminal
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField)


open NearBook
open KoalaRect (axisDegree)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false

theorem same_degree {S : Finset Surface} {f g : Equation}
    (fpr : ProjectedProduct S f) (gpr : ProjectedProduct S g) : f.natDegree=g.natDegree :=
  Nat.le_antisymm
    (natDegree_le_of_dvd (NativeOrdinateMass.divides_of_member fpr gpr.vanishes) gpr.primitive.ne_zero)
    (natDegree_le_of_dvd (NativeOrdinateMass.divides_of_member gpr fpr.vanishes) fpr.primitive.ne_zero)

theorem subset_degree {S R : Finset Surface} {f g : Equation}
    (sub : S⊆R) (fpr : ProjectedProduct S f) (gpr : ProjectedProduct R g) :
    f.natDegree≤g.natDegree :=
  natDegree_le_of_dvd (NativeOrdinateMass.divides_of_member fpr (fun q h=>gpr.vanishes q (sub h)))
    gpr.primitive.ne_zero






























































/-- The on-graph projection and an ordinate equation for the off-graph
parents. Empty off-graph support is represented by the unit polynomial. -/
theorem partition {S : Finset Surface} (geo : ∀ q∈S, Parent q)
    {f : Equation} (full : ProjectedProduct S f) (c : ℕ) (large : c<f.natDegree)
    {G : Pade.Row SeedField} (N : PadeNativeQuotient.Native G) (gp : G.primitive)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) c) :
    ∃ H J : Equation,
      NativeWitnessBank.witnessed N (owning N.poly S) H ∧
      (ProjectedProduct (outside N.poly S) J ∨ outside N.poly S=∅ ∧ J=1) ∧
      J.natDegree≤c-G.graphDegree ∧ f.natDegree≤H.natDegree+J.natDegree := by
  classical
  have costa : G.graphDegree≤c := by
    have ctl := control ∅ (fun _=>0) (by simp)
    simpa only [card_empty,zero_add,Pade.Row.degree_map] using ctl
  obtain ⟨J,part,bound⟩ :
      ∃ J : Equation, (ProjectedProduct (outside N.poly S) J ∨ outside N.poly S=∅ ∧ J=1) ∧
        J.natDegree≤c-G.graphDegree := by
    by_cases there : (outside N.poly S).Nonempty
    · obtain ⟨J,proj,cap⟩ := NativeGraphMarks.off_owner N geo control there
      exact ⟨J,Or.inl proj,Nat.le_sub_of_add_le cap⟩
    · exact ⟨1,Or.inr ⟨not_nonempty_iff_eq_empty.mp there,rfl⟩,by simp⟩
  have vanish (q : Surface) (mem : q∈outside N.poly S) : C J∈q.asIdeal := by
    rcases part with proj | ⟨empty,_⟩
    · exact proj.vanishes q mem
    · rw [empty] at mem; exact (notMem_empty q mem).elim
  have jne : J≠0 := by rcases part with proj | ⟨_,rfl⟩; exacts [proj.primitive.ne_zero,one_ne_zero]
  have on : (owning N.poly S).Nonempty := by
    by_contra none
    have div := NativeOrdinateMass.divides_of_member full (D:=J) (by
      intro q mem
      by_cases g : N.poly∈q.asIdeal
      · exact (none ⟨q,mem_filter.mpr ⟨mem,g⟩⟩).elim
      · exact vanish q (mem_filter.mpr ⟨mem,g⟩))
    have d := natDegree_le_of_dvd div jne
    omega
  obtain ⟨H,witness⟩ := NativeWitnessBank.exists_witnessed N gp on
    (fun q mem=>geo q (mem_filter.mp mem).1) (fun q mem=>(mem_filter.mp mem).2)
  have div := NativeOrdinateMass.divides_of_member full (D:=H*J) (by
    intro q mem
    rw [map_mul]
    by_cases g : N.poly∈q.asIdeal
    · exact Ideal.mul_mem_right _ _ (witness.1.vanishes q (mem_filter.mpr ⟨mem,g⟩))
    · exact Ideal.mul_mem_left _ _ (vanish q (mem_filter.mpr ⟨mem,g⟩)))
  have hne := witness.1.primitive.ne_zero
  have deg := natDegree_le_of_dvd div (mul_ne_zero hne jne)
  rw [natDegree_mul hne jne] at deg
  exact ⟨H,J,witness,part,bound,deg⟩

end
end Research6966.NearTerminal
