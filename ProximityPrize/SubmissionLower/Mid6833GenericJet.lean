/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Research adaptation of the 68.32 public proof architecture.
Prior authors: Lucieno (PR 618) and BitWonka (PR 581). Apache-2.0.
This file verifies an interpolation or scalar-list statement. -/

import ProximityPrize.SubmissionLower.Koala6831ResidualInactive
import ProximityPrize.SubmissionLower.Koala6831ResidualLocalTop
import ProximityPrize.SubmissionLower.Koala6831ResidualLowerBlock


namespace ProximityPrize.SubmissionLower.FrontierGenericJet
open scoped BigOperators
open Koala6831Residual SecondJetRelaxedGlobalIndex
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetSpecialize SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
variable {K N : Type*} [Field K] [Fintype N]
private theorem inactiveWitness {I : Type} [Fintype I] [DecidableEq I]
    (exp : I → Fin 5 →₀ ℕ) (m L B s U w : ℕ) (D : ℕ → ℕ) (hw : 2 ≤ w)
    (nodes : N ↪ K) (u0 u1 : N → K) (i : I) (n : N)
    (hB : 2*exp i 1+exp i 3 ≤ B) (hs : exp i 1 ≤ s)
    (hU : sourceMiddle (exp i) ≤ U) (hL : exp i 1+exp i 2+exp i 3+exp i 4 ≤ L)
    (hD : exp i 0+w*exp i 2+(w-1)*exp i 3+(w-2)*exp i 1 < D (exp i 1))
    (ht : ¬(sourceMiddle (exp i) = U ∧ exp i 2 < m)) :
    ∃ P : SecondJetRelaxedSpace.source (K := K) m L B s (U-1) (fun h => (D h+B-1)/w),
      SecondJetRank.contactMap m (P : SecondJetBasis.Jet (SecondJetLocal.Base (K := K))) =
      globalContactMap exp m (nodes : N → K) u0 u1 (Pi.single i (1 : K)) n := by
  have mem := inactive_column_mem_lower m L B s U w D hw
    (nodes n) (u0 n) (u1 n) (exp i) hB hs hU hL hD ht
  exact ⟨⟨_, mem⟩, (globalContactMap_single exp m nodes u0 u1 i n).symm⟩


/-- Dimension-to-vanishing bridge, uniform in field, nodes, agreement, weights and
all caps. The active top-column term retains the improvement in Lucieno PR 618. -/
theorem exists_jet_of_dimension
    (A w m B s U L k n0 : ℕ) (hA : 0 < A) (hw : 2 ≤ w) (hwa : w-2 ≤ A)
    (hB : 2*s ≤ B) (hk : k < m)
    (D : ℕ → ℕ) (hD : ∀ h, D h = m*A - reserve k n0 h*(A-(w-2)))
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hgate : Fintype.card N *
        SecondJetRelaxedGlobalMap.rankBound m L B s (U-1) (fun h => (D h+B-1)/w) +
      Fintype.card { i : Index D w L B s U //
        i.1.val+i.2.1.val+i.2.2.1.val = U ∧ i.2.2.1.val < m } <
      Fintype.card (Index D w L B s U)) :
    ∃ P : Poly (K := K), P ≠ 0 ∧
        (∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧
          e 1+e 2+e 3+e 4 ≤ L ∧ e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D (e 1)) ∧
        (∀ i, MvPolynomial.X 0^m ∣ substitute (K := K) (localize (nodes i) (u0 i) (u1 i) P)) ∧
        ∀ d ≤ k, ∀ f : Polynomial K, f.natDegree ≤ w → ∀ z : K, ∀ S : Finset N,
          A ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
          specialize f z ((pderiv 1)^[d] P) = 0 := by
  classical
  let exp : Index D w L B s U → Fin 5 →₀ ℕ := SecondJetRelaxedGlobalIndex.exponent
  let caps (h : ℕ) := (D h+B-1)/w
  let W := lowerNodeSpace (K := K) (N := N) m L B s U caps
  let active : Index D w L B s U → Prop := fun i =>
    i.1.val+i.2.1.val+i.2.2.1.val = U ∧ i.2.2.1.val < m
  have inj : Function.Injective exp := SecondJetRelaxedGlobalIndex.exponent_injective _ _ _ _ _ _
  have bounds (i : Index D w L B s U) :
      2*exp i 1+exp i 3 ≤ B ∧ exp i 1 ≤ s ∧ exp i 1+exp i 2+exp i 3 ≤ U ∧
      exp i 1+exp i 2+exp i 3+exp i 4 ≤ L ∧
      exp i 0+w*exp i 2+(w-1)*exp i 3+(w-2)*exp i 1 < D (exp i 1) :=
    SecondJetRelaxedGlobalIndex.exponent_bounds _ _ _ _ _ _ hB i
  have inactive (i : Index D w L B s U) (hi : ¬active i) :
      globalContactMap exp m nodes u0 u1 (Pi.single i (1 : K)) ∈ W := by
    apply lowerNodeSpace_mem
    intro n
    obtain ⟨hb,hs,hu,hl,hd⟩ := bounds i
    have ht : ¬(sourceMiddle (exp i) = U ∧ exp i 2 < m) := by
      rcases i with ⟨h,r,y,x,z⟩
      simpa [active,exp,sourceMiddle,SecondJetRelaxedGlobalIndex.exponent,add_right_comm] using hi
    exact inactiveWitness exp m L B s U w D hw nodes u0 u1 i n hb hs hu hl hd ht
  have rank := lowerNodeSpace_rank (K := K) (N := N) m L B s U caps
  obtain ⟨P,hp,supp,contact⟩ := exists_global_contact_of_inactive_mem exp inj m nodes u0 u1 W active
    inactive _ rank hgate
  have hbounds (e : Fin 5 →₀ ℕ) (he : e ∈ P.support) :
      2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ L ∧
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D (e 1) := by
    obtain ⟨i,rfl⟩ := supp e he
    exact bounds i
  have flat (i : N) := SecondJetGlobalDifferentiation.nested_to_flat_contact _ m (contact i)
  refine ⟨P,hp,hbounds,flat,?_⟩
  intro d hd f hf z S hS hval
  apply derivative_vanish P m A w k n0 d hA hwa (lt_of_le_of_lt hd hk) hd ?_
    nodes u0 u1 flat f hf z S hS hval
  intro e he
  have hd := (hbounds e he).2.2.2.2
  rw [hD] at hd
  omega
end
end ProximityPrize.SubmissionLower.FrontierGenericJet
#print axioms ProximityPrize.SubmissionLower.FrontierGenericJet.exists_jet_of_dimension
