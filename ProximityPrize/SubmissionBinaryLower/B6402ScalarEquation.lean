import ProximityPrize.SubmissionBinaryLower.B6402HardAuxiliary
import ProximityPrize.SubmissionBinaryLower.P64Cofactor

/-! A single good seed specializes the shared auxiliary to a nonzero
ordinary bivariate equation for every scalar witness in a family. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ScalarEquation
open Polynomial B6401ContactKerD BCHKSSubstitutionVanish
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K : Type*} [Field K] [Fintype K]

theorem count (p : BiPoly (Polynomial K)) (hn : p≠0) (h : ℕ)
    (cap : ∀ j a,((p.coeff j).coeff a).natDegree≤h) (E : Finset K) (room : E.card+h<Fintype.card K)
    (T : Finset (K[X])) (vanish : ∀ z∉E,∀ Q∈T,BCHKSSubstitutionVanish.triEval p z Q=0) :
    T.card≤p.natDegree := by
  classical
  let j := p.natDegree
  let a := (p.coeff j).natDegree
  let c := (p.coeff j).coeff a
  have hp : p.coeff j≠0 := by simpa only [j,coeff_natDegree] using leadingCoeff_ne_zero.mpr hn
  have hc : c≠0 := by simpa only [c,a,coeff_natDegree] using leadingCoeff_ne_zero.mpr hp
  let bad := E∪c.roots.toFinset
  have lt : bad.card<Fintype.card K := (Finset.card_union_le _ _).trans_lt
    ((Nat.add_le_add_left ((Multiset.toFinset_card_le _).trans ((card_roots' c).trans (cap j a))) _).trans_lt room)
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (show bad.card<(Finset.univ : Finset K).card by simpa using lt)
  have ze : z∉E := fun he => hz (Finset.mem_union_left _ he)
  have good : c.eval z≠0 := fun hz' => hz (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ((mem_roots hc).mpr hz')))
  let q := BCHKSSubstitutionVanish.specializeZ p z
  have hq : q≠0 := by
    intro eq
    have h := congrArg (fun g : BiPoly K => (g.coeff j).coeff a) eq
    apply good
    simpa only [q,BCHKSSubstitutionVanish.specializeZ,coeff_map,coe_mapRingHom,coe_evalRingHom,coeff_zero,c] using h
  have sub : T ⊆ q.roots.toFinset := by
    intro f hf
    rw [Multiset.mem_toFinset,mem_roots hq]
    exact vanish z ze f hf
  calc T.card≤q.roots.toFinset.card := Finset.card_le_card sub
       _ ≤ q.roots.card := Multiset.toFinset_card_le _
       _ ≤ q.natDegree := card_roots' _
       _ ≤ p.natDegree := natDegree_map_le

#print axioms count
end ProximityPrize.SubmissionBinaryLower.B6402ScalarEquation
