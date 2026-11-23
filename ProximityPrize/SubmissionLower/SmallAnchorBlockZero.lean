/-
The band and block definitions are from public Proximity Prize peer submission
657, commit e07f14a81dfe2cf1bda985e67040ad4d31fe81ab.
-/
import ProximityPrize.SubmissionLower.Final50RankCore
import ProximityPrize.SubmissionLower.Fast054

set_option Elab.async false
set_option autoImplicit false

namespace SmallAnchorBlockZero
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift jetIndex targetOrder
  backShift_homogeneous backShift_index_order jetIndex_formula targetOrder_formula degree_formula)
open MvPolynomial

/-- Above the multiplicity plus the band degree, the entire block vanishes. -/
theorem block_eq_zero {d s : ℕ} (hs : 102 + d ≤ s) (g : ℤ) :
    Final50RankCore.blockAt d s g=0:=by
  apply LinearMap.ext
  intro P
  have hP:=(mem_restrictSupport_iff Geom).mp P.property
  have hdeg : (P : Form).IsWeightedHomogeneous (fun _ => (1 : ℕ)) d := by
    intro e he
    rw [← Finsupp.degree_eq_weight_one]
    exact (hP (MvPolynomial.mem_support_iff.mpr he)).1
  have hidx : (P : Form) ∈ restrictWeightedOrder jetIndex (-g).toNat := by
    refine mem_restrictWeightedOrder.mpr fun e he => ?_
    have h:=(hP he).2.1
    omega
  have hd' := backShift_homogeneous hdeg
  have hi' := backShift_index_order hidx
  change weightedTruncation targetOrder (Final50RankCore.orderCutoff s g).toNat
    (backShift (P:Form))=0
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  refine mem_restrictWeightedOrder.mpr fun e he => ?_
  have hd:=hd' (MvPolynomial.mem_support_iff.mp he)
  rw [← Finsupp.degree_eq_weight_one,degree_formula] at hd
  have hi:=mem_restrictWeightedOrder.mp hi' e he
  rw [jetIndex_formula] at hi
  rw [targetOrder_formula]
  unfold Final50RankCore.orderCutoff
  omega

theorem rank_eq_zero {d s : ℕ} (hs : 102 + d ≤ s) (g : ℤ) :
    Module.finrank Geom (LinearMap.range (Final50RankCore.blockAt d s g))=0:=by
  rw [block_eq_zero hs g,LinearMap.range_zero,finrank_bot]

/-- All offsets in the last anchor grade have rank zero. -/
theorem new_grade_zero (d : ℕ) (hd : d ≤ 34) :
    ∀ g:ℤ,Module.finrank Geom (LinearMap.range (Final50RankCore.blockAt d 137 g))=0 :=
  rank_eq_zero (d:=d) (s:=137) (by omega)

#print axioms new_grade_zero
end SmallAnchorBlockZero
