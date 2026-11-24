import ProximityPrize.SubmissionLower.ZzNTDEa
set_option Elab.async false
set_option autoImplicit true
namespace P1_6_1_3_2
noncomputable section
open MvPolynomial P1_6_1_3

open scoped BigOperators
variable {R:Type*} [CommRing R]
private theorem sum_target_monomial {q:ℕ} {P:Poly R}
    (hP:P.IsWeightedHomogeneous (fun _=>(1 :ℕ)) q) :
    (∑ e :Target q,monomial e.val (P.coeff e.val))=P:= by
  classical
  ext m
  simp only [coeff_sum,coeff_monomial]
  by_cases hm:m.degree=q
  · rw [Finset.sum_eq_single (⟨m,hm⟩:Target q)]
    · simp
    · intro b _ hb
      exact ite_eq_right (fun h=>hb (Subtype.ext h))
    · simp
  · rw [Finset.sum_eq_zero]
    · exact (not_ne_iff.mp fun hc=>hm (by
        rw [Finsupp.degree_eq_weight_one]
        exact hP hc)).symm
    · intro e _
      exact ite_eq_right (fun (h:e.val=m)=>hm (h ▸ e.property))
end
end P1_6_1_3_2
