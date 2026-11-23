import ProximityPrize.SubmissionLower.FadicVar

/-!
# Weighted-degree bounds of the anchor factor

Generic lemmas that turn the shape of a polynomial and the accepted pointwise active bound
(`m 0 + 2 m 1 + 2 m 2 + 2 m 3 ≤ K` on every monomial) into the hypotheses of
`FadicGate.exists_varGateSpace`.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2_2 (JetExp oldWeight gradeWeight)
open MvPolynomial
open scoped BigOperators

variable {R:Type*} [CommSemiring R]

theorem wdeg_top_eq_degreeOf (g : MvPolynomial (Fin 4) R) :
    g.weightedTotalDegree topWeight=g.degreeOf 3:=by
  rw [degreeOf_eq_sup]
  unfold weightedTotalDegree
  exact Finset.sup_congr rfl fun m _ => w_top m

theorem taper_ge_grade (g : MvPolynomial (Fin 4) R) :
    26*g.weightedTotalDegree gradeWeight≤g.weightedTotalDegree taperWeight:=by
  classical
  rcases g.support.eq_empty_or_nonempty with he | hne
  · simp [weightedTotalDegree,he]
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup g.support hne
      (fun s => Finsupp.weight gradeWeight s)
    have h1:g.weightedTotalDegree gradeWeight=Finsupp.weight gradeWeight m:=hmax
    have h2:=le_weightedTotalDegree taperWeight hm
    rw [w_taper'] at h2
    rw [h1]
    omega

/-- The taper degree is bounded by the grade and index bounds, and by the active bound. -/
theorem taper_le (g : MvPolynomial (Fin 4) R) (b j K : ℕ)
    (hb : ∀ m ∈ g.support,Finsupp.weight gradeWeight m≤b)
    (hj : ∀ m ∈ g.support,Finsupp.weight oldWeight m≤j)
    (hK : ∀ m ∈ g.support,m 0+2*m 1+2*m 2+2*m 3≤K) :
    g.weightedTotalDegree taperWeight≤min (26*b+25*j) (b+25*K):=by
  unfold weightedTotalDegree
  apply Finset.sup_le
  intro m hm
  have h1:=hb m hm
  have h2:=hj m hm
  have h3:=hK m hm
  rw [w_grade] at h1
  rw [w_old] at h2
  rw [w_taper]
  apply le_min <;> omega

end FadicGate

#print axioms FadicGate.wdeg_top_eq_degreeOf
#print axioms FadicGate.taper_ge_grade
#print axioms FadicGate.taper_le
