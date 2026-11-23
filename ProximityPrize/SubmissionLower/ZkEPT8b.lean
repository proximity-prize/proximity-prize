import ProximityPrize.SubmissionLower.Z66Jm5b
set_option Elab.async false
namespace qGWTmVd
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe q1kuFjb
open cu (L)
open scoped Classical WithZero
private def swap:Curve[X] ≃+* MvPolynomial (Fin 2) L[X] :=
  ((MvPolynomial.optionEquivLeft L (Fin 2)).symm.trans
    (MvPolynomial.optionEquivRight L (Fin 2))).toRingEquiv
private theorem coeff_swap (g:Curve[X]) (a :Fin 2 →₀ ℕ) (j:ℕ) :
    ((swap g).coeff a).coeff j=(g.coeff j).coeff a := by
  change (((MvPolynomial.optionEquivRight L (Fin 2))
    ((MvPolynomial.optionEquivLeft L (Fin 2)).symm g)).coeff a).coeff j= _
  rw [MvPolynomial.optionEquivRight_coeff_coeff,← MvPolynomial.optionEquivLeft_coeff_coeff,
    AlgEquiv.apply_symm_apply]
private def slice (g:MvPolynomial (Fin 2) L[X]) (j:ℕ) :Curve :=
  ∑ a∈g.support,MvPolynomial.monomial a ((g.coeff a).coeff j)
private theorem slice_coeff (g:MvPolynomial (Fin 2) L[X]) (j:ℕ) :
    slice g j=(swap.symm g).coeff j:= by
  apply MvPolynomial.ext
  intro a
  have h:=coeff_swap (swap.symm g) a j
  rw [RingEquiv.apply_symm_apply] at h
  rw [← h]
  unfold slice
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,Finset.sum_ite_eq']
  by_cases ha :a∈g.support
  · simp only [ha,ite_true]
  · simp only [ha,ite_false,MvPolynomial.notMem_support_iff.mp ha,coeff_zero]
theorem restrict_coeff {q:Curve} (B:CurveModel q) (F:Raw) (i j:ℕ) :
    ((restrict B F).coeff i).coeff j =
      ∑ a∈(F.coeff i).support,
        algebraMap L B.E (((F.coeff i).coeff a).coeff j) *
          a.prod (fun k n=>B.seed k^n) := by
  let g:=F.coeff i
  change ((F.map (MvPolynomial.eval₂Hom (mapRingHom (algebraMap L B.E))
    (C ∘ B.seed))).coeff i).coeff j= _
  rw [coeff_map]
  change (MvPolynomial.eval₂Hom (mapRingHom (algebraMap L B.E)) (C ∘ B.seed) g).coeff j= _
  conv_lhs=>rw [g.as_sum]
  rw [map_sum,finsetSum_coeff]
  apply sum_congr rfl
  intro a _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Function.comp_apply,← map_pow C]
  rw [show (a.prod fun k n=>C (B.seed k^n))=C (a.prod fun k n=>B.seed k^n) by
    simp only [Finsupp.prod,map_prod]]
  rw [coeff_mul_C,coe_mapRingHom,coeff_map]
theorem restrict_ne {q:Curve} (hq:Irreducible q) (B:CurveModel q)
    {F:Raw} (hF:Moving F) :restrict B F≠0:= by
  intro hz
  have hp:Irreducible (C (swap (C q)) :Raw) :=
    (Polynomial.prime_C_iff.mpr (((Polynomial.prime_C_iff.mpr hq.prime).irreducible).map swap).prime).irreducible
  have hd:C (swap (C q))∣F:= by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    rw [← map_dvd_iff swap.symm]
    rw [RingEquiv.symm_apply_apply,C_dvd_iff_dvd_coeff]
    intro j
    have hm:slice (F.coeff i) j∈RingHom.ker
        (MvPolynomial.eval₂Hom (algebraMap L B.E) B.seed) := by
      rw [RingHom.mem_ker,slice,map_sum]
      simp only [MvPolynomial.eval₂Hom_monomial]
      rw [← restrict_coeff B F i j,hz,coeff_zero,coeff_zero]
    rw [B.equation,Ideal.mem_span_singleton,slice_coeff] at hm
    exact hm
  simpa only [natDegree_C,Nat.lt_irrefl] using (hF.2 _ hp hd).1
theorem restrict_degree {q:Curve} (B:CurveModel q) (F:Raw) :
    (restrict B F).natDegree≤F.natDegree :=natDegree_map_le
end
end qGWTmVd
