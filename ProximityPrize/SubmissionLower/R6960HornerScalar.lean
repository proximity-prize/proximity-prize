import ProximityPrize.SubmissionLower.R6960HornerIntegral
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityPolynomial

set_option Elab.async false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.Horner
noncomputable section
open Polynomial
open scoped Polynomial BigOperators

section TwoCharts
variable {k E : Type*} [Field k] [Field E] [Algebra (RatFunc k) E]

/-- Integrality with the indicated coefficient embedding, so the finite
and reciprocal charts can use different maps from the same polynomial type. -/
def IntegralOver (ι : k[X] →+* E) (u : E) : Prop := @IsIntegral k[X] E _ _ ι.toAlgebra u

abbrev finiteScalar : k[X] →+* E := (algebraMap (RatFunc k) E).comp (algebraMap k[X] (RatFunc k))

abbrev infinityScalar : k[X] →+* E := (algebraMap (RatFunc k) E).comp (MonicChart.AtInfinity k)

private theorem horner_map_scale {A F : Type*} [CommRing A] [Nontrivial A] [CommRing F]
    (p q : A[X]) (j qj : A→+* F) (s : F)
    (scale : ∀ n,qj (q.coeff n)=s*j (p.coeff n)) {d : ℕ} (pos : 0<d) :
    (hornerPolynomial q d).map qj=C s*(hornerPolynomial p d).map j := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => simp only [coeff_C_mul,coeff_map,hornerPolynomial,coeff_X_mul_zero,map_zero,mul_zero]
  | succ n =>
    simp only [coeff_C_mul,coeff_map,hornerPolynomial,coeff_X_mul,coeff_tail _ pos]
    exact scale (d+n)

private theorem eval_scalar {A F : Type*} [CommRing A] [CommRing F] [Algebra F E]
    (p : A[X]) (j : A→+* F) (y : E) :
    aeval y (p.map j)=p.eval₂ ((algebraMap F E).comp j) y := by
  rw [aeval_def,eval₂_map]

/-- If all scalar coefficient degrees are at most `v`, each Horner
section has an infinity pole of order at most `v` in the reciprocal
polynomial chart of the same root field. -/
theorem scalar_horner_charts (p : k[X][X]) (v : ℕ)
    (width : ∀ j,(p.coeff j).natDegree≤v) {d : ℕ} (pos : 0<d) (y : E)
    (root : aeval y (p.map (algebraMap k[X] (RatFunc k)))=0) :
    IntegralOver (finiteScalar (k:=k) (E:=E)) (horner finiteScalar p d y) ∧
    IntegralOver (infinityScalar (k:=k) (E:=E))
      ((algebraMap (RatFunc k) E (RatFunc.X⁻¹))^v*horner finiteScalar p d y) := by
  let j := algebraMap k[X] (RatFunc k)
  let j' := MonicChart.AtInfinity k
  let s : RatFunc k := (RatFunc.X⁻¹)^v
  let q := MonicChart.weightedInfinity p v 0
  have scale (n : ℕ) : j' (q.coeff n)=s*j (p.coeff n) := by
    unfold q
    rw [MonicChart.coeff_weightedInfinity,zero_mul,Nat.sub_zero,MonicChart.reverse_atInfinity _ _ (width n)]
    exact mul_comm _ _
  have mapQ : q.map j'=C s*p.map j := by
    ext n
    rw [coeff_map,coeff_C_mul,coeff_map,scale]
  have qroot : q.eval₂ (infinityScalar (k:=k) (E:=E)) y=0 := by
    rw [←eval_scalar q j',mapQ,map_mul,root,mul_zero]
  have relation : horner infinityScalar q d y=(algebraMap (RatFunc k) E s)*horner finiteScalar p d y := by
    rw [horner,horner,←eval_scalar _ j',←eval_scalar _ j,
      horner_map_scale p q j j' s scale pos,map_mul,aeval_C]
  refine ⟨?_,?_⟩
  · let : Algebra k[X] E := (finiteScalar (k:=k) (E:=E)).toAlgebra
    exact horner_integral p pos y (by rw [eval_scalar p j] at root; exact root)
  · let : Algebra k[X] E := (infinityScalar (k:=k) (E:=E)).toAlgebra
    rw [show (algebraMap (RatFunc k) E (RatFunc.X⁻¹))^v=algebraMap (RatFunc k) E s from (map_pow _ _ _).symm,
      ←relation]
    exact horner_integral q pos y qroot
end TwoCharts

section Independence
variable {A F E : Type*} [CommRing A] [Nontrivial A] [Field F] [Field E] [Algebra F E]

/-- The constant section followed by the triangular Horner sections. -/
def sectionPoly (p : A[X]) (i : Fin p.natDegree) : A[X] :=
  if i.val=0 then 1 else hornerPolynomial p (p.natDegree-i.val+1)

private theorem sectionPoly_degree (p : A[X]) (i : Fin p.natDegree) :
    (sectionPoly p i).natDegree=i.val ∧ sectionPoly p i≠0 := by
  by_cases zero : i.val=0
  · simp [sectionPoly,zero]
  have ne : p≠0 := by
    intro h
    have small := i.isLt
    have hz : p.natDegree=0 := (congrArg natDegree h).trans natDegree_zero
    omega
  let d := p.natDegree-i.val+1
  have pos : 0<d := by change 0<_+1; omega
  have form : sectionPoly p i=hornerPolynomial p d := by simp only [sectionPoly,zero,ite_false,d]
  have lead : (sectionPoly p i).coeff i.val≠0 := by
    obtain ⟨j,eq⟩ := Nat.exists_eq_succ_of_ne_zero zero
    rw [form,hornerPolynomial,eq,coeff_X_mul,coeff_tail _ pos]
    have sum : d+j=p.natDegree := by
      change p.natDegree-i.val+1+j=p.natDegree
      have hi := i.isLt
      omega
    rw [sum,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr ne
  refine ⟨le_antisymm ?_ (le_natDegree_of_ne_zero lead),?_⟩
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n nbig
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    rw [form,hornerPolynomial,coeff_X_mul,coeff_tail _ pos]
    apply coeff_eq_zero_of_natDegree_lt
    have hi := i.isLt
    change p.natDegree<p.natDegree-i.val+1+j
    omega
  · exact fun eq=>lead (by rw [eq,coeff_zero])

/-- The constant plus the `e−1` Horner sections are independent when
the ordinate has minimal polynomial degree `e` over the rational base. -/
theorem sections_independent (ι : A→+* F) (inj : Function.Injective ι) (p : A[X])
    (y : E) (degree : (minpoly F y).natDegree=p.natDegree) :
    LinearIndependent F (fun i : Fin p.natDegree=>aeval y ((sectionPoly p i).map ι)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g zero i
  by_contra ni
  let Q := ∑ j, g j • (sectionPoly p j).map ι
  have qeval : aeval y Q=0 := by simpa only [Q,map_sum,map_smul] using zero
  have epos : 0<p.natDegree := i.isLt.pos
  have mapdegree (j : Fin p.natDegree) : ((sectionPoly p j).map ι).natDegree=j.val := by
    rw [natDegree_map_eq_of_injective inj,(sectionPoly_degree p j).1]
  have qb : Q.natDegree≤p.natDegree-1 := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_smul_le _ _).trans (by rw [mapdegree]; have hj := j.isLt; omega)
  have qzero : Q=0 := by
    by_contra nq
    have dq := natDegree_le_of_dvd (minpoly.dvd F y qeval) nq
    omega
  let S := Finset.univ.filter fun j : Fin p.natDegree=>g j≠0
  have hS : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ni⟩⟩
  let m := S.max' hS
  have hm : m∈S := Finset.max'_mem _ _
  have cm : g m≠0 := (Finset.mem_filter.mp hm).2
  have lead : (((sectionPoly p m).map ι).coeff m.val)≠0 := by
    rw [←mapdegree m,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr ((Polynomial.map_ne_zero_iff inj).mpr (sectionPoly_degree p m).2)
  have bad := congrArg (fun f : F[X]=>f.coeff m.val) qzero
  unfold Q at bad
  rw [Polynomial.finsetSum_coeff,Finset.sum_eq_single m,coeff_smul,smul_eq_mul,coeff_zero] at bad
  · exact (mul_ne_zero cm lead) bad
  · intro j _ jm
    by_cases h : g j=0
    · rw [h,zero_smul,coeff_zero]
    · have jle : j≤m := Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have jlt : j.val<m.val := lt_of_le_of_ne jle (Fin.val_injective.ne jm)
      rw [coeff_smul,coeff_eq_zero_of_natDegree_lt (mapdegree j |>.trans_lt jlt),smul_zero]
  · simp

end Independence

#print axioms scalar_horner_charts
#print axioms sections_independent
end
end Lower6960.Horner
