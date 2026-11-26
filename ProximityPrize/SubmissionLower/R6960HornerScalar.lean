import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing

set_option Elab.async false

-- merged module R6960HornerIntegral
section Merged_R6960HornerIntegral
set_option Elab.async false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.Horner
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
variable {A E : Type*} [CommRing A] [Field E]
def hornerPolynomial (p : (Polynomial A)) (d : ℕ) : (Polynomial A) := Polynomial.X * (p /ₘ (Polynomial.X ^ d))
def horner (ι : A →+* E) (p : (Polynomial A)) (d : ℕ) (y : E) : E :=
  (hornerPolynomial p d).eval₂ ι y
theorem horner_eq (ι : A →+* E) (p : (Polynomial A)) (d : ℕ) (y : E) :
    horner ι p d y=y*(p /ₘ (Polynomial.X ^ d)).eval₂ ι y := by
  rw [horner,hornerPolynomial,eval₂_mul,eval₂_X]
private theorem remainder_degree [Nontrivial A] (p : (Polynomial A)) {d : ℕ} (pos : 0<d) :
    (p %ₘ (Polynomial.X ^ d)).natDegree<d := by
  have nz : (Polynomial.X : (Polynomial A))^d≠1 := by
    intro h
    have deg := congrArg natDegree h
    rw [natDegree_X_pow,natDegree_one] at deg
    omega
  simpa only [natDegree_X_pow] using natDegree_modByMonic_lt p (monic_X_pow d) nz
private theorem backward_eval (ι : A →+* E) (p : (Polynomial A)) {d : ℕ} (pos : 0<d) (y : E)
    (yn : y≠0) (root : p.eval₂ ι y=0) :
    horner ι p d y=-((p %ₘ (Polynomial.X ^ d)).reflect (d-1)).eval₂ ι y⁻¹ := by
  let : Nontrivial A := ι.domain_nontrivial
  let r := p %ₘ (Polynomial.X ^ d)
  let q := p /ₘ (Polynomial.X ^ d)
  have qr : r.eval₂ ι y + y^d*q.eval₂ ι y=0 := by
    have h := congrArg (fun f : (Polynomial A)=>f.eval₂ ι y) (modByMonic_add_div p (Polynomial.X ^ d))
    rw [eval₂_add,eval₂_mul,eval₂_X_pow,root] at h
    exact h
  let : Invertible y := invertibleOfNonzero yn
  have rd : r.natDegree≤d-1 := by
    change (p %ₘ (Polynomial.X ^ d)).natDegree≤d-1
    have lt := remainder_degree p pos
    omega
  have ref := eval₂_reflect_mul_pow ι y (d-1) r rd
  rw [invOf_eq_inv] at ref
  have split : y^d=y^(d-1)*y := by
    rw [←pow_succ,Nat.sub_add_cancel pos]
  apply mul_right_cancel₀ (pow_ne_zero (d-1) yn)
  calc
    horner ι p d y*y^(d-1)=y^d*q.eval₂ ι y := by
      rw [horner_eq,split]
      change y*q.eval₂ ι y*y^(d-1)=_
      ring
    _ = -r.eval₂ ι y := by linear_combination qr
    _ = -((r.reflect (d-1)).eval₂ ι y⁻¹)*y^(d-1) := by rw [neg_mul,ref]
private theorem eval_in_valuation (V : ValuationSubring E) (ι : A →+* E)
    (coeffs : ∀ a,ι a∈V) {y : E} (hy : y∈V) (p : (Polynomial A)) : p.eval₂ ι y∈V := by
  rw [eval₂_eq_sum]
  exact V.toSubring.sum_mem fun i _=>V.toSubring.mul_mem (coeffs (p.coeff i)) (V.toSubring.pow_mem hy i)
theorem horner_integral [Algebra A E] (p : (Polynomial A)) {d : ℕ} (pos : 0<d) (y : E)
    (root : p.eval₂ (algebraMap A E) y=0) :
    IsIntegral A (horner (algebraMap A E) p d y) := by
  change horner (algebraMap A E) p d y∈(integralClosure A E).toSubring
  rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R:=(integralClosure A E).toSubring),Subring.mem_iInf]
  rintro ⟨V,contains⟩
  have coeffs (a : A) : algebraMap A E a∈V := contains (show IsIntegral A (algebraMap A E a) from isIntegral_algebraMap)
  by_cases yn : y=0
  · simp only [horner_eq,yn,zero_mul]
    exact V.zero_mem
  rcases V.mem_or_inv_mem y with hy|hy
  · exact eval_in_valuation V (algebraMap A E) coeffs hy _
  · rw [backward_eval (algebraMap A E) p pos y yn root]
    exact V.toSubring.neg_mem (eval_in_valuation V (algebraMap A E) coeffs hy _)
theorem coeff_tail [Nontrivial A] (p : (Polynomial A)) {d : ℕ} (pos : 0<d) (j : ℕ) :
    (p /ₘ (Polynomial.X ^ d)).coeff j=p.coeff (d+j) := by
  have rzero : (p %ₘ (Polynomial.X ^ d)).coeff (d+j)=0 :=
    coeff_eq_zero_of_natDegree_lt ((remainder_degree p pos).trans_le (Nat.le_add_right _ _))
  have eq := congrArg (fun f : (Polynomial A)=>f.coeff (d+j)) (modByMonic_add_div p (Polynomial.X ^ d))
  rw [coeff_add,rzero,zero_add,Nat.add_comm d j,coeff_X_pow_mul] at eq
  simpa only [Nat.add_comm j d] using eq
end
end Lower6960.Horner

end Merged_R6960HornerIntegral

-- merged module R6960HornerScalar
section Merged_R6960HornerScalar
set_option Elab.async false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.Horner
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
section TwoCharts
variable {k E : Type*} [Field k] [Field E] [Algebra (RatFunc k) E]
def IntegralOver (ι : (Polynomial k) →+* E) (u : E) : Prop := @IsIntegral (Polynomial k) E _ _ ι.toAlgebra u
abbrev finiteScalar : (Polynomial k) →+* E := (algebraMap (RatFunc k) E).comp (algebraMap (Polynomial k) (RatFunc k))
abbrev infinityScalar : (Polynomial k) →+* E := (algebraMap (RatFunc k) E).comp (MonicChart.AtInfinity k)
private theorem horner_map_scale {A F : Type*} [CommRing A] [Nontrivial A] [CommRing F]
    (p q : (Polynomial A)) (j qj : A→+* F) (s : F)
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
    (p : (Polynomial A)) (j : A→+* F) (y : E) :
    aeval y (p.map j)=p.eval₂ ((algebraMap F E).comp j) y := by
  rw [aeval_def,eval₂_map]
theorem scalar_horner_charts (p : (Polynomial (Polynomial k))) (v : ℕ)
    (width : ∀ j,(p.coeff j).natDegree≤v) {d : ℕ} (pos : 0<d) (y : E)
    (root : aeval y (p.map (algebraMap (Polynomial k) (RatFunc k)))=0) :
    IntegralOver (finiteScalar (k:=k) (E:=E)) (horner finiteScalar p d y) ∧
    IntegralOver (infinityScalar (k:=k) (E:=E))
      ((algebraMap (RatFunc k) E (RatFunc.X⁻¹))^v*horner finiteScalar p d y) := by
  let j := algebraMap (Polynomial k) (RatFunc k)
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
  · let : Algebra (Polynomial k) E := (finiteScalar (k:=k) (E:=E)).toAlgebra
    exact horner_integral p pos y (by rw [eval_scalar p j] at root; exact root)
  · let : Algebra (Polynomial k) E := (infinityScalar (k:=k) (E:=E)).toAlgebra
    rw [show (algebraMap (RatFunc k) E (RatFunc.X⁻¹))^v=algebraMap (RatFunc k) E s from (map_pow _ _ _).symm,
      ←relation]
    exact horner_integral q pos y qroot
end TwoCharts
section Independence
variable {A F E : Type*} [CommRing A] [Nontrivial A] [Field F] [Field E] [Algebra F E]
def sectionPoly (p : (Polynomial A)) (i : Fin p.natDegree) : (Polynomial A) :=
  if i.val=0 then 1 else hornerPolynomial p (p.natDegree-i.val+1)
private theorem sectionPoly_degree (p : (Polynomial A)) (i : Fin p.natDegree) :
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
theorem sections_independent (ι : A→+* F) (inj : Function.Injective ι) (p : (Polynomial A))
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
  have bad := congrArg (fun f : (Polynomial F)=>f.coeff m.val) qzero
  unfold Q at bad
  rw [Polynomial.finsetSum_coeff,Finset.sum_eq_single m,Polynomial.coeff_smul,smul_eq_mul,coeff_zero] at bad
  · exact (mul_ne_zero cm lead) bad
  · intro j _ jm
    by_cases h : g j=0
    · rw [h,zero_smul,coeff_zero]
    · have jle : j≤m := Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have jlt : j.val<m.val := lt_of_le_of_ne jle (Fin.val_injective.ne jm)
      rw [Polynomial.coeff_smul,coeff_eq_zero_of_natDegree_lt (mapdegree j |>.trans_lt jlt),smul_zero]
  · simp
end Independence
end
end Lower6960.Horner

end Merged_R6960HornerScalar
