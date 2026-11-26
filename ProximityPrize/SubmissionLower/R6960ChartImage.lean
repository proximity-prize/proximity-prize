import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.High6966RescueGeometry
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.R6960Anchor6966Columns
import ProximityPrize.SubmissionLower.R6960Anchor6966Dimension
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Front6960Rank5
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Gates
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0
import ProximityPrize.SubmissionLower.R6960Low6960Tiles1
import ProximityPrize.SubmissionLower.R6960Low6960Tiles10
import ProximityPrize.SubmissionLower.R6960Low6960Tiles11
import ProximityPrize.SubmissionLower.R6960Low6960Tiles12
import ProximityPrize.SubmissionLower.R6960Low6960Tiles13
import ProximityPrize.SubmissionLower.R6960Low6960Tiles14
import ProximityPrize.SubmissionLower.R6960Low6960Tiles15
import ProximityPrize.SubmissionLower.R6960Low6960Tiles16
import ProximityPrize.SubmissionLower.R6960Low6960Tiles17
import ProximityPrize.SubmissionLower.R6960Low6960Tiles2
import ProximityPrize.SubmissionLower.R6960Low6960Tiles3
import ProximityPrize.SubmissionLower.R6960Low6960Tiles4
import ProximityPrize.SubmissionLower.R6960Low6960Tiles5
import ProximityPrize.SubmissionLower.R6960Low6960Tiles6
import ProximityPrize.SubmissionLower.R6960Low6960Tiles7
import ProximityPrize.SubmissionLower.R6960Low6960Tiles8
import ProximityPrize.SubmissionLower.R6960Low6960Tiles9
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6960ChartImage
set_option Elab.async false




set_option Elab.async false

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartImage
open Polynomial MonicChart
open scoped Polynomial BigOperators
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq (RatFunc K)]

/-- Scalar corrections made independently in ambient coordinates land back in a fixed
field-linear subspace once the negative abscissa twist exceeds its equation degrees. -/
theorem eventually_in_subspace (V : Submodule (RatFunc K) (J → RatFunc K)) :
    ∃ H : ℕ, ∀ a : ℕ, H<a → ∀ c v w : J → RatFunc K, v∈V → w∈V →
      (∀ j, c j-v j ∈ (algebraMap (Polynomial K) (RatFunc K)).range) →
      (∀ j, RatFunc.X^a*(c j-w j) ∈ (Infinity K)) → c∈V := by
  classical
  obtain ⟨Q,compl⟩ := V.exists_isCompl
  let P := Q.projection V compl.symm
  let M := LinearMap.toMatrix' P
  let ι := algebraMap (Polynomial K) (RatFunc K)
  obtain ⟨d,clear⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun x : J×J => M x.1 x.2)
  choose pol value using clear
  have entry (i j : J) : ι (pol (i,j))=ι (d:(Polynomial K))*M i j := by
    simpa only [Algebra.smul_def] using value (i,j)
  let H:=Finset.univ.sup (fun p : J×J => (pol p).natDegree)
  refine ⟨H,fun a ha c v w hv hw finite infinity => ?_⟩
  have equation (i : J) (u : J → RatFunc K) :
      ι (d:(Polynomial K))*P u i=∑ j,ι (pol (i,j))*u j := by
    rw [←LinearMap.toMatrix'_mulVec P u]
    change _*(∑ j,M i j*u j) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [entry,mul_assoc])
  have residual (i : J) (l : J→RatFunc K) (hl : l∈V) :
      ι (d:(Polynomial K))*P c i=∑ j,ι (pol (i,j))*(c j-l j) := by
    have pl : P l=0 := Q.projection_apply_of_mem_right compl.symm hl
    simpa only [map_sub,pl,sub_zero,Pi.sub_apply,Pi.zero_apply] using equation i (c-l)
  have projected : P c=0 := by
    funext i
    let q:=ι (d:(Polynomial K))*P c i
    have fin : q∈ι.range := by
      dsimp only [q]
      rw [residual i v hv]
      exact ι.range.sum_mem (fun j _ => ι.range.mul_mem ⟨_,rfl⟩ (finite j))
    have inf : RatFunc.X*q ∈ (Infinity K) := by
      change RatFunc.X*(ι (d:(Polynomial K))*P c i) ∈ (Infinity K)
      rw [residual i w hw,Finset.mul_sum]
      apply (Infinity K).sum_mem
      intro j _
      have bound : (pol (i,j)).natDegree ≤ a-1 :=
        (Finset.le_sup (f:=fun p:J×J=>(pol p).natDegree) (Finset.mem_univ (i,j))).trans
          (show H≤a-1 by omega)
      let r:=inftyRingEval K ((pol (i,j)).reflect (a-1))
      have form : (r:RatFunc K)=ι (pol (i,j))*RatFunc.X⁻¹^(a-1) :=
        reverse_atInfinity _ _ bound
      have eq : (r:RatFunc K)*(RatFunc.X^a*(c j-w j)) =
          RatFunc.X*(ι (pol (i,j))*(c j-w j)) := by
        have split : a-1+1=a := Nat.sub_add_cancel (by omega)
        have cancel : (RatFunc.X⁻¹ : RatFunc K)^(a-1)*RatFunc.X^a=RatFunc.X := by
          conv_lhs => rhs; rw [←split,pow_succ]
          rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ RatFunc.X_ne_zero,one_pow,one_mul]
        rw [form]
        linear_combination ι (pol (i,j))*(c j-w j)*cancel
      exact eq ▸ (Infinity K).toSubring.mul_mem r.property (infinity j)
    obtain ⟨p,pe⟩:=fin
    have integral : IsIntegral (Polynomial K) q := pe ▸ isIntegral_algebraMap
    have intInf : IsIntegral (Infinity K) (RatFunc.X*q) :=
      isIntegral_algebraMap (x:=(⟨_,inf⟩ : Infinity K))
    have zero : q=0 := DifferentialPoles.negative_twist q integral (by simpa using intInf)
    exact (mul_eq_zero.mp zero).resolve_left
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) _)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property))
  exact (Q.projection_apply_eq_zero_iff compl.symm).mp projected

#print axioms eventually_in_subspace
end Lower6960.ChartImage

end
end Merged6967_R6960ChartImage

section Merged6967_R6960HornerScalar
set_option Elab.async false





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
#print axioms horner_integral
#print axioms coeff_tail
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
#print axioms scalar_horner_charts
#print axioms sections_independent
end
end Lower6960.Horner

end Merged_R6960HornerScalar

end Merged6967_R6960HornerScalar

section Merged6967_R6960MonicChartActual
set_option Elab.async false





































set_option Elab.async false

-- merged module R6960Low6960Tiles18
section Merged_R6960Low6960Tiles18

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group18
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [45104106503, 83659405335, 66463107123, 81696668163, 47303101963], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [58040064011, 83676385311, 40659820603, 77351440911, 42991853071], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [66613552143, 79347934247, 23463178303, 73056544271, 25811987983], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [70891876371, 75019482155, 10561502275, 68778358283, 12943866379], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [75086314519, 70623855663, 64567346679, 142919159, 73089957383], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [75086383131, 57873174579, 73073248779], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [75036120095, 44971564087, 68811838979, 47337150979], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [70825107491, 36364854331], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [70690892839, 23463178303, 64533720575, 25879096831], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [66446325803, 14856468547, 60171647503, 17222055439], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [62134584367, 6266536003, 60171716111], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [57806065715, 51598561803, 59033099], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤49) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 18 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤136 ∧ 8+a.j≤57 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
end Low6960Allocation.Group18

end Merged_R6960Low6960Tiles18

-- merged module R6960Low6960Count
section Merged_R6960Low6960Count

set_option Elab.async false

namespace Lower6960.Low
open Low6960Allocation (Band Receipt Gates bandOrders)

private def receipts : ∀ k : Band, Receipt k
  | ⟨0,_⟩ => Low6960Allocation.Group0.receipt
  | ⟨1,_⟩ => Low6960Allocation.Group1.receipt
  | ⟨2,_⟩ => Low6960Allocation.Group2.receipt
  | ⟨3,_⟩ => Low6960Allocation.Group3.receipt
  | ⟨4,_⟩ => Low6960Allocation.Group4.receipt
  | ⟨5,_⟩ => Low6960Allocation.Group5.receipt
  | ⟨6,_⟩ => Low6960Allocation.Group6.receipt
  | ⟨7,_⟩ => Low6960Allocation.Group7.receipt
  | ⟨8,_⟩ => Low6960Allocation.Group8.receipt
  | ⟨9,_⟩ => Low6960Allocation.Group9.receipt
  | ⟨10,_⟩ => Low6960Allocation.Group10.receipt
  | ⟨11,_⟩ => Low6960Allocation.Group11.receipt
  | ⟨12,_⟩ => Low6960Allocation.Group12.receipt
  | ⟨13,_⟩ => Low6960Allocation.Group13.receipt
  | ⟨14,_⟩ => Low6960Allocation.Group14.receipt
  | ⟨15,_⟩ => Low6960Allocation.Group15.receipt
  | ⟨16,_⟩ => Low6960Allocation.Group16.receipt
  | ⟨17,_⟩ => Low6960Allocation.Group17.receipt
  | ⟨18,_⟩ => Low6960Allocation.Group18.receipt
  | ⟨n+19,h⟩ => absurd h (by omega)

private theorem receipts_orders : (fun k => (receipts k).orders) = bandOrders :=
  funext fun k => by fin_cases k <;> rfl

/-- The 69.61 low count for the actual family at every positive height through 2358, given the
payment `gates` of the gated shapes (empty band and bands `(w,3,1)`, `w ≤ 5`) by the two-cut gates. -/
theorem count (gates : Gates) {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179818 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2358) :
    Γ.card≤266228295297719504 := by
  obtain ⟨G,gate,htab⟩ := gates
  rw [← receipts_orders] at htab
  exact count_with_receipts receipts htab gate M F lo hi

#print axioms count
end Lower6960.Low

end Merged_R6960Low6960Count

-- merged module R6960Front6960Assembly
section Merged_R6960Front6960Assembly
set_option Elab.async false
namespace Lower6960
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Front6960Radius (p q)
theorem low_front_count (gates : Low6960Allocation.Gates) : Front6960.c6 := by
  intro _ _ M _ F lo hi
  exact Low.count gates M F lo hi
theorem protocol_claim (gates : Low6960Allocation.Gates)
    (high : ∀ {u deleted Γ} (M : P1.ModelAt 33579 u deleted) (_F : P1.FamilyAt 179818 M Γ),
      2359 ≤ M.overhead → M.overhead ≤ 33579 → Γ.card ≤ 266228295297719504) :
    ProtocolClaim 6961 p q := by
  apply ProximityPrize.SubmissionLower.Front6960Radius.extend
  apply Front6960.of_children Front6960ListBank.scalar_list
    Front6960_1.proof Front6960_2.proof
    (Front6960_3.of_children Front6960_3_1.proof Front6960_3_2.proof)
    (Front6960_4.of_children Front6960_4_1.proof Front6960_4_2.proof)
    Front6960_5.proof (low_front_count gates)
  intro _ _ M _ F lo hi
  exact high M F lo hi
theorem protocol_claim_of_retained (gates : Low6960Allocation.Gates) (retained : RetainedCount) : ProtocolClaim 6961 p q :=
  protocol_claim gates (fun M F lo hi => high_count_of_retained retained M F lo hi)
#print axioms protocol_claim_of_retained
#print axioms low_front_count
#print axioms protocol_claim
end Lower6960

end Merged_R6960Front6960Assembly

-- merged module R6960RetainedCompressionAssembly
section Merged_R6960RetainedCompressionAssembly

set_option Elab.async false
namespace Lower6960

/-- The 69.61 claim reduces to the remaining bounded-weight,
positive-seed, nonpure marked-factor estimate. -/
theorem protocol_claim_of_nonpure (gates : Low6960Allocation.Gates) (count : RetainedCompression.NonPureFactorPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6961
      ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q :=
  protocol_claim_of_retained gates (RetainedCompression.retained_of_nonpure count)

#print axioms protocol_claim_of_nonpure
end Lower6960

end Merged_R6960RetainedCompressionAssembly

-- merged module R6960RetainedLinearBase
section Merged_R6960RetainedLinearBase
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial nonZeroDivisors
variable {F E : Type} [Field F] [Field E] [Algebra F E]
abbrev Fn (F : Type) [Field F] := FractionRing (Polynomial F)
def constants : (Polynomial F) →+* (Polynomial E) := mapRingHom (algebraMap F E)
theorem constants_injective : Function.Injective (constants (F:=F) (E:=E)) :=
  Polynomial.map_injective _ (algebraMap F E).injective
def rationalConstants : Fn F →+* Fn E :=
  IsFractionRing.map (constants_injective (F:=F) (E:=E))
abbrev incl (F : Type) [Field F] := algebraMap (Polynomial F) (Fn F)
theorem incl_injective (F : Type) [Field F] : Function.Injective (incl F) :=
  IsFractionRing.injective (Polynomial F) (Fn F)
@[simp] theorem rationalConstants_incl (a : (Polynomial F)) :
    rationalConstants (E:=E) (incl F a)=incl E (constants a) := by
  unfold rationalConstants IsFractionRing.map
  exact IsLocalization.map_eq _ _
@[simp] theorem eval_constants (a : (Polynomial F)) (x : F) :
    (constants (E:=E) a).eval (algebraMap F E x)=algebraMap F E (a.eval x) :=
  Polynomial.eval_map_apply (algebraMap F E) (p:=a) x
private theorem base_multiple_linear [Algebra.IsAlgebraic F E] (x : F) (r : E)
    (away : r≠algebraMap F E x) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧ (Polynomial.X-C r)∣constants b := by
  have integ : IsIntegral F r := Algebra.IsIntegral.isIntegral r
  let b := minpoly F r
  have root : (constants (E:=E) b).eval r=0 := by
    change (b.map (algebraMap F E)).eval r=0
    rw [eval_map]
    exact minpoly.aeval F r
  refine ⟨b,?_ ,dvd_iff_isRoot.mpr root⟩
  intro zero
  have dvd : Polynomial.X-C x∣b := dvd_iff_isRoot.mpr zero
  have assoc := (irreducible_X_sub_C x).associated_of_dvd (minpoly.irreducible integ) dvd
  obtain ⟨a,eq⟩ := assoc.symm.dvd
  have mapped := congrArg (fun g : (Polynomial F) => (constants (E:=E) g).eval r) eq
  change (constants (E:=E) (Polynomial.X-C x)).eval r=(constants (E:=E) (b*a)).eval r at mapped
  rw [map_mul,eval_mul,root,zero_mul] at mapped
  have eq' : (constants (E:=E) (Polynomial.X-C x)).eval r=r-algebraMap F E x := by
    simp only [constants,coe_mapRingHom,Polynomial.map_sub,Polynomial.map_X,
      Polynomial.map_C,eval_sub,eval_X,eval_C]
  rw [eq'] at mapped
  exact away (sub_eq_zero.mp mapped)
theorem base_multiple [IsAlgClosed E] [Algebra.IsAlgebraic F E]
    (x : F) (q : (Polynomial E)) (regular : q.eval (algebraMap F E x)≠0) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧ q∣constants b := by
  induction q using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at regular
  | unit q hu => exact ⟨1,by simp,hu.dvd⟩
  | mul a q an ir ih =>
    rw [eval_mul] at regular
    have qa : a.eval (algebraMap F E x)≠0 := fun z=>regular (by rw [z,mul_zero])
    have qq : q.eval (algebraMap F E x)≠0 := fun z=>regular (by rw [z,zero_mul])
    obtain ⟨u,hu,dU⟩ := ih qa
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_root q (degree_pos_of_irreducible ir).ne'
    have away : r≠algebraMap F E x := fun h=>qq (h ▸ hr)
    have n : Polynomial.X-C r∣q := dvd_iff_isRoot.mpr hr
    have tied := (irreducible_X_sub_C r).associated_of_dvd ir n
    obtain ⟨v,hv,dV⟩ := base_multiple_linear x r away
    exact ⟨v*u,by rw [eval_mul]; exact mul_ne_zero hv hu,
      by rw [map_mul]; exact mul_dvd_mul (tied.symm.dvd.trans dV) dU⟩
def base : (Polynomial F) →+* Fn E := (incl E).comp constants
theorem polynomial_integral [Algebra.IsAlgebraic F E] (p : (Polynomial E)) :
    (base (F:=F) (E:=E)).IsIntegralElem (incl E p) := by
  let j := base (F:=F) (E:=E)
  letI : Algebra (Polynomial F) (Fn E) := j.toAlgebra
  have const (a : E) : IsIntegral (Polynomial F) (incl E (C a)) := by
    let η : E →+* Fn E := (incl E).comp C
    have h : (algebraMap F E).IsIntegralElem a := Algebra.IsIntegral.isIntegral a
    have mapped := h.map η
    have eq : η.comp (algebraMap F E)=j.comp C := by
      apply RingHom.ext
      intro t
      simp [η,j,base,constants]
    rw [eq] at mapped
    exact mapped.of_comp
  have abscissa : IsIntegral (Polynomial F) (incl E (Polynomial.X : (Polynomial E))) := by
    have eq : (algebraMap (Polynomial F) (Fn E)) Polynomial.X=incl E (Polynomial.X : (Polynomial E)) := by
      change j Polynomial.X=_
      simp [j,base,constants]
    exact eq ▸ isIntegral_algebraMap
  change IsIntegral (Polynomial F) (incl E p)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
    exact (const a).mul (abscissa.pow n)
theorem integral_is_polynomial {r : Fn E} (h : (base (F:=F) (E:=E)).IsIntegralElem r) :
    ∃ p : (Polynomial E), incl E p=r := by
  have integral : IsIntegral (Polynomial E) r := h.of_comp
  exact (isIntegrallyClosed_iff (K:=Fn E)).mp (inferInstance : IsIntegrallyClosed (Polynomial E)) integral
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearBase

-- merged module R6960RetainedLinearFactor
section Merged_R6960RetainedLinearFactor
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2300000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial nonZeroDivisors
variable {F E : Type} [Field F] [Field E] [Algebra F E]
abbrev Plane (F : Type) [Field F] := Polynomial (Polynomial F)
def arithmetic (P : Plane F) : Polynomial (Fn F) := P.map (incl F)
def geometric (P : Plane F) : Polynomial (Fn E) := P.map (base (E:=E))
theorem geometric_map (P : Plane F) : geometric (E:=E) P=(arithmetic P).map rationalConstants := by
  unfold geometric arithmetic
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  simp [base]
theorem geometric_deg (P : Plane F) : (geometric (E:=E) P).natDegree=P.natDegree := by
  have injective : Function.Injective (base (F:=F) (E:=E)) :=
    (incl_injective E).comp (constants_injective (F:=F) (E:=E))
  exact natDegree_map_eq_of_injective injective P
theorem arithmetic_irred {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree) :
    Irreducible (arithmetic P) :=
  (ir.isPrimitive (Nat.ne_of_gt pos)).irreducible_iff_irreducible_map_fraction_map.mp ir
theorem node_not_zero {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree) (x : F) :
    P.map (evalRingHom x)≠0 := by
  intro zero
  have prime := ir.isPrimitive (Nat.ne_of_gt pos)
  apply (irreducible_X_sub_C x).not_isUnit
  apply isPrimitive_iff_isUnit_of_C_dvd.mp prime
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  have gone := congrArg (fun Q : (Polynomial F) => Q.coeff i) zero
  simpa only [Polynomial.IsRoot,coeff_map,coe_evalRingHom,coeff_zero] using gone
abbrev numerator (r : Fn E) : (Polynomial E) := IsFractionRing.num (Polynomial E) r
abbrev denominator (r : Fn E) : (Polynomial E) := (IsFractionRing.den (Polynomial E) r).val
theorem denominator_ne (r : Fn E) : denominator r≠0 :=
  nonZeroDivisors.coe_ne_zero (IsFractionRing.den (Polynomial E) r)
theorem numerator_eq (r : Fn E) : r*incl E (denominator r)=incl E (numerator r) :=
  (IsFractionRing.num_mul_den_eq_num_iff_eq' (A:=(Polynomial E))).mpr rfl
private def line (r : Fn E) : Plane E := C (denominator r)*Polynomial.X+C (-numerator r)
private theorem line_primitive (r : Fn E) : (line r).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro b hb
  have coef := (C_dvd_iff_dvd_coeff ..).mp hb
  have first : b∣denominator r := by simpa [line] using coef 1
  have second : b∣numerator r := dvd_neg.mp (by simpa [line] using coef 0)
  exact IsFractionRing.num_den_reduced (Polynomial E) r second first
private theorem mapped_line (r : Fn E) :
    (line r).map (incl E)=C (incl E (denominator r))*(Polynomial.X-C r) := by
  simp only [line,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.map_neg,map_neg]
  rw [← numerator_eq r]
  rw [mul_sub, mul_comm r, C_mul]
  ring
private theorem line_prod_primitive (s : Multiset (Fn E)) : ((s.map line).prod).IsPrimitive := by
  letI : NormalizedGCDMonoid (Polynomial E) := Classical.choice inferInstance
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons,Multiset.prod_cons]
    exact (line_primitive r).mul ih
private theorem mapped_lines (s : Multiset (Fn E)) :
    ((s.map line).prod).map (incl E)=C ((s.map (fun r=>incl E (denominator r))).prod) *
      (s.map (fun r=>Polynomial.X-C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,mapped_line,ih,C_mul]
    ring
theorem exists_regular_root {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree)
    (splits : (geometric (E:=E) P).Splits) (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    ∃ r ∈ (geometric (E:=E) P).roots,
      (denominator r).eval (algebraMap F E x)≠0 ∧
      (numerator r).eval (algebraMap F E x)=(denominator r).eval (algebraMap F E x)*algebraMap F E t := by
  classical
  let Qe := P.map (constants (F:=F) (E:=E))
  let L := geometric (E:=E) P
  let rs := L.roots
  let G := (rs.map line).prod
  let b := (rs.map (fun r=>incl E (denominator r))).prod
  have Pn := ir.ne_zero
  have geo : Qe.map (incl E)=L := by
    simp [Qe, L, geometric, base, Polynomial.map_map]
  have dn : b≠0 := by
    apply Multiset.prod_ne_zero
    intro mem
    obtain ⟨r,_,eq⟩ := Multiset.mem_map.mp mem
    exact ((map_ne_zero_iff _ (incl_injective E)).mpr (denominator_ne r)) eq
  have Gmap : G.map (incl E)=C b*(rs.map (fun r=>Polynomial.X-C r)).prod := mapped_lines rs
  have fac := splits.eq_prod_roots
  have mapped_dvd : G.map (incl E)∣Qe.map (incl E) := by
    refine ⟨C (L.leadingCoeff/b),?_⟩
    rw [geo,Gmap]
    change L=C b*(rs.map (fun r=>Polynomial.X-C r)).prod*C (L.leadingCoeff/b)
    calc
      _ = C L.leadingCoeff*(rs.map (fun r=>Polynomial.X-C r)).prod := fac
      _ = _ := by
        rw [mul_right_comm,← C_mul,← mul_div_assoc,mul_div_cancel_left₀ _ dn]
  obtain ⟨q,hq⟩ := (line_prod_primitive rs).dvd_of_fraction_map_dvd_fraction_map mapped_dvd
  have Gn : G≠0 := (line_prod_primitive rs).ne_zero
  have Yn : Qe≠0 := by
    have inj : Function.Injective (Polynomial.mapRingHom (constants (F:=F) (E:=E))) :=
      Polynomial.map_injective _ (constants_injective (F:=F) (E:=E))
    exact (map_ne_zero_iff _ inj).mpr Pn
  have qn : q≠0 := fun z=>Yn (by rw [hq,z,mul_zero])
  have degg : G.natDegree=P.natDegree := by
    rw [← natDegree_map_eq_of_injective (incl_injective E) G,Gmap,natDegree_C_mul dn,
      natDegree_multiset_prod_X_sub_C_eq_card,← splits.natDegree_eq_card_roots]
    exact geometric_deg P
  have degY : Qe.natDegree=P.natDegree := natDegree_map_eq_of_injective constants_injective _
  have size : q.natDegree=0 := by
    rw [hq,natDegree_mul Gn qn,degg] at degY
    omega
  let c := q.coeff 0
  have facY : Qe=G*C c := hq.trans (by rw [eq_C_of_natDegree_eq_zero size])
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let node := evalRingHom x'
  have compare : Qe.map node=(P.map (evalRingHom x)).map (algebraMap F E) := by
    apply Polynomial.ext
    intro i
    simp only [Qe,coeff_map,node,coe_evalRingHom,eval_constants,x']
  have Yn' : Qe.map node≠0 := by
    rw [compare]
    intro zero
    apply node_not_zero ir pos x
    apply Polynomial.map_injective _ (algebraMap F E).injective
    simpa only [Polynomial.map_zero] using zero
  have cn' : c.eval x'≠0 := by
    intro ch
    apply Yn'
    rw [facY,Polynomial.map_mul,Polynomial.map_C,coe_evalRingHom,ch,C_0,mul_zero]
  have hit' : (Qe.map node).eval t'=0 := by
    rw [compare,eval_map_apply,hit,map_zero]
  let select : Plane E →+* E := (evalRingHom t').comp (mapRingHom node)
  change select Qe=0 at hit'
  rw [facY,map_mul] at hit'
  have pc : select (C c)=c.eval x' := by
    simp only [select, RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C,
      coe_evalRingHom,eval_C,node]
  rw [pc] at hit'
  have gone := (mul_eq_zero.mp hit').resolve_right cn'
  change select (rs.map line).prod=0 at gone
  rw [← Multiset.prod_hom, Multiset.map_map] at gone
  obtain ⟨r,hr,val⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp gone)
  have v : (denominator r).eval x'*t'+(-(numerator r)).eval x'=0 := by
    simpa [select,node,line] using val
  rw [eval_neg] at v
  have relation : (numerator r).eval x'=(denominator r).eval x'*t' := by
    linear_combination -v
  have den : (denominator r).eval x'≠0 := by
    intro collapse
    have num : (numerator r).eval x'=0 := by rw [relation,collapse,zero_mul]
    have d₀ : Polynomial.X-C x'∣numerator r := dvd_iff_isRoot.mpr num
    have d₁ : Polynomial.X-C x'∣denominator r := dvd_iff_isRoot.mpr collapse
    exact (irreducible_X_sub_C x').not_isUnit (IsFractionRing.num_den_reduced (Polynomial E) r d₀ d₁)
  exact ⟨r,hr,den,relation⟩
#print axioms node_not_zero
#print axioms exists_regular_root
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearFactor

-- merged module R6960RetainedLinearConjugacy
section Merged_R6960RetainedLinearConjugacy

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2700000

namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private theorem base_injective : Function.Injective (base (F:=F) (E:=E)) :=
  (incl_injective E).comp (constants_injective (F:=F) (E:=E))

private theorem adjoint_conjugates {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree)
    (b : (Polynomial F)) (x t : F) {r s : Fn E} (hr : r∈(geometric (E:=E) P).roots)
    (hs : s∈(geometric (E:=E) P).roots) :
    (base (F:=F) (E:=E)).IsIntegralElem ((base b)*(r-base (C t))/(base (Polynomial.X-C x))) →
    (base (F:=F) (E:=E)).IsIntegralElem ((base b)*(s-base (C t))/(base (Polynomial.X-C x))) := by
  let Q := arithmetic P
  letI : Fact (Irreducible Q) := ⟨arithmetic_irred ir pos⟩
  let j := (AdjoinRoot.of Q).comp (incl F)
  let u : AdjoinRoot Q := j b*(AdjoinRoot.root Q-j (C t))/j (Polynomial.X-C x)
  have raw (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      Q.eval₂ (rationalConstants (F:=F) (E:=E)) a=0 := by
    have injective : Function.Injective (Polynomial.mapRingHom (base (F:=F) (E:=E))) :=
      Polynomial.map_injective _ base_injective
    have nonzero : geometric (E:=E) P≠0 := (map_ne_zero_iff _ injective).mpr ir.ne_zero
    have ez := (mem_roots nonzero).mp ha
    change (geometric (E:=E) P).eval a=0 at ez
    rw [geometric_map,eval_map] at ez
    exact ez
  let lift (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :=
    AdjoinRoot.lift (rationalConstants (F:=F) (E:=E)) a (raw a ha)
  have extends_base (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      (lift a ha).comp j=base (F:=F) (E:=E) := by
    apply RingHom.ext
    intro a'
    dsimp [lift,j]
    rw [AdjoinRoot.lift_of,rationalConstants_incl]
    rfl
  have eq (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      lift a ha u=base b*(a-base (C t))/base (Polynomial.X-C x) := by
    simp only [u,map_div₀,map_mul,map_sub]
    have root : lift a ha (AdjoinRoot.root Q)=a := AdjoinRoot.lift_root (raw a ha)
    have one (v : (Polynomial F)) : lift a ha (j v)=base v := DFunLike.congr_fun (extends_base a ha) v
    simp only [root,one]
  intro original
  have at_r : ((lift r hr).comp j).IsIntegralElem (lift r hr u) := by
    rwa [extends_base r hr,eq r hr]
  have integral : j.IsIntegralElem u :=
    at_r.of_map (lift r hr).injective
  have at_s := integral.map (lift s hs)
  rwa [extends_base s hs,eq s hs] at at_s

/-- Lift the received ordinate along one primitive branch. Every conjugate
has a common arithmetic denominator and the same physical residue. -/
theorem common_numerators [IsAlgClosed E] [Algebra.IsAlgebraic F E] {P : Plane F}
    (ir : Irreducible P) (pos : 0<P.natDegree)
    (splits : (geometric (E:=E) P).Splits) (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧
      ∀ r∈(geometric (E:=E) P).roots, ∃ a : (Polynomial E),
        incl E a=base b*r ∧
        a.eval (algebraMap F E x)=algebraMap F E (b.eval x)*algebraMap F E t := by
  obtain ⟨r,hr,rden,rt⟩ := exists_regular_root (E:=E) ir pos splits x t hit
  obtain ⟨b,hb,m,hm⟩ := base_multiple x (denominator r) rden
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let pX : (Polynomial E) := Polynomial.X-C x'
  have pX_image : base (Polynomial.X-C x) = incl E pX := by
    simp [base,constants,pX,x']
  have x_nonzero : base (E:=E) (Polynomial.X-C x)≠0 :=
    (map_ne_zero_iff _ base_injective).mpr (X_sub_C_ne_zero _)
  have t_image : base (C t)=incl E (C t') := by simp [base,constants,t']
  have exact_root : pX ∣ numerator r-C t'*denominator r := by
    apply dvd_iff_isRoot.mpr
    change (numerator r-C t'*denominator r).eval x'=0
    rw [eval_sub,eval_mul,eval_C,rt]
    ring
  obtain ⟨c,hc⟩ := exact_root
  have b_image : base b=incl E (denominator r*m) := by
    change incl E (constants b)=_
    rw [hm]
  have b_slope : base b*(r-base (C t))/base (Polynomial.X-C x)=incl E (c*m) := by
    apply (div_eq_iff x_nonzero).mpr
    calc
      _ = incl E ((numerator r-C t'*denominator r)*m) := by
        rw [b_image,t_image]
        simp only [map_mul,map_sub]
        rw [← numerator_eq r]
        ring
      _ = _ := by rw [hc,pX_image]; simp only [map_mul]; ring
  have regular : (base (F:=F) (E:=E)).IsIntegralElem
      (base b*(r-base (C t))/base (Polynomial.X-C x)) := by
    rw [b_slope]
    exact polynomial_integral (c*m)
  refine ⟨b,hb,?_⟩
  intro s hs
  have h := adjoint_conjugates ir pos b x t hr hs regular
  obtain ⟨n,hn⟩ := integral_is_polynomial h
  let a := constants (E:=E) b*C t'+pX*n
  have eq : base b*(s-base (C t))=incl E n*base (Polynomial.X-C x) :=
    (div_eq_iff x_nonzero).mp hn.symm
  refine ⟨a,?_ ,?_⟩
  · unfold a
    simp only [map_add,map_mul]
    have b_incl : incl E (constants (E:=E) b)=base b := rfl
    rw [b_incl,← t_image,← pX_image]
    linear_combination -eq
  · simp [a,pX,x',t',eval_constants]

#print axioms common_numerators
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearConjugacy

-- merged module R6960RetainedLinearSpecialization
section Merged_R6960RetainedLinearSpecialization
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial
variable {F E : Type} [Field F] [Field E] [Algebra F E]
private def linearAt (B A : (Polynomial E)) : Plane E := C B*Polynomial.X-C A
private theorem map_linearAt (B A : (Polynomial E)) (r : Fn E) (ha : incl E A=incl E B*r) :
    (linearAt B A).map (incl E)=C (incl E B)*(Polynomial.X-C r) := by
  simp only [linearAt,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    ha,C_mul,mul_sub]
private theorem mapped_all (B : (Polynomial E)) (A : Fn E→(Polynomial E)) (s : Multiset (Fn E))
    (h : ∀ r∈s,incl E (A r)=incl E B*r) :
    ((s.map (fun r=>linearAt B (A r))).prod).map (incl E)=C ((incl E B)^s.card) *
      (s.map (fun r=>Polynomial.X-C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := h r (Multiset.mem_cons_self r s)
    have rest := ih (fun a ha=>(h a (Multiset.mem_cons_of_mem ha)))
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,map_linearAt B _ r hr,
      rest,Multiset.card_cons,pow_succ,C_mul]
    ring
private theorem specialized_all (B : (Polynomial E)) (A : Fn E→(Polynomial E)) (s : Multiset (Fn E)) (x t : E)
    (h : ∀ r∈s,(A r).eval x=B.eval x*t) :
    ((s.map (fun r=>linearAt B (A r))).prod).map (evalRingHom x)=
      C ((B.eval x)^s.card)*(Polynomial.X-C t)^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := h r (Multiset.mem_cons_self r s)
    have first : (linearAt B (A r)).map (evalRingHom x)=C (B.eval x)*(Polynomial.X-C t) := by
      simp only [linearAt,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
        Polynomial.map_X,coe_evalRingHom,hr,C_mul,mul_sub]
    have rest := ih (fun a ha=>h a (Multiset.mem_cons_of_mem ha))
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,first,rest,
      Multiset.card_cons,pow_succ,C_mul]
    ring
theorem pure_specialization [IsAlgClosed E] [Algebra.IsAlgebraic F E] {P : Plane F}
    (ir : Irreducible P) (pos : 0<P.natDegree) (splits : (geometric (E:=E) P).Splits)
    (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    P.map (evalRingHom x)=C (P.map (evalRingHom x)).leadingCoeff*(Polynomial.X-C t)^P.natDegree := by
  classical
  let G := geometric (E:=E) P
  let roots := G.roots
  let Q := P.map (constants (F:=F) (E:=E))
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let atX := evalRingHom x'
  let degree := P.natDegree
  have lifts : Q.map (incl E)=G := by
    simp [Q,G,geometric,base,Polynomial.map_map]
  have d : roots.card=degree := splits.natDegree_eq_card_roots.symm.trans (geometric_deg P)
  obtain ⟨b,hb,numerators⟩ := common_numerators (E:=E) ir pos splits x t hit
  let B := constants (E:=E) b
  let A (r : Fn E) : (Polynomial E) := if h : r∈roots then (numerators r h).choose else 0
  have den : B.eval x'≠0 := by rw [eval_constants]; exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hb
  have both (r : Fn E) (h : r∈roots) :
      incl E (A r)=incl E B*r ∧ (A r).eval x'=B.eval x'*t' := by
    simpa only [A,dite_eq_left h,eval_constants,x',t',B,base,RingHom.comp_apply] using
      (numerators r h).choose_spec
  let H := (roots.map (fun r=>linearAt B (A r))).prod
  have shape : H.map (incl E)=C ((incl E B)^degree)*(roots.map (fun r=>Polynomial.X-C r)).prod := by
    rw [mapped_all B A roots (fun r hr=>(both r hr).1),d]
  have fibre : H.map atX=C ((B.eval x')^degree)*(Polynomial.X-C t')^degree := by
    rw [specialized_all B A roots x' t' (fun r hr=>(both r hr).2),d]
  have lead : incl E Q.leadingCoeff=G.leadingCoeff := by
    rw [← lifts, leadingCoeff_map_of_injective (incl_injective E)]
  have packed : C (B^degree)*Q=C Q.leadingCoeff*H := by
    apply Polynomial.map_injective _ (incl_injective E)
    rw [Polynomial.map_mul,Polynomial.map_C,map_pow,lifts,Polynomial.map_mul,Polynomial.map_C,lead,shape]
    calc
      C ((incl E B)^degree)*G =
          C ((incl E B)^degree)*(C G.leadingCoeff*(roots.map (fun r=>Polynomial.X-C r)).prod) :=
        congrArg _ splits.eq_prod_roots
      _ = _ := by ring
  have mapped := congrArg (Polynomial.map atX) packed
  simp only [Polynomial.map_mul,Polynomial.map_C,atX,coe_evalRingHom,eval_pow] at mapped
  change C ((B.eval x')^degree)*(Q.map atX)=C (Q.leadingCoeff.eval x')*(H.map atX) at mapped
  rw [fibre] at mapped
  have qeq : Q.map atX=C (Q.leadingCoeff.eval x')*(Polynomial.X-C t')^degree := by
    apply mul_left_cancel₀ (a:=C ((B.eval x')^degree)) (C_ne_zero.mpr (pow_ne_zero _ den))
    calc
      _ = C (Q.leadingCoeff.eval x')*(C ((B.eval x')^degree)*(Polynomial.X-C t')^degree) := mapped
      _ = _ := by ring
  have lead_eq : (Q.map atX).leadingCoeff=Q.leadingCoeff.eval x' := by
    have monic : ((Polynomial.X-C t')^degree).Monic := (monic_X_sub_C t').pow _
    rw [qeq,leadingCoeff_mul,leadingCoeff_C,monic.leadingCoeff,mul_one]
  rw [← lead_eq] at qeq
  have recover : Q.map atX=(P.map (evalRingHom x)).map (algebraMap F E) := by
    apply Polynomial.ext
    intro i
    simp only [Q,atX,coeff_map,coe_evalRingHom,eval_constants,x']
  apply Polynomial.map_injective _ (algebraMap F E).injective
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,← leadingCoeff_map_of_injective (algebraMap F E).injective,← recover]
  exact qeq
#print axioms pure_specialization
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearSpecialization

-- merged module R6960RetainedLinearAssembly
section Merged_R6960RetainedLinearAssembly
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open RetainedCompression (Curve ordinate parameter height heightCap wordDegree MarkedFiber
  PureNodes atNode NonPureFactorPrice view view_y scalar)
open scoped Polynomial
abbrev Seed := Fn L
def toSeed : Ordinate →+* Plane Seed :=
  mapRingHom (mapRingHom (incl L))
theorem toSeed_injective : Function.Injective toSeed :=
  Polynomial.map_injective _ (Polynomial.map_injective _ (incl_injective L))
theorem toSeed_degree (P : Ordinate) : (toSeed P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ (incl_injective L)) P
private def seedScalar (b : (Polynomial L)) : Plane Seed := C (C (incl L b))
private theorem seedScalar_isUnit (b : (Polynomial L)) (hb : b≠0) : IsUnit (seedScalar b) :=
  isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (incl_injective L)).mpr hb)))
private theorem clear_seed (Q : Plane Seed) :
    ∃ (b : (Polynomial L)) (R : Ordinate), b≠0 ∧ toSeed R=seedScalar b*Q := by
  obtain ⟨b,R,nonzero,hr⟩ := RetainedCompression.clear_abscissa Q
  refine ⟨b,R.map Bivariate.swap.toRingHom,nonzero,?_⟩
  show (R.map Bivariate.swap.toRingHom).map (mapRingHom (incl L))=_
  rw [Polynomial.map_map]
  exact hr
private theorem lifted_scalar_product (P : Ordinate) (a b : (Polynomial L)) :
    toSeed (C (C (a*b))*P)=seedScalar a*seedScalar b*toSeed P := by
  rw [map_mul]
  simp only [toSeed,coe_mapRingHom,Polynomial.map_C,map_mul,seedScalar]
theorem toSeed_irreducible {P : Ordinate} (ir : Irreducible P) (pos : 0<P.natDegree) :
    Irreducible (toSeed P) := by
  have pn : toSeed P≠0 := (map_ne_zero_iff _ toSeed_injective).mpr ir.ne_zero
  have prime : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp ir
  refine ⟨fun u => ?_, fun A B split => ?_⟩
  · have d := natDegree_eq_zero_of_isUnit u
    rw [toSeed_degree] at d
    omega
  obtain ⟨a,U,an,ua⟩ := clear_seed A
  obtain ⟨b,V,bn,vb⟩ := clear_seed B
  have product : U*V=P*C (C (a*b)) := by
    apply toSeed_injective
    rw [mul_comm P, lifted_scalar_product,map_mul,ua,vb,split]
    ring
  have dvd : P∣U*V := ⟨_,product⟩
  have with_unit {c : (Polynomial L)} {H : Ordinate} {J : Plane Seed}
      (cn : c≠0) (h : toSeed H=seedScalar c*J) (dv : P∣H) : toSeed P∣J := by
    have image := map_dvd toSeed dv
    rw [h] at image
    exact (seedScalar_isUnit c cn).dvd_mul_left.mp image
  have other {J K : Plane Seed} (dv : toSeed P∣J) (eq : toSeed P=J*K) : IsUnit K := by
    obtain ⟨c,fac⟩ := dv
    have unit : (1 : Plane Seed)=c*K := by
      apply mul_left_cancel₀ pn
      rw [mul_one,← mul_assoc,← fac,← eq]
    exact isUnit_of_dvd_one ⟨c,unit.trans (mul_comm c K)⟩
  rcases prime.dvd_mul.mp dvd with h | h
  · exact Or.inr (other (with_unit an ua h) split)
  · exact Or.inl (other (with_unit bn vb h) (split.trans (mul_comm A B)))
def GeometricallyLinear (P : Ordinate) : Prop :=
  (geometric (E:=AlgebraicClosure Seed) (toSeed P)).Splits
private theorem node_map (P : Ordinate) (i : I) :
    (toSeed P).map (evalRingHom (incl L (C (algebraMap K L (node i)))))=
    (atNode P i).map (incl L) := by
  apply Polynomial.ext
  intro j
  simp only [toSeed,atNode,coe_mapRingHom,coeff_map,coe_evalRingHom]
  exact Polynomial.eval_map_apply (incl L) _
theorem pure_of_geometrically_linear (w : I→K) (P : Ordinate)
    (ir : Irreducible P) (pos : 0<P.natDegree) (linear : GeometricallyLinear P) :
    PureNodes w P := by
  intro i hit
  let x := incl L (C (algebraMap K L (node i)))
  let t := incl L (C (algebraMap K L (w i)))
  have equal : (toSeed P).map (evalRingHom x)=(atNode P i).map (incl L) := node_map P i
  have root : ((toSeed P).map (evalRingHom x)).eval t=0 := by
    rw [equal,eval_map_apply,hit,map_zero]
  have degree : 0<(toSeed P).natDegree := by rw [toSeed_degree]; exact pos
  have formula := pure_specialization (E:=AlgebraicClosure Seed)
    (toSeed_irreducible ir pos) degree linear x t root
  rw [equal,toSeed_degree] at formula
  apply Polynomial.map_injective _ (incl_injective L)
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,← leadingCoeff_map_of_injective (incl_injective L)]
  exact formula
def NonlinearFactorPrice : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
    Word 179818 wordDegree M.word F.scalar T→
    ∀ f : Curve (Polynomial L), Irreducible f →
      3≤f.degreeOf ordinate → f.degreeOf ordinate<48 → 0<f.degreeOf parameter →
      height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      ¬GeometricallyLinear (view f) →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤MarkedSheet.rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
        (f.degreeOf ordinate-1)*(f.degreeOf ordinate)
theorem nonpure_of_nonlinear (price : NonlinearFactorPrice) : NonPureFactorPrice := by
  intro u deleted M Γ F T sub W f ir lo hi sv cap nonpure marks
  apply price F T sub W f ir lo hi sv cap _ marks
  intro linear
  apply nonpure
  have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
  have pos : 0<(view f).natDegree := by rw [view_y]; omega
  exact pure_of_geometrically_linear M.word _ irr pos linear
theorem protocol_claim_of_nonlinear (gates : Low6960Allocation.Gates) (price : NonlinearFactorPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6961
      ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q :=
  Lower6960.protocol_claim_of_nonpure gates (nonpure_of_nonlinear price)
#print axioms toSeed_irreducible
#print axioms pure_of_geometrically_linear
#print axioms protocol_claim_of_nonlinear
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearAssembly

-- merged module R6960MonicChartFinite
section Merged_R6960MonicChartFinite
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Differential
theorem constant_evaluation_avoids {K : Type*} [Field K] [Infinite K]
    (f : (Polynomial (Polynomial K))) (primitive : f.IsPrimitive) (q : (Polynomial K)) (ir : Irreducible q) :
    ∃ c : K, ¬q∣f.eval (C c) := by
  let J : Ideal (Polynomial K) := Ideal.span {q}
  letI : J.IsPrime := (Ideal.span_singleton_prime ir.ne_zero).mpr ir.prime
  let ρ := Ideal.Quotient.mk J
  let embed : K→+*((Polynomial K)⧸J) := ρ.comp C
  by_contra! no
  have roots : (Set.range embed : Set ((Polynomial K)⧸J)) ⊆ {z | (f.map ρ).IsRoot z} := by
    rintro _ ⟨c,rfl⟩
    change (f.map ρ).eval (ρ (C c))=0
    rw [Polynomial.eval_map_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr (no c)
  have zero : f.map ρ=0 := eq_zero_of_infinite_isRoot (f.map ρ)
    ((Set.infinite_range_of_injective embed.injective).mono roots)
  apply ir.not_isUnit
  apply (isPrimitive_iff_isUnit_of_C_dvd.mp primitive) q
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro j
  have vanish := congrArg (fun P : (Polynomial ((Polynomial K)⧸J)) => P.coeff j) zero
  rw [coeff_map,coeff_zero] at vanish
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp vanish)
section Finite
variable {K F E : Type*} [Field K] [Infinite K] [Field F] [Field E]
    [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra F E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) F E] [Algebra.IsSeparable F E] [FiniteDimensional F E]
    [Differential (Polynomial K)] [Differential E] [DifferentialAlgebra (Polynomial K) E]
theorem clears_finite (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (primitive : f.IsPrimitive)
    (e2 : 2≤f.natDegree) (degree : f.natDegree=b.dim) (tame : (f.natDegree:F)≠0)
    (root : aeval b.gen f=0) (x : E) (integral : IsIntegral (Polynomial K) x) :
    IsIntegral (Polynomial K) (algebraMap (Polynomial K) E ((paddedRes f)^2)*x′) := by
  apply ChartIntegrality.integral_from_places F
  intro q ir
  obtain ⟨c,n⟩ := constant_evaluation_avoids f primitive q ir
  let u := f.eval (C c)
  have un : u≠0 := by
    intro h
    apply n
    change q∣u
    rw [h]
    exact dvd_zero q
  let k := 2*((f.natDegree-1)*(f.natDegree-2))
  refine ⟨u^k,fun h=>n (ir.prime.dvd_of_dvd_pow h),?_⟩
  rw [←mul_assoc,←map_mul]
  exact scaled_raw_square_clears b f (C c) un e2 degree tame root x integral
end Finite
section Actual
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y)
abbrev Scalar := RetainedLinear.Seed
theorem actual_finite {E : Type*} [Field E] [Algebra (RatFunc Scalar) E]
    [Algebra (Polynomial Scalar) E] [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential E] [DifferentialAlgebra (Polynomial Scalar) E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x : E) (int : IsIntegral (Polynomial Scalar) x) :
    IsIntegral (Polynomial Scalar)
      (algebraMap (Polynomial Scalar) E ((paddedRes (RetainedLinear.toSeed (view f)))^2)*x′) := by
  let P := RetainedLinear.toSeed (view f)
  have deg : P.natDegree=f.degreeOf ordinate := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have pos : 0<(view f).natDegree := by rw [view_y]; omega
  have pir : Irreducible P :=
    RetainedLinear.toSeed_irreducible ((MulEquiv.irreducible_iff view).mpr ir) pos
  have pd : P.natDegree≠0 := by omega
  have prim := pir.isPrimitive pd
  let ι := algebraMap (Polynomial Scalar) (RatFunc Scalar)
  let Q := P.map ι
  have irrQ : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rootQ : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rootQ
  have assoc := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd irrQ dvd
  have oq : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd assoc.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd irrQ.ne_zero)
  have dim : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) (RatFunc Scalar)) P).symm.trans
      (oq.trans b.natDegree_minpoly)
  let seed : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  haveI : CharP (RatFunc Scalar) K1.p :=
    charP_of_injective_ringHom ((RatFunc.C : Scalar→+*RatFunc Scalar).comp seed).injective K1.p
  have tame : (P.natDegree:RatFunc Scalar)≠0 := by
    intro zero
    have h := (CharP.cast_eq_zero_iff (RatFunc Scalar) K1.p P.natDegree).mp zero
    have lt : P.natDegree<K1.p := by rw [deg]; exact hi.trans (by decide)
    exact pd (Nat.eq_zero_of_dvd_of_lt h lt)
  exact clears_finite b P prim (by omega) dim tame root x int
end Actual
#print axioms clears_finite
#print axioms actual_finite
end
end Lower6960.MonicChart

end Merged_R6960MonicChartFinite

-- merged module R6960MonicChartInfinityClearing
section Merged_R6960MonicChartInfinityClearing

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 3600000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential

private def scaleBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (b : PowerBasis F E) (u : Fˣ) : PowerBasis F E where
  gen := algebraMap F E (u:F)*b.gen
  dim := b.dim
  basis := b.basis.unitsSMul (fun j=>u^j.val)
  basis_eq_pow j := by
    rw [Module.Basis.unitsSMul_apply,Units.smul_def,Units.val_pow_eq_pow_val,b.basis_eq_pow,
      Algebra.smul_def,map_pow,mul_pow]

section Infinity

variable {K E : Type*} [Field K] [Infinite K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Differential (Infinity K)] [Differential E] [DifferentialAlgebra (Infinity K) E]

local notation "S" => Infinity K
local notation "F" => RatFunc K

private theorem primitive_unit_infty (p : (Polynomial (Polynomial K))) (prim : p.IsPrimitive) :
    ∃ i, IsUnit ((p.map (inftyRingEval K)).coeff i) := by
  by_contra! no
  have dvd : C (Polynomial.X : (Polynomial K))∣p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro j
    apply X_dvd_iff.mpr
    by_contra nz
    exact no j (by rw [coeff_map]; exact inftyRingEval_isUnit _ nz)
  exact not_isUnit_X ((isPrimitive_iff_isUnit_of_C_dvd.mp prim) _ dvd)

/-- The weighted infinity chart controls derivatives by its own padded
resultant. Primitive part is taken before choosing the monic chart, and
its content factor is returned to the resultant. -/
theorem clears_homogeneous_infinity (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d : ℕ)
    (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (root : aeval b.gen f=0) (x : E) (hx : IsIntegral S x) :
    IsIntegral S (algebraMap S E ((inftyRingEval K (paddedRes (weightedInfinity f H d)))^2)*x′) := by
  classical
  letI : NormalizedGCDMonoid (Polynomial K) := Classical.choice inferInstance
  let e := f.natDegree
  let t := ((RatFunc.X : F)⁻¹)
  let a := t^d
  have an : a≠0 := pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero)
  let v := scaleBasis b (Units.mk0 a an)
  have vg : v.gen=algebraMap F E a*b.gen := rfl
  have vd : v.dim=b.dim := rfl
  let fI := weightedInfinity f H d
  let j := inftyRingEval K
  let r := fI.map j
  let p := fI.primPart.map j
  let c := j fI.content
  let ι := algebraMap S F
  have rdegree : r.natDegree=e := (natDegree_map_eq_of_injective inftyRingEval_injective _).trans
    (infinity_degree f H d)
  have pdegree : p.natDegree=e := by
    rw [natDegree_map_eq_of_injective inftyRingEval_injective,natDegree_primPart,infinity_degree]
  have rawSplit : r=C c*p := by
    have eq := congrArg (Polynomial.map j) fI.eq_C_content_mul_primPart
    simpa only [Polynomial.map_mul,Polynomial.map_C] using eq
  have cn : c≠0 := by
    intro zero
    rw [rawSplit,zero,C_0,zero_mul,natDegree_zero] at rdegree
    omega
  have mapped_r : r.map ι=fI.map (AtInfinity K) := by
    rw [Polynomial.map_map]
    rfl
  have rroot : aeval v.gen r=0 := by
    rw [← aeval_map_algebraMap F,mapped_r,infinity_field f H d weights,map_mul]
    have baseRoot : aeval b.gen (f.map (algebraMap (Polynomial K) F))=0 := by
      rw [aeval_map_algebraMap]
      exact root
    have newRoot : aeval v.gen ((f.map (algebraMap (Polynomial K) F)).scaleRoots a)=0 := by
      rw [vg]
      exact scaleRoots_eval₂_eq_zero (algebraMap F E) baseRoot
    rw [newRoot,mul_zero]
  have proot : aeval v.gen p=0 := by
    rw [rawSplit,map_mul,aeval_C] at rroot
    have injective : Function.Injective (algebraMap S E) := by
      rw [IsScalarTower.algebraMap_eq S F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective _ _)
    exact (mul_eq_zero.mp rroot).resolve_left ((map_ne_zero_iff _ injective).mpr cn)
  let emb : K→+*IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp (j.comp C)
  letI : Infinite (IsLocalRing.ResidueField S) := Infinite.of_injective emb emb.injective
  have unit : ∃ i, IsUnit (p.coeff i) := primitive_unit_infty _ fI.isPrimitive_primPart
  have bounded := raw_square_clears_local v p unit (pdegree.trans (dim.trans vd.symm))
    (pdegree.symm ▸ e2) proot x hx
  have mapped_result : j (paddedRes fI)=paddedRes r := by
    unfold paddedRes
    rw [←resultant_map_map,←derivative_map]
    have d := natDegree_map_eq_of_injective inftyRingEval_injective fI
    rw [←d]
  have content_result : paddedRes r=c^(e+(e-1))*paddedRes p := by
    unfold paddedRes
    rw [rdegree,rawSplit,derivative_C_mul,resultant_C_mul_left,resultant_C_mul_right,←mul_assoc,←pow_add]
    rw [show e-1+e=e+(e-1) by omega,←pdegree]
  rw [mapped_result,content_result,mul_pow,map_mul,mul_assoc]
  exact isIntegral_algebraMap.mul bounded

end Infinity

#print axioms clears_homogeneous_infinity
end
end Lower6960.MonicChart

end Merged_R6960MonicChartInfinityClearing

-- merged module R6960MonicChartCoboundary
section Merged_R6960MonicChartCoboundary
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3600000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential
open Lower6960.RetainedCompression (derivative_weighted_add_le)
theorem inverse_abscissa_derivative {E : Type*} [Field E] [Differential E]
    (x : E) (coordinate : x′=1) : (x⁻¹)′=-(x⁻¹)^2 := by
  have h := (Differential.deriv (R:=E)).leibniz_inv x
  rw [coordinate,smul_eq_mul,mul_one] at h
  exact h
private theorem derivative_power_zero {E : Type*} [Field E] [Differential E]
    (p : ℕ) [CharP E p] (x : E) : (x^p)′=0 := by
  rw [Differential.deriv.leibniz_pow,nsmul_eq_mul,CharP.cast_eq_zero,zero_mul]
section Inverse
variable {K E : Type*} [Field K] [Infinite K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Differential (Infinity K)] [Differential E] [DifferentialAlgebra (Infinity K) E]
local notation "S" => Infinity K
local notation "F" => RatFunc K
theorem clears_inverse_power (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d : ℕ)
    (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim) (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d)
    (nonzero : paddedRes f≠0) (root : aeval b.gen f=0) (x : E) (hx : IsIntegral S x) :
    IsIntegral S (algebraMap F E (((RatFunc.X : F)⁻¹)^
      (2*(resultantWidth f.natDegree H d-(paddedRes f).natDegree)))*x′) := by
  let r := resultantWidth f.natDegree H d-(paddedRes f).natDegree
  let t := inftyRingEval K (Polynomial.X : (Polynomial K))
  let u := inftyRingEval K (paddedRes f).reverse
  have co : ((paddedRes f).reverse).coeff 0≠0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr nonzero
  have unit : IsUnit u := inftyRingEval_isUnit _ co
  obtain ⟨w,hw⟩ := unit
  have hom := clears_homogeneous_infinity b f H d e2 dim weights root x hx
  rw [infinity_resultant f H d (by omega) tame weights resBound,
    reflected_local_factor _ _ resBound] at hom
  change IsIntegral S (algebraMap S E ((t^r*u)^2)*x′) at hom
  have cancel : (↑w⁻¹:S)^2*(t^r*u)^2=t^(2*r) := by
    have single : (↑w⁻¹:S)*(t^r*u)=t^r := by
      rw [←hw,mul_comm (↑w⁻¹:S),mul_assoc,Units.mul_inv,mul_one]
    rw [←mul_pow,single,←pow_mul,Nat.mul_comm]
  have mul := (isIntegral_algebraMap (x:=(↑w⁻¹:S)^2)).mul hom
  rw [←mul_assoc,←map_mul,cancel] at mul
  have loc : algebraMap S F t=(RatFunc.X : F)⁻¹ := mapped_X_infty
  rw [IsScalarTower.algebraMap_apply S F E,map_pow,loc] at mul
  exact mul
section Both
variable [Differential (Polynomial K)] [DifferentialAlgebra (Polynomial K) E]
theorem common_coboundary_zero_generic (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d p : ℕ)
    [CharP E p] (primitive : f.IsPrimitive) (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim)
    (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d)
    (widthRoom : 2*resultantWidth f.natDegree H d<p)
    (nonzero : paddedRes f≠0) (root : aeval b.gen f=0)
    (x y z : E) (fx : IsIntegral (Polynomial K) x) (iy : IsIntegral S y)
    (overlap : y=(algebraMap F E RatFunc.X)^p*x+z^p) :
    x′=0 := by
  let r := resultantWidth f.natDegree H d-(paddedRes f).natDegree
  let Xval := algebraMap F E (RatFunc.X : F)
  have xn : Xval≠0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr RatFunc.X_ne_zero
  have inv := clears_inverse_power b f H d e2 dim tame weights resBound nonzero root y iy
  have dv : y′=Xval^p*x′ := by
    rw [overlap,map_add,Differential.deriv.leibniz,derivative_power_zero p,
      derivative_power_zero p,smul_eq_mul,smul_eq_mul,mul_zero,add_zero,add_zero]
  rw [dv] at inv
  have le : 2*r≤p := by dsimp only [r]; omega
  have cancel : (Xval⁻¹)^(2*r)*Xval^p=Xval^(p-2*r) := by
    have e : p=2*r+(p-2*r) := (Nat.add_sub_of_le le).symm
    calc
      _ = (Xval⁻¹)^(2*r)*(Xval^(2*r)*Xval^(p-2*r)) := by
        rw [←pow_add,←e]
      _ = _ := by rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ xn,one_pow,one_mul]
  have hi : IsIntegral S (Xval^(p-2*r)*x′) := by
    rw [←cancel,mul_assoc]
    change IsIntegral S (((algebraMap F E (RatFunc.X : F))⁻¹)^(2*r)*(Xval^p*x′))
    rw [←map_inv₀,←map_pow]
    exact inv
  have fit : 2*(paddedRes f).natDegree<p-2*r := by dsimp only [r]; omega
  have tame' : (f.natDegree:F)≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr tame
  exact DifferentialPoles.pole_budget (paddedRes f) nonzero (p-2*r) fit (x′)
    (clears_finite b f primitive e2 dim tame' root x fx) hi
end Both
end Inverse
#print axioms clears_inverse_power
#print axioms common_coboundary_zero_generic
end
end Lower6960.MonicChart

end Merged_R6960MonicChartCoboundary

-- merged module R6960MonicChartActual
section Merged_R6960MonicChartActual

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y height heightCap wordDegree abscissa_coeff_height)
open scoped Polynomial Differential
open Lower6960.RetainedCompression (derivative_weighted_add_le)

private theorem width_at_cutoff (e d : ℕ) (pos : 0<e) :
    resultantWidth e (heightCap e d) d=(3*e-1)*(e-1)*d := by
  have mul : d*e≤heightCap e d := by
    unfold heightCap
    rw [mul_comm d e]
    exact Nat.mul_le_mul_right d (by omega)
  have eq := resultantWidth_eq (e:=e) (d:=d) pos mul
  have identity : (2*e-1)*heightCap e d=d*e^2+(3*e-1)*(e-1)*d := by
    obtain ⟨k,h⟩ := Nat.exists_eq_add_of_le (show 1≤e from pos)
    unfold heightCap
    rw [h,show 2*(1+k)-1=2*k+1 by omega,show 3*(1+k)-1=3*k+2 by omega,
      show 1+k-1=k by omega]
    ring
  omega

/-- For the actual bounded projected factor, the overlap of the finite
and infinity chart coefficients has zero derivative. The only overlap
input is their Frobenius relation in the root field. -/
theorem actual_coboundary_zero {E : Type*} [Field E] [DecidableEq (RatFunc Scalar)]
    [Algebra (RatFunc Scalar) E] [Algebra (Polynomial Scalar) E]
    [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential (Infinity Scalar)] [Differential E]
    [DifferentialAlgebra (Polynomial Scalar) E] [DifferentialAlgebra (Infinity Scalar) E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap (RatFunc Scalar) E RatFunc.X)^K1.p*x+z^K1.p) :
    x′=0 := by
  let seed : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  letI : CharP Scalar K1.p := charP_of_injective_ringHom seed.injective K1.p
  let inE : Scalar→+*E := (algebraMap (RatFunc Scalar) E).comp RatFunc.C
  letI : CharP E K1.p := charP_of_injective_ringHom inE.injective K1.p
  let P := RetainedLinear.toSeed (view f)
  let e := f.degreeOf ordinate
  let H := heightCap e wordDegree
  have deg : P.natDegree=e := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have e2 : 2≤P.natDegree := by omega
  have ep : 0<P.natDegree := by omega
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have tame : (P.natDegree:Scalar)≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff Scalar K1.p P.natDegree).mp zero
    exact ep.ne' (Nat.eq_zero_of_dvd_of_lt dvd (deg.symm ▸ hi.trans (by decide)))
  have coefficient (j : ℕ) : (P.coeff j).natDegree=((view f).coeff j).natDegree := by
    unfold P RetainedLinear.toSeed
    simp only [coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
  have weights (j : ℕ) (jle : j≤P.natDegree) :
      (P.coeff j).natDegree+wordDegree*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add,mul_comm wordDegree]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f wordDegree j zero).trans bounded
  have Hfit : wordDegree*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H wordDegree := by
    have h := Lower6960.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H wordDegree ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=wordDegree) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H wordDegree<K1.p := by
    rw [deg,width_at_cutoff e wordDegree (by omega)]
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right wordDegree
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 (by omega : e≤47)) 1)
       (Nat.sub_le_sub_right (by omega : e≤47) 1)))).trans_lt (by decide +kernel)
  have tameA : (P.natDegree:(Polynomial Scalar))≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (Polynomial.C : Scalar→+*(Polynomial Scalar)) Polynomial.C_injective).mpr tame
  have dp := derivative_degree P ep tameA
  have der : P.derivative≠0 := by intro zero; rw [zero,natDegree_zero] at dp; omega
  have resNZ : paddedRes P≠0 := Polynomial.resultant_derivative_ne_zero_of_irreducible P pir der
  have prim := pir.isPrimitive ep.ne'
  let ι := algebraMap (Polynomial Scalar) (RatFunc Scalar)
  let Q := P.map ι
  have iq : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rq
  have associated := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd associated.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  have dimension : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) (RatFunc Scalar)) P).symm.trans
      (size.trans b.natDegree_minpoly)
  exact common_coboundary_zero_generic b P H wordDegree K1.p prim e2 dimension tame weights
    resBound room resNZ root x y z fx iy overlap

#print axioms actual_coboundary_zero
end
end Lower6960.MonicChart

end Merged_R6960MonicChartActual

end Merged6967_R6960MonicChartActual

section Merged6967_R6966ProofFarSourceArithmetic
set_option Elab.async false



set_option Elab.async false

namespace Research6966.FarSourceArithmetic
open Finset
open K1_14 (Shape slots)
open K1_14_4 (shapeSum_swap)
open Lower6960.HelperSource (phaseLayer compressedPhase column_eq gain_eq_compressed surplus WidthGuard)
open HelperWindowPrefix (volume volume_eq_shapeSum)
open HelperWindowGrouping (sumCount sumCount_eq)
set_option maxHeartbeats 1000000

abbrev agreement : ℕ := 179759
abbrev firstHeight : ℕ := 2523
abbrev heightCap : ℕ := 33697

def fastLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  let j := (i+δ)*d
  let used := (i+δ)*c
  let step := 131071-h
  if j≤s.J ∧ used+j≤s.B then
    slots s.U ((i+δ)*v)*
      volume (s.m*A-2*h*(r+i)-(step-1)*j) (s.B-used-j) (s.J-j) step
  else 0

theorem fastLayer_eq (s : Shape) (A h r d c v δ i : ℕ) (narrow : s.J<131071-h) :
    fastLayer s A h r d c v δ i = phaseLayer s A h r d c v δ i := by
  unfold fastLayer phaseLayer
  dsimp only
  rw [P1_7_1_3.evaluate_eq]
  simp_rw [column_eq]
  let j := (i+δ)*d
  let used := (i+δ)*c
  let step := 131071-h
  let stop := s.m*A-2*h*(r+i)-(step-1)*j
  let B := s.B-used-j
  let J := s.J-j
  let box : Shape := ⟨s.m,B,J,s.U⟩
  change (if j≤s.J ∧ used+j≤s.B then slots s.U ((i+δ)*v)*volume stop B J step else 0) =
    slots s.U ((i+δ)*v)*
      ∑ a ∈ range (s.J+1-j), ∑ q ∈ Ico (j+a) (s.B+1-used),
        (s.m*A+(j+a)-q*step-2*h*(r+i))
  by_cases room : j≤s.J ∧ used+j≤s.B
  · rw [ite_eq_left room]
    have nw : box.J<step := (Nat.sub_le _ _).trans_lt narrow
    rw [show volume stop B J step = _ from volume_eq_shapeSum box stop step nw,
      ← shapeSum_swap box, show s.J+1-j=J+1 by dsimp only [J];omega]
    congr 1
    apply sum_congr rfl
    intro a _
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    have lengths : s.B+1-used-(j+a)=B+1-a := by dsimp only [B];omega
    rw [lengths]
    apply sum_congr rfl
    intro t _
    have pos : 1≤step := (Nat.zero_le _).trans_lt narrow
    have fixed : (step-1)*j+j=j*step := by
      have eq := congrArg (·*j) (Nat.sub_add_cancel pos : step-1+1=step)
      rwa [Nat.add_mul,Nat.one_mul,Nat.mul_comm step j] at eq
    have pays : a≤(a+t)*step := by
      exact (Nat.le_add_right a t).trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a+t) pos)
    have product : (j+a+t)*step=j*step+(a+t)*step := by
      rw [Nat.add_assoc,Nat.add_mul]
    change stop+a-step*(a+t) = s.m*A+(j+a)-(j+a+t)*step-2*h*(r+i)
    rw [Nat.mul_comm step (a+t), product]
    dsimp only [stop]
    omega
  · rw [ite_eq_right room]
    symm
    apply mul_eq_zero.mpr
    right
    by_cases enough : j≤s.J
    · have large : s.B+1-used≤j := by omega
      apply sum_eq_zero
      intro a _
      rw [sum_Ico_eq_sum_range, show s.B+1-used-(j+a)=0 by omega, range_zero, sum_empty]
    · rw [show s.J+1-j=0 by omega,range_zero,sum_empty]

def fastPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  sumCount (fastLayer s A h r d c v δ) (s.J/d+1)

theorem fastPhase_eq (s : Shape) (A h r d c v δ : ℕ) (narrow : s.J<131071-h) :
    fastPhase s A h r d c v δ = compressedPhase s A h r d c v δ := by
  unfold fastPhase compressedPhase
  rw [sumCount_eq,P1_7_1_3.evaluate_eq]
  exact sum_congr rfl (fun i _=>fastLayer_eq s A h r d c v δ i narrow)

structure Request where
  bank : P1_7.Bank
  reserve : ℕ
  slope : ℕ
  excess : ℕ
  seed : ℕ

def value (q : Request) (h : ℕ) : ℤ :=
  (fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 0-
    fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 1 : ℕ) -
      (P1_7.debit h q.bank : ℤ)

theorem value_eq (q : Request) (h : ℕ) (pos : 0<q.slope) (narrow : q.bank.shape.J<131071-h) :
    value q h=surplus q.bank agreement h q.reserve q.slope q.excess q.seed := by
  unfold value surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ pos,fastPhase_eq _ _ _ _ _ _ _ _ narrow,fastPhase_eq _ _ _ _ _ _ _ _ narrow]

structure Checked (q : Request) : Prop where
  rank : P3_7_1.BankOK q.bank
  width : WidthGuard q.bank agreement firstHeight q.reserve
  reserve_fit : 2*q.reserve≤q.bank.shape.B
  positive_slope : 0<q.slope
  narrow : q.bank.shape.J<131071-(firstHeight+1)
  positive : 0<value q firstHeight
  increases : value q firstHeight≤value q (firstHeight+1)

theorem Checked.window {q : Request} (cert : Checked q) {h : ℕ} (lo : firstHeight≤h) (hi : h≤heightCap) :
    WidthGuard q.bank agreement h q.reserve :=
  Lower6960.HelperSource.width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width

theorem Checked.gain {q : Request} (cert : Checked q) {h : ℕ} (lo : firstHeight≤h) (hi : h≤heightCap) :
    P1_7.debit h q.bank<Lower6960.HelperSource.gain q.bank.shape agreement h q.reserve q.slope q.excess q.seed := by
  have earlier := cert.narrow.trans_le (Nat.sub_le_sub_left (Nat.le_succ firstHeight) _)
  have pos := cert.positive
  have next := cert.increases
  rw [value_eq _ _ cert.positive_slope earlier] at pos
  rw [value_eq _ _ cert.positive_slope earlier,value_eq _ _ cert.positive_slope cert.narrow] at next
  exact Lower6960.HelperSource.surplus_positive _ _ _ _ _ _ _ _ lo (hi.trans (by decide)) pos next

#print axioms fastPhase_eq
#print axioms Checked.gain
end Research6966.FarSourceArithmetic

end Merged6967_R6966ProofFarSourceArithmetic

section Merged6967_R6966ProofHelperKnownPrime
set_option Elab.async false




set_option Elab.async false

namespace Research6966.HelperKnownPrime
open Polynomial Finset
open K1_14 (Jet L triangle shapeSum)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_mul seedDegree_mul)
open Lower6960.PrefixRows (Common)
open HelperAvoidance (debitAt triSlots)
noncomputable section

private theorem slope_le {f:Jet} (nz:f≠0) : f.natDegree≤jetDegree f := by
  have coef : (f.coeff f.natDegree).coeff f.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have bound:=(K1_14_2_2_2_1.jetDegree_le f _).1 le_rfl _ _ coef
  omega

/-- Given a known common prime, pay the buffered source for the product
with any other coprime common prime. Both factors spend their pole weight. -/
theorem not_coprime {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (bank:P1_7.Bank) {G H:Jet}
    (g:Common (evaluated Crt word bank.shape (N-1)) G)
    (other:Common (evaluated Crt word bank.shape (N-1)) H) (cop:IsRelPrime G H)
    (M:HelperPhysicalModel.Model Crt G) {a L0 u Lother:ℕ} (secondWeight:Lother≤131071-h-1)
    (degree:a≤jetDegree G) (wt:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (width:u≤seedDegree G) (seedChar:bank.shape.U<K1.p) (small:bank.shape.B<K1.p)
    (nz:0<N) (wide:bank.shape.B*(131071-h)≤N) (node:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank+∑ W∈range N,
      debitAt bank.shape h N W (a+1) 2 (L0+Lother) (triSlots bank.shape.U (u+1)) <
      triangle bank.shape.U*shapeSum bank.shape (fun q j=>N+j-q*(131071-h))) : False := by
  classical
  obtain ⟨T⟩:=HelperPhysicalModel.exists_model Crt other.1 other.2.1
  have slope:=slope_le other.1.ne_zero
  have sj:1≤jetDegree H:=other.2.1.trans_le slope
  have us:1≤seedDegree H:=by
    obtain ⟨j,i,seed⟩:=other.2.2.1
    have b:=(K1_14_2_2_2_1.seedDegree_le H _).1 le_rfl j i
    omega
  let w:=131071-h
  have wp:0<w:=by dsimp [w];omega
  have rhs:=HelperWeightCap.weight_lower T other.1.ne_zero w wp
  have wh : w-1≤RawPhysicalDegree.weight w (w-1) T.raw := by
    have prod:(w-1)*jetDegree H+jetDegree H=w*jetDegree H := by
      rw [←Nat.succ_mul,show (w-1).succ=w by omega]
    have ge:=Nat.mul_le_mul_left (w-1) sj
    omega
  have dg : a+1≤jetDegree (G*H) := by rw [jetDegree_mul g.1.ne_zero other.1.ne_zero];omega
  have ds : 2≤(G*H).natDegree := by rw [natDegree_mul g.1.ne_zero other.1.ne_zero];have := g.2.1;have := other.2.1;omega
  have du : u+1≤seedDegree (G*H) := by rw [seedDegree_mul g.1.ne_zero other.1.ne_zero];omega
  have dw : L0+Lother≤RawPhysicalDegree.weight w (w-1) (M.mul T).raw := by
    change _≤RawPhysicalDegree.weight w (w-1) (M.raw*T.raw)
    rw [RawPhysicalDegree.weight_product _ _ M.primitive.ne_zero T.primitive.ne_zero]
    exact Nat.add_le_add wt (secondWeight.trans wh)
  apply HelperAvoidance.triangle_contradiction hp hl Crt word bank (M.mul T)
    (mul_ne_zero g.1.ne_zero other.1.ne_zero) dg ds dw du small nz wide node pole positive
  intro W hw P inside
  apply Lower6960.HelperPrefix.product_power cop
  · apply RectangularHelperShift.common_power hp hw Crt word bank.shape _ g.1 g.2.1 g.2.2.1 seedChar _ P inside
    rw [RectangularHelperShift.all_axes]
    exact g.2.2.2
  · apply RectangularHelperShift.common_power hp hw Crt word bank.shape _ other.1 other.2.1 other.2.2.1 seedChar _ P inside
    rw [RectangularHelperShift.all_axes]
    exact other.2.2.2

theorem unique_from_known {V:Submodule K1_14.FX Jet} {G:Jet} (g:Common V G)
    (pinned:∀ H,Common V H → IsRelPrime G H → False) :
    ∀ N H, Common V N → Common V H → IsRelPrime N H → False := by
  intro N H n h cop
  by_cases dv:G∣N
  · have assoc:=g.1.associated_of_dvd n.1 dv
    exact pinned H h (fun d hd dh => cop (hd.trans assoc.dvd) dh)
  · exact pinned N n (g.1.isRelPrime_iff_not_dvd.mpr dv)

#print axioms not_coprime
#print axioms unique_from_known
end
end Research6966.HelperKnownPrime

end Merged6967_R6966ProofHelperKnownPrime

section Merged6967_R6966ProofHelperRescueSource
set_option Elab.async false





set_option Elab.async false

namespace Research6966.HelperRescueSource
open Finset Polynomial
open K1_14 (Shape Jet L shapeSum triangle)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open HelperAvoidance (debitAt triSlots)
open HelperWindowIntervals (cutoff bound slotLimit triangle_tail)
open HelperWindowPrefix (volume)
open Lower6960.Rescue6966Source (bank reserve jetCap seedCap)
open scoped Polynomial
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

abbrev agreement : ℕ := 179759
abbrev firstHeight : ℕ := 2317
abbrev lastHeight : ℕ := 2522

structure Request where
  bank : P1_7.Bank
  reserve : ℕ
  degree : ℕ
  lower : ℕ
  weight : ℕ

def lowerFromUpper (u : ℕ) : ℕ :=
  if u ≤ 1 then 1 else if u ≤ 3 then 2 else if u ≤ 8 then 4
  else if u ≤ 15 then 9 else if u ≤ 25 then 16 else if u ≤ 40 then 26
  else if u ≤ 50 then 41 else if u ≤ 70 then 51 else 71

def sourceLower (r : Fin 54) : ℕ := lowerFromUpper (seedCap r)

def sourceWeight (r : Fin 54) : ℕ :=
  if jetCap r = 2 then (QuadraticBudget.band (seedCap r)).2
  else jetCap r*(131071-lastHeight)-1

def request (r : Fin 54) (i : Fin 17) : Request :=
  ⟨bank r i,reserve r i,jetCap r,sourceLower r,sourceWeight r⟩

def Request.top (q : Request) (h : ℕ) : ℕ := cutoff q.bank.shape agreement h q.reserve

def Positive (q : Request) (lo hi : ℕ) : Prop :=
  let S := q.bank.shape
  let width := triangle S.U
  width*q.bank.nodeRows+hi*(2*(S.U+1))*q.bank.poleMoment+
      bound S agreement q.reserve lo hi q.degree 1 q.weight (slotLimit S S.U q.lower)
        (triSlots S.U q.lower) <
    width*volume (q.top hi) S.B S.J (131071-lo)

instance (q : Request) (lo hi : ℕ) : Decidable (Positive q lo hi) := by
  unfold Positive
  infer_instance

def Cover (q : Request) (lo : ℕ) : List ℕ → Prop
  | [] => lo = lastHeight+1
  | hi::next => lo ≤ hi ∧ hi ≤ lastHeight ∧ Positive q lo hi ∧ Cover q (hi+1) next

private theorem cover_height {q : Request} {ends : List ℕ} {lo h : ℕ}
    (c : Cover q lo ends) (hl : lo ≤ h) (hh : h ≤ lastHeight) :
    ∃ bot top, bot ≤ h ∧ h ≤ top ∧ top ≤ lastHeight ∧ Positive q bot top := by
  induction ends generalizing lo with
  | nil =>
    change lo=lastHeight+1 at c
    omega
  | cons top ends ih =>
    obtain ⟨_,htop,cert,more⟩ := c
    by_cases hb : h ≤ top
    · exact ⟨lo,top,hl,hb,htop,cert⟩
    · exact ih more (by omega)

structure Checked (q : Request) : Prop where
  nodes : P1_7_1.nodeRows q.bank.shape = q.bank.nodeRows
  pole : P1_7_1.groupedPoleMoment q.bank.shape.B q.bank.shape.J ≤ q.bank.poleMoment
  narrow : q.bank.shape.J < 131071-lastHeight
  room : q.bank.shape.B*(131071-firstHeight)+2*firstHeight*q.reserve < q.bank.shape.m*agreement
  reserve_fit : 2*q.reserve ≤ q.bank.shape.B
  intervals : ∃ ends : List ℕ, Cover q firstHeight ends

theorem node_check (b : P1_7.Bank) (hm : 2*b.shape.J ≤ b.shape.m)
    (hB : b.shape.m+b.shape.J ≤ b.shape.B+1)
    (check : 262144*P1_7_1_2.sixPerNode (b.shape.m-2*b.shape.J) b.shape.J = 6*b.nodeRows) :
    P1_7_1.nodeRows b.shape = b.nodeRows := by
  have exactRows := P1_7_1_2.six_nodeRows b.shape hm hB
  rw [check] at exactRows
  omega

theorem Checked.width {q : Request} (cert : Checked q) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    q.bank.shape.B*(131071-h) < q.top h := by
  have lo' : 2317 ≤ h := lo
  have hi' : h ≤ 2522 := hi
  have delta : 131071-firstHeight = (131071-h)+(h-firstHeight) := by
    change 128754=(131071-h)+(h-2317)
    omega
  have res : 2*h*q.reserve = 2*firstHeight*q.reserve+(h-firstHeight)*(2*q.reserve) := by
    conv_lhs => rw [show h = firstHeight+(h-firstHeight) by omega]
    ring
  have more := Nat.mul_le_mul_left (h-firstHeight) cert.reserve_fit
  have atStart := cert.room
  rw [delta,Nat.mul_add] at atStart
  rw [Nat.mul_comm (h-firstHeight) q.bank.shape.B] at more
  change q.bank.shape.B*(131071-h) < q.bank.shape.m*agreement-2*h*q.reserve
  rw [res]
  omega

theorem Checked.debit_positive {q : Request} (cert : Checked q) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    P1_7.debit h q.bank+
        (∑ W ∈ range (q.top h), debitAt q.bank.shape h (q.top h) W q.degree 1 q.weight
          (triSlots q.bank.shape.U q.lower)) <
      triangle q.bank.shape.U*shapeSum q.bank.shape (fun t j => q.top h+j-t*(131071-h)) := by
  obtain ⟨ends,c⟩ := cert.intervals
  obtain ⟨bot,top,hb,ht,htop,num⟩ := cover_height c lo hi
  have narrow := cert.narrow.trans_le (Nat.sub_le_sub_left htop 131071)
  have hp : 0 < h := (show 0 < firstHeight by decide).trans_le lo
  let S := q.bank.shape
  have result := HelperWindowIntervals.positive S agreement q.reserve bot top h q.degree 1 q.weight
    (slotLimit S S.U q.lower) (triangle S.U) (2*(S.U+1)) q.bank.nodeRows q.bank.poleMoment
    (triSlots S.U q.lower) hp hb ht narrow (triangle_tail S q.degree S.U q.lower) num
  simpa only [P1_7.debit,Request.top,S,Nat.mul_left_comm h 2,Nat.mul_assoc] using result

theorem avoiding_rows (r : Fin 54) (checked : ∀ i, Checked (request r i))
    {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G) (slope : 0 < G.natDegree)
    (seeded : UsesSeed G) (degree : jetCap r ≤ jetDegree G) (seed : sourceLower r ≤ seedDegree G)
    (weight : sourceWeight r ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw) :
    ∀ i, ∃ Q ∈ evaluated Crt word (bank r i).shape (Lower6960.Rescue6966Source.cutoff h r i), ¬G∣Q := by
  intro i
  let q := request r i
  have cert : Checked q := checked i
  obtain ⟨_,_,charB,charU,_⟩ := Lower6960.Rescue6966Source.shape_guards r i
  have hp : 0<h := (show 0 < firstHeight by decide).trans_le lo
  have hl : h≤131070 := hi.trans (by decide)
  have wide := cert.width lo hi
  have pos : 0 < q.top h := (Nat.zero_le _).trans_lt wide
  exact HelperAvoidance.triangle_avoiding hp hl Crt word q.bank phys irr slope seeded charU
    degree slope weight seed charB pos wide.le cert.nodes cert.pole (cert.debit_positive lo hi)

/-- The ordinary physical weight lower bound supplies every degree-three
through degree-seven rescue cutoff from the actual common factor. -/
theorem high_degree_weight (r : Fin 54) {h : ℕ} (hi : h ≤ lastHeight) (hd : 3 ≤ jetCap r)
    {D : PoleData h} {Crt : CRTLift D} {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (nz : G ≠ 0) (slope : G.natDegree = 1) (degree : jetCap r ≤ jetDegree G) :
    sourceWeight r ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw := by
  have present := HelperWeightCap.weight_lower phys nz (131071-h) (by have h' : h ≤ 2522 := hi; omega)
  rw [slope] at present
  have fit := Nat.mul_le_mul (Nat.sub_le_sub_left hi 131071) degree
  rw [sourceWeight,ite_eq_right (by omega),Nat.mul_comm (jetCap r)]
  omega

/-- Every certified source row is passed to the actual 17-stage rescue of
the marked P1 family. -/
theorem prepare (r : Fin 54) (checked : ∀ i, Checked (request r i))
    {u deleted} {M : Lower6960.Rescue6966.Model u deleted} {Γ} (F : Lower6960.Rescue6966.Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : firstHeight ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ lastHeight)
    (noPole : ∀ j i,(D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G) (slope : 0 < G.natDegree)
    (seeded : UsesSeed G) (caps : RowCaps G (Lower6960.Rescue6966.primeShape r))
    (degree : jetCap r ≤ jetDegree G) (seed : sourceLower r ≤ seedDegree G)
    (weight : sourceWeight r ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ R : Lower6960.Rescue6966.Run F Crt G, R.rect = r :=
  Lower6960.Rescue6966.prepare_from_rows F Crt hi noPole residues r irr caps
    (avoiding_rows r checked lo hi Crt (Lower6960.Rescue6966.word M) phys irr slope seeded degree seed weight)

#print axioms avoiding_rows
#print axioms high_degree_weight
#print axioms prepare
end Research6966.HelperRescueSource

end Merged6967_R6966ProofHelperRescueSource

section Merged6967_R6966ProofHelperWindowCertificate
set_option Elab.async false


set_option Elab.async false

namespace Research6966.HelperWindowCertificate
open Finset
open K1_14 (Shape shapeSum triangle)
open HelperAvoidance (debitAt rectSlots triSlots)
open HelperWindowIntervals (cutoff bound slotLimit triangle_tail rectangle_tail box axis)
open HelperWindowPrefix (volume)
set_option maxHeartbeats 850000

structure Witness where
  degree : ℕ
  rect : Bool
  lower : ℕ
  reserve : ℕ
  m : ℕ
  B : ℕ
  J : ℕ
  v : ℕ
  nodes : ℕ
  pole : ℕ

def agreement : ℕ := 179759
def firstHeight : ℕ := 2317
def lastHeight : ℕ := 2522
def seedCap : ℕ := 443000

def Witness.shape (b : Witness) : Shape :=
  ⟨b.m,b.B,b.J,if b.rect then seedCap else b.v⟩

def Witness.bank (b : Witness) : P1_7.Bank := ⟨b.shape,b.nodes,b.pole⟩

def Witness.weight (b : Witness) : ℕ := b.degree*(131071-lastHeight)-1

def Witness.width (b : Witness) : ℕ :=
  if b.rect then KoalaRect.area (box seedCap b.v) else triangle b.v

def Witness.rate (b : Witness) : ℕ :=
  if b.rect then box seedCap b.v 0+box seedCap b.v 1+2 else 2*(b.v+1)

def Witness.slots (b : Witness) (k : ℕ) : ℕ :=
  if b.rect then rectSlots (box seedCap b.v) (axis b.lower) k else triSlots b.v b.lower k

def Witness.top (b : Witness) (h : ℕ) : ℕ := cutoff b.shape agreement h b.reserve

def Witness.loop (b : Witness) (lo hi : ℕ) : ℕ :=
  bound b.shape agreement b.reserve lo hi b.degree 1 b.weight
    (slotLimit b.shape b.v b.lower) b.slots

def Positive (b : Witness) (lo hi : ℕ) : Prop :=
  b.width*b.nodes+hi*b.rate*b.pole+b.loop lo hi <
    b.width*volume (b.top hi) b.B b.J (131071-lo)

instance (b : Witness) (lo hi : ℕ) : Decidable (Positive b lo hi) := by
  unfold Positive
  infer_instance

def Cover (b : Witness) (lo : ℕ) : List ℕ → Prop
  | [] => lo = lastHeight+1
  | hi :: rest => lo ≤ hi ∧ hi ≤ lastHeight ∧ Positive b lo hi ∧ Cover b (hi+1) rest

theorem cover_height {b : Witness} {endpoints : List ℕ} {lo h : ℕ}
    (cover : Cover b lo endpoints) (low : lo ≤ h) (high : h ≤ lastHeight) :
    ∃ lo hi, lo ≤ h ∧ h ≤ hi ∧ hi ≤ lastHeight ∧ Positive b lo hi := by
  induction endpoints generalizing lo with
  | nil =>
    change lo=lastHeight+1 at cover
    omega
  | cons hi ends ih =>
    obtain ⟨_, hh, pos, tail⟩ := cover
    by_cases first : h ≤ hi
    · exact ⟨lo, hi, low, first, hh, pos⟩
    · exact ih tail (by omega)

theorem node_check (b : Witness) (hm : 2*b.J ≤ b.m) (hb : b.m+b.J ≤ b.B+1)
    (h : 262144*P1_7_1_2.sixPerNode (b.m-2*b.J) b.J = 6*b.nodes) :
    P1_7_1.nodeRows b.shape = b.nodes := by
  have eq := P1_7_1_2.six_nodeRows b.shape hm hb
  change 6*P1_7_1.nodeRows b.shape = 262144*P1_7_1_2.sixPerNode (b.m-2*b.J) b.J at eq
  rw [h] at eq
  omega

theorem weight_room (b : Witness) {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight)
    (hs : 2*b.reserve ≤ b.B) (hw : b.B*(131071-firstHeight) ≤ b.top firstHeight) :
    b.B*(131071-h) ≤ b.top h := by
  have delta : 131071-firstHeight = (131071-h)+(h-firstHeight) := by
    have last : lastHeight ≤ 131071 := by decide
    omega
  have res : 2*h*b.reserve = 2*firstHeight*b.reserve+(h-firstHeight)*(2*b.reserve) := by
    conv_lhs => rw [show h = firstHeight+(h-firstHeight) by omega]
    ring
  have more := Nat.mul_le_mul_left (h-firstHeight) hs
  have pre : b.B*(131071-firstHeight)+2*firstHeight*b.reserve ≤ b.m*agreement := by
    change b.B*(131071-firstHeight) ≤ b.m*agreement-2*firstHeight*b.reserve at hw
    by_cases nz : b.B*(131071-firstHeight) = 0
    · have bp : 0 < 131071-firstHeight := by decide
      have bz : b.B = 0 := (Nat.mul_eq_zero.mp nz).resolve_right bp.ne'
      have : b.reserve=0 := by omega
      rw [this, Nat.mul_zero, Nat.add_zero, nz]
      exact Nat.zero_le _
    · omega
  change b.B*(131071-h) ≤ b.m*agreement-2*h*b.reserve
  rw [res]
  rw [delta, Nat.mul_add] at pre
  rw [Nat.mul_comm (h-firstHeight) b.B] at more
  omega

theorem cutoff_order (b : Witness) {h : ℕ} (pos : 0 < b.top h) :
    b.top h-1+2*h*b.reserve < b.shape.m*agreement := by
  change 0 < b.m*agreement-2*h*b.reserve at pos
  change b.m*agreement-2*h*b.reserve-1+2*h*b.reserve < b.m*agreement
  omega

structure Verified (b : Witness) : Prop where
  node_eq : P1_7_1.nodeRows b.shape = b.nodes
  pole_ge : P1_7_1.groupedPoleMoment b.B b.J ≤ b.pole
  caps : b.B ≤ 5585 ∧ b.J ≤ 1200 ∧ b.v ≤ seedCap ∧ 0 < b.m ∧ 2*b.reserve ≤ b.B
  width_at_first : b.B*(131071-firstHeight) ≤ b.top firstHeight
  endpoints : ∃ endpoints : List ℕ, Cover b firstHeight endpoints

theorem Verified.raw_positive {b : Witness} (checked : Verified b) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    b.width*b.nodes+h*b.rate*b.pole+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight b.slots) <
      b.width*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  obtain ⟨ends, cover⟩ := checked.endpoints
  obtain ⟨bot, top, hb, ht, htop, cert⟩ := cover_height cover lo hi
  have tail : ∀ k > slotLimit b.shape b.v b.lower,
      b.slots k = 0 ∨ b.shape.B < k*b.degree ∨ b.shape.J < k*1 := by
    intro k big
    cases tag : b.rect
    · simpa only [Witness.slots,tag,Bool.false_eq_true,ite_false] using
        triangle_tail b.shape b.degree b.v b.lower k big
    · simpa only [Witness.slots,tag,ite_true] using
        rectangle_tail b.shape b.degree seedCap b.v b.lower k big
  have pos : 0 < h := (show 0 < firstHeight by decide).trans_le lo
  have narrow : b.shape.J < 131071-top := by
    change b.J < 131071-top
    have small := checked.caps.2.1
    have last : lastHeight = 2522 := rfl
    omega
  exact HelperWindowIntervals.positive b.shape agreement b.reserve bot top h b.degree 1 b.weight _
    b.width b.rate b.nodes b.pole b.slots pos hb ht narrow tail cert

theorem Verified.rectangle {b : Witness} (checked : Verified b) (rect : b.rect = true) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    KoalaRect.rectDebit h b.nodes b.pole (box seedCap b.v)+
        (∑ W ∈ range (b.top h),
          debitAt b.shape h (b.top h) W b.degree 1 b.weight (rectSlots (box seedCap b.v) (axis b.lower))) <
      KoalaRect.area (box seedCap b.v)*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  have slots : b.slots = rectSlots (box seedCap b.v) (axis b.lower) := by
    funext k
    simp only [Witness.slots,rect,ite_true]
  simpa only [Witness.width,Witness.rate,slots,rect,ite_true,KoalaRect.rectDebit]
    using checked.raw_positive lo hi

theorem Verified.triangle {b : Witness} (checked : Verified b) (tri : b.rect = false) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    P1_7.debit h b.bank+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight (triSlots b.v b.lower)) <
      triangle b.v*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  have pos := checked.raw_positive lo hi
  have slots : b.slots = triSlots b.v b.lower := by
    funext k
    simp only [Witness.slots,tri,Bool.false_eq_true,ite_false]
  simpa only [Witness.width,Witness.rate,slots,tri,Bool.false_eq_true,ite_false,Nat.mul_left_comm h 2,
    Nat.mul_assoc,P1_7.debit,Witness.bank,Witness.shape] using pos

#print axioms Verified.rectangle
#print axioms Verified.triangle
end Research6966.HelperWindowCertificate

end Merged6967_R6966ProofHelperWindowCertificate

section Merged6967_R6966ProofNativeMarkedTariff
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NativeMarkedTariff
open Finset Polynomial
open K1 (K p)
open K1_14 (FX L Seeds Equation liftPoly atX graphEval seedEmbedding)
open K1_14_2 (SeedField)
open KoalaRect (axisDegree axisDegree_le_iff)
open Lower6960.TerminalMarked (determinant det_axis)
open Lower6960.RetainedCompression (project incl specialize MarkedFiber integral_project_with_width)
open CurvatureSquares (Ordinate zView)
noncomputable section
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

def width (total u v:ℕ) := min (p*total) (u+p*v)
private abbrev graph : Seeds→+*FX[X] := (K1_14.frobeniusGraph (F:=FX) p).toRingHom

private theorem frob_total (Q:Seeds) : (graph Q).natDegree≤p*Q.totalDegree := by
  apply (MvPolynomial.natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro m hm
  have bound:=MvPolynomial.le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl)] at bound
  simp only [Fin.sum_univ_two] at bound
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  change m 0+m 1*2130706433 ≤ 2130706433*Q.totalDegree
  omega

theorem coeff_cap {f:Equation} {total u v:ℕ} (t:∀i,(f.coeff i).totalDegree≤total)
    (h0:axisDegree f 0≤u) (h1:axisDegree f 1≤v) (i:ℕ) :
    ((project f).coeff i).natDegree≤width total u v := by
  change ((f.map graph).coeff i).natDegree≤_
  rw [coeff_map]
  exact le_min ((frob_total _).trans (Nat.mul_le_mul_left _ (t i)))
    (K1_14.frobeniusGraph_degree p u v _ ((axisDegree_le_iff ..).mp h0 i) ((axisDegree_le_iff ..).mp h1 i))

private theorem determinant_degree {f:Equation} (pos:0<f.natDegree) {w:ℕ}
    (cap:∀i,((project f).coeff i).natDegree≤w) :
    (graph (determinant f)).natDegree≤(2*f.natDegree-1)*w := by
  unfold determinant
  rw [←resultant_map_map]
  have hd j : ((f.derivative.map graph).coeff j).natDegree≤w := by
    rw [coeff_map,coeff_derivative,map_mul]
    have c:=cap (j+1)
    change ((f.map graph).coeff (j+1)).natDegree≤w at c
    rw [coeff_map] at c
    calc
      _ ≤ (graph (f.coeff (j+1))).natDegree+(graph ((j:Seeds)+1)).natDegree := natDegree_mul_le
      _ ≤ w+0 := Nat.add_le_add c (by simp)
      _ = _ := Nat.add_zero _
  have bh : ∀ j,((f.map graph).coeff j).natDegree≤w := cap
  apply (Polynomial.natDegree_resultant_le_of_coeff_natDegree_le _ _ _ _ w w bh hd).trans
  rw [←Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem graph_eval (Q:Seeds) (z:K) : (graph Q).eval (seedEmbedding z)=graphEval z Q := by
  have eh : (evalRingHom (seedEmbedding z)).comp graph=graphEval z := by
    apply MvPolynomial.ringHom_ext
    · intro c;simp [graph,K1_14.frobeniusGraph,graphEval]
    · intro i;fin_cases i <;> simp [graph,K1_14.frobeniusGraph,graphEval]
  exact DFunLike.congr_fun eh Q

/-- The same physical parameter width pays for the determinant and the
good-label factor tariff. It can be certified either by the seeded
ordinate section or by the two separate rectangular witness bounds. -/
theorem split {T:Finset K} (label:K→K) (s:K→K[X]) (inj:Set.InjOn label (T:Set K))
    {f:Equation} (pos:0<f.natDegree) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    {w:ℕ} (cap:∀i,((project f).coeff i).natDegree≤w)
    (small:(2*f.natDegree-1)*axisDegree f 0<p)
    (roots:∀γ∈T,(f.map (graphEval (label γ))).eval (atX (s γ))=0) :
    ∃ (S:Finset K) (P:Ordinate), S⊆T ∧ P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤w ∧
      (∀γ∈S,MarkedFiber P (algebraMap K L (label γ)) (liftPoly (s γ))) ∧
      T.card≤(2*f.natDegree-1)*w+S.card := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let S:=T\B
  have nz:determinant f≠0:=resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have ne:graph (determinant f)≠0:=K1_14.frobeniusGraph_ne_zero p (by decide) _ nz
    ((det_axis f 0).trans_lt small)
  have eq:(B.image (fun γ=>seedEmbedding (label γ))).card=B.card :=
    card_image_of_injOn (fun x hx y hy h=>inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 (seedEmbedding.injective h))
  have bad:B.card≤(2*f.natDegree-1)*w:=by
    rw [←eq]
    apply le_trans _ (determinant_degree pos cap)
    apply Polynomial.card_le_degree_of_subset_roots
    rintro _ hz
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
    exact (mem_roots ne).mpr ((graph_eval _ _).trans (mem_filter.mp hγ).2)
  have axisSmall:axisDegree f 0<p:=
    (Nat.le_mul_of_pos_left _ (by omega : 0<2*f.natDegree-1)).trans_lt small
  have fn:f≠0:=by intro eq;simp [eq] at pos
  obtain ⟨d,P,dn,pn,de,wd,called⟩:=integral_project_with_width f fn axisSmall w cap
  refine ⟨S,P,sdiff_subset,pn,de,wd,?_,?_⟩
  · intro γ hγ
    have hT:γ∈T:=(mem_sdiff.mp hγ).1
    have safe:graphEval (label γ) (determinant f)≠0 := fun zero=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hT,zero⟩)
    have full:=natDegree_map_eq_of_resultant_derivative_padded_ne_zero _ _ le_rfl safe
    have sg:=separable_map_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe
    have nz':incl d≠0:=(map_ne_zero_iff incl (IsFractionRing.injective (Polynomial L) FX)).mpr dn
    have eq:=called (label γ)
    refine ⟨?_,?_,?_⟩
    · rw [←natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX),eq,natDegree_C_mul nz',full,de]
    · rw [eq];exact sg.unit_mul (isUnit_C.mpr nz'.isUnit)
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq,map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr (roots γ hT))
  · have partition:=card_sdiff_add_card_eq_card (show B⊆T from filter_subset ..)
    change T.card≤_+(T\B).card
    omega

#print axioms coeff_cap
#print axioms split
end
end Research6966.NativeMarkedTariff

end Merged6967_R6966ProofNativeMarkedTariff

section Merged6967_R6966ProofNativeWitnessBank
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NativeWitnessBank
open Polynomial Finset Module
open K1_14 (Jet Shape L Equation shapeSum)
open K1_14_1 (CRTLift PoleData)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Parent Surface ProjectedProduct OrderAt)
open KoalaRect (rectEvaluated area rectDebit)
open HelperAvoidance (debitAt rectSlots triSlots)
open PadeNativeQuotient (Native)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false

theorem irreducible {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) : Irreducible N.poly := by
  classical
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  let F:=FractionRing Equation
  let f:=algebraMap Equation F
  refine (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
    (R:=Equation) (K:=F) (p:=N.poly) N.primitive).mpr ?_
  apply irreducible_of_degree_eq_one
  have fi:=IsFractionRing.injective Equation F
  have nz:N.poly.map f≠0:=(map_ne_zero_iff (mapRingHom f) (map_injective _ fi)).mpr N.primitive.ne_zero
  change (N.poly.map f).degree=1
  rw [degree_eq_natDegree nz,natDegree_map_eq_of_injective fi,NativeGraphMarks.slope_degree N gp];rfl

def witnessed {G:Pade.Row K1_14_3.SeedField} (N:Native G) (parents:Finset Surface) (H:Equation) : Prop :=
  ProjectedProduct parents H ∧ ∀ Q:Jet,∀ J k:ℕ,Q.natDegree≤J →
    (∀ q∈parents,OrderAt q Q k) → H^k∣TerminalProjection.cleared
      (NativeGraphExceptional.den N) (NativeGraphExceptional.rhs N) Q J

theorem exists_witnessed {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive)
    {parents:Finset Surface} (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (owner:∀ q∈parents,N.poly∈q.asIdeal) : ∃ H:Equation,witnessed N parents H :=
  NativeProjectedWitness.projected_factor N gp parents nonempty geo owner

private theorem consume {h agreement r:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) {parents:Finset Surface} {H:Equation}
    (chosen:witnessed N parents H) {s envelope:Shape} {top:ℕ} (cut:top-1+2*h*r<s.m*agreement)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (U width:Fin 2→ℕ)
    (widthFit:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q)
    (Q:Jet) (row:Q∈rectEvaluated Crt word s (top-1) U) (avoid:¬N.poly∣Q) :
    (r+1)*H.natDegree≤s.B+(G.graphDegree-1)*s.J ∧
      ∀ z,(r+1)*KoalaRect.axisDegree H z≤U z+s.J*width z := by
  have ev:=KoalaRect.rectEvaluated_le Crt word s (top-1) U row
  have nz:Q≠0:=by rintro rfl;exact avoid (dvd_zero _)
  have cap (j:ℕ) (mem:j∈Q.support) : (Q.coeff j).natDegree+j≤s.B ∧ j≤s.J := by
    have top: (Q.coeff j).coeff (Q.coeff j).natDegree≠0:=by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr (mem_support_iff.mp mem)
    exact ⟨(K1_14_1.evaluated_shape Crt word ev j _ top).1,(K1_14_1.evaluated_shape Crt word ev j _ top).2.1⟩
  have sj:Q.natDegree≤s.J:=(cap _ (natDegree_mem_support_of_nonzero nz)).2
  exact NativeProjectedWitness.avoiding_widths N gp chosen.1.primitive.ne_zero Q (r+1) s.J s.B U width
    avoid sj (fun j mem=>(cap j mem).1) (KoalaRect.rectEvaluated_axis Crt word row) widthFit
    (chosen.2 Q s.J (r+1) sj (fun q hq=>TerminalBanks.retained_order Crt word (geo q hq)
      (pass q hq) fits small cut ev))

/-- Every positive rectangle bounds the *same* fixed native projected
product in both seed axes and the ordinate, directly from terminal passes. -/
theorem rectangle {h agreement r top:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} {H:Equation} (chosen:witnessed N parents H) {s envelope:Shape}
    (U lower width:Fin 2→ℕ) (isSeed:K1_14_2.UsesSeed N.poly) (char:s.U<K1.p) (charB:s.B<K1.p)
    {L0 nodes moment:ℕ} (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (axisLow:∀ z,lower z≤PadeNativeQuotient.axis N.poly z)
    (axisHigh:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (box:U 0+U 1≤s.U) (wide:s.B*(131071-h)≤top) (nt:0<top)
    (nodeCap:P1_7_1.nodeRows s≤nodes) (poleCap:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (positive:rectDebit h nodes moment U + ∑ W∈range top,debitAt s h top W G.graphDegree 1 L0 (rectSlots U lower) <
      area U*shapeSum s (fun q j=>top+j-q*(131071-h)))
    (cut:top-1+2*h*r<s.m*agreement) (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p)
    (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q) :
    (r+1)*H.natDegree≤s.B+(G.graphDegree-1)*s.J ∧ ∀ z,(r+1)*KoalaRect.axisDegree H z≤U z+s.J*width z := by
  have nd:=NativeGraphMarks.slope_degree N gp
  obtain ⟨Q,mem,avoid⟩:=HelperAvoidance.rect_avoiding hp hl Crt word s U lower phys (irreducible N gp)
    (by omega) isSeed char (HelperWeightCap.native_degree N gp).ge nd.ge lCap axisLow box charB nt wide nodeCap poleCap positive
  exact consume Crt word N gp chosen cut fits small U width axisHigh geo pass Q mem avoid

theorem triangular {h agreement r top:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} {H:Equation} (chosen:witnessed N parents H) (bank:P1_7.Bank) {envelope:Shape}
    (width:Fin 2→ℕ) (isSeed:K1_14_2.UsesSeed N.poly) (char:bank.shape.U<K1.p) (charB:bank.shape.B<K1.p)
    {L0 lower:ℕ} (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (uLow:lower≤seedDegree N.poly) (axisHigh:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (wide:bank.shape.B*(131071-h)≤top) (nt:0<top)
    (nodeCap:P1_7_1.nodeRows bank.shape=bank.nodeRows) (poleCap:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank + ∑ W∈range top,debitAt bank.shape h top W G.graphDegree 1 L0 (triSlots bank.shape.U lower) <
      K1_14.triangle bank.shape.U*shapeSum bank.shape (fun q j=>top+j-q*(131071-h)))
    (cut:top-1+2*h*r<bank.shape.m*agreement) (fits:TerminalBanks.inside bank.shape envelope) (small:r+1<K1.p)
    (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q) :
    (r+1)*H.natDegree≤bank.shape.B+(G.graphDegree-1)*bank.shape.J ∧
      ∀ z,(r+1)*KoalaRect.axisDegree H z≤bank.shape.U+bank.shape.J*width z := by
  have nd:=NativeGraphMarks.slope_degree N gp
  obtain ⟨Q,mem,avoid⟩:=HelperAvoidance.triangle_avoiding hp hl Crt word bank phys (irreducible N gp)
    (by omega) isSeed char (HelperWeightCap.native_degree N gp).ge nd.ge lCap uLow charB nt wide nodeCap poleCap positive
  rw [←RectangularHelperShift.all_axes] at mem
  exact consume Crt word N gp chosen cut fits small _ width axisHigh geo pass Q mem avoid

#print axioms rectangle
#print axioms triangular
end
end Research6966.NativeWitnessBank

end Merged6967_R6966ProofNativeWitnessBank

section Merged6967_R6966ProofSpreadInterval
set_option Elab.async false





set_option Elab.async false

namespace Research6966.SpreadInterval
open Finset
open K1_14 (Shape)
open K1_14_4 (gradeWidth)
open KoalaRect (area rectPower rectDebit)
open PadeCutoff (capacity)
open HelperWindowPrefix (volume)
open HelperWindowGrouping (sumCount sumCount_eq)
set_option maxHeartbeats 1100000

abbrev D : ℕ := 131071

def maxOrder (s : Shape) (e : ℕ) : ℕ := s.J+s.B/e+1

def upperCut (N h k : ℕ) : ℕ := N-2*h*(k-1)-1

def lowerBox (B N h k : ℕ) : ℕ := min B ((N-2*h*k)/(D-h))

def upperBox (B J N h k : ℕ) : ℕ := min B ((upperCut N h k+J)/(D-h))

def cost (s : Shape) (A e a n lo hi k : ℕ) : ℕ :=
  let N := s.m*A
  let B := upperBox s.B s.J N hi k
  let L := lowerBox s.B N lo k
  let W := SpreadWindow.boundary s.B s.J (D-hi) (upperCut N hi k)
  min (SpreadWindow.lex B s.J e k) (W-SpreadGain.lower L s.J a n k)

def costSum (s : Shape) (A e a n lo hi : ℕ) : ℕ :=
  sumCount (fun r => cost s A e a n lo hi (r+1)) (maxOrder s e)

def Positive (s : Shape) (A e a n nodes moment lo hi : ℕ) (U : Fin 2 → ℕ) : Prop :=
  let sums := costSum s A e a n lo hi
  rectDebit lo nodes moment U+area U*(2*lo)*sums < area U*volume (s.m*A) s.B s.J (D-lo) ∧
    rectDebit hi nodes moment U+area U*(2*hi)*sums < area U*volume (s.m*A) s.B s.J (D-hi)

instance (s : Shape) (A e a n nodes moment lo hi : ℕ) (U : Fin 2 → ℕ) :
    Decidable (Positive s A e a n nodes moment lo hi U) := by unfold Positive; infer_instance

private theorem payment_mono {q c lo hi : ℕ} (within : hi ≤ D) (step : lo ≤ hi) (rich : c ≤ q) :
    q*(D-hi)+hi*c ≤ q*(D-lo)+lo*c := by
  have equation : D-lo=(D-hi)+(hi-lo) := by omega
  have offset : hi*c=lo*c+(hi-lo)*c := by rw [← Nat.add_mul,Nat.add_sub_of_le step]
  have sparse : (hi-lo)*c ≤ q*(hi-lo) := by
    rw [Nat.mul_comm q]; exact Nat.mul_le_mul_left _ rich
  rw [equation,Nat.mul_add,offset]
  omega

private theorem payment_base {c h : ℕ} (ch : h≤D) : c*(D-h)+h*c=D*c := by
  rw [Nat.mul_comm h c,← Nat.mul_add,Nat.sub_add_cancel ch,Nat.mul_comm]

theorem cash_bound {N h hi W k q j : ℕ} (bound : 2*D*k<N)
    (high : hi<D) (height : h≤hi) (inside : W+2*h*(k-1)<N)
    (weight : q*(D-h)≤W+j) :
    q*(D-hi)≤upperCut N hi k+j := by
  let r := 2*(k-1)
  have inside' : W+h*r<N := by dsimp only [r]; rwa [show h*(2*(k-1))=2*h*(k-1) by ring]
  have final : q*(D-hi)+hi*r<N+j := by
    by_cases big : r≤q
    · have bill := payment_mono high.le height big
      omega
    · have low : q≤r := by omega
      have step := Nat.mul_le_mul_right (D-hi) low
      have base := payment_base (c:=r) high.le
      have top : D*r<N := by
        have rail : D*r≤2*D*k := by
          rw [show 2*D*k=D*(2*k) by ring]
          exact Nat.mul_le_mul_left D (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))
        exact rail.trans_lt bound
      omega
  unfold upperCut
  have cut : hi*r=2*hi*(k-1) := by dsimp [r];ring
  rw [cut] at final
  have hfit : 2*hi*(k-1)<N := by
    have p : 2*hi*(k-1) ≤ 2*D*k :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 high.le) (Nat.sub_le _ _)
    exact p.trans_lt bound
  omega

private theorem b_lower {B N lo h hi k : ℕ} (height : lo≤h) (right : h≤hi) (hiD : hi<D)
    (bound : 2*D*k<N) : lowerBox B N lo k≤lowerBox B N h k := by
  let t := (N-2*lo*k)/(D-lo)
  have lp : 0<D-lo := by omega
  have hp : 0<D-h := by omega
  have first : 2*k * (D-lo)+lo*(2*k)=2*D*k := by
    rw [payment_base (by omega : lo≤D)]
    ring
  have paid : t*(D-lo)≤N-2*lo*k := Nat.div_mul_le_self .. 
  have meaningful : 2*k≤t := by
    apply (Nat.le_div_iff_mul_le lp).mpr
    have equal : lo*(2*k)=2*lo*k := by ring
    omega
  have atLo : t*(D-lo)+lo*(2*k)≤N := by
    have fit : 2*lo*k≤N := (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 (by omega : lo≤D))).trans bound.le
    have equal : lo*(2*k)=2*lo*k := by ring
    omega
  have atH := (payment_mono (by omega : h≤D) height meaningful).trans atLo
  have ht : t≤(N-2*h*k)/(D-h) := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [show h*(2*k)=2*h*k by ring] at atH
    omega
  exact min_le_min le_rfl ht

theorem grade_upper {s : Shape} {A h hi W k : ℕ} (bound : 2*D*k<s.m*A)
    (high : hi<D) (height : h≤hi) (inside : W+2*h*(k-1)<s.m*A) :
    ∀ j≤s.J, gradeWidth (D-h) s.B W j ≤ upperBox s.B s.J (s.m*A) hi k+1-j := by
  intro j hj
  let b := min s.B ((W+j)/(D-h))
  have hpos : 0<D-h := by omega
  have hipos : 0<D-hi := by omega
  have fit : b*(D-h)≤W+j := (Nat.le_div_iff_mul_le hpos).mp (min_le_right ..)
  have lease := (cash_bound bound high height inside fit).trans (Nat.add_le_add_left hj _)
  have qb : b≤upperBox s.B s.J (s.m*A) hi k :=
    le_min (min_le_left _ _) ((Nat.le_div_iff_mul_le hipos).mpr lease)
  unfold gradeWidth
  rw [show min (s.B+1) ((W+j)/(D-h)+1)=b+1 by dsimp only [b];omega]
  exact Nat.sub_le_sub_right (Nat.succ_le_succ qb) _

private theorem window_upper {s : Shape} {A h hi W k : ℕ} (bound : 2*D*k<s.m*A)
    (high : hi<D) (height : h≤hi) (inside : W+2*h*(k-1)<s.m*A)
    (narrow : s.J<D-hi) :
    (PadeFiltered.physicalWindow s.B s.J (D-h) W).card ≤
      SpreadWindow.boundary s.B s.J (D-hi) (upperCut (s.m*A) hi k) := by
  have wp : 0<D-h := by omega
  have wip : 0<D-hi := by omega
  rw [SpreadWindow.boundary_eq _ _ _ _ narrow]
  apply card_le_card
  intro t mem
  obtain ⟨insideBox,fit⟩ := mem_filter.mp mem
  apply mem_filter.mpr
  refine ⟨insideBox, ?_⟩
  apply (SpreadWindow.weight_iff (D-hi) t.1 t.2 _ wip).mpr
  exact cash_bound bound high height inside
    ((SpreadWindow.weight_iff (D-h) t.1 t.2 W wp).mp fit)

private theorem cost_at {s : Shape} {A h e a n lo hi W : ℕ} (U : Fin 2 → ℕ)
    (hp : 0<h) (left : lo≤h) (right : h≤hi) (hiD : hi<D) (narrow : s.J<D-hi)
    (ap : 0<a) (ep : 0<e) (full : 2*D*maxOrder s e<s.m*A)
    (hw : W<s.m*A) (valid : rectPower A h s W≤maxOrder s e) :
    capacity A h e a n s U W ≤ area U*cost s A e a n lo hi (rectPower A h s W) := by
  let k := rectPower A h s W
  have kp : 0<k := (show 0<1 by decide).trans_le (Nat.le_add_right _ _)
  have money : 2*D*k<s.m*A := (Nat.mul_le_mul_left _ valid).trans_lt full
  have radius : W+2*h*(k-1)<s.m*A := by
    have guard := K1_14_4.power_threshold (s.m*A) (2*h) W 0 (k-1) hw (by omega)
    simp only [Nat.zero_add,Nat.sub_zero] at guard
    exact guard.mp (show k-1<k by omega)
  have b_le := b_lower left right hiD money (B:=s.B)
  have graph := SpreadGain.lower_le _ _ s.J a n k ap b_le
  have box := window_upper money hiD right radius narrow
  have wp : 0 < D-h := by omega
  have lexical := SpreadWindow.rect_lex A h e k W _ s U wp ep rfl
    (grade_upper money hiD right radius)
  let L := SpreadWindow.lex (upperBox s.B s.J (s.m*A) hi k) s.J e k
  let G := SpreadWindow.boundary s.B s.J (D-hi) (upperCut (s.m*A) hi k)-
    SpreadGain.lower (lowerBox s.B (s.m*A) lo k) s.J a n k
  change capacity A h e a n s U W≤area U*min L G
  have graphCap :
      ((PadeFiltered.physicalWindow s.B s.J (D-h) W).card-
        PadeRank.gain a n k (lowerBox s.B (s.m*A) h k+1) (s.J+1))*area U ≤ G*area U := by
    apply Nat.mul_le_mul_right
    exact (Nat.sub_le_sub_right box _).trans (Nat.sub_le_sub_left graph _)
  rcases le_total L G with le|le
  · rw [min_eq_left le,Nat.mul_comm]
    exact (min_le_left _ _).trans lexical
  · rw [min_eq_right le,Nat.mul_comm]
    exact (min_le_right _ _).trans graphCap

/-- Every group of constant Hasse order has a common capacity bound at
all heights in the interval. The initial and final scalar comparisons
therefore exclude the actual native graph at every such height. -/
theorem excluded {s : Shape} {A e a n nodes moment lo hi h : ℕ} {U : Fin 2 → ℕ}
    (lp : 0<lo) (left : lo≤h) (right : h≤hi) (hiD : hi<D) (narrow : s.J<D-hi)
    (ap : 0<a) (ep : 0<e) (wide : s.B*(D-lo)≤s.m*A) (full : 2*D*maxOrder s e<s.m*A)
    (cert : Positive s A e a n nodes moment lo hi U) :
    PadeCutoff.excluded A h e a n s U nodes moment := by
  have hp := lp.trans_le left
  have cap := SpreadBucket.sum_capacity (s:=s) (A:=A) (e:=e) (a:=a) (n:=n)
    (U:=U) (K:=maxOrder s e) hp (cost s A e a n lo hi)
    (fun W hw valid => cost_at U hp left right hiD narrow ap ep full hw valid)
    (by
      intro W _ far
      have wp : 0 < D-h := by omega
      have z := SpreadWindow.rect_zero A h e W s U wp ep far
      simp [capacity,z])
  have rlo : volume (s.m*A) s.B s.J (D-lo) = SpreadBucket.raw s A lo := by
    rw [HelperWindowPrefix.volume_eq_shapeSum s _ _ (narrow.trans_le (Nat.sub_le_sub_left (left.trans right) _))]
    simp only [SpreadBucket.raw,Nat.mul_comm (D-lo)]
  have rhi : volume (s.m*A) s.B s.J (D-hi) = SpreadBucket.raw s A hi := by
    rw [HelperWindowPrefix.volume_eq_shapeSum s _ _ narrow]
    simp only [SpreadBucket.raw,Nat.mul_comm (D-hi)]
  have fast : ∑ W ∈ range (s.m*A), capacity A h e a n s U W ≤ area U*(2*h)*costSum s A e a n lo hi := by
    simpa only [costSum,sumCount_eq] using cap
  exact SpreadBucket.excluded_of_endpoints left right hiD.le wide fast
    (cert.1.trans_eq (congrArg (area U*·) rlo)) (cert.2.trans_eq (congrArg (area U*·) rhi))

#print axioms excluded
end Research6966.SpreadInterval

end Merged6967_R6966ProofSpreadInterval
