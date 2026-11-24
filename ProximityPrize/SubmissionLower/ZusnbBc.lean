import ProximityPrize.SubmissionLower.Z4EMMWa
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Finsupp.add_apply → zSs, IsScalarTower.algebraMap_eq → zYY, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, MvPolynomial.monomial → ztt, Polynomial.X → z7y, RingHom.comp_apply → zQb
namespace qFwMjQd
noncomputable section
open cu (L)
open q8Z6NHc (Index jo)
open Polynomial
private theorem map_onLine {R σ S A:Type} [CommRing R] [CommRing S] [CommRing A]
    (k :R →+* S) (u v :σ→S) (T:S) (φ:S →+* A)
    (r : (z3y σ R)[X]) :
    (onLine k u v T r).map φ=onLine (φ.comp k) (φ ∘ u) (φ ∘ v) (φ T) r := by
  change ((mapRingHom φ).comp (onLine k u v T)) r= _
  apply zmU
  apply Polynomial.ringHom_ext
  · intro q
    simp only [zQb,onLine,coe_eval₂RingHom,eval₂_C]
    change ((mapRingHom φ).comp (zOD (C.comp k)
      (fun i=>C (u i)+C (v i)*z7y))) q= _
    change _=zOD (C.comp (φ.comp k))
      (fun i=>C (φ (u i))+C (φ (v i))*z7y) q
    apply zmU
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp
  · simp [onLine]
private abbrev Probe (σ:Type) :=(z3y σ L)[X]
private def probe {σ:Type} : LineRing σ →+* Probe σ :=
  zOD (C.comp znf) fun
    | none=>Polynomial.X
    | some (false,_)=>0
    | some (true,i)=>C (MvPolynomial.X i)
private def pureLine {σ:Type} (r : (z3y σ L)[X]) : (Probe σ)[X] :=
  onLine (C.comp znf) (fun _=>0) (fun i=>C (z9v i)) z7y r
private theorem pureLine_monomials {σ:Type} (n:ℕ) (m:σ →₀ ℕ) (r :L) :
    pureLine (monomial n (ztt m r)) =
      monomial (m.sum fun _ e=>e) (monomial n (ztt m r)) := by
  classical
  unfold pureLine onLine
  rw [coe_eval₂RingHom,eval₂_monomial,MvPolynomial.eval₂Hom_monomial]
  simp only [C_0,zero_add,zQb,Finsupp.prod,mul_pow,← map_pow,
    Finset.prod_mul_distrib,← map_prod,Finset.prod_pow_eq_pow_sum]
  have h:=MvPolynomial.monomial_eq (s :=m) (a :=r)
  simp only [Finsupp.prod] at h
  rw [← mul_assoc,← map_mul,← map_mul,← h]
  rw [C_mul_X_pow_eq_monomial,monomial_mul_C,C_mul_X_pow_eq_monomial]
  rfl
private theorem pureLine_coeff {σ:Type} (r : (z3y σ L)[X])
    (j i:ℕ) (m:σ →₀ ℕ) :
    (((pureLine r).coeff j).coeff i).coeff m =
      if j=(m.sum fun _ e=>e) then (r.coeff i).coeff m else 0:= by
  classical
  induction r using Polynomial.induction_on' with
  | add u v hu hv =>
    have h:pureLine (u+v)=pureLine u+pureLine v :=map_add _ _ _
    simp only [h,coeff_add,AddMonoidAlgebra.coeff_add,zSs,hu,hv]
    split <;> simp
  | monomial n q =>
    induction q using MvPolynomial.induction_on' with
    | add u v hu hv =>
      have h:monomial n (u+v)=monomial n u+monomial n v :=map_add _ _ _
      have h' : pureLine (monomial n (u+v)) =
          pureLine (monomial n u)+pureLine (monomial n v) := by rw [h]; exact map_add _ _ _
      rw [h']
      conv_rhs=>rw [h]
      simp only [coeff_add,AddMonoidAlgebra.coeff_add,zSs,hu,hv]
      split <;> simp
    | monomial l x =>
      rw [pureLine_monomials,coeff_monomial]
      by_cases hl:l=m
      · subst l
        by_cases hj: (m.sum fun _ e=>e)=j
        · subst j
          by_cases hn:n=i <;> simp [coeff_monomial,hn]
        · simp [hj,Ne.symm hj]
      · split <;> by_cases hn:n=i <;>
          simp [coeff_monomial,MvPolynomial.coeff_monomial,hl,hn]
theorem coefficient_le_line_degree {d s a :ℕ} (r : (jo d s a)[X]) (i:ℕ) :
    (r.coeff i).totalDegree≤(aOw r).natDegree := by
  classical
  let σ:=Index d s a
  let P: (LineRing σ)[X] :=onLine znf
    (fun j=>z9v (some (false,j))) (fun j=>z9v (some (true,j)))
    (z9v none) r
  have hP:P.map (probe :LineRing σ →+* Probe σ)=pureLine r := by
    simpa [P,probe,pureLine,Function.comp_def,RingHom.comp_assoc] using
      map_onLine znf (fun j:σ=>z9v (some (false,j)))
        (fun j=>z9v (some (true,j))) (z9v none) probe r
  let φ:=algebraMap (LineRing σ) (Ez σ)
  have hφ:Function.Injective φ:= by
    rw [show φ= _ from zYY (LineRing σ) (FractionRing (LineRing σ)) (Ez σ)]
    exact (algebraMap (FractionRing (LineRing σ)) (Ez σ)).injective.comp
      (IsFractionRing.injective (LineRing σ) (FractionRing (LineRing σ)))
  have hline :P.map φ=aOw r := by
    have hk :φ.comp znf=algebraMap L (Ez σ) :=
      (zYY L (LineRing σ) (Ez σ)).symm
    have h:=map_onLine znf (fun j:σ=>z9v (some (false,j)))
      (fun j=>z9v (some (true,j))) (z9v none) φ r
    rw [hk] at h
    exact h
  apply Finset.sup_le
  intro m hm
  apply le_natDegree_of_ne_zero
  intro hz
  rw [← hline,coeff_map] at hz
  have hp:=hφ (hz.trans (map_zero φ).symm)
  have hzero : (pureLine r).coeff (m.sum fun _ e=>e)=0:= by
    rw [← hP,coeff_map,hp,map_zero]
  have hrec:=pureLine_coeff r (m.sum fun _ e=>e) i m
  rw [hzero] at hrec
  exact (MvPolynomial.mem_support_iff.mp hm) (by simpa using hrec.symm)
end
end qFwMjQd
