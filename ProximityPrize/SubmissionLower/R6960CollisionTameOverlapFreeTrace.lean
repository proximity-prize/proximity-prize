import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import Mathlib.Algebra.Polynomial.FieldDivision
import ProximityPrize.SubmissionLower.R6960LineEulerFree

set_option Elab.async false

-- merged module R6960CollisionTameOverlapUnit
section Merged_R6960CollisionTameOverlapUnit
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LaurentPolynomial
open scoped Polynomial
section Unit
variable {R : Type*} [CommRing R] [IsDomain R]
theorem laurent_unit_over_domain (f : LaurentPolynomial R) (unit : IsUnit f) :
    ∃ (c : R) (m : ℤ),IsUnit c ∧ f=LaurentPolynomial.C c*T m := by
  obtain ⟨u,rfl⟩ := unit
  obtain ⟨n,a,ea⟩ := LaurentPolynomial.exists_T_pow (u:LaurentPolynomial R)
  obtain ⟨l,b,eb⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹:LaurentPolynomial R)
  have ab : a*b=(Polynomial.X : (Polynomial R))^(n+l) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul,ea,eb,Polynomial.toLaurent_X_pow,mul_mul_mul_comm,Units.mul_inv,one_mul,←T_add]
    push_cast
    rfl
  obtain ⟨j,_,assoc⟩ := (dvd_prime_pow (Polynomial.prime_X (R:=R)) (n+l)).mp (show a∣_ from ⟨b,ab.symm⟩)
  obtain ⟨v,hv⟩ := assoc.symm
  obtain ⟨c,cu,cv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  have aa : a=(Polynomial.X : (Polynomial R))^j*Polynomial.C c := by rw [cv,hv]
  refine ⟨c,(j:ℤ)-n,cu,?_⟩
  have shifted : (u:LaurentPolynomial R)*T (n:ℤ)=LaurentPolynomial.C c*T (j:ℤ) := by
    rw [←ea,aa,map_mul,Polynomial.toLaurent_X_pow,Polynomial.toLaurent_C,mul_comm]
  calc
    (u:LaurentPolynomial R) = ((u:LaurentPolynomial R)*T (n:ℤ))*T (-(n:ℤ)) := by
      rw [mul_assoc,←T_add,add_neg_cancel,T_zero,mul_one]
    _ = LaurentPolynomial.C c*T ((j:ℤ)-n) := by rw [shifted,mul_assoc,T_sub]
end Unit
section CoefficientMap
variable {R S : Type*} [CommRing R] [CommRing S]
private def unitT (S : Type*) [CommRing S] : (LaurentPolynomial S)ˣ :=
  ⟨T 1,T (-1),by rw [←T_add,show (1:ℤ)+(-1)=0 by decide,T_zero],
    by rw [←T_add,show (-1:ℤ)+1=0 by decide,T_zero]⟩
def laurentCoefficients (f : R→+*S) : LaurentPolynomial R→+*LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp f) (unitT S)
@[simp] theorem laurentCoefficients_C (f : R→+*S) (a : R) :
    laurentCoefficients f (LaurentPolynomial.C a)=LaurentPolynomial.C (f a) :=
  LaurentPolynomial.eval₂_C _ _ _
@[simp] theorem laurentCoefficients_T (f : R→+*S) (m : ℤ) :
    laurentCoefficients f (T m)=T m := by
  cases m with
  | ofNat n =>
    change laurentCoefficients f (T (n:ℤ))=T (n:ℤ)
    rw [laurentCoefficients,LaurentPolynomial.eval₂_T_n]
    change (T (1:ℤ):LaurentPolynomial S)^n=T (n:ℤ)
    rw [T_pow,mul_one]
  | negSucc n =>
    change laurentCoefficients f (T (-(↑(n+1):ℤ)))=T (-(↑(n+1):ℤ))
    rw [laurentCoefficients,LaurentPolynomial.eval₂_T_neg_n]
    change (T (-1):LaurentPolynomial S)^(n+1)=T (-(↑(n+1):ℤ))
    rw [T_pow,mul_neg_one]
@[simp] theorem laurentCoefficients_polynomial (f : R→+*S) (p : (Polynomial R)) :
    laurentCoefficients f p.toLaurent=(p.map f).toLaurent := by
  have eq : (laurentCoefficients f).comp Polynomial.toLaurent=
      Polynomial.toLaurent.comp (Polynomial.mapRingHom f) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,Polynomial.toLaurent_C,Polynomial.coe_mapRingHom,
        Polynomial.map_C,laurentCoefficients_C]
    · simp only [RingHom.comp_apply,Polynomial.toLaurent_X,Polynomial.coe_mapRingHom,
        Polynomial.map_X,laurentCoefficients_T]
  exact RingHom.congr_fun eq p
@[simp] theorem laurentCoefficients_inverse (f : R→+*S) (p : (Polynomial R)) :
    laurentCoefficients f (invert p.toLaurent)=invert ((p.map f).toLaurent) := by
  let v := (invert (R:=S)).toRingEquiv.toRingHom
  let u := (invert (R:=R)).toRingEquiv.toRingHom
  have eq : (laurentCoefficients f).comp (u.comp Polynomial.toLaurent)=
      v.comp (Polynomial.toLaurent.comp (Polynomial.mapRingHom f)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change laurentCoefficients f (invert ((Polynomial.C a).toLaurent))=
        invert (((Polynomial.C a).map f).toLaurent)
      simp only [Polynomial.toLaurent_C,Polynomial.map_C,invert_C,laurentCoefficients_C]
    · change laurentCoefficients f (invert ((Polynomial.X (R:=R)).toLaurent))=
        invert (((Polynomial.X (R:=R)).map f).toLaurent)
      simp only [Polynomial.toLaurent_X,Polynomial.map_X,invert_T,laurentCoefficients_T]
  exact RingHom.congr_fun eq p
end CoefficientMap
section Degree
variable {k K : Type*} [Field k] [Field K]
theorem plane_overlap_unit (δfin δinf : (Polynomial (Polynomial k)))
    (glue : (Ideal.span {δfin.toLaurent} : Ideal (LaurentPolynomial (Polynomial k)))=
      Ideal.span {invert δinf.toLaurent}) :
    ∃ (c : k) (m : ℤ),c≠0 ∧
      δfin.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δinf.toLaurent := by
  have assoc : Associated (invert δinf.toLaurent) δfin.toLaurent :=
    Ideal.span_singleton_eq_span_singleton.mp glue.symm
  obtain ⟨u,hu⟩ := assoc
  obtain ⟨a,m,au,eq⟩ := laurent_unit_over_domain (u:LaurentPolynomial (Polynomial k)) u.isUnit
  obtain ⟨c,cu,hc⟩ := Polynomial.isUnit_iff.mp au
  refine ⟨c,m,cu.ne_zero,?_⟩
  rw [←hu,eq,←hc,mul_comm]
private theorem associated_constant {u v : (Polynomial K)} (h : Associated u v) :
    ∃ c : K, c≠0 ∧ u=Polynomial.C c*v := by
  obtain ⟨x,hx⟩ := h.symm
  obtain ⟨c,cu,eq⟩ := Polynomial.isUnit_iff.mp x.isUnit
  exact ⟨c,cu.ne_zero,by rw [←hx,eq,mul_comm]⟩
theorem overlap_transition_exponent (δfin δinf : (Polynomial (Polynomial k))) (c : k) (cn : c≠0) (m : ℤ)
    (glue : δfin.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δinf.toLaurent)
    (spec : (Polynomial k)→+*K) (nonzero : δfin.map spec≠0)
    (finDisc infDisc : (Polynomial K)) (hf : Associated finDisc (δfin.map spec))
    (hi : Associated infDisc (δinf.map spec))
    (G : LaurentPolynomial K) (gUnit : IsUnit G)
    (trace : invert infDisc.toLaurent=G^2*finDisc.toLaurent) :
    ∃ d : ℤ,G.degree=(d:WithBot ℤ) ∧ 2*d+m=0 := by
  let fin := (δfin.map spec).toLaurent
  let inf := invert (δinf.map spec).toLaurent
  let scalar := spec (Polynomial.C c)
  have scalar_ne : scalar≠0 := (map_ne_zero_iff _ (spec.comp Polynomial.C).injective).mpr cn
  have h := congrArg (laurentCoefficients spec) glue
  have specialized : fin=LaurentPolynomial.C scalar*T m*inf := by
    simpa only [fin,inf,scalar,map_mul,laurentCoefficients_polynomial,laurentCoefficients_inverse,
      laurentCoefficients_C,laurentCoefficients_T] using h
  have fn : fin≠0 := (map_ne_zero_iff _ Polynomial.toLaurent_injective).mpr nonzero
  have inn : inf≠0 := by
    intro z
    exact fn (by rw [specialized,z,mul_zero])
  obtain ⟨a,an,eqf⟩ := associated_constant hf
  obtain ⟨b,bn,eqi⟩ := associated_constant hi
  have F := congrArg (Polynomial.toLaurent (R:=K)) eqf
  rw [map_mul,Polynomial.toLaurent_C] at F
  change finDisc.toLaurent=LaurentPolynomial.C a*fin at F
  have I := congrArg ((invert (R:=K)).toRingEquiv.toRingHom.comp (Polynomial.toLaurent (R:=K))) eqi
  change invert infDisc.toLaurent=invert ((Polynomial.C b*(δinf.map spec)).toLaurent) at I
  rw [map_mul,Polynomial.toLaurent_C,map_mul,invert_C] at I
  obtain ⟨w,d,wn,mon⟩ := LineEuler.unit_monomial G gUnit
  rw [I,F,specialized,mon] at trace
  have eq : LaurentPolynomial.C b * inf = LaurentPolynomial.C (w^2*a*scalar)*T (d+d+m)*inf := by
    rw [map_mul,map_mul,map_pow,T_add,T_add,pow_two]
    convert trace using 1; ring
  have base := mul_right_cancel₀ inn eq
  have degree := congrArg LaurentPolynomial.degree base
  rw [LaurentPolynomial.degree_C bn,degree_C_mul_T _ _ (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 wn) an) scalar_ne)] at degree
  have z := WithBot.coe_inj.mp degree
  exact ⟨d,by rw [mon,degree_C_mul_T _ _ wn],by omega⟩
#print axioms plane_overlap_unit
#print axioms overlap_transition_exponent
end Degree
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameOverlapUnit

-- merged module R6960CollisionTameOverlapFreeTrace
section Merged_R6960CollisionTameOverlapFreeTrace
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Matrix Module LineEuler LaurentPolynomial
open scoped Polynomial Matrix BigOperators
variable {k U V M ι : Type*} [Field k] [CommRing U] [CommRing V] [CommRing M]
  [Algebra (Polynomial k) U] [Algebra (Polynomial k) V] [Algebra (Laurent k) M] [Fintype ι] [DecidableEq ι]
theorem free_trace_matrix_on_torus (s : Bool) (b : Basis ι (Polynomial k) U)
    (f : ChartMap (k:=k) s U M) (loc : IsChartLocalization s f)
    (r : U→+*M) (agree : ∀ x,f x=r x) :
    (Algebra.traceMatrix (Polynomial k) b).map (chartEmbedding s (k:=k))=
      Algebra.traceMatrix (Laurent k) (localFreeBasis s b f loc) := by
  let B := localFreeBasis s b f loc
  have tr (x : U) : chartEmbedding s (Algebra.trace (Polynomial k) U x)=Algebra.trace (Laurent k) M (r x) := by
    rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace B]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change chartEmbedding s ((Algebra.leftMulMatrix b x) i i)=((Algebra.leftMulMatrix B (r x)) i i)
    rw [Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
      show B i=r (b i) from (localFreeBasis_apply s b f loc i).trans (agree _),←map_mul,←agree]
    exact (localFreeBasis_repr s b f loc _ i).symm
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,Algebra.traceMatrix_apply,Algebra.traceForm_apply,localFreeBasis_apply,
    agree,←map_mul]
  exact tr (b i*b j)
section Both
variable (bf : Basis ι (Polynomial k) U) (bi : Basis ι (Polynomial k) V)
  (ff : ChartMap (k:=k) false U M) (fi : ChartMap (k:=k) true V M)
  (lf : IsChartLocalization false ff) (li : IsChartLocalization true fi)
private theorem free_expansion (i : ι) :
    (∑ j,freeTransition bf bi ff fi lf li j i • localFreeBasis false bf ff lf j)=localFreeBasis true bi fi li i := by
  let fin := localFreeBasis false bf ff lf
  let inf := localFreeBasis true bi fi li
  have coord : freeTransition bf bi ff fi lf li *ᵥ Pi.single i (1:Laurent k) = fin.equivFun (inf i) := by
    rw [freeTransition_mulVec]
    have same : inf.equivFun (inf i)=Pi.single i 1 := by
      funext j
      rw [Basis.equivFun_apply,Basis.repr_self]
      simp only [Finsupp.single_eq_pi_single]
    rw [←same,LinearEquiv.symm_apply_apply]
  have repr : ∀ j,freeTransition bf bi ff fi lf li j i=fin.equivFun (inf i) j := by
    rw [Matrix.mulVec_single_one] at coord
    exact fun j=>congrFun coord j
  rw [show (∑ j,freeTransition bf bi ff fi lf li j i • fin j)=(∑ j,fin.equivFun (inf i) j • fin j)
    from Finset.sum_congr rfl (fun j _=>congrArg (· • fin j) (repr j))]
  exact (fin.equivFun_symm_apply (fin.equivFun (inf i))).symm.trans (fin.equivFun.symm_apply_apply (inf i))
theorem free_trace_transition (r0 : U→+*M) (r1 : V→+*M)
    (h0 : ∀ x,ff x=r0 x) (h1 : ∀ x,fi x=r1 x) :
    invert ((Algebra.traceMatrix (Polynomial k) bi).det.toLaurent)=
      (freeTransition bf bi ff fi lf li).det^2*(Algebra.traceMatrix (Polynomial k) bf).det.toLaurent := by
  let G := freeTransition bf bi ff fi lf li
  let tr := Algebra.traceForm (Laurent k) M
  let X := Algebra.traceMatrix (Polynomial k) bf
  let Y := Algebra.traceMatrix (Polynomial k) bi
  let D := Algebra.traceMatrix (Laurent k) (localFreeBasis false bf ff lf)
  let N := Algebra.traceMatrix (Laurent k) (localFreeBasis true bi fi li)
  have change : N=G.transpose*D*G := by
    change tupleGram tr (localFreeBasis true bi fi li)=G.transpose*tupleGram tr (localFreeBasis false bf ff lf)*G
    rw [←tupleGram_change]
    exact congrArg (tupleGram tr) (funext fun i=>(free_expansion bf bi ff fi lf li i).symm)
  have detF : D.det=X.det.toLaurent := by
    have eq := congrArg Matrix.det (free_trace_matrix_on_torus false bf ff lf r0 h0)
    have det : (X.map (chartEmbedding false (k:=k))).det=chartEmbedding false X.det :=
      ((chartEmbedding false (k:=k)).toRingHom.map_det X).symm
    exact eq.symm.trans det
  have detI : N.det=invert Y.det.toLaurent := by
    have eq := congrArg Matrix.det (free_trace_matrix_on_torus true bi fi li r1 h1)
    have det : (Y.map (chartEmbedding true (k:=k))).det=chartEmbedding true Y.det :=
      ((chartEmbedding true (k:=k)).toRingHom.map_det Y).symm
    exact eq.symm.trans det
  change invert Y.det.toLaurent=G.det^2*X.det.toLaurent
  rw [←detI,change,det_mul,det_mul,det_transpose,detF]
  ring
end Both
#print axioms free_trace_transition
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameOverlapFreeTrace
