import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import Mathlib.Algebra.Polynomial.FieldDivision

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

/-- A unit over an integral coefficient domain has one Laurent exponent
and a unit coefficient. -/
theorem laurent_unit_over_domain (f : LaurentPolynomial R) (unit : IsUnit f) :
    ∃ (c : R) (m : ℤ),IsUnit c ∧ f=LaurentPolynomial.C c*T m := by
  obtain ⟨u,rfl⟩ := unit
  obtain ⟨n,a,ea⟩ := LaurentPolynomial.exists_T_pow (u:LaurentPolynomial R)
  obtain ⟨l,b,eb⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹:LaurentPolynomial R)
  have ab : a*b=(Polynomial.X : R[X])^(n+l) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul,ea,eb,Polynomial.toLaurent_X_pow,mul_mul_mul_comm,Units.mul_inv,one_mul,←T_add]
    push_cast
    rfl
  obtain ⟨j,_,assoc⟩ := (dvd_prime_pow (Polynomial.prime_X (R:=R)) (n+l)).mp (show a∣_ from ⟨b,ab.symm⟩)
  obtain ⟨v,hv⟩ := assoc.symm
  obtain ⟨c,cu,cv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  have aa : a=(Polynomial.X : R[X])^j*Polynomial.C c := by rw [cv,hv]
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

/-- Change only scalar coefficients on the affine Laurent overlap. -/
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

@[simp] theorem laurentCoefficients_polynomial (f : R→+*S) (p : R[X]) :
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

@[simp] theorem laurentCoefficients_inverse (f : R→+*S) (p : R[X]) :
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

/-- Two actual principal generators on adjacent plane charts differ on
the overlap by a constant in the ground field and one abscissa exponent. -/
theorem plane_overlap_unit (δfin δinf : k[X][X])
    (glue : (Ideal.span {δfin.toLaurent} : Ideal (LaurentPolynomial k[X]))=
      Ideal.span {invert δinf.toLaurent}) :
    ∃ (c : k) (m : ℤ),c≠0 ∧
      δfin.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δinf.toLaurent := by
  have assoc : Associated (invert δinf.toLaurent) δfin.toLaurent :=
    Ideal.span_singleton_eq_span_singleton.mp glue.symm
  obtain ⟨u,hu⟩ := assoc
  obtain ⟨a,m,au,eq⟩ := laurent_unit_over_domain (u:LaurentPolynomial k[X]) u.isUnit
  obtain ⟨c,cu,hc⟩ := Polynomial.isUnit_iff.mp au
  refine ⟨c,m,cu.ne_zero,?_⟩
  rw [←hu,eq,←hc,mul_comm]

private theorem associated_constant {u v : K[X]} (h : Associated u v) :
    ∃ c : K, c≠0 ∧ u=Polynomial.C c*v := by
  obtain ⟨x,hx⟩ := h.symm
  obtain ⟨c,cu,eq⟩ := Polynomial.isUnit_iff.mp x.isUnit
  exact ⟨c,cu.ne_zero,by rw [←hx,eq,mul_comm]⟩

/-- The same overlap unit fixes the determinant exponent after every
coefficient specialization where the normalized discriminant is nonzero.
The orientation is `δfin = c·t^m·δinf(t⁻¹)`. -/
theorem overlap_transition_exponent (δfin δinf : k[X][X]) (c : k) (cn : c≠0) (m : ℤ)
    (glue : δfin.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δinf.toLaurent)
    (spec : k[X]→+*K) (nonzero : δfin.map spec≠0)
    (finDisc infDisc : K[X]) (hf : Associated finDisc (δfin.map spec))
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
