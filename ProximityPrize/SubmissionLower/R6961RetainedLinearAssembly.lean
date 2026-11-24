import ProximityPrize.SubmissionLower.R6961RetainedLinearSpecialization

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

namespace Lower6961.RetainedLinear
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate)
open RetainedShortening (Word)
open RetainedCompression (Curve ordinate parameter MarkedFiber PureNodes atNode view view_y)
open scoped Polynomial

abbrev Seed := Fn L

/-- Extend the scalar variable to its function field while keeping the
abscissa and ordinate as independent polynomial variables. -/
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

/-- Localizing at the nonzero scalar polynomials preserves irreducibility
when the ordinate degree is positive. -/
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

/-- Geometric linearity is expressed by splitting over the rational
abscissa field with algebraically closed scalar constants. -/
def GeometricallyLinear (P : Ordinate) : Prop :=
  (geometric (E:=AlgebraicClosure Seed) (toSeed P)).Splits

private theorem node_map (P : Ordinate) (i : I) :
    (toSeed P).map (evalRingHom (incl L (C (algebraMap K L (node i)))))=
    (atNode P i).map (incl L) := by
  apply Polynomial.ext
  intro j
  simp only [toSeed,atNode,coe_mapRingHom,coeff_map,coe_evalRingHom]
  exact Polynomial.eval_map_apply (incl L) _

/-- Geometrically linear components of the actual projected curve force
received-node purity. Embeddings of the arithmetic root field transfer
the received residue to every rational geometric branch. -/
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

end
end Lower6961.RetainedLinear
