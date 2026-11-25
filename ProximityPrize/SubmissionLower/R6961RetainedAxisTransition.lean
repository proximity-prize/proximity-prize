import ProximityPrize.SubmissionLower.R6961MonicChartProbes
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import ProximityPrize.SubmissionLower.R6961RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960RetainedCrossingComparison
import Mathlib.RingTheory.Polynomial.Ideal
import ProximityPrize.SubmissionLower.R6960LineEulerFree

set_option Elab.async false

-- merged module R6961RetainedCrossingBasis
section Merged_R6961RetainedCrossingBasis

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedCrossingBasis
open Algebra Module
open scoped TensorProduct BigOperators

variable {A F E : Type*} [CommRing A]
  [Field F] [Algebra A F] [IsFractionRing A F] [Field E]
  [Algebra A E] [Algebra F E] [IsScalarTower A F E]

abbrev Order (A E : Type*) [CommRing A] [Field E] [Algebra A E] := integralClosure A E

/-- One denominator controls all coordinates of all integral elements. -/
theorem normal_frame (A F E : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra A E] [Algebra F E]
    [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ b : Basis (Fin (finrank F E)) F E, (∀ i, IsIntegral A (b i)) ∧
      ∃ d : A, d≠0 ∧ ∀ x : Order A E, ∀ i, ∃ c : A,
        algebraMap A F c=algebraMap A F d * b.repr (x:E) i := by
  classical
  obtain ⟨S,b,hb⟩:=FiniteDimensional.exists_is_basis_integral A F E
  let e := (Fintype.equivFin S).trans (finCongr (finrank_eq_card_basis b).symm)
  let B:=b.reindex e
  have ib (i) : IsIntegral A (B i) := by simpa [B] using hb (e.symm i)
  obtain ⟨d,nd,hd⟩:=exists_integral_multiples A F (Finset.univ.image B.traceDual)
  refine ⟨B,ib,d,nd,fun x i => ?_⟩
  have it:=isIntegral_trace (L:=F) ((hd (B.traceDual i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))).mul x.property)
  have eq : trace F E ((d • B.traceDual i)*(x:E))=algebraMap A F d*B.repr (x:E) i := by
    have co:=B.traceDual.traceDual_repr_apply (x:E) i
    rw [Basis.traceDual_traceDual,traceForm_apply] at co
    rw [smul_mul_assoc,←IsScalarTower.algebraMap_smul F,map_smul,smul_eq_mul,mul_comm (B.traceDual i),←co]
  exact IsIntegrallyClosed.isIntegral_iff.mp (eq ▸ it)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion in the integral basis and its cleared inverse, over the original order. -/
theorem frame_maps (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i)) (d : A)
    (coords : ∀ x : Order A E, ∀ i, ∃ c : A,
        algebraMap A F c=algebraMap A F d*b.repr (x:E) i) :
    ∃ toOrder : (ι→A) →ₗ[A] Order A E, ∃ back : Order A E →ₗ[A] (ι→A),
      (∀ i,toOrder (Pi.single i 1)=⟨b i,ib i⟩) ∧
      back.comp toOrder=d • LinearMap.id ∧ toOrder.comp back=d • LinearMap.id := by
  classical
  let inj:=IsFractionRing.injective A F
  choose c hc using coords
  let back : Order A E →ₗ[A] (ι→A) :=
    { toFun:=c
      map_add':=by
        intro u v; ext i; apply inj
        simp only [hc,map_add,Pi.add_apply,Subalgebra.coe_add,Finsupp.add_apply,mul_add]
      map_smul':=by
        intro r u; ext i; apply inj
        change algebraMap A F (c (r • u) i)=algebraMap A F (r*c u i)
        rw [hc,map_mul,hc]
        change _*b.repr (r • (u:E)) i=_
        rw [←IsScalarTower.algebraMap_smul F r (u:E),map_smul,Finsupp.smul_apply,smul_eq_mul]
        ring }
  let vec (i:ι) : Order A E := ⟨b i,ib i⟩
  let synth := (Pi.basisFun A ι).constr A vec
  have synth_eq (v : ι→A) : synth v=∑i,v i • vec i := by
    simp [synth,Basis.constr_apply_fintype]
  have std (i : ι) : synth (Pi.single i 1)=vec i := by
    rw [←Pi.basisFun_apply]
    exact Basis.constr_basis ..
  refine ⟨synth,back,std,?_,?_⟩
  · apply (Pi.basisFun A ι).ext
    intro i
    rw [Pi.basisFun_apply]
    change back (synth (Pi.single i 1))=d • Pi.single i 1
    rw [std]
    funext j
    apply inj
    change algebraMap A F (c (vec i) j)=algebraMap A F (d * (Pi.single i (1:A) : ι→A) j)
    rw [hc,map_mul]
    simp [vec,Basis.repr_self,Pi.single_apply,Finsupp.single_apply,eq_comm]
  · apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (synth (c u):E)=d • (u:E)
    rw [synth_eq,←IsScalarTower.algebraMap_smul F d (u:E)]
    push_cast
    calc ∑ i, c u i • (b i) = ∑ i, (algebraMap A F d*b.repr (u:E) i) • b i := by
           apply Finset.sum_congr rfl
           intro i _
           rw [←IsScalarTower.algebraMap_smul F, hc]
         _ = _ := by simp only [mul_smul,←Finset.smul_sum,b.sum_repr]

#print axioms normal_frame
#print axioms frame_maps

theorem specialized_basis (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i)) (d : A)
    (coords : ∀ x : Order A E, ∀ i, ∃ c : A,
        algebraMap A F c=algebraMap A F d*b.repr (x:E) i)
    (k : Type*) [Field k] [Algebra A k] (unit : algebraMap A k d≠0) :
    ∃ B : Basis ι k (k ⊗[A] Order A E), ∀ i,B i=1 ⊗ₜ[A] (⟨b i,ib i⟩ : Order A E) := by
  obtain ⟨front,back,standard,left,right⟩:=frame_maps b ib d coords
  let f:=front.baseChange k
  let g:=back.baseChange k
  have l (x) : g (f x)=algebraMap A k d • x := by
    have eq := congrArg (LinearMap.baseChange k) left
    rw [LinearMap.baseChange_comp,LinearMap.baseChange_smul,LinearMap.baseChange_id] at eq
    simpa [f,g,algebraMap_smul] using LinearMap.congr_fun eq x
  have r (x) : f (g x)=algebraMap A k d • x := by
    have eq := congrArg (LinearMap.baseChange k) right
    rw [LinearMap.baseChange_comp,LinearMap.baseChange_smul,LinearMap.baseChange_id] at eq
    simpa [f,g,algebraMap_smul] using LinearMap.congr_fun eq x
  let equiv := LinearEquiv.ofBijective f (show Function.Bijective f from ⟨
    fun x y eq => by
      have v := congrArg g eq; rw [l,l] at v
      exact (smul_right_injective _ unit) v,
    fun x => ⟨(algebraMap A k d)⁻¹ • g x,by rw [map_smul,r,inv_smul_smul₀ unit]⟩⟩)
  refine ⟨((Pi.basisFun A ι).baseChange k).map equiv,fun i=>?_⟩
  change f (((Pi.basisFun A ι).baseChange k) i)=_
  rw [Basis.baseChange_apply,Pi.basisFun_apply]
  change 1 ⊗ₜ[A] front (Pi.single i 1)=_
  rw [standard]

#print axioms specialized_basis
end Lower6961.RetainedCrossingBasis

end
end Merged_R6961RetainedCrossingBasis

-- merged module R6961RetainedCrossingTrace
section Merged_R6961RetainedCrossingTrace

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedCrossingBasis
open Algebra Module Matrix
open scoped TensorProduct BigOperators
variable {A F E k ι : Type*} [CommRing A] [Field F] [Field E] [Field k]
  [Algebra A F] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [Algebra A k]
  [Fintype ι] [DecidableEq ι]

private theorem specialized_coordinates (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i))
    (B : Basis ι k (k ⊗[A] Order A E)) (val : ∀ i,B i=1 ⊗ₜ[A] (⟨b i,ib i⟩ : Order A E))
    (d : A) (x : Order A E) (c : ι→A)
    (coord : ∀ i, algebraMap A F (c i)=algebraMap A F d*b.repr (x:E) i) (i : ι) :
    algebraMap A k d * B.repr (1 ⊗ₜ[A] x) i=algebraMap A k (c i) := by
  let v (i:ι) : Order A E := ⟨b i,ib i⟩
  have before : d • x=∑ i,c i • v i := by
    apply Subtype.ext
    change d • (x:E)=_
    push_cast
    rw [←IsScalarTower.algebraMap_smul F d (x:E)]
    calc _ = ∑ i,(algebraMap A F d*b.repr (x:E) i) • b i := by
               simp only [mul_smul,←Finset.smul_sum,b.sum_repr]
         _ = _ := by
               apply Finset.sum_congr rfl
               intro j _
               rw [←coord,algebraMap_smul]
  have after : algebraMap A k d • (1 ⊗ₜ[A] x) = ∑ j, algebraMap A k (c j) • B j := by
    simpa only [TensorProduct.tmul_sum,TensorProduct.tmul_smul,algebraMap_smul,val,v] using
      congrArg (fun y : Order A E => (1:k) ⊗ₜ[A] y) before
  simpa only [B.repr_self,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true] using congrArg (fun y => B.repr y i) after

theorem specialize_trace [IsDomain A] [IsFractionRing A F]
    (b : Basis ι F E) (ib : ∀ i,IsIntegral A (b i))
    (B : Basis ι k (k ⊗[A] Order A E)) (val : ∀ i,B i=1 ⊗ₜ[A] (⟨b i,ib i⟩ : Order A E))
    (d : A) (dn : algebraMap A k d≠0)
    (coords : ∀ x : Order A E, ∀ j, ∃ c : A,algebraMap A F c=algebraMap A F d*b.repr (x:E) j)
    (x : Order A E) (t : A) (ht : algebraMap A F t=trace F E x.val) :
    algebraMap A k t=trace k (k ⊗[A] Order A E) (1 ⊗ₜ[A] x) := by
  let v (i:ι) : Order A E := ⟨b i,ib i⟩
  choose C hc using fun i j=>coords (x*v i) j
  have before : d*t=∑ i,C i i := by
    apply IsFractionRing.injective A F
    rw [map_mul,ht,trace_eq_matrix_trace b,Matrix.trace,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Matrix.diag,Algebra.leftMulMatrix_eq_repr_mul,Subalgebra.coe_mul,v] using (hc i i).symm
  apply mul_left_cancel₀ dn
  rw [←map_mul,before,map_sum,trace_eq_matrix_trace B,Matrix.trace,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag,Algebra.leftMulMatrix_eq_repr_mul]
  change algebraMap A k (C i i)=algebraMap A k d*B.repr ((1 ⊗ₜ[A] x)*B i) i
  rw [val,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  exact (specialized_coordinates b ib B val d (x*v i) (C i) (hc i) i).symm

#print axioms specialize_trace
end Lower6961.RetainedCrossingBasis

end
end Merged_R6961RetainedCrossingTrace

-- merged module R6961RetainedGoodCrossing
section Merged_R6961RetainedGoodCrossing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedCrossingBasis
open Module Algebra Matrix Polynomial
open scoped TensorProduct BigOperators Polynomial

private theorem reduced_of_discriminant {k S ι : Type*} [Field k] [CommRing S] [Algebra k S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι k S) (nz : discr k b≠0) : IsReduced S := by
  have inj : Function.Injective (traceMatrix k b).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nz))
  constructor
  intro x nil
  apply b.equivFun.injective
  apply inj
  rw [map_zero,Matrix.mulVec_zero,traceMatrix_of_basis_mulVec]
  ext i
  exact (Algebra.isNilpotent_trace_of_isNilpotent (R:=k) ((Commute.all x (b i)).isNilpotent_mul_right nil)).eq_zero

/-- A single nonzero element of the plane cuts out all places where this integral
frame or its trace determinant can fail. It works for point and generic-line fibres. -/
theorem good_open (A F E : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra A E] [Algebra F E]
    [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ guard : A, guard≠0 ∧ ∀ (k : Type) [Field k] (φ : A →+* k), φ guard≠0 →
      letI := φ.toAlgebra
      Nonempty (Basis (Fin (finrank F E)) k (k ⊗[A] Order A E)) ∧ IsReduced (k ⊗[A] Order A E) := by
  classical
  obtain ⟨b,ib,d,dn,coords⟩:=normal_frame A F E
  have tr (i j) : ∃ t:A,algebraMap A F t=trace F E (b i*b j) :=
    IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace ((ib i).mul (ib j)))
  choose entries spec using tr
  let G : Matrix (Fin (finrank F E)) (Fin (finrank F E)) A := entries
  have generic : G.map (algebraMap A F) = traceMatrix F b := by
    ext i j; exact spec i j
  have disc : G.det≠0 := by
    intro eq
    apply discr_not_zero_of_basis F b
    rw [discr_def,←generic]
    exact ((algebraMap A F).map_det G).symm.trans (eq ▸ map_zero _)
  refine ⟨d*G.det,mul_ne_zero dn disc,fun k _ φ good => ?_⟩
  let := φ.toAlgebra
  rw [map_mul] at good
  have ud : algebraMap A k d≠0 := left_ne_zero_of_mul good
  obtain ⟨B,specB⟩:=specialized_basis b ib d coords k ud
  refine ⟨⟨B⟩,reduced_of_discriminant B ?_⟩
  have eq : G.map φ=traceMatrix k B := by
    ext i j
    rw [Matrix.map_apply,traceMatrix_apply,traceForm_apply,specB,specB,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
    exact specialize_trace b ib B specB d ud coords
      (⟨b i,ib i⟩*⟨b j,ib j⟩) (entries i j) (spec i j)
  rw [discr_def,←eq]
  exact (φ.map_det G) ▸ right_ne_zero_of_mul good

open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open MonicFourChartDescent (baseChart)
open MonicChartProbes (planeEquiv)
open scoped Lower6961.MonicChartProbes
open RetainedCompression (Curve ordinate view)
open Lower6961.MonicChart (root_finrank)

private theorem away_coordinate (P : (Polynomial L)) (pn : P≠0) :
    ∃ a:L, a≠0 ∧ P.eval a≠0 := by
  classical
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 P.roots.toFinset)
  exact ⟨a,fun z=>ha (z ▸ Finset.mem_insert_self ..),
    fun v=>ha (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((mem_roots pn).mpr v)))⟩

/-- Choose a transverse crossing at finite nonzero coordinates. The normalized point
fibre and the generic points of both lines are reduced, of the original ordinate rank. -/
theorem actual_good_lines {E : Type} [Field E] [Algebra ChartField E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<K1.p)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    let A:=baseChart (false,false)
    let eqv:= (planeEquiv (false,false)).symm.toRingHom
    ∃ x z:L, x≠0 ∧ z≠0 ∧ ∀ (k : Type) [Field k] (φ : A →+* k),
      ((RingHom.ker φ) ≤ RingHom.ker (((evalRingHom x).comp (mapRingHom (evalRingHom z))).comp eqv)) →
      letI := φ.toAlgebra
      Nonempty (Basis (Fin (f.degreeOf ordinate)) k (k ⊗[A] Order A E)) ∧
        IsReduced (k ⊗[A] Order A E) := by
  classical
  let A:=baseChart (false,false)
  let : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hi basis root
  let : Algebra (Polynomial Scalar) E := ((algebraMap ChartField E).comp (algebraMap (Polynomial Scalar) ChartField)).toAlgebra
  let : IsScalarTower (Polynomial Scalar) ChartField E := IsScalarTower.of_algebraMap_eq
    (R:=(Polynomial Scalar)) (S:=ChartField) (A:=E) fun _=>rfl
  have deg : finrank ChartField E=f.degreeOf ordinate := Lower6961.MonicChart.root_finrank f ir lo basis
    (by rw [aeval_map_algebraMap] at root; exact root)
  obtain ⟨g,nz,openSet⟩:=good_open A ChartField E
  let P := (planeEquiv (false,false)).symm g
  have pn : P≠0 := (map_ne_zero_iff _ (planeEquiv (false,false)).symm.injective).mpr nz
  obtain ⟨z,zn,goodZ⟩:=away_coordinate P.leadingCoeff (leadingCoeff_ne_zero.mpr pn)
  let Q := P.map (evalRingHom z)
  have qn : Q≠0 := by
    intro zero
    have van:=congrArg (fun h:(Polynomial L)=>h.coeff P.natDegree) zero
    exact goodZ (by simpa only [Q,coeff_map,coeff_natDegree,coeff_zero,coe_evalRingHom] using van)
  obtain ⟨x,xn,goodX⟩:=away_coordinate Q qn
  refine ⟨x,z,xn,zn,fun k _ φ le => ?_⟩
  have pass : φ g≠0 := by
    intro zero
    have bad:=le (RingHom.mem_ker.mpr zero)
    exact goodX bad
  simpa only [deg] using openSet k φ pass

#print axioms good_open
#print axioms actual_good_lines
end Lower6961.RetainedCrossingBasis

end
end Merged_R6961RetainedGoodCrossing

-- merged module R6961RetainedAxisResidues
section Merged_R6961RetainedAxisResidues

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedRestrictionTorus
open K1_14 (L)
open Lower6960.ChartSections (Chart)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests MonicChartLaurent
open Polynomial
open Lower6961.RetainedRestrictionTorus (linear)
open scoped Polynomial

def coordinate (zAxis : Bool) : ChartField := if zAxis then scalarCoordinate else RatFunc.X
def axisBit (s : Chart) (zAxis : Bool) : Bool := if zAxis then s.2 else s.1
def localFrame (s : Chart) (zAxis : Bool) : ChartField :=
  if axisBit s zAxis then coordinate zAxis else 1
def divisor (zAxis : Bool) (c:L) : ChartField := coordinate zAxis-constants c

theorem coord_ne (j : Bool) : coordinate j≠0 := by cases j <;> simp [coordinate,scalar_ne,RatFunc.X_ne_zero]
theorem localFrame_ne (s : Chart) (j : Bool) : localFrame s j≠0 := by
  unfold localFrame; split <;> first | exact one_ne_zero | exact coord_ne _

theorem divisor_ne (j : Bool) (c:L) : divisor j c≠0 := by
  have nz:RetainedLineRestriction.lines c c≠0 := by
    have := MonicChartProbes.planeMap_injective (false,false)
    let a:Lower6960.PlaneConstants.Plane L:=Polynomial.X-C (C c)
    let b:Lower6960.PlaneConstants.Plane L:=C (Polynomial.X-C c)
    have h:= (map_ne_zero_iff _ this).mpr (mul_ne_zero (X_sub_C_ne_zero (C c))
      (C_ne_zero.mpr (X_sub_C_ne_zero c)))
    simpa [RetainedLineRestriction.lines,chartCoordinate] using h
  cases j
  · exact left_ne_zero_of_mul nz
  · exact right_ne_zero_of_mul nz

theorem xcut_value (s : Chart) (c:L) : (xcut s c : ChartField) = divisor false c/localFrame s false := by
  change planeMap s ((Lower6961.RetainedRestrictionTorus.linear s.1 c).map C)=_
  unfold Lower6961.RetainedRestrictionTorus.linear
  by_cases h:s.1=true <;> simp [h,map_sub,map_mul,divisor,localFrame,coordinate,axisBit,
    chartCoordinate,sub_mul,RatFunc.X_ne_zero,div_eq_mul_inv]
theorem zcut_value (s : Chart) (c:L) : (zcut s c : ChartField) = divisor true c/localFrame s true := by
  change planeMap s (C (Lower6961.RetainedRestrictionTorus.linear s.2 c))=_
  unfold Lower6961.RetainedRestrictionTorus.linear
  by_cases h:s.2=true <;> simp [h,map_sub,map_mul,divisor,localFrame,coordinate,axisBit,
    chartCoordinate,sub_mul,scalar_ne,div_eq_mul_inv]

theorem base_torus (s : Chart) : baseChart s≤torus :=
  (into_cleared _ (edge s s)).trans (to_torus s s)
theorem torus_coordinate (j : Bool) (b : Bool) : chartCoordinate b (coordinate j)∈torus := by
  apply base_torus (b,b)
  cases j <;> apply Subring.subset_closure <;> simp [coordinate]
theorem torus_frame (s : Chart) (j : Bool) : localFrame s j∈torus ∧ (localFrame s j)⁻¹∈torus := by
  unfold localFrame
  split
  · exact ⟨torus_coordinate j false,torus_coordinate j true⟩
  · simp
theorem chart_constant (s : Chart) (c:L) : constants c∈baseChart s :=
  Subring.subset_closure (Or.inl ⟨c,rfl⟩)

variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def Congruent (j : Bool) (c : L) (u v : E) : Prop :=
  ∃ r : E, IsIntegral torus r ∧ u-v=ι (divisor j c)*r

theorem Congruent.refl (j : Bool) (c : L) (u : E) : Congruent j c u u := ⟨0,isIntegral_zero,by simp⟩
theorem Congruent.symm {j c} {u v:E} (h : Congruent j c u v) : Congruent j c v u := by
  obtain ⟨r,hr,eq⟩:=h; exact ⟨-r,hr.neg,by rw [mul_neg,←eq,neg_sub]⟩
theorem Congruent.trans {j c} {u v w:E} (h : Congruent j c u v) (h' : Congruent j c v w) :
    Congruent j c u w := by
  obtain ⟨a,ia,eq⟩:=h; obtain ⟨b,ib,eq'⟩:=h'
  exact ⟨a+b,ia.add ib,by rw [mul_add,←eq,←eq']; abel⟩
theorem Congruent.sub {j c} {u v w h:E} (a : Congruent j c u v) (b : Congruent j c w h) :
    Congruent j c (u-w) (v-h) := by
  obtain ⟨r,ir,ea⟩:=a; obtain ⟨q,iq,eb⟩:=b
  exact ⟨r-q,ir.sub iq,by rw [mul_sub,←ea,←eb]; abel⟩

private theorem local_int {s : Chart} {a : ChartField} (ha:a∈baseChart s) : IsIntegral (baseChart s) (ι a : E) :=
  isIntegral_algebraMap (x:=(⟨a,ha⟩:baseChart s))
private theorem torus_int {a : ChartField} (ha:a∈torus) : IsIntegral torus (ι a : E) :=
  isIntegral_algebraMap (x:=(⟨a,ha⟩:torus))

/-- A transition regular on an overlap that inverts only the transverse coordinate
has a regular representative on the original chart after taking the line residue. -/
theorem line_representative (j : Bool) (c : L) (nc : c≠0) (s t : Chart)
    (parallel : axisBit s (!j)=axisBit t (!j)) (y : E) (regular : IsIntegral (overlapRing s t) y) :
    ∃ v:E,IsIntegral (baseChart s) v ∧ Congruent j c y v := by
  let A:=baseChart s
  let g:=edge s t
  let val : L:=if axisBit s j=axisBit t j then 1 else if axisBit s j then c⁻¹ else c
  have vn : val≠0 := by dsimp only [val]; split <;> first | exact one_ne_zero | split <;> simp [nc]
  have valMem:=chart_constant s val
  let cv:A:=⟨constants val,valMem⟩
  obtain ⟨n,cleared⟩:=localize_integral A _ g (edge_ne s t) le_rfl y regular
  obtain ⟨q,factor⟩: g-cv∣g^n-cv^n := sub_dvd_pow_sub_pow _ _ _
  have unitval : ι (constants val)≠(0:E) :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr ((map_ne_zero_iff _ constants.injective).mpr vn)
  have step : ∃ r : ChartField,r∈torus ∧ boundary s t-constants val=divisor j c*r := by
    by_cases same : axisBit s j=axisBit t j
    · refine ⟨0,torus.zero_mem,?_⟩
      cases j <;> simp_all [boundary,axisBit,val]
    · have eq : boundary s t=chartCoordinate (axisBit s j) (coordinate j) := by
        cases j <;> simp_all [axisBit,boundary,coordinate]
      rw [eq]
      have vv : val = if axisBit s j then c⁻¹ else c := by simp only [val,same,ite_false]
      rw [vv]
      by_cases neg : axisBit s j=true
      · refine ⟨-(coordinate j)⁻¹*constants c⁻¹,torus.mul_mem (torus.neg_mem (torus_coordinate j true))
          (base_torus s (chart_constant s c⁻¹)),?_⟩
        simp only [neg,ite_true,chartCoordinate,map_inv₀,divisor]
        field_simp [coord_ne j, (map_ne_zero_iff _ constants.injective).mpr nc]
        <;> ring
      · exact ⟨1,torus.one_mem,by simp [neg,chartCoordinate,divisor]⟩
  obtain ⟨r,ir,eq⟩:=step
  let b:=ι (constants val)
  let G:=ι (boundary s t)
  have inv : IsIntegral A (b⁻¹) := by
    have h : IsIntegral A (ι (constants val⁻¹)):=local_int (chart_constant s val⁻¹)
    simpa [b] using h
  refine ⟨b⁻¹^n*(G^n*y),(inv.pow n).mul cleared,?_⟩
  have it:= order_mono (to_torus s t) regular
  have iq : IsIntegral torus (ι (q:ChartField)) := torus_int (base_torus s q.property)
  refine ⟨-(b⁻¹^n*(ι r*ι (q:ChartField))*y),
    (((order_mono (base_torus s) (inv.pow n)).mul ((torus_int ir).mul iq)).mul it).neg,?_⟩
  have eq' : G-b=ι (divisor j c)*ι r := by simpa only [map_sub,map_mul,G,b] using congrArg ι eq
  have powers : G^n-b^n=(G-b)*ι (q:ChartField) := by
    have mapped:=congrArg (fun v:A=>ι (v:ChartField)) factor
    change ι ((boundary s t)^n-(constants val)^n) = ι ((boundary s t-constants val)*(q:ChartField)) at mapped
    simpa only [map_pow,map_sub,map_mul,G,b] using mapped
  have cancel : b⁻¹^n*b^n=1 := by rw [←mul_pow,inv_mul_cancel₀ unitval,one_pow]
  calc y-b⁻¹^n*(G^n*y) = -(b⁻¹^n*((G^n-b^n)*y)) := by linear_combination -y*cancel
       _ = _ := by rw [powers,eq']; ring

#print axioms line_representative
end Lower6961.RetainedRestrictionTorus

end
end Merged_R6961RetainedAxisResidues

-- merged module R6961RetainedPairedResidues
section Merged_R6961RetainedPairedResidues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6961.RetainedRestrictionTorus
open Lower6961.MonicChart (ChartField)
open K1_14 (L)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent ChartOverlapTests Polynomial
open RetainedCompression (Curve ordinate view height heightCap MarkedBand)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def Matched (x z : L) (u v:E) : Prop := ∃ a b:E,IsIntegral torus a ∧ IsIntegral torus b ∧
  u-v=ι (divisor false x)*a+ι (divisor true z)*b

theorem frame_integral (s : Chart) (j : Bool) :
    IsIntegral torus (ι (localFrame s j) : E) ∧ IsIntegral torus (ι (localFrame s j)⁻¹ : E) := by
  have p:=torus_frame s j
  exact ⟨isIntegral_algebraMap (x:=(⟨_,p.1⟩:torus)),isIntegral_algebraMap (x:=(⟨_,p.2⟩:torus))⟩

private theorem base_x (s : Chart) (x:L) : algebraMap (baseChart s) E (xcut s x) =
    ι (divisor false x)/ι (localFrame s false) := by
  change ι ((xcut s x):ChartField)=_
  rw [xcut_value,map_div₀]
private theorem base_z (s : Chart) (z:L) : algebraMap (baseChart s) E (zcut s z) =
    ι (divisor true z)/ι (localFrame s true) := by
  change ι ((zcut s z):ChartField)=_
  rw [zcut_value,map_div₀]

private theorem glue (s : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (u v:E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v) (h:Matched x z u v) :
    ∃ y:E,IsIntegral (baseChart s) y ∧ Congruent false x u y ∧ Congruent true z v y := by
  obtain ⟨a,b,ia,ib,eq⟩:=h
  have fn (j : Bool) : (ι (localFrame s j) : E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s j)
  have m:=lift_on_chart s x z nx nz u v hu hv ⟨ι (localFrame s false)*a,ι (localFrame s true)*b,
    (frame_integral s false).1.mul ia,(frame_integral s true).1.mul ib,by
      rw [base_x,base_z,eq]; field_simp [fn]⟩
  obtain ⟨y,a',b',hy,ia',ib',dx,dz⟩:=m
  refine ⟨y,hy,⟨ι ((localFrame s false)⁻¹)*a',
    (frame_integral s false).2.mul (order_mono (base_torus s) ia'),?_⟩,Congruent.symm
      ⟨ι ((localFrame s true)⁻¹)*b',(frame_integral s true).2.mul (order_mono (base_torus s) ib'),?_⟩⟩
  · rw [dx,base_x,map_inv₀,div_eq_mul_inv,mul_assoc]
  · rw [dz,base_z,map_inv₀,div_eq_mul_inv,mul_assoc]

private theorem product_residue [FiniteDimensional ChartField E]
    (s t : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (v:E)
    (reg : IsIntegral (overlapRing s t) v) (vx : Congruent false x v 0) (vz : Congruent true z v 0) :
    ∃ r:E, IsIntegral (overlapRing s t) r ∧
      v=ι (RetainedLineRestriction.lines x z / frame 1 1 s)*r := by
  obtain ⟨a,ia,ea⟩:=vx; obtain ⟨b,ib,eb⟩:=vz
  rw [sub_zero] at ea eb
  let Xv:=ι (divisor false x)
  let Zv:=ι (divisor true z)
  let P:=ι (localFrame s false)
  let Q:=ι (localFrame s true)
  have mne (p:ChartField) (pn:p≠0) : (ι p:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr pn
  have xn : Xv≠0:=mne _ (divisor_ne false x)
  have zn : Zv≠0:=mne _ (divisor_ne true z)
  have pn : P≠0:=mne _ (localFrame_ne s false)
  have qn : Q≠0:=mne _ (localFrame_ne s true)
  let r:=P*Q*v/(Xv*Zv)
  have xeq : algebraMap (baseChart s) E (xcut s x)*r=Q*b := by
    rw [base_x]; change Xv/P*(P*Q*v/(Xv*Zv))=Q*b
    change v=Zv*b at eb
    rw [eb]; field_simp
  have zeq : algebraMap (baseChart s) E (zcut s z)*r=P*a := by
    rw [base_z]; change Zv/Q*(P*Q*v/(Xv*Zv))=P*a
    change v=Xv*a at ea
    rw [ea]; field_simp
  have both : algebraMap (baseChart s) E (xcut s x*zcut s z)*r=v := by
    rw [map_mul,base_x,base_z]; change Xv/P*(Zv/Q)*(P*Q*v/(Xv*Zv))=v
    field_simp
  refine ⟨r,cancel_both s t x z nx nz r (both ▸ reg)
    (xeq ▸ (frame_integral s true).1.mul ib) (zeq ▸ (frame_integral s false).1.mul ia),?_⟩
  have e : frame 1 1 s=localFrame s false*localFrame s true := by simp [frame,localFrame,axisBit,coordinate]
  rw [e,map_div₀,map_mul]
  rw [RetainedLineRestriction.lines,map_mul]
  change v=(Xv*Zv)/(P*Q)*(P*Q*v/(Xv*Zv))
  field_simp

def reference (j bit : Bool) : Chart := if j then (bit,false) else (false,bit)

def LineData (j : Bool) (c:L) (u:Chart→E) (v:Bool→E) : Prop :=
  (∀ b, IsIntegral (baseChart (reference j b)) (v b)) ∧
  Congruent j c (u (false,false)-u (reference j true)) (v false-v true)

private theorem lift_axis (j : Bool) (c:L) (nc:c≠0) (u:Chart→E) (v:Bool→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (data : LineData j c u v) (s:Chart) :
    ∃ w:E,IsIntegral (baseChart s) w ∧ Congruent j c (u s-(u (false,false)-v false)) w := by
  let bit:=axisBit s (!j)
  let t:=reference j bit
  have parallel : axisBit s (!j)=axisBit t (!j) := by cases j <;> simp [bit,t,reference,axisBit]
  have r := (reg s t).add (order_mono (chart_cover s t) (data.1 bit))
  obtain ⟨w,hw,cw⟩:=line_representative j c nc s t parallel (u s-u t+v bit) r
  refine ⟨w,hw,Congruent.trans ?_ cw⟩
  have shared : Congruent j c (u (false,false)-u t) (v false-v bit) := by
    cases h:bit with
    | false => have t0:t=(false,false) := by cases j <;> simp [t,h,reference]
               rw [t0,sub_self,sub_self]; exact Congruent.refl j c 0
    | true => simpa only [t,h] using data.2
  obtain ⟨d,id,eq⟩:=shared.symm
  exact ⟨d,id,by rw [←eq]; abel⟩

/-- Only two transition differences and one crossing value are needed to detect an
untwisted obstruction on the original four normalized charts. -/
theorem split_of_paired_data (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) (u:Chart→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (v w:Bool→E)
    (dv : LineData false x u v) (dw : LineData true z u w) (joined : Matched x z (v false) (w false)) :
    ∃ c:E, Correction 0 0 u c := by
  let : FiniteDimensional ChartField E := basis.finite
  choose a ia ca using lift_axis false x nx u v reg dv
  choose b ib cb using lift_axis true z nz u w reg dw
  obtain ⟨h₁,h₂,ih₁,ih₂,joint⟩:=joined
  have m (s:Chart) : Matched x z (a s) (b s) := by
    obtain ⟨p,ip,ep⟩:=ca s
    obtain ⟨q,iq,eq⟩:=cb s
    refine ⟨h₁-p,h₂+q,ih₁.sub ip,ih₂.add iq,?_⟩
    rw [mul_sub,mul_add]
    linear_combination joint-ep+eq
  choose l il ax az using fun s=>glue s x z nx nz (a s) (b s) (ia s) (ib s) (m s)
  have residual (s t : Chart) (j:Bool) (d:L) (y:E) (lift:∀ i,Congruent j d (u i-y) (l i)) :
      Congruent j d ((u s-u t)-(l s-l t)) 0 := by
    obtain ⟨r,hr,eq⟩:=(lift s).sub (lift t)
    refine ⟨r,hr,?_⟩
    rw [sub_zero,←eq]; abel
  have restriction (s t : Chart) := product_residue s t x z nx nz ((u s-u t)-(l s-l t))
    ((reg s t).sub ((order_mono (into_cleared _ (edge s t)) (il s)).sub (order_mono (chart_cover s t) (il t))))
    (residual s t _ _ _ (fun i=>(ca i).trans (ax i))) (residual s t _ _ _ (fun i=>(cb i).trans (az i)))
  obtain ⟨p,ip,eq⟩:=RetainedLineRestriction.split_of_split_on_lines B f ir lo hi bounded basis root x z
    (fun s t=>u s-u t) (fun _ _ _=>by abel) l il restriction
  refine ⟨u (false,false)-p (false,false),fun s=>?_⟩
  have id : u s-(u (false,false)-p (false,false))=p s := by linear_combination eq s (false,false)
  simpa [id,frame] using ip s

#print axioms split_of_paired_data
end Lower6961.RetainedRestrictionTorus

end
end Merged_R6961RetainedPairedResidues

-- merged module R6961RetainedSurfaceClass
section Merged_R6961RetainedSurfaceClass

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedSurfaceClass
open Lower6960.ChartSections (Chart)
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6961.MonicChartLaurent

variable (E : Type) [Field E] [Algebra ChartField E]
abbrev Tor := integralClosure torus E

private def constantsTor : L →+* Tor E :=
  ((algebraMap (↥torus) (Tor E)).comp (constants.codRestrict torus
    (fun c=>base_torus (false,false) (chart_constant _ c))))
scoped instance constantAlgebra : Algebra L (Tor E) := (constantsTor E).toAlgebra
open scoped Lower6961.RetainedSurfaceClass

private def scalar (a:ChartField) (reg:a∈torus) : Tor E :=
  algebraMap (↥torus) (Tor E) ⟨a,reg⟩

def cut (j : Bool) (c:L) : Tor E := scalar E (divisor j c) (torus.sub_mem
  (torus_coordinate j false) (base_torus (false,false) (chart_constant _ c)))

def axisIdeal (j:Bool) (c:L) : Ideal (Tor E) := Ideal.span {cut E j c}
abbrev Axis (j:Bool) (c:L) := (Tor E) ⧸ axisIdeal E j c
abbrev Crossing (x z:L) := Tor E ⧸ (axisIdeal E false x ⊔ axisIdeal E true z)
abbrev red (j:Bool) (c:L) : Tor E →ₗ[L] Axis E j c :=
  (Ideal.Quotient.mkₐ L (axisIdeal E j c)).toLinearMap

def crossingX (x z:L) : Axis E false x →ₗ[L] Crossing E x z :=
  (Ideal.Quotient.factorₐ L (show axisIdeal E false x ≤ axisIdeal E false x ⊔ axisIdeal E true z from le_sup_left)).toLinearMap
def crossingZ (x z:L) : Axis E true z →ₗ[L] Crossing E x z :=
  (Ideal.Quotient.factorₐ L (show axisIdeal E true z ≤ axisIdeal E false x ⊔ axisIdeal E true z from le_sup_right)).toLinearMap

def chartSpace (s:Chart) : Submodule L (Tor E) where
  carrier:={u | IsIntegral (baseChart s) (u:E)}
  zero_mem' := isIntegral_zero
  add_mem' a b:=a.add b
  smul_mem' r _ hu:=
    (isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant s r⟩:baseChart s))).mul hu

def chartImage (j:Bool) (c:L) (bit:Bool) :=
  (chartSpace E (reference j bit)).map (red E j c)

def difference (j:Bool) (c:L) :
    (chartImage E j c false × chartImage E j c true) →ₗ[L] Axis E j c :=
  (chartImage E j c false).subtype.coprod (-(chartImage E j c true).subtype)

def evalX (x z:L) := (crossingX E x z).comp
  ((chartImage E false x false).subtype.comp (LinearMap.fst L (chartImage E false x false) (chartImage E false x true)))
def evalZ (x z:L) := (crossingZ E x z).comp
  ((chartImage E true z false).subtype.comp (LinearMap.fst L (chartImage E true z false) (chartImage E true z true)))
abbrev Paired (x z:L) := (Axis E false x × Axis E true z) ⧸
  Lower6960.RetainedNodalIndex.boundaries (difference E false x) (difference E true z) (evalX E x z) (evalZ E x z)

def potentials : Submodule L (Chart→Tor E) where
  carrier := {u | ∀ s t, IsIntegral (overlapRing s t) ((u s:E)-(u t:E))}
  zero_mem' := fun s t=>by simpa using (isIntegral_zero (B:=E) (R:=overlapRing s t))
  add_mem' {u v} hu hv s t := by
    change IsIntegral _ (((u s:E)+v s)-((u t:E)+v t))
    convert (hu s t).add (hv s t) using 1 <;> abel
  smul_mem' r u hu s t := by
    change IsIntegral _ ((algebraMap ChartField E (constants r))*(u s:E)-(algebraMap ChartField E (constants r))*(u t:E))
    rw [←mul_sub]
    exact (isIntegral_algebraMap (A:=E) (x:=(⟨constants r,into_cleared _ (edge s t) (chart_constant s r)⟩:overlapRing s t))).mul (hu s t)

def coboundaries : Submodule L (potentials E) where
  carrier := {u | ∃ c:E, ∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)}
  zero_mem' := ⟨0,fun s=>by simpa using (isIntegral_zero (B:=E) (R:=baseChart s))⟩
  add_mem' {u v} hu hv := by
    obtain ⟨c,hc⟩:=hu; obtain ⟨d,hd⟩:=hv
    refine ⟨c+d,fun s=>?_⟩
    change IsIntegral _ (((u.1 s:E)+v.1 s)-(c+d))
    convert (hc s).add (hd s) using 1 <;> abel
  smul_mem' r u hu := by
    obtain ⟨c,hc⟩:=hu
    let scalar:=algebraMap ChartField E (constants r)
    refine ⟨scalar*c,fun s=>?_⟩
    change IsIntegral _ (scalar*(u.1 s:E)-scalar*c)
    rw [←mul_sub]
    exact (isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant s r⟩:baseChart s))).mul (hc s)

private def atChart (s:Chart) : potentials E→ₗ[L]Tor E :=
  (LinearMap.proj s).comp (potentials E).subtype
def rawMap (x z:L) : potentials E →ₗ[L] Paired E x z :=
  let lines:=(red E false x ∘ₗ (atChart E (false,false)-atChart E (reference false true))).prod
    (red E true z ∘ₗ (atChart E (false,false)-atChart E (reference true true)))
  (Lower6960.RetainedNodalIndex.boundaries (difference E false x) (difference E true z) (evalX E x z) (evalZ E x z)).mkQ.comp lines

private theorem raw_zero (x z:L) (u:potentials E) : rawMap E x z u=0 ↔
    ∃ v:Bool→Tor E, ∃ w:Bool→Tor E,
      (∀ b,IsIntegral (baseChart (reference false b)) (v b:E)) ∧
      (∀ b,IsIntegral (baseChart (reference true b)) (w b:E)) ∧
      red E false x (u.1 (false,false)-u.1 (reference false true))=red E false x (v false-v true) ∧
      red E true z (u.1 (false,false)-u.1 (reference true true))=red E true z (w false-w true) ∧
      (Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z)) (v false) =
        Ideal.Quotient.mk _ (w false) := by
  rw [show rawMap E x z u=0 ↔ _ from Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,eq,edge⟩
    obtain ⟨v0,iv0,h0⟩:=a.property
    obtain ⟨v1,iv1,h1⟩:=b.property
    obtain ⟨w0,iw0,g0⟩:=c.property
    obtain ⟨w1,iw1,g1⟩:=d.property
    let v (i:Bool):Tor E:=if i then v1 else v0
    let w (i:Bool):Tor E:=if i then w1 else w0
    refine ⟨v,w,(fun i=>by cases i <;> first | exact iv0 | exact iv1),
      (fun i=>by cases i <;> first | exact iw0 | exact iw1),?_,?_,?_⟩
    · change _=red E false x (v0-v1)
      rw [map_sub (red E false x) v0 v1,h0,h1]
      have e:= (congrArg Prod.fst edge).symm
      change red E false x (u.1 (false,false)-u.1 (reference false true))=a.1+ -b.1 at e
      simpa only [sub_eq_add_neg] using e
    · change _=red E true z (w0-w1)
      rw [map_sub (red E true z) w0 w1,g0,g1]
      have e:= (congrArg Prod.snd edge).symm
      change red E true z (u.1 (false,false)-u.1 (reference true true))=c.1+ -d.1 at e
      simpa only [sub_eq_add_neg] using e
    · change crossingX E x z a.1+ -(crossingZ E x z c.1)=0 at eq
      rw [←h0,←g0] at eq
      change (Ideal.Quotient.mk _ v0)+ -(Ideal.Quotient.mk _ w0)=0 at eq
      rw [←sub_eq_add_neg] at eq
      exact sub_eq_zero.mp eq
  · rintro ⟨v,w,iv,iw,ex,ez,node⟩
    let a (i:Bool): chartImage E false x i:=⟨_,⟨v i,iv i,rfl⟩⟩
    let b (i:Bool): chartImage E true z i:=⟨_,⟨w i,iw i,rfl⟩⟩
    refine ⟨((a false,a true),(b false,b true)),?_,?_⟩
    · change Ideal.Quotient.mk _ (v false)+ -Ideal.Quotient.mk _ (w false)=0
      rw [node,add_neg_cancel]
    · apply Prod.ext
      · change red E false x (v false)+ -(red E false x (v true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ex.symm
      · change red E true z (w false)+ -(red E true z (w true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ez.symm

theorem congr_of_eq (j c) (a b:Tor E) (eq : red E j c a=red E j c b) :
    Congruent j c (a:E) (b:E) := by
  obtain ⟨r,hr⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp eq)
  exact ⟨r,r.property,congrArg Subtype.val hr⟩

private theorem matched_of_eq (x z:L) (a b:Tor E)
    (eq : Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z) a=Ideal.Quotient.mk _ b) :
    Matched x z (a:E) (b:E) := by
  obtain ⟨u,hu,v,hv,l⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq.mp eq)
  obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton.mp hv
  exact ⟨r,t,r.property,t.property,congrArg Subtype.val l.symm⟩

open RetainedCompression (Curve ordinate view height heightCap MarkedBand)

/-- The actual bounded cover's untwisted obstruction space embeds in the quotient
formed by the two torus fibres and a single shared crossing. -/
theorem restriction_kernel (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) :
    (rawMap E x z).ker=coboundaries E := by
    ext u
    change rawMap E x z u=0 ↔ ∃ c:E,∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)
    rw [raw_zero]
    constructor
    · rintro ⟨v,w,iv,iw,ex,ez,node⟩
      have r:=split_of_paired_data B f ir lo hi bounded basis root x z nx nz
        (fun s=>(u.1 s:E)) u.property (fun b=>(v b:E)) (fun b=>(w b:E))
        ⟨iv,congr_of_eq E false x _ _ ex⟩ ⟨iw,congr_of_eq E true z _ _ ez⟩
        (matched_of_eq E x z _ _ node)
      obtain ⟨c,hc⟩:=r
      exact ⟨c,fun s=>by simpa [frame] using hc s⟩
    · rintro ⟨c,hc⟩
      have ic : IsIntegral torus c := by
        have ii:=(u.1 (false,false)).property.sub (order_mono (base_torus (false,false)) (hc (false,false)))
        simpa only [sub_sub_cancel] using ii
      let ct : Tor E:=⟨c,ic⟩
      let v (j b:Bool):Tor E:=u.1 (reference j b)-ct
      have start (j:Bool) : reference j false=(false,false) := by cases j <;> rfl
      refine ⟨v false,v true,(fun b=>hc _),(fun b=>hc _),?_,?_,?_⟩
      · apply congrArg (red E false x); simp only [v,start]; abel
      · apply congrArg (red E true z); simp only [v,start]; abel
      · rfl
#print axioms restriction_kernel
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedSurfaceClass

-- merged module R6961RetainedCrossingComparison
section Merged_R6961RetainedCrossingComparison

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6960.ChartSections (Chart)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests RetainedRestrictionTorus
open Polynomial Module Algebra
open scoped Lower6961.RetainedSurfaceClass Polynomial TensorProduct

abbrev Base := baseChart (false,false)
abbrev finiteOrder (E : Type) [Field E] [Algebra ChartField E] := integralClosure Base E
def baseConstants : L →+* Base := constants.codRestrict Base (chart_constant (false,false))
scoped instance baseAlgebra : Algebra L Base := baseConstants.toAlgebra
def finiteConstant (E : Type) [Field E] [Algebra ChartField E] : L→+*finiteOrder E :=
  (algebraMap Base (finiteOrder E)).comp baseConstants
scoped instance finiteAlgebra (E : Type) [Field E] [Algebra ChartField E] : Algebra L (finiteOrder E) :=
  (finiteConstant E).toAlgebra
scoped instance finiteTower (E : Type) [Field E] [Algebra ChartField E] :
    IsScalarTower L Base (finiteOrder E) := IsScalarTower.of_algebraMap_eq (R:=L) (S:=Base) (A:=finiteOrder E) fun _=>rfl

def point (x z:L) : Base→ₐ[L]L :=
  { toRingHom:=((evalRingHom x).comp (mapRingHom (evalRingHom z))).comp (planeEquiv (false,false)).symm.toRingHom
    commutes':=fun a=>by
      have eq:algebraMap L Base a=planeEquiv (false,false) (C (C a)) := Subtype.ext (planeMap_constants ..).symm
      rw [eq]; simp }

def finiteX (x:L) : Base := planeEquiv (false,false) (Polynomial.X-C (C x))
def finiteZ (z:L) : Base := planeEquiv (false,false) (C (Polynomial.X-C z))

theorem finiteX_val (x:L) : (finiteX x:ChartField)=divisor false x := by
  change planeMap _ _=_
  simp [divisor,coordinate,chartCoordinate]
theorem finiteZ_val (z:L) : (finiteZ z:ChartField)=divisor true z := by
  change planeMap _ _=_
  simp [divisor,coordinate,chartCoordinate]

theorem point_kernel (x z:L) : RingHom.ker (point x z).toRingHom =
    Ideal.span ({finiteX x}:Set Base)⊔Ideal.span {finiteZ z} := by
  let e:=planeEquiv (false,false)
  have pol (p:Lower6960.PlaneConstants.Plane L) : point x z (e p)=(p.eval (C x)).eval z := by
    change eval x ((e.symm (e p)).map (evalRingHom z))=(p.eval (C x)).eval z
    rw [e.symm_apply_apply]
    simpa using (Polynomial.eval_map_apply (evalRingHom z) (p:=p) (x:=C x))
  ext a
  obtain ⟨p,rfl⟩:=e.surjective a
  rw [RingHom.mem_ker]
  change point x z (e p)=0 ↔ _
  rw [pol,←Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero,
    Ideal.mem_span_pair]
  constructor
  · rintro ⟨b,c,eq⟩
    rw [←eq,map_add,map_mul,map_mul]
    exact Submodule.mem_sup.mpr ⟨_,Ideal.mem_span_singleton.mpr (dvd_mul_left (finiteX x) (e c)),
      _,Ideal.mem_span_singleton.mpr (dvd_mul_left (finiteZ z) (e b)),add_comm ..⟩
  · intro h
    obtain ⟨b,bx,c,cz,eq⟩:=Submodule.mem_sup.mp h
    obtain ⟨b',rfl⟩:=Ideal.mem_span_singleton.mp bx
    obtain ⟨c',rfl⟩:=Ideal.mem_span_singleton.mp cz
    refine ⟨e.symm c',e.symm b',e.injective ?_⟩
    simp only [map_add,map_mul,e.apply_symm_apply]
    rw [←eq]; change c'*finiteZ z+b'*finiteX x=finiteX x*b'+finiteZ z*c'
    ring

variable (E : Type) [Field E] [Algebra ChartField E]

def fromFinite : finiteOrder E→ₐ[L]Tor E where
  toFun y:=⟨y,order_mono (base_torus (false,false)) y.property⟩
  map_one':=rfl
  map_zero':=rfl
  map_add' _ _:=rfl
  map_mul' _ _:=rfl
  commutes' _:=rfl

def toCross (x z:L) : finiteOrder E→ₐ[L]Crossing E x z :=
  (Ideal.Quotient.mkₐ L (axisIdeal E false x⊔axisIdeal E true z)).comp (fromFinite E)

private theorem scaled (x z:L) (v:Tor E) :
    ∃ n : ℕ, ∃ y:finiteOrder E, toCross E x z y =
      (algebraMap L (Crossing E x z) (x*z))^n * Ideal.Quotient.mk _ v := by
  let J:=axisIdeal E false x⊔axisIdeal E true z
  let π:=Ideal.Quotient.mk J
  let Xp:Tor E:=⟨algebraMap ChartField E RatFunc.X,isIntegral_algebraMap (x:=(⟨_,torus_coordinate false false⟩:torus))⟩
  let Zp:Tor E:=⟨algebraMap ChartField E scalarCoordinate,isIntegral_algebraMap (x:=(⟨_,torus_coordinate true false⟩:torus))⟩
  have xx : π Xp=algebraMap L _ x := by
    apply Ideal.Quotient.eq.mpr
    have eq : Xp-algebraMap L (Tor E) x=cut E false x := by
      apply Subtype.ext; exact (map_sub (algebraMap ChartField E) _ _).symm
    rw [eq]; exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
  have zz : π Zp=algebraMap L _ z := by
    apply Ideal.Quotient.eq.mpr
    have eq : Zp-algebraMap L (Tor E) z=cut E true z := by
      apply Subtype.ext; exact (map_sub (algebraMap ChartField E) _ _).symm
    rw [eq]; exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨n,h⟩:=clear_torus (false,false) v.val v.property
  let y:finiteOrder E:=⟨_,h⟩
  have val : fromFinite E y=(Xp*Zp)^n*v := by
    apply Subtype.ext
    change (algebraMap ChartField E (boundary _ _))^n * v.val = (_*_)^n*v.val
    simp [boundary,opposite,chartCoordinate,map_mul,Xp,Zp]
  refine ⟨n,y,?_⟩
  change π (fromFinite E y)=_
  rw [val,map_mul,map_pow,map_mul,xx,zz,map_mul]

theorem cross_surjective (x z:L) (nx:x≠0) (nz:z≠0) : Function.Surjective (toCross E x z) := by
  intro w
  obtain ⟨v,rfl⟩:=Ideal.Quotient.mk_surjective w
  obtain ⟨n,y,eq⟩:=scaled E x z v
  refine ⟨(x*z)⁻¹^n • y,?_⟩
  rw [AlgHom.map_smul_of_tower,eq,←map_pow,←Algebra.smul_def,smul_smul,←mul_pow,inv_mul_cancel₀ (mul_ne_zero nx nz),one_pow,one_smul]

#print axioms point_kernel
#print axioms cross_surjective

theorem toCross_kernel (x z:L) (nx:x≠0) (nz:z≠0) :
    RingHom.ker (toCross E x z).toRingHom=(RingHom.ker (point x z).toRingHom).map
      (algebraMap Base (finiteOrder E)) := by
  let S:=finiteOrder E
  let Xp:=algebraMap Base S (finiteX x)
  let Zp:=algebraMap Base S (finiteZ z)
  have xeq : fromFinite E Xp=cut E false x := Subtype.ext (congrArg (algebraMap ChartField E) (finiteX_val x))
  have zeq : fromFinite E Zp=cut E true z := Subtype.ext (congrArg (algebraMap ChartField E) (finiteZ_val z))
  have xf : (xcut (false,false) x:ChartField)=divisor false x := by simp [xcut_value,localFrame,axisBit]
  have zf : (zcut (false,false) z:ChartField)=divisor true z := by simp [zcut_value,localFrame,axisBit]
  rw [point_kernel,Ideal.map_sup,Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton]
  change RingHom.ker _=Ideal.span ({Xp}:Set S) ⊔Ideal.span {Zp}
  apply le_antisymm
  · intro y hy
    have zero : fromFinite E y∈axisIdeal E false x ⊔ axisIdeal E true z :=
      Ideal.Quotient.eq_zero_iff_mem.mp hy
    obtain ⟨_,h₁,_,h₂,eq⟩:=Submodule.mem_sup.mp zero
    obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton.mp h₁
    obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp h₂
    have coeffX : algebraMap Base E (xcut (false,false) x)=algebraMap ChartField E (divisor false x) :=
      congrArg (algebraMap ChartField E) xf
    have coeffZ : algebraMap Base E (zcut (false,false) z)=algebraMap ChartField E (divisor true z) :=
      congrArg (algebraMap ChartField E) zf
    obtain ⟨w,a',b',_,ia,ib,la,lb⟩:=lift_on_chart (false,false) x z nx nz (y:E) (0:E)
      y.property isIntegral_zero ⟨a,b,a.property,b.property,by
        rw [sub_zero,coeffX,coeffZ]; exact congrArg Subtype.val eq.symm⟩
    refine Submodule.mem_sup.mpr ⟨Xp*⟨a',ia⟩,Ideal.mem_span_singleton.mpr (dvd_mul_right ..),
      Zp*⟨b',ib⟩,Ideal.mem_span_singleton.mpr (dvd_mul_right ..),Subtype.ext ?_⟩
    rw [sub_zero,coeffZ] at lb; rw [coeffX] at la
    change algebraMap ChartField E (finiteX x:ChartField)*a'+algebraMap ChartField E (finiteZ z:ChartField)*b'=y
    rw [finiteX_val,finiteZ_val,←la,←lb,sub_add_cancel]
  · apply sup_le
    · apply Ideal.span_le.mpr; rintro _ ⟨⟩
      change Ideal.Quotient.mk _ (fromFinite E Xp)=0
      rw [xeq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
    · apply Ideal.span_le.mpr; rintro _ ⟨⟩
      change Ideal.Quotient.mk _ (fromFinite E Zp)=0
      rw [zeq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))

def crossingEquiv (x z:L) (nx:x≠0) (nz:z≠0) :
    letI := (point x z).toRingHom.toAlgebra
    Crossing E x z ≃ₐ[L] (L ⊗[Base] finiteOrder E) := by
  letI := (point x z).toRingHom.toAlgebra
  let e:=Ideal.quotientKerAlgEquivOfSurjective (cross_surjective E x z nx nz)
  let transport:=Ideal.quotientEquivAlgOfEq L (toCross_kernel E x z nx nz)
  exact e.symm.trans (transport.trans (Lower6960.RetainedFibreQuotient.atPoint (S:=finiteOrder E) (point x z)))

open RetainedCompression (Curve ordinate view)
/-- The crossing space in the actual restriction map is reduced and has precisely
the ordinate degree, for one finite pair off the coordinate boundary. -/
theorem actual_crossing (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<K1.p) (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ x z:L,x≠0 ∧ z≠0 ∧ Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧
      IsReduced (Crossing E x z) := by
  obtain ⟨x,z,nx,nz,good⟩:=RetainedCrossingBasis.actual_good_lines f ir lo hi basis root
  letI := (point x z).toRingHom.toAlgebra
  obtain ⟨⟨B⟩,reduced⟩:=good L (point x z).toRingHom le_rfl
  let e:=crossingEquiv E x z nx nz
  refine ⟨x,z,nx,nz,⟨B.map e.symm.toLinearEquiv⟩,?_⟩
  constructor
  intro a ha
  exact e.injective ((ha.map e.toRingHom).eq_zero.trans (map_zero e).symm)

#print axioms actual_crossing
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedCrossingComparison

-- merged module R6961RetainedAxisCharts
section Merged_R6961RetainedAxisCharts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent MonicChartProbes RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
open Lower6961.RetainedSurfaceClass (chartSpace)
variable (E : Type) [Field E] [Algebra ChartField E]

/-- The orientation places the fixed coordinate outside and the variable along the
line inside the iterated polynomial ring. The latter may be reciprocal. -/
def oriented (j b : Bool) : Lower6960.PlaneConstants.Plane L ≃+*baseChart (reference j b) :=
  if j then Bivariate.swap.toRingEquiv.trans (planeEquiv _) else planeEquiv _

theorem oriented_var (j b : Bool) :
    ((oriented j b Polynomial.X):ChartField)=coordinate j := by
  cases j <;> change planeMap _ _=_
  · simp [reference,coordinate,chartCoordinate]
  · change planeMap _ (Bivariate.swap Polynomial.X)=_
    rw [Bivariate.swap_Y,planeMap_scalar]; rfl

theorem oriented_line (j b : Bool) :
    ((oriented j b (C Polynomial.X)):ChartField)=chartCoordinate b (coordinate (!j)) := by
  cases j <;> change planeMap _ _=_
  · rw [planeMap_scalar]; rfl
  · change planeMap _ (Bivariate.swap (C Polynomial.X))=_
    rw [Bivariate.swap_X,planeMap_abscissa]; rfl

theorem oriented_const (j b : Bool) (r:L) :
    ((oriented j b (C (C r))):ChartField)=constants r := by
  cases j <;> change planeMap _ _=_
  · exact planeMap_constants ..
  · change planeMap _ (Bivariate.swap (C (C r)))=_
    rw [Bivariate.swap_C_C,planeMap_constants]

def along (j b:Bool) : (Polynomial L)→+* Tor E :=
  let x:=chartCoordinate b (coordinate (!j))
  let t : Tor E:=⟨algebraMap ChartField E x,
    isIntegral_algebraMap (x:=(⟨x,torus_coordinate (!j) b⟩:torus))⟩
  eval₂RingHom (algebraMap L (Tor E)) t

def intoTorus (s:Chart) : integralClosure (baseChart s) E →+* Tor E :=
  Subring.inclusion (show (integralClosure (baseChart s) E).toSubring≤(Tor E).toSubring
    from fun _ h=>order_mono (base_torus s) h)

def embedBase (s:Chart) : baseChart s→+*Tor E :=
  (intoTorus E s).comp (algebraMap (baseChart s) (integralClosure (baseChart s) E))

theorem finite_along (j b:Bool) (P:(Polynomial L)) :
    embedBase E (reference j b) (oriented j b (C P))=along E j b P := by
  let h:=(embedBase E (reference j b)).comp ((oriented j b).toRingHom.comp C)
  have eq : h=along E j b := Polynomial.ringHom_ext
    (fun r=>by
      apply Subtype.ext
      change algebraMap ChartField E ((oriented j b (C (C r))):ChartField) = _
      rw [oriented_const]
      simp [along,eval₂RingHom]; rfl)
    (by
      apply Subtype.ext
      change algebraMap ChartField E ((oriented j b (C Polynomial.X)):ChartField)=_
      rw [oriented_line]
      simp [along,eval₂RingHom])
  exact DFunLike.congr_fun eq P

def polyMap (j:Bool) (c:L) (b:Bool) : (Polynomial L)→+*Axis E j c :=
  (Ideal.Quotient.mk (axisIdeal E j c)).comp (along E j b)

private theorem eval_fixed (j:Bool) (c:L) (b:Bool) (P:Lower6960.PlaneConstants.Plane L) :
    red E j c (embedBase E (reference j b) (oriented j b P))=polyMap E j c b (P.eval (C c)) := by
  let s:=reference j b
  let π:=Ideal.Quotient.mk (axisIdeal E j c)
  let F:=π.comp ((embedBase E s).comp (oriented j b).toRingHom)
  let G:=(polyMap E j c b).comp (evalRingHom (C c))
  have eq : F=G := by
    apply Polynomial.ringHom_ext
    · intro q
      change π (embedBase E s (oriented j b (C q)))=polyMap E j c b ((C q).eval (C c))
      rw [finite_along,eval_C]; rfl
    · change π (embedBase E s (oriented j b Polynomial.X)) = polyMap E j c b (Polynomial.X.eval (C c))
      rw [eval_X]
      change π (embedBase E s (oriented j b Polynomial.X))=π (along E j b (C c))
      apply Ideal.Quotient.eq.mpr
      have diff : embedBase E s (oriented j b Polynomial.X) - along E j b (C c)=cut E j c := by
        rw [←finite_along]
        apply Subtype.ext
        change algebraMap ChartField E ((oriented j b Polynomial.X):ChartField) -
          algebraMap ChartField E ((oriented j b (C (C c))):ChartField) = _
        rw [oriented_var,oriented_const]
        exact (map_sub (algebraMap ChartField E) _ _).symm
      rw [diff]; exact Ideal.subset_span (Set.mem_singleton _)
  exact DFunLike.congr_fun eq P

def polyImage (j:Bool) (c:L) (b:Bool) :
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    Submodule (Polynomial L) (Axis E j c) := by
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  refine { carrier := (chartImage E j c b : Set _)
           zero_mem' := (chartImage E j c b).zero_mem
           add_mem' := (chartImage E j c b).add_mem
           smul_mem' := ?_ }
  rintro p _ ⟨u,hu,rfl⟩
  let s:=reference j b
  have inChart:IsIntegral (baseChart s) ((along E j b p):E) := by
    rw [←finite_along]; exact isIntegral_algebraMap
  refine ⟨along E j b p*u,inChart.mul hu,?_⟩
  exact map_mul (Ideal.Quotient.mk (axisIdeal E j c)) _ _

/-- The finite chart of the selected line is the image of the surface order, as a
module over the ordinary polynomial ring of the line. -/
theorem chart_finite [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (j:Bool) (c:L) (b:Bool) :
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    Module.Finite (Polynomial L) (polyImage E j c b) := by
  classical
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  let s:=reference j b
  let A:=baseChart s
  let O:=integralClosure A E
  have fin := IsIntegralClosure.finite A ChartField E O
  obtain ⟨G,gen⟩:=fin.1
  let V : Submodule (Polynomial L) (Axis E j c) := polyImage E j c b
  let : Module (Polynomial L) V := V.module
  let f (a:O):V:=⟨red E j c (intoTorus E s a),⟨_,a.property,rfl⟩⟩
  let h: Submodule (Polynomial L) V := Submodule.span (Polynomial L) ((G.image f : Finset V):Set V)
  refine ⟨⟨G.image f,top_unique (fun v _ => ?_)⟩⟩
  suffices covers : ∀ w:O, w∈Submodule.span A (G:Set O) → f w∈h by
    obtain ⟨u,hu,eq⟩:=v.property
    let w:O:=⟨u,hu⟩
    have hval:f w=v := Subtype.ext eq
    exact hval ▸ covers w (gen ▸ mem_top)
  intro w all
  induction all using Submodule.span_induction with
  | mem u hu => exact Submodule.subset_span (Finset.mem_image_of_mem f hu)
  | zero => exact h.zero_mem
  | add u v _ _ a b => exact h.add_mem a b
  | smul r u _ ih =>
    let p:=(oriented j b).symm r
    convert h.smul_mem (p.eval (C c)) ih using 1
    apply Subtype.ext
    rw [Submodule.coe_smul (p:=V),Algebra.smul_def r u]
    change Ideal.Quotient.mk _ (intoTorus E s (algebraMap A O r*u)) =
      polyMap E j c b (p.eval (C c))*Ideal.Quotient.mk _ (intoTorus E s u)
    rw [map_mul,map_mul]
    have scalar:=eval_fixed E j c b p
    rw [show oriented j b p=r from (oriented j b).apply_symm_apply r] at scalar
    exact congrArg (·*_) scalar

#print axioms chart_finite
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedAxisCharts

-- merged module R6961RetainedAxisFree
section Merged_R6961RetainedAxisFree

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent MonicChartProbes RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass Lower6961.MonicChartProbes
open Lower6961.RetainedSurfaceClass (oriented_var oriented_const finite_along embedBase)
open Lower6961.RetainedRestrictionTorus (rel_equiv)

variable (E : Type) [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
local notation "ι" => algebraMap ChartField E

/-- On a chosen line, a nonzero polynomial in its running coordinate cannot kill
a nonzero section, including on a reducible fibre. Both coordinate orientations use
divisibility in the original surface normalization. -/
theorem no_axis_torsion (j:Bool) (c:L) (b:Bool) (p:(Polynomial L)) (pn:p≠0) (u:Tor E)
    (zero : polyMap E j c b p * red E j c u=0) : red E j c u=0 := by
  let s:=reference j b
  let A:=baseChart s
  let : UniqueFactorizationMonoid A := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let i:=algebraMap A E
  let h:=oriented j b (Polynomial.X-C (C c))
  let a:=oriented j b (C p)
  have hn : h≠0 := (map_ne_zero_iff _ (oriented j b).injective).mpr (X_sub_C_ne_zero _)
  have an : a≠0 := (map_ne_zero_iff _ (oriented j b).injective).mpr (C_ne_zero.mpr pn)
  have cop : IsRelPrime a h := by
    apply Lower6961.RetainedRestrictionTorus.rel_equiv (oriented j b)
    simpa using Lower6960.TwoRulings.independent_denominators p (Polynomial.X-C c) pn (X_sub_C_ne_zero _)
  have hf : (h:ChartField)=divisor j c := by
    change ((oriented j b (Polynomial.X-C (C c))):ChartField)=_
    rw [map_sub]
    change ((oriented j b Polynomial.X):ChartField)-((oriented j b (C (C c))):ChartField)=_
    rw [Lower6961.RetainedSurfaceClass.oriented_var,Lower6961.RetainedSurfaceClass.oriented_const]; rfl
  have cp : (along E j b p:E)=i a := by
    rw [←Lower6961.RetainedSurfaceClass.finite_along]; rfl
  let D:=ι (divisor j c)
  have dn : D≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne j c)
  obtain ⟨v,hv⟩:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp
    (show Ideal.Quotient.mk (axisIdeal E j c) (along E j b p*u)=0 from (map_mul ..).trans zero))
  let y:=(u:E)/D
  have uy : i h*y=u := by
    change ι (h:ChartField)*((u:E)/D)=_
    rw [hf]; change D*((u:E)/D)=_
    field_simp
  have vy : i a*y=v := by
    have eq := congrArg (fun r:Tor E=>(r:E)) hv
    change (along E j b p:E)*(u:E)=D*(v:E) at eq
    rw [cp] at eq
    change i a*((u:E)/D)=_
    rw [←mul_div_assoc,eq,mul_div_cancel_left₀ _ dn]
  obtain ⟨m,hm⟩:=clear_torus s _ u.property
  obtain ⟨n,hn'⟩:=clear_torus s _ v.property
  let G:=edge s (opposite s)
  change IsIntegral A (i G^m*(u:E)) at hm
  change IsIntegral A (i G^n*(v:E)) at hn'
  have extra (q:A) (v:E) (iv:IsIntegral A v) : IsIntegral A (i q*v) := isIntegral_algebraMap.mul iv
  have whole : IsIntegral A (i G^(m+n)*y) := by
    apply Lower6960.NormalizedFiber.integral_of_coprime_clearings ChartField hn an cop.symm _
    · change IsIntegral A (i h*(i G^(m+n)*y))
      have hh:= extra (G^n) _ hm
      rw [←uy,map_pow] at hh
      convert hh using 1 <;> rw [pow_add] <;> ring
    · change IsIntegral A (i a*(i G^(m+n)*y))
      have hh:= extra (G^m) _ hn'
      rw [←vy,map_pow] at hh
      convert hh using 1 <;> rw [pow_add] <;> ring
  have gn : i G≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (edge_ne s (opposite s))
  have inv : (boundary s (opposite s))⁻¹∈torus := by
    rw [all_charts s]
    exact ⟨1,by simp [edge_ne]⟩
  have torInv : IsIntegral torus (i G)⁻¹ := by
    have t:IsIntegral torus (ι ((boundary s (opposite s))⁻¹)) := isIntegral_algebraMap (x:=(⟨_,inv⟩:torus))
    change IsIntegral torus (ι (boundary s (opposite s)))⁻¹
    simpa only [map_inv₀] using t
  have iy := (torInv.pow (m+n)).mul (order_mono (base_torus s) whole)
  rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ gn,one_pow,one_mul] at iy
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  refine Ideal.mem_span_singleton.mpr ⟨⟨y,iy⟩,Subtype.ext ?_⟩
  change (u:E)=D*y
  change (u:E)=ι (divisor j c)*y
  rw [←hf]; exact uy.symm

theorem chart_free [Algebra.IsSeparable ChartField E] (j:Bool) (c:L) (b:Bool) :
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    Module.Free (Polynomial L) (polyImage E j c b) := by
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  have :=chart_finite E j c b
  have : Module.IsTorsionFree (Polynomial L) (polyImage E j c b) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro p u hz
    by_cases pn:p=0
    · exact Or.inl pn
    right
    obtain ⟨w,_,ew⟩:=u.property
    apply Subtype.ext
    rw [←ew]
    apply no_axis_torsion E j c b p pn
    rw [ew]
    exact congrArg Subtype.val hz
  infer_instance

#print axioms no_axis_torsion
#print axioms chart_free
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedAxisFree

-- merged module R6961RetainedAxisTransition
section Merged_R6961RetainedAxisTransition

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections RetainedRestrictionTorus ChartOverlapTests
open Module Submodule Algebra Polynomial Lower6960.LineEuler LaurentPolynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
variable (E : Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def torVar (j b:Bool) : Tor E := ⟨ι (chartCoordinate b (coordinate j)),
  isIntegral_algebraMap (x:=(⟨_,torus_coordinate j b⟩:torus))⟩
def varUnit (j:Bool) : (Tor E)ˣ := ⟨torVar E j false,torVar E j true,by
  apply Subtype.ext; change ι (coordinate j)*ι ((coordinate j)⁻¹)=1
  rw [←map_mul,mul_inv_cancel₀ (coord_ne j),map_one],by
  apply Subtype.ext; change ι ((coordinate j)⁻¹)*ι (coordinate j)=1
  rw [←map_mul,inv_mul_cancel₀ (coord_ne j),map_one]⟩

def axisLaurent (j:Bool) (c:L) : Laurent L→+*Axis E j c :=
  (Ideal.Quotient.mk _).comp (LaurentPolynomial.eval₂ (algebraMap L (Tor E)) (varUnit E (!j)))
scoped instance axisAlgebra (j:Bool) (c:L) : Algebra (Laurent L) (Axis E j c) :=
  @RingHom.toAlgebra (Laurent L) (Axis E j c) _ (Ideal.Quotient.commSemiring (axisIdeal E j c)) (axisLaurent E j c)
scoped instance chartModule (j:Bool) (c:L) (b:Bool) : Module (Polynomial L) (chartImage E j c b) :=
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
  (polyImage E j c b).module

theorem signed_chart (j:Bool) (c:L) (b:Bool) :
    (axisLaurent E j c).comp (chartEmbedding b).toRingHom=polyMap E j c b := by
  let π:=Ideal.Quotient.mk (axisIdeal E j c)
  apply Polynomial.ringHom_ext
  · intro r
    change π (LaurentPolynomial.eval₂ _ _ (chartEmbedding b (Polynomial.C r)))=π (along E j b (Polynomial.C r))
    have co : chartEmbedding b (Polynomial.C r)=LaurentPolynomial.C r := by
      cases b <;> simp [chartEmbedding,infinityEmbedding_apply]
    have eq : along E j b (Polynomial.C r)=algebraMap L (Tor E) r := eval₂_C _ _
    rw [co,LaurentPolynomial.eval₂_C,eq]
  · have v : chartEmbedding b (Polynomial.X : (Polynomial L))=T (if b then (-1:ℤ) else 1) := by
      cases b <;> simp [chartEmbedding,infinityEmbedding_apply]
    change π (LaurentPolynomial.eval₂ _ _ (chartEmbedding b Polynomial.X))=π (along E j b Polynomial.X)
    rw [v,LaurentPolynomial.eval₂_T]
    have alongX:along E j b Polynomial.X=torVar E (!j) b := eval₂_X _ _
    rw [alongX]
    cases b <;> simp [varUnit]

theorem laurent_scalar_tower (j:Bool) (c:L) : IsScalarTower L (Laurent L) (Axis E j c) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply]
  change algebraMap L (Axis E j c) r=axisLaurent E j c (LaurentPolynomial.C r)
  simp [axisLaurent]

def nativeMap (j:Bool) (c:L) (b:Bool) : ChartMap (k:=L) b (chartImage E j c b) (Axis E j c) :=
  letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (chartEmbedding (k:=L) b).toRingHom
  { toFun := fun u=>u.val
    map_add' := fun _ _=>rfl
    map_smul' := fun p u=>by
      change polyMap E j c b p*u.val=axisLaurent E j c (chartEmbedding b p)*u.val
      exact congrArg (·*u.val) (DFunLike.congr_fun (signed_chart E j c b) p).symm }

theorem fixed_value (j:Bool) (c:L) : red E j c (torVar E j false)=algebraMap L (Axis E j c) c := by
  apply Ideal.Quotient.eq.mpr
  have eq : torVar E j false-algebraMap L (Tor E) c=cut E j c := by
    apply Subtype.ext; exact (map_sub (algebraMap ChartField E) _ _).symm
  rw [eq]; exact Ideal.subset_span (Set.mem_singleton _)

/-- Inverting the running coordinate of either actual line chart gives its entire
torus fibre. The transverse coordinate specializes to a nonzero scalar. -/
theorem native_localization (j:Bool) (c:L) (nc:c≠0) (b:Bool) : IsChartLocalization b (nativeMap E j c b) := by
  apply isChartLocalization_of_clearing b _ (fun _ _ h=>Subtype.ext h)
  intro v
  obtain ⟨u,rfl⟩:=Ideal.Quotient.mk_surjective v
  let s:=reference j b
  obtain ⟨n,h⟩:=clear_torus s (u:E) u.property
  let V:=torVar E (!j) b
  let W:=torVar E j false
  have bw : boundary s (opposite s)=chartCoordinate b (coordinate (!j))*coordinate j := by
    cases j <;> cases b <;> simp [s,reference,boundary,opposite,coordinate,chartCoordinate,mul_comm]
  let y:Tor E:=(V*W)^n*u
  have yi : IsIntegral (baseChart s) (y:E) := by
    rw [bw,map_mul] at h
    exact h
  let w : chartImage E j c b := ⟨red E j c y,⟨y,yi,rfl⟩⟩
  refine ⟨n, (c⁻¹^n) • w,?_⟩
  let π:=Ideal.Quotient.mk (axisIdeal E j c)
  change (axisLaurent E j c ((chartEmbedding b Polynomial.X)^n))*π u=algebraMap L (Axis E j c) (c⁻¹^n)*π y
  have xe : axisLaurent E j c (chartEmbedding b Polynomial.X)=π V := by
    exact (DFunLike.congr_fun (signed_chart E j c b) Polynomial.X).trans
      (congrArg π (show along E j b Polynomial.X=V from eval₂_X (algebraMap L (Tor E)) V))
  have we : π W=algebraMap L (Axis E j c) c := fixed_value E j c
  rw [map_pow,xe,show π y= (π V*π W)^n*π u by simp [y,π],we,
    mul_pow (π V) ((algebraMap L (Axis E j c)) c) n,map_pow]
  -- The residue ring need not be a field, so cancel using its scalar action.
  have cancel : (algebraMap L (Axis E j c) c⁻¹)^n * (algebraMap L (Axis E j c) c)^n=1 := by
    have scalar : c⁻¹^n*c^n=1 := by rw [←mul_pow,inv_mul_cancel₀ nc,one_pow]
    simpa only [map_mul,map_pow,map_one] using congrArg (algebraMap L (Axis E j c)) scalar
  calc _ = 1*((π V)^n*π u) := (one_mul _).symm
       _ = _ := by rw [←cancel]; ring

#print axioms native_localization
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedAxisTransition
