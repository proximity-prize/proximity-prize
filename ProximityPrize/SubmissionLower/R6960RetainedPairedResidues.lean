import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift

set_option Elab.async false

-- merged module R6960RetainedCrossingBasis
section Merged_R6960RetainedCrossingBasis

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedCrossingBasis
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

end Lower6960.RetainedCrossingBasis

end
end Merged_R6960RetainedCrossingBasis

-- merged module R6960RetainedCrossingTrace
section Merged_R6960RetainedCrossingTrace

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedCrossingBasis
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

end Lower6960.RetainedCrossingBasis

end
end Merged_R6960RetainedCrossingTrace

-- merged module R6960RetainedGoodCrossing
section Merged_R6960RetainedGoodCrossing
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedCrossingBasis
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
open MonicChart (ChartField Scalar)
open MonicFourChartDescent (baseChart)
open MonicChartProbes (planeEquiv)
open scoped Lower6960.MonicChartProbes
open RetainedCompression (Curve ordinate view)
open Lower6960.MonicChart (root_finrank)
private theorem away_coordinate (P : (Polynomial L)) (pn : P≠0) :
    ∃ a:L, a≠0 ∧ P.eval a≠0 := by
  classical
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 P.roots.toFinset)
  exact ⟨a,fun z=>ha (z ▸ Finset.mem_insert_self ..),
    fun v=>ha (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((mem_roots pn).mpr v)))⟩
theorem actual_good_lines {E : Type} [Field E] [Algebra ChartField E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
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
  have deg : finrank ChartField E=f.degreeOf ordinate := Lower6960.MonicChart.root_finrank f ir lo basis
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
end Lower6960.RetainedCrossingBasis

end
end Merged_R6960RetainedGoodCrossing

-- merged module R6960RetainedAxisResidues
section Merged_R6960RetainedAxisResidues

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedRestrictionTorus
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests MonicChartLaurent
open Polynomial
open Lower6960.RetainedRestrictionTorus (linear)
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
    let a:PlaneConstants.Plane L:=Polynomial.X-C (C c)
    let b:PlaneConstants.Plane L:=C (Polynomial.X-C c)
    have h:= (map_ne_zero_iff _ this).mpr (mul_ne_zero (X_sub_C_ne_zero (C c))
      (C_ne_zero.mpr (X_sub_C_ne_zero c)))
    simpa [RetainedLineRestriction.lines,chartCoordinate] using h
  cases j
  · exact left_ne_zero_of_mul nz
  · exact right_ne_zero_of_mul nz

theorem xcut_value (s : Chart) (c:L) : (xcut s c : ChartField) = divisor false c/localFrame s false := by
  change planeMap s ((Lower6960.RetainedRestrictionTorus.linear s.1 c).map C)=_
  unfold Lower6960.RetainedRestrictionTorus.linear
  by_cases h:s.1=true <;> simp [h,map_sub,map_mul,divisor,localFrame,coordinate,axisBit,
    chartCoordinate,sub_mul,RatFunc.X_ne_zero,div_eq_mul_inv]
theorem zcut_value (s : Chart) (c:L) : (zcut s c : ChartField) = divisor true c/localFrame s true := by
  change planeMap s (C (Lower6960.RetainedRestrictionTorus.linear s.2 c))=_
  unfold Lower6960.RetainedRestrictionTorus.linear
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

end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedAxisResidues

-- merged module R6960RetainedPairedResidues
section Merged_R6960RetainedPairedResidues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedRestrictionTorus
open MonicChart (ChartField)
open K1_14 (L)
open MonicFourChartDescent ChartSections MonicChartLaurent ChartOverlapTests Polynomial
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def Matched (x z : L) (u v:E) : Prop := ∃ a b:E,IsIntegral torus a ∧ IsIntegral torus b ∧
  u-v=ι (divisor false x)*a+ι (divisor true z)*b

theorem frame_integral (s : Chart) (j : Bool) :
    IsIntegral torus (ι (localFrame s j) : E) ∧ IsIntegral torus (ι (localFrame s j)⁻¹ : E) := by
  have p:=torus_frame s j
  exact ⟨isIntegral_algebraMap (x:=(⟨_,p.1⟩:torus)),isIntegral_algebraMap (x:=(⟨_,p.2⟩:torus))⟩






























































def reference (j bit : Bool) : Chart := if j then (bit,false) else (false,bit)

def LineData (j : Bool) (c:L) (u:Chart→E) (v:Bool→E) : Prop :=
  (∀ b, IsIntegral (baseChart (reference j b)) (v b)) ∧
  Congruent j c (u (false,false)-u (reference j true)) (v false-v true)





















































end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedPairedResidues
