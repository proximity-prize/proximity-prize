import ProximityPrize.SubmissionLower.R6960RetainedCrossingTrace

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
open MonicChart (ChartField Scalar)
open MonicFourChartDescent (baseChart)
open MonicChartProbes (planeEquiv)
open scoped Lower6960.MonicChartProbes
open RetainedCompression (Curve ordinate view)
open private Lower6960.MonicChart.root_finrank from ProximityPrize.SubmissionLower.R6960MonicChartFrobenius

private theorem away_coordinate (P : L[X]) (pn : P≠0) :
    ∃ a:L, a≠0 ∧ P.eval a≠0 := by
  classical
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 P.roots.toFinset)
  exact ⟨a,fun z=>ha (z ▸ Finset.mem_insert_self ..),
    fun v=>ha (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((mem_roots pn).mpr v)))⟩

/-- Choose a transverse crossing at finite nonzero coordinates. The normalized point
fibre and the generic points of both lines are reduced, of the original ordinate rank. -/
theorem actual_good_lines {E : Type} [Field E] [Algebra ChartField E]
    (f : Curve L[X]) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap Scalar[X] ChartField))=0) :
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
  let : Algebra Scalar[X] E := ((algebraMap ChartField E).comp (algebraMap Scalar[X] ChartField)).toAlgebra
  let : IsScalarTower Scalar[X] ChartField E := IsScalarTower.of_algebraMap_eq
    (R:=Scalar[X]) (S:=ChartField) (A:=E) fun _=>rfl
  have deg : finrank ChartField E=f.degreeOf ordinate := Lower6960.MonicChart.root_finrank f ir lo basis
    (by rw [aeval_map_algebraMap] at root; exact root)
  obtain ⟨g,nz,openSet⟩:=good_open A ChartField E
  let P := (planeEquiv (false,false)).symm g
  have pn : P≠0 := (map_ne_zero_iff _ (planeEquiv (false,false)).symm.injective).mpr nz
  obtain ⟨z,zn,goodZ⟩:=away_coordinate P.leadingCoeff (leadingCoeff_ne_zero.mpr pn)
  let Q := P.map (evalRingHom z)
  have qn : Q≠0 := by
    intro zero
    have van:=congrArg (fun h:L[X]=>h.coeff P.natDegree) zero
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
end Lower6960.RetainedCrossingBasis
