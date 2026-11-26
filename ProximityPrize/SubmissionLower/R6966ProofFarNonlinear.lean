import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreNormalization
import ProximityPrize.SubmissionLower.R6960MarkedProtocol
set_option Elab.async false



set_option Elab.async false

section Merged_R6960RetainedTwistedBudget
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedTwistedRestriction
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
open Lower6960.RetainedSurfaceClass (chartSpace congr_of_eq)
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

open RetainedCompression (Curve ordinate view height heightCap)

theorem initial_far (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height 164768 f≤heightCap (f.degreeOf ordinate) 164768) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [FiniteDimensional L (Paired E x z)] {b:ℕ}
    (size:finrank L (Paired E x z)≤b) : Budget E 0 b := by
  have spaces:charts E 0=potentials E := by
    ext u; change (∀s t,Over s t 0 _ )↔_
    simp only [Over,pow_zero,one_mul]; rfl
  let e:=LinearEquiv.ofEq _ _ spaces
  let f₀:=(rawMap E x z).comp e.toLinearMap
  apply RetainedCodimension.from_map f₀ _ _ size
  ext u
  change e u∈(rawMap E x z).ker ↔ ∃ c:E,∀s, Regular s 0 ((u.1 s:E)-c)
  rw [restriction_kernel_far E f ir lo hi bounded basis root x z nx nz]
  simp only [Regular,pow_zero,one_mul]; rfl

#print axioms initial_far

/-- Uniform surface bound for every positive abscissa twist of the same actual
factor. The degrees s,t are measured on its own two specialized chart orders. -/
theorem actual_all_twists_far (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height 164768 f≤heightCap (f.degreeOf ordinate) 164768) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ (x z:L) (nx:x≠0) (nz:z≠0) (m n s t:ℕ),
      ∃ (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
        (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)),
        (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
        (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
        Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧ IsReduced (Crossing E x z) ∧
        ∀ i:ℕ, Budget E i (s+(i+1)*t) := by
  have : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hi basis root
  obtain ⟨x,z,nx,nz,⟨B⟩,red⟩:=actual_crossing E f ir lo hi basis root
  have : FiniteDimensional L (Crossing E x z) := Module.Finite.of_basis B
  obtain ⟨m,⟨xf⟩,⟨xi⟩⟩:=native_frames E false x nx
  obtain ⟨n,⟨zf⟩,⟨zi⟩⟩:=native_frames E true z nz
  obtain ⟨finite,s,t,dt,ds,base⟩:=paired_bound E x z nx nz xf xi zf zi
  obtain ⟨fg,fo,d,ed,index⟩:=native_euler E false x nx xf xi
  have de : d= -(t:ℤ) := WithBot.coe_injective (ed.symm.trans dt)
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fg
  have inject:=global_eval_injective E false x z nx nz xf
  have eRank := LinearMap.finrank_le_finrank_of_injective inject
  change finrank L (LineGlobals E false x)≤finrank L (Crossing E x z) at eRank
  have mrank:=node_rank_le E false x z nx nz xf
  have line : finrank L (LineObstructions E false x)≤t := by omega
  refine ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B⟩,red,fun i=>?_⟩
  induction i with
  | zero => simpa only [zero_add,one_mul] using initial_far E f ir lo hi bounded basis root x z nx nz base
  | succ i ih =>
    simpa only [Nat.succ_eq_add_one,Nat.add_mul,one_mul,Nat.add_assoc] using grow E i x nx ih line

#print axioms actual_all_twists_far
end Lower6960.RetainedTwistedRestriction

end
end Merged_R6960RetainedTwistedBudget

section Merged_R6960MarkedVerticalProfile
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 14000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open RetainedCompression (Curve ordinate view view_y height heightCap)
open RetainedRestrictionTorus RetainedSurfaceClass CollisionMarked Polynomial LineEuler Algebra Module Submodule Horner
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6960.Horner Lower6960.RetainedSurfaceClass
local instance profileScalarDecidable_far : DecidableEq Scalar := Classical.decEq _
local instance profileFieldDecidable_far : DecidableEq ChartField := Classical.decEq _
local instance (priority:=2300) profileScalarBase_far : Algebra Scalar ChartField:=RatFunc.instAlgebraOfPolynomial Scalar Scalar
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
local instance profileNodeRing_far (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

/-- The vertical deficit of this precise surface is positive on the nonlinear
branch, is tame at the profile prime, and supplies the physical function rank. -/
theorem vertical_profile_far (f:Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height 164768 f≤heightCap (f.degreeOf ordinate) 164768) (nonlin:¬RetainedLinear.GeometricallyLinear (view f))
    (b:PowerBasis ChartField E) (dim:b.dim=(view f).natDegree)
    (root:aeval b.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (small:finrank L (Crossing E x z)<K1.p) {n:ℕ}
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true))
    (s:ℕ) (measure:(transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
    0<s ∧ 2*s<K1.p ∧ ∀(U:Finset L)(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j)) →
      finrank Scalar (span Scalar (Set.range v))+s≤(view f).natDegree*s := by
  classical
  let Q:=RetainedLinear.toSeed (view f)
  have e0:Q.natDegree=(view f).natDegree:=RetainedLinear.toSeed_degree _
  have e1:(view f).natDegree=f.degreeOf ordinate:=view_y f
  have rank:finrank ChartField E=(view f).natDegree:=b.finrank.trans dim
  have gen:=generic_measure_eq_native (E:=E) true x z nx nz K1.p small zf zi s measure
  dsimp only at gen
  rw [generic_algebra_vertical] at gen
  obtain ⟨F,I,det⟩:=gen
  have positive:0<s := by
    by_contra! h
    have zd:s=0:=by omega
    rw [zd,Nat.cast_zero,neg_zero,WithBot.coe_zero] at det
    obtain ⟨w,ind,integ⟩:=constant_frame F I det
    have pos:0<finrank ChartField E:=Module.finrank_pos
    letI:Nonempty (Fin (finrank ChartField E)):=⟨⟨0,pos⟩⟩
    exact nonlin (actual_geometric_of_constants (view f) ((MulEquiv.irreducible_iff view).mpr ir)
      (by omega) b root w ind (Fintype.card_fin _) integ)
  have width (j:ℕ):(Q.coeff j).natDegree≤heightCap (f.degreeOf ordinate) 164768 := by
    have d:(Q.coeff j).natDegree=((view f).coeff j).natDegree:=by
      simp only [Q,RetainedLinear.toSeed,Polynomial.coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
    rw [d]
    by_cases z:(view f).coeff j=0
    · rw [z,natDegree_zero];omega
    · exact (Nat.le_add_right _ _).trans ((RetainedCompression.abscissa_coeff_height f 164768 j z).trans bounded)
  have hr (n':ℕ) (eq:n'=Q.natDegree)
      (F':Basis (Fin n') (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) false))
      (I':Basis (Fin n') (Polynomial Scalar) (chartOrder (k:=Scalar) (E:=E) true))
      (dd:(normalizedTransition F' I').det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
      s≤(Q.natDegree-1)*heightCap (f.degreeOf ordinate) 164768 := by
    subst n'
    obtain ⟨d,dg,db⟩:=actual_horner_budget Q _ (by omega) width b.gen root
      (b.natDegree_minpoly.trans (dim.trans e0.symm)) F' I'
    have eq:d= -(s:ℤ):=WithBot.coe_injective (dg.symm.trans dd)
    rw [eq,neg_neg] at db
    exact_mod_cast db
  have cap:=hr _ (rank.trans e0.symm) F I det
  have tame:2*s<K1.p := by
    have h:2*((f.degreeOf ordinate-1)*heightCap (f.degreeOf ordinate) 164768)<K1.p := by
      exact (by decide +kernel : ∀j:Fin 48,2*((j.val-1)*heightCap j.val 164768)<K1.p) ⟨_,hi⟩
    rw [e0,e1] at cap;omega
  refine ⟨positive,tame,fun U m v regular=>?_⟩
  have bound:=actual_vertical_rank F I s positive det U m v regular
  rwa [Fintype.card_fin,rank] at bound

#print axioms vertical_profile_far
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedVerticalProfile

section Merged_R6960MarkedProtocol
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1 (K)
open K1_14 (L liftPoly)
open MonicChart (Scalar ChartField)
open RetainedCompression (Curve ordinate parameter view view_y height heightCap scalar MarkedFiber)
open RetainedTwistedRestriction RetainedSurfaceClass CollisionMarked Polynomial Module Algebra Finset
open scoped Polynomial Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass
local instance protocolScalarDec_far : DecidableEq Scalar:=Classical.decEq _
local instance protocolFieldDec_far : DecidableEq ChartField:=Classical.decEq _
local instance protocolNodeRing_far {E:Type} [Field E] [Algebra ChartField E] (x z:L):CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

theorem nonlinear_far (T : Finset K) (label : K → L) (inj : Function.Injective label)
    (word : K → Polynomial L) (f : Curve (Polynomial L)) (ir : Irreducible f)
    (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48) (seed : 0<f.degreeOf parameter)
    (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
    (nonlin : ¬RetainedLinear.GeometricallyLinear (view f))
    (marks : ∀ γ∈T, MarkedFiber (view f) (label γ) (word γ)) :
    T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate := by
  classical
  let P:=view f
  let Q:(Polynomial ChartField):=(RetainedLinear.toSeed P).map (algebraMap (Polynomial Scalar) ChartField)
  have pi:Irreducible P:=(MulEquiv.irreducible_iff view).mpr ir
  have degP:P.natDegree=f.degreeOf ordinate:=view_y f
  have seedI:=RetainedLinear.toSeed_irreducible pi (by omega : 0<P.natDegree)
  have degS: (RetainedLinear.toSeed P).natDegree=P.natDegree:=RetainedLinear.toSeed_degree P
  have qi:Irreducible Q := (seedI.isPrimitive (by omega)).irreducible_iff_irreducible_map_fraction_map.mp seedI
  letI : Fact (Irreducible Q):=⟨qi⟩
  let E:=AdjoinRoot Q
  let b:PowerBasis ChartField E:=AdjoinRoot.powerBasis qi.ne_zero
  have root:aeval b.gen Q=0 := (AdjoinRoot.aeval_eq Q).trans (AdjoinRoot.mk_self)
  have dim:b.dim=P.natDegree:=(natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) ChartField)
    (RetainedLinear.toSeed P)).trans degS
  have : FiniteDimensional ChartField E:=b.finite
  have : Algebra.IsSeparable ChartField E:=MonicChartProbes.actual_separable f ir lo hi b root
  letI : CharP Scalar K1.p:=charP_of_injective_ringHom inner.injective K1.p
  obtain ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B⟩,reduced,surface⟩:=
    actual_all_twists_far E f ir lo hi bounded b root
  have : FiniteDimensional L (Crossing E x z):=Module.Finite.of_basis B
  have small:finrank L (Crossing E x z)<K1.p := by
    rw [finrank_eq_card_basis B,Fintype.card_fin];exact hi.trans (by decide)
  obtain ⟨positive,tame,vrank⟩:=vertical_profile_far f ir lo hi bounded nonlin b dim root x z nx nz small zf zi s ds
  have tariff:=actual_horizontal_horner f ir lo hi b root x z nx nz K1.p small xf xi t dt
  obtain ⟨δf,δi,nf,ni,df,di,xc,zc,tail⟩:=
    actual_measured_discriminants x z nx nz K1.p small xf xi zf zi s t ds dt
  let S:=T.image label
  let wt (z:L):(Polynomial L):=word (Function.invFun label z)
  have mark (z:L) (mem:z∈S):MarkedFiber P z (wt z) := by
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp mem
    change MarkedFiber P _ (word (Function.invFun label (label a)))
    rw [Function.leftInverse_invFun inj];exact marks a ha
  have pn:projectedRaw P≠0:=by intro zero;have eq:=projectedRaw_degree P;rw [zero,natDegree_zero] at eq;omega
  have bound:=all_labels (E:=E) K1.p P pn (by omega) (degP ▸ hi.trans (by decide : 48<K1.p))
    (f.degreeOf parameter) seed b dim (projected_root_of_seed P b.gen root) s t positive tame
    (degP.symm ▸ tariff) (by simpa only [Nat.sub_add_cancel positive] using surface (s-1))
    δf δi nf ni df di xc zc tail S wt mark vrank
  rwa [show S.card=T.card from card_image_of_injective _ inj,degP] at bound

#print axioms nonlinear_far
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedProtocol
