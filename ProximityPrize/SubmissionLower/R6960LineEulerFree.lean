import ProximityPrize.SubmissionLower.R6960LineEulerNormalization

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open Polynomial LaurentPolynomial Module
open scoped Polynomial BigOperators Matrix
open private Lower6960.LineEuler.chartLocalization from ProximityPrize.SubmissionLower.R6960LineEulerNormalization

variable {k ι M U V : Type*} [Field k]
  [AddCommGroup M] [Module (Laurent k) M]
  [AddCommGroup U] [Module k[X] U] [AddCommGroup V] [Module k[X] V]

/-- The scalar action on the Laurent module uses the indicated polynomial
chart. The module can come from a proper suborder after specialization. -/
abbrev ChartMap (s : Bool) (U M : Type*) [AddCommGroup U] [Module k[X] U]
    [AddCommGroup M] [Module (Laurent k) M] :=
  letI : Module k[X] M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  U→ₗ[k[X]] M

/-- The common module is obtained by inverting the chart variable in the
source polynomial module. -/
def IsChartLocalization (s : Bool) (f : ChartMap (k:=k) s U M) : Prop :=
  let : Module k[X] M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  IsLocalizedModule (Submonoid.powers (Polynomial.X : k[X])) f

/-- An injective chart map with explicit denominator clearings realizes
localization at the chart coordinate. -/
theorem isChartLocalization_of_clearing (s : Bool) (f : ChartMap (k:=k) s U M)
    (inj : Function.Injective f)
    (clearing : ∀ v : M,∃ (n : ℕ) (u : U), (chartEmbedding s (Polynomial.X : k[X]))^n • v=f u) :
    IsChartLocalization s f := by
  let : Algebra k[X] (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Module k[X] M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  let powers := Submonoid.powers (Polynomial.X : k[X])
  let : IsLocalization powers (Laurent k) := Lower6960.LineEuler.chartLocalization (k:=k) s
  change IsLocalizedModule powers f
  constructor
  · intro a
    obtain ⟨u,hu⟩ := IsLocalization.map_units (Laurent k) a
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun v : M=>chartEmbedding s (a:k[X]) • v)
    change (u:Laurent k)=chartEmbedding s (a:k[X]) at hu
    rw [←hu]
    refine ⟨?_,?_⟩
    · intro x y eq
      have inv := congrArg (fun z : M=>(↑u⁻¹:Laurent k) • z) eq
      simpa only [←mul_smul,Units.inv_mul,one_smul] using inv
    · intro v
      refine ⟨(↑u⁻¹:Laurent k) • v,?_⟩
      change (u:Laurent k) • ((↑u⁻¹:Laurent k) • v)=v
      rw [←mul_smul,Units.mul_inv,one_smul]
  · intro v
    obtain ⟨n,u,eq⟩ := clearing v
    exact ⟨⟨u,⟨(Polynomial.X:k[X])^n,n,rfl⟩⟩,by
      change chartEmbedding s ((Polynomial.X:k[X])^n) • v=f u
      rw [map_pow,eq]⟩
  · intro x y eq
    exact ⟨1,by rw [inj eq]⟩

private def localFreeData (s : Bool) (b : Basis ι k[X] U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) :
    {B : Basis ι (Laurent k) M // (∀ i,B i=f (b i)) ∧
      ∀ u i,B.repr (f u) i=chartEmbedding s (b.repr u i)} := by
  let : Algebra k[X] (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Module k[X] M := Module.compHom M (chartEmbedding (k:=k) s).toRingHom
  let : IsScalarTower k[X] (Laurent k) M := ⟨fun p r v=>by
    change (chartEmbedding s p*r) • v=chartEmbedding s p • (r • v)
    exact mul_smul _ _ _⟩
  let : IsLocalization.Away (Polynomial.X : k[X]) (Laurent k) :=
    Lower6960.LineEuler.chartLocalization (k:=k) s
  let powers := Submonoid.powers (Polynomial.X : k[X])
  let : IsLocalizedModule powers f := loc
  refine ⟨b.ofIsLocalizedModule (Laurent k) powers f,?_,?_⟩
  · intro i
    exact b.ofIsLocalizedModule_apply (Laurent k) powers f i
  · intro u i
    exact b.ofIsLocalizedModule_repr_apply (Laurent k) powers f u i

/-- A polynomial basis extends to the given common Laurent module. -/
def localFreeBasis (s : Bool) (b : Basis ι k[X] U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) : Basis ι (Laurent k) M := (localFreeData s b f loc).1

@[simp] theorem localFreeBasis_apply (s : Bool) (b : Basis ι k[X] U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) (i : ι) : localFreeBasis s b f loc i=f (b i) :=
  (localFreeData s b f loc).2.1 i

@[simp] theorem localFreeBasis_repr (s : Bool) (b : Basis ι k[X] U) (f : ChartMap (k:=k) s U M)
    (loc : IsChartLocalization s f) (u : U) (i : ι) :
    (localFreeBasis s b f loc).repr (f u) i=chartEmbedding s (b.repr u i) :=
  (localFreeData s b f loc).2.2 u i

private def chartLattice (s : Bool) : Submodule k (ι→Laurent k) :=
  if s then upperLattice k ι 0 else finiteLattice k ι

private theorem chartLattice_iff (s : Bool) (v : ι→Laurent k) : v∈chartLattice s ↔
    ∃ q : ι→k[X],∀ i,chartEmbedding s (q i)=v i := by
  cases s with
  | false => exact mem_finiteLattice v
  | true =>
    change v∈upperLattice k ι 0 ↔ _
    rw [←range_shiftVector 0,LinearMap.mem_range]
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨q,fun i=>by simp [chartEmbedding]⟩
    · rintro ⟨q,hq⟩
      exact ⟨q,funext fun i=>by simpa [chartEmbedding] using hq i⟩

private theorem coordinate_image [Finite ι] (s : Bool) (b : Basis ι k[X] U)
    (f : ChartMap (k:=k) s U M) (loc : IsChartLocalization s f) (v : M) :
    (localFreeBasis s b f loc).equivFun v∈chartLattice s ↔ ∃ u : U,f u=v := by
  rw [chartLattice_iff]
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨b.equivFun.symm q,(localFreeBasis s b f loc).equivFun.injective (funext fun i=>?_ )⟩
    rw [Basis.equivFun_apply,localFreeBasis_repr,←Basis.equivFun_apply,LinearEquiv.apply_symm_apply]
    exact hq i
  · rintro ⟨u,rfl⟩
    exact ⟨b.equivFun u,fun i=>by rw [Basis.equivFun_apply,Basis.equivFun_apply,localFreeBasis_repr]⟩

variable [Fintype ι] [DecidableEq ι]

section Both
variable (bf : Basis ι k[X] U) (bi : Basis ι k[X] V)
    (ff : ChartMap (k:=k) false U M) (fi : ChartMap (k:=k) true V M)
    (lf : IsChartLocalization false ff) (li : IsChartLocalization true fi)

/-- The transition of two free polynomial modules embedded in their
common Laurent localization. -/
def freeTransition : Matrix ι ι (Laurent k) :=
  LinearMap.toMatrix' (((localFreeBasis true bi fi li).equivFun.symm.trans
    (localFreeBasis false bf ff lf).equivFun).toLinearMap)

theorem freeTransition_mulVec (v : ι→Laurent k) :
    freeTransition bf bi ff fi lf li *ᵥ v =
      (localFreeBasis false bf ff lf).equivFun ((localFreeBasis true bi fi li).equivFun.symm v) := by
  rw [←Matrix.toLin'_apply,freeTransition,Matrix.toLin'_toMatrix']
  rfl

theorem freeTransition_unit : IsUnit (freeTransition bf bi ff fi lf li) := by
  let e := (localFreeBasis true bi fi li).equivFun.symm.trans (localFreeBasis false bf ff lf).equivFun
  apply isUnit_iff_exists_inv.mpr
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap,?_⟩
  apply Matrix.toLin'.injective
  rw [freeTransition,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact e.comp_symm

omit [DecidableEq ι] in
theorem free_finite_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v∈finiteLattice k ι ↔ ∃ u : U,ff u=v :=
  coordinate_image false bf ff lf v

theorem free_infinity_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v∈transitionLattice (freeTransition bf bi ff fi lf li) ↔
      ∃ w : V,fi w=v := by
  have i : (localFreeBasis true bi fi li).equivFun v∈upperLattice k ι 0 ↔ ∃ w : V,fi w=v :=
    coordinate_image true bi fi li v
  constructor
  · rintro ⟨w,hw,eq⟩
    apply i.mp
    change (freeTransition bf bi ff fi lf li)*ᵥw=(localFreeBasis false bf ff lf).equivFun v at eq
    rw [freeTransition_mulVec] at eq
    have v_eq := (localFreeBasis false bf ff lf).equivFun.injective eq
    have w_eq : w=(localFreeBasis true bi fi li).equivFun v := by
      rw [←v_eq,LinearEquiv.apply_symm_apply]
    exact w_eq ▸ hw
  · intro vi
    refine ⟨_,i.mpr vi,?_⟩
    change (freeTransition bf bi ff fi lf li)*ᵥ((localFreeBasis true bi fi li).equivFun v)=_
    rw [freeTransition_mulVec,LinearEquiv.symm_apply_apply]

/-- Membership in the intersection defining global sections means
membership in the actual images of both original free chart modules. -/
theorem free_global_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v ∈
      finiteLattice k ι⊓transitionLattice (freeTransition bf bi ff fi lf li) ↔
    (∃ u : U,ff u=v) ∧ (∃ w : V,fi w=v) :=
  and_congr (free_finite_iff bf ff lf v) (free_infinity_iff bf bi ff fi lf li v)

/-- A vector represents zero in first cohomology exactly when it is a
sum of elements of the two original chart images. -/
theorem free_boundary_iff (v : M) :
    (localFreeBasis false bf ff lf).equivFun v ∈
      finiteLattice k ι⊔transitionLattice (freeTransition bf bi ff fi lf li) ↔
    ∃ (u : U) (w : V),ff u+fi w=v := by
  let e := (localFreeBasis false bf ff lf).equivFun
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x,hx,y,hy,eq⟩
    have ex : e (e.symm x)∈finiteLattice k ι := by rwa [LinearEquiv.apply_symm_apply]
    have ey : e (e.symm y)∈transitionLattice (freeTransition bf bi ff fi lf li) := by
      rwa [LinearEquiv.apply_symm_apply]
    obtain ⟨u,eu⟩ := (free_finite_iff bf ff lf (e.symm x)).mp ex
    obtain ⟨w,ew⟩ := (free_infinity_iff bf bi ff fi lf li (e.symm y)).mp ey
    refine ⟨u,w,e.injective ?_⟩
    rw [map_add,eu,ew,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    exact eq
  · rintro ⟨u,w,rfl⟩
    exact ⟨e (ff u),(free_finite_iff bf ff lf _).mpr ⟨u,rfl⟩,e (fi w),
      (free_infinity_iff bf bi ff fi lf li _).mpr ⟨w,rfl⟩,(e.map_add _ _).symm⟩

/-- The Euler index of the two actual free chart modules. Their images can
be proper submodules of any ambient normalization. -/
theorem free_euler :
    FiniteDimensional k (H0 (freeTransition bf bi ff fi lf li)) ∧
    FiniteDimensional k (H1 (freeTransition bf bi ff fi lf li)) ∧
    ∃ d : ℤ,(freeTransition bf bi ff fi lf li).det.degree=(d:WithBot ℤ) ∧
      (finrank k (H0 (freeTransition bf bi ff fi lf li)):ℤ)-
        (finrank k (H1 (freeTransition bf bi ff fi lf li)):ℤ)=(Fintype.card ι:ℤ)+d :=
  euler_index _ (freeTransition_unit bf bi ff fi lf li)
end Both

#print axioms isChartLocalization_of_clearing
#print axioms freeTransition_unit
#print axioms free_global_iff
#print axioms free_boundary_iff
#print axioms free_euler
end
end Lower6960.LineEuler
