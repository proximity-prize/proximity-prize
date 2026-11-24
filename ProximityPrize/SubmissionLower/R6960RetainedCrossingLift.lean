import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import ProximityPrize.SubmissionLower.R6960RetainedLineRestriction

-- merged module R6960TwoRulings
section Merged_R6960TwoRulings
noncomputable section
set_option Elab.async false
namespace Lower6960.TwoRulings
open Polynomial
open scoped Polynomial
variable {k : Type*} [Field k]
abbrev Plane (k : Type*) [Field k] := Polynomial (Polynomial k)
theorem independent_denominators (a b : (Polynomial k)) (an : a≠0) (bn : b≠0) :
    IsRelPrime (C a : Plane k) (b.map (C : k→+*(Polynomial k))) := by
  intro d da db
  have cd := natDegree_le_of_dvd da (C_ne_zero.mpr an)
  rw [natDegree_C] at cd
  have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero cd)
  rw [eq] at db ⊢
  apply isUnit_C.mpr
  have dvd := (C_dvd_iff_dvd_coeff _ _).mp db b.natDegree
  rw [coeff_map,coeff_natDegree] at dvd
  exact isUnit_of_dvd_unit dvd (isUnit_C.mpr (leadingCoeff_ne_zero.mpr bn).isUnit)
variable {E : Type*} [Field E] [Algebra (Plane k) E]
theorem affine_iff (F : Type*) [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]
    [Algebra F E] [IsScalarTower (Plane k) F E] [FiniteDimensional F E] (x : E) :
    IsIntegral (Plane k) x ↔
      (∃ a:(Polynomial k), a≠0 ∧ IsIntegral (Plane k) (algebraMap (Plane k) E (C a)*x)) ∧
      (∃ b:(Polynomial k), b≠0 ∧ IsIntegral (Plane k) (algebraMap (Plane k) E (b.map (C : k→+*(Polynomial k)))*x)) := by
  constructor
  · intro h
    exact ⟨⟨1,one_ne_zero,by simpa using h⟩,⟨1,one_ne_zero,by simpa using h⟩⟩
  · rintro ⟨⟨a,an,ai⟩,⟨b,bn,bi⟩⟩
    exact NormalizedFiber.integral_of_coprime_clearings F (C_ne_zero.mpr an)
      ((Polynomial.map_ne_zero_iff C_injective).mpr bn) (independent_denominators a b an bn) x ai bi
#print axioms affine_iff
def innerDenominators (k : Type*) [Field k] : Submonoid (Plane k) :=
  (nonZeroDivisors (Polynomial k)).map (C : (Polynomial k)→+*Plane k).toMonoidHom
def outerDenominators (k : Type*) [Field k] : Submonoid (Plane k) :=
  (nonZeroDivisors (Polynomial k)).map (mapRingHom (C : k→+*(Polynomial k))).toMonoidHom
theorem two_generic_lines (F : Type*) [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]
    [Algebra F E] [IsScalarTower (Plane k) F E] [FiniteDimensional F E]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra (Plane k) R] [Algebra (Plane k) S]
    [IsLocalization (innerDenominators k) R] [IsLocalization (outerDenominators k) S]
    [Algebra R E] [Algebra S E] [IsScalarTower (Plane k) R E] [IsScalarTower (Plane k) S E]
    (x : E) : IsIntegral (Plane k) x ↔ IsIntegral R x ∧ IsIntegral S x := by
  constructor
  · intro i; exact ⟨i.tower_top,i.tower_top⟩
  · rintro ⟨hR,hS⟩
    apply (affine_iff F x).mpr
    obtain ⟨d,good⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (innerDenominators k) x hR
    obtain ⟨a,ha,eq⟩ := d.property
    obtain ⟨d',good'⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (outerDenominators k) x hS
    obtain ⟨b,hb,eq'⟩ := d'.property
    refine ⟨⟨a,mem_nonZeroDivisors_iff_ne_zero.mp ha,?_⟩,
      ⟨b,mem_nonZeroDivisors_iff_ne_zero.mp hb,?_⟩⟩
    · change C a=d.val at eq
      rw [eq]
      simpa only [Submonoid.smul_def,Algebra.smul_def] using good
    · change b.map C=d'.val at eq'
      rw [eq']
      simpa only [Submonoid.smul_def,Algebra.smul_def] using good'
#print axioms two_generic_lines
theorem ruling_basis (A F E : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E),n=Module.finrank F E ∧
      ∀ x : E, IsIntegral A x ↔ ∀ i, b.repr x i∈Set.range (algebraMap A F) := by
  classical
  let S:=integralClosure A E
  have : Module.IsTorsionFree A E := .trans_faithfulSMul A F E
  have : Module.Free A S := IsIntegralClosure.module_free A F E S
  have : Module.Finite A S := IsIntegralClosure.finite A F E S
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization A F E S
  let j:=Module.Free.ChooseBasisIndex A S
  let a:=(Module.Free.chooseBasis A S).reindex (Fintype.equivFin j)
  let b:=Module.Basis.localizationLocalization F (nonZeroDivisors A) E a
  refine ⟨Fintype.card j,b,by simpa using (Module.finrank_eq_card_basis b).symm,?_⟩
  intro x
  constructor
  · intro hx i
    let y : S:=⟨x,hx⟩
    refine ⟨a.repr y i,?_⟩
    exact (a.localizationLocalization_repr_algebraMap F (nonZeroDivisors A) E y i).symm
  · intro all
    choose c value using all
    rw [←b.sum_repr x]
    apply IsIntegral.sum
    intro i _
    rw [←value i,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    have int : IsIntegral A (b i) := by
      rw [show b i=algebraMap S E (a i) from a.localizationLocalization_apply F (nonZeroDivisors A) E i]
      exact (a i).property
    exact isIntegral_algebraMap.mul int
#print axioms ruling_basis
end Lower6960.TwoRulings

end
end Merged_R6960TwoRulings

-- merged module R6960RetainedRestrictionTorus
section Merged_R6960RetainedRestrictionTorus

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedRestrictionTorus
open K1_14 (L)
open ChartSections (Chart overlap)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent MonicChartProbes ChartOverlapTests
open Polynomial
open scoped Polynomial Lower6960.MonicChartProbes
abbrev torus := overlapRing (false,false) (true,true)
def opposite (s : Chart) : Chart := (!s.1,!s.2)

theorem all_charts (s : Chart) : torus=overlapRing s (opposite s) := by
  ext r
  rw [show (r∈torus) ↔ _ from mem_overlap_iff (false,false) (true,true) r,mem_overlap_iff]
  rcases s with ⟨x,z⟩
  cases x <;> cases z <;> simp [overlap,opposite]

theorem to_torus (s t : Chart) : overlapRing s t≤torus := by
  intro r hr
  obtain ⟨q,hq,_⟩ := (mem_overlap_iff s t r).mp hr
  exact (mem_overlap_iff _ _ r).mpr ⟨q,hq,by simp [overlap]⟩

theorem order_mono {E : Type*} [Field E] [Algebra ChartField E] {R S : Subring ChartField}
    (le : R≤S) {y:E} (h:IsIntegral R y) : IsIntegral S y := by
  let : Algebra R S := (Subring.inclusion le).toAlgebra
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq (R:=R) (S:=S) (A:=E) fun _=>rfl
  exact h.tower_top

def edge (s t : Chart) : baseChart s := ⟨boundary s t,boundary_mem s t⟩

theorem edge_ne (s t : Chart) : boundary s t≠0 := by
  intro eq; have h:=boundaries_cancel s t; simp [eq] at h

theorem clear_torus {E : Type*} [Field E] [Algebra ChartField E] (s : Chart)
    (u : E) (h : IsIntegral torus u) :
    ∃ n : ℕ,IsIntegral (baseChart s) ((algebraMap ChartField E (boundary s (opposite s)))^n*u) := by
  rw [all_charts s] at h
  exact localize_integral _ _ (edge s (opposite s)) (edge_ne s (opposite s)) le_rfl u h

def linear (b : Bool) (c : L) : (Polynomial L) := if b then 1-C c*Polynomial.X else Polynomial.X-C c
private theorem at_zero (b : Bool) (c:L) (nz:c≠0) : (linear b c).eval 0≠0 := by
  cases b <;> simp [linear,nz]
private theorem lne (b : Bool) (c:L) (nz:c≠0) : linear b c≠0 := by
  intro eq; exact at_zero b c nz (by rw [eq,eval_zero])

def xcut (s : Chart) (x : L) : baseChart s := planeEquiv s ((linear s.1 x).map C)
def zcut (s : Chart) (z : L) : baseChart s := planeEquiv s (C (linear s.2 z))

theorem rel_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R≃+*S) {a b : R}
    (h : IsRelPrime a b) : IsRelPrime (e a) (e b) := by
  intro d da db
  have ha : e.symm d ∣ a := by simpa using map_dvd e.symm da
  have hb : e.symm d ∣ b := by simpa using map_dvd e.symm db
  simpa using (h ha hb).map e

theorem cuts_rel (s : Chart) (x z : L) (nx:x≠0) (nz:z≠0) :
    IsRelPrime (xcut s x) (zcut s z) := rel_equiv _ (TwoRulings.independent_denominators
      (linear s.2 z) (linear s.1 x) (lne _ _ nz) (lne _ _ nx)).symm

private theorem prime_axis (a : (Polynomial L)) (hn : a.eval 0≠0) :
    IsCoprime Polynomial.X a := by
  apply (irreducible_X (R:=L)).coprime_iff_not_dvd.mpr
  intro dv
  apply hn
  exact (dvd_iff_isRoot.mp (show Polynomial.X-C (0:L) ∣ a by simpa using dv))

theorem boundary_rel (s : Chart) (x z : L) (nx : x≠0) (nz : z≠0) :
    IsRelPrime (edge s (opposite s)) (xcut s x*zcut s z) := by
  let a:=linear s.1 x
  let b:=linear s.2 z
  have an:=lne s.1 x nx
  have bn:=lne s.2 z nz
  let i:= (Polynomial.mapRingHom (C : L→+*(Polynomial L)))
  let j:= (C : (Polynomial L)→+*(Polynomial (Polynomial L)))
  have e : edge s (opposite s)=planeEquiv s (i Polynomial.X * j Polynomial.X) := by
    apply Subtype.ext
    change boundary s (opposite s)=planeMap s (i Polynomial.X*j Polynomial.X)
    rw [map_mul,show i Polynomial.X=Polynomial.X from map_X _,planeMap_abscissa]
    change _=chartCoordinate s.1 RatFunc.X * planeMap s (C Polynomial.X)
    rw [planeMap_scalar]
    rcases s with ⟨y,v⟩; cases y <;> cases v <;> simp [boundary,opposite]
  rw [e,xcut,zcut,←map_mul]
  apply rel_equiv
  have h₁ := ((prime_axis a (at_zero _ _ nx)).map i).isRelPrime
  have h₂ := ((prime_axis b (at_zero _ _ nz)).map j).isRelPrime
  exact (h₁.mul_right (TwoRulings.independent_denominators b Polynomial.X bn X_ne_zero).symm).mul_left
    ((TwoRulings.independent_denominators Polynomial.X a X_ne_zero an).mul_right h₂)

variable {E : Type*} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]

/-- Independent divisibility by the two line equations on the torus already gives
divisibility by their product on every actual normalized overlap. -/
theorem cancel_both (s t : Chart) (x z : L) (nx:x≠0) (nz:z≠0) (u : E)
    (localProduct : IsIntegral (overlapRing s t)
      (algebraMap (baseChart s) E (xcut s x*zcut s z)*u))
    (onX : IsIntegral torus (algebraMap (baseChart s) E (xcut s x)*u))
    (onZ : IsIntegral torus (algebraMap (baseChart s) E (zcut s z)*u)) :
    IsIntegral (overlapRing s t) u := by
  let A:=baseChart s
  let : UniqueFactorizationMonoid A := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let a:=xcut s x
  let b:=zcut s z
  let g:=edge s (opposite s)
  let h:=edge s t
  have na : a≠0 := (map_ne_zero_iff _ (planeEquiv s).injective).mpr
    ((Polynomial.map_ne_zero_iff C_injective).mpr (lne s.1 x nx))
  have nb : b≠0 := (map_ne_zero_iff _ (planeEquiv s).injective).mpr (C_ne_zero.mpr (lne _ _ nz))
  obtain ⟨i,hi⟩:=clear_torus s _ onX
  obtain ⟨j,hj⟩:=clear_torus s _ onZ
  obtain ⟨m,hm⟩:=localize_integral A _ h (edge_ne s t) le_rfl _ localProduct
  let ι:=algebraMap A E
  have eqG : ι g=algebraMap ChartField E (boundary s (opposite s)) := rfl
  have eqH : ι h=algebraMap ChartField E (boundary s t) := rfl
  have extra (c:A) (v:E) (hv:IsIntegral A v) : IsIntegral A (ι c*v) := isIntegral_algebraMap.mul hv
  change IsIntegral A (ι g^i*(ι a*u)) at hi
  change IsIntegral A (ι g^j*(ι b*u)) at hj
  change IsIntegral A (ι h^m*(ι (a*b)*u)) at hm
  have bothCleared : IsIntegral A (ι (g^(i+j))*u) := by
    apply NormalizedFiber.integral_of_coprime_clearings ChartField na nb (cuts_rel s x z nx nz) _
    · change IsIntegral A (ι a*(ι (g^(i+j))*u))
      convert extra (g^j) _ hi using 1 <;> simp only [map_pow,pow_add,map_mul] <;> ring
    · change IsIntegral A (ι b*(ι (g^(i+j))*u))
      convert extra (g^i) _ hj using 1 <;> simp only [map_pow,pow_add,map_mul] <;> ring
  have ng : g≠0 := fun eq=>edge_ne s (opposite s) (congrArg Subtype.val eq)
  have clean : IsIntegral A (ι (h^m)*u) := by
    apply NormalizedFiber.integral_of_coprime_clearings ChartField (mul_ne_zero na nb) (pow_ne_zero _ ng)
      ((boundary_rel s x z nx nz).symm.pow_right) _
    · change IsIntegral A (ι (a*b)*(ι (h^m)*u))
      convert hm using 1 <;> simp only [map_pow,map_mul] <;> ring
    · convert extra (h^m) _ bothCleared using 1 <;> ring
  let T:=overlapRing s t
  have inv : (boundary s t)⁻¹∈T := ⟨1,by simp [edge_ne]⟩
  have ai : IsIntegral T (algebraMap ChartField E ((boundary s t)⁻¹)) :=
    isIntegral_algebraMap (x:=(⟨_,inv⟩:T))
  have result := (ai.pow m).mul (order_mono (into_cleared A h) clean)
  change IsIntegral T _ at result
  simpa only [map_inv₀,map_pow,eqH,←mul_assoc,←mul_pow,
    inv_mul_cancel₀ ((map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (edge_ne s t)),one_pow,one_mul] using result

#print axioms cuts_rel
#print axioms boundary_rel
#print axioms cancel_both
end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedRestrictionTorus

-- merged module R6960RetainedCrossingLift
section Merged_R6960RetainedCrossingLift
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedRestrictionTorus
open K1_14 (L)
open MonicChart (ChartField)
open ChartSections (Chart)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests Polynomial
open scoped Polynomial
open Lower6960.RetainedRestrictionTorus (linear)
private def cx (s : Chart) : baseChart s := planeEquiv s Polynomial.X
private def cz (s : Chart) : baseChart s := planeEquiv s (C Polynomial.X)
private def kc (s : Chart) : L→+*baseChart s := (planeEquiv s).toRingHom.comp (C.comp C)
private theorem shapeX (s : Chart) (x:L) : xcut s x =
    if s.1 then 1-kc s x*cx s else cx s-kc s x := by
  unfold xcut Lower6960.RetainedRestrictionTorus.linear
  split <;> simp [kc,cx,map_sub,map_one,map_mul]
private theorem shapeZ (s : Chart) (z:L) : zcut s z =
    if s.2 then 1-kc s z*cz s else cz s-kc s z := by
  unfold zcut Lower6960.RetainedRestrictionTorus.linear
  split <;> simp [kc,cz,map_sub,map_one,map_mul]
private theorem edge_eq (s : Chart) : edge s (opposite s)=cx s*cz s := by
  apply Subtype.ext
  change boundary s (opposite s)=planeMap s Polynomial.X*planeMap s (C Polynomial.X)
  rw [planeMap_abscissa,planeMap_scalar]
  rcases s with ⟨i,j⟩; cases i <;> cases j <;> simp [boundary,opposite]
private theorem unit_at_node {R : Type*} [CommRing R] (π : L→+*R) (b : Bool) (c : L) (nc:c≠0)
    (v:R) (zero : (if b then 1-π c*v else v-π c)=0) : IsUnit v := by
  cases b with
  | false =>
    change v-π c=0 at zero
    exact (sub_eq_zero.mp zero) ▸ nc.isUnit.map π
  | true =>
    change 1-π c*v=0 at zero
    exact ⟨⟨v,π c,(mul_comm ..).trans (sub_eq_zero.mp zero).symm,(sub_eq_zero.mp zero).symm⟩,rfl⟩
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem lift_on_chart (s : Chart) (x z : L) (nx:x≠0) (nz:z≠0) (u v : E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v)
    (matchPoint : ∃ a b:E,IsIntegral torus a ∧ IsIntegral torus b ∧
      u-v=algebraMap (baseChart s) E (xcut s x)*a+algebraMap (baseChart s) E (zcut s z)*b) :
    ∃ y a b:E,IsIntegral (baseChart s) y ∧ IsIntegral (baseChart s) a ∧
      IsIntegral (baseChart s) b ∧ u-y=algebraMap (baseChart s) E (xcut s x)*a ∧
      y-v=algebraMap (baseChart s) E (zcut s z)*b := by
  let A:=baseChart s
  let S:=integralClosure A E
  let ι:=algebraMap A S
  let p:=ι (xcut s x)
  let q:=ι (zcut s z)
  let I:=Ideal.span ({p}:Set S)⊔Ideal.span {q}
  let π:=Ideal.Quotient.mk I
  let g:=edge s (opposite s)
  have pzero : π p=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton p)))
  have qzero : π q=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton q)))
  have ux : IsUnit (π (ι (cx s))) := by
    apply unit_at_node (R:=↥S ⧸ I) ((π.comp ι).comp (kc s)) s.1 x nx (π (ι (cx s)))
    change π (ι (xcut s x))=0 at pzero
    rw [shapeX] at pzero
    by_cases hs:s.1=true <;> simpa [hs] using pzero
  have uz : IsUnit (π (ι (cz s))) := by
    apply unit_at_node (R:=↥S ⧸ I) ((π.comp ι).comp (kc s)) s.2 z nz (π (ι (cz s)))
    change π (ι (zcut s z))=0 at qzero
    rw [shapeZ] at qzero
    by_cases hs:s.2=true <;> simpa [hs] using qzero
  have unit : IsUnit (π (ι g)) := by
    change IsUnit (π (ι (edge s (opposite s))))
    rw [edge_eq,map_mul,map_mul]; exact ux.mul uz
  obtain ⟨a,b,ia,ib,eq⟩:=matchPoint
  obtain ⟨m,cm⟩:=clear_torus s _ ia
  obtain ⟨n,cn⟩:=clear_torus s _ ib
  let U:S:=⟨u,hu⟩
  let V:S:=⟨v,hv⟩
  let G:=algebraMap A E g
  let ca:S:=⟨G^m*a,cm⟩
  let cb:S:=⟨G^n*b,cn⟩
  have cleared : (ι g)^(m+n)*(U-V)=p*((ι g)^n*ca)+q*((ι g)^m*cb) := by
    apply Subtype.ext
    change G^(m+n)*(u-v)=algebraMap A E (xcut s x)*(G^n*(G^m*a))+
      algebraMap A E (zcut s z)*(G^m*(G^n*b))
    rw [eq,pow_add]; ring
  have zero : π (U-V)=0 := by
    apply (unit.pow (m+n)).mul_right_inj.mp
    rw [mul_zero,←map_pow,←map_mul,cleared,map_add,map_mul,pzero,zero_mul,map_mul,qzero,zero_mul,add_zero]
  obtain ⟨_,hp,_,hq,sum⟩:=Submodule.mem_sup.mp (show U-V ∈ I from Ideal.Quotient.eq_zero_iff_mem.mp zero)
  obtain ⟨a',rfl⟩:=Ideal.mem_span_singleton.mp hp
  obtain ⟨b',rfl⟩:=Ideal.mem_span_singleton.mp hq
  let y:=U-p*a'
  refine ⟨y,a',b',y.property,a'.property,b'.property,?_,?_⟩
  · exact congrArg Subtype.val (show U-y=p*a' from sub_sub_cancel ..)
  · have lift : y-V=q*b' := by
      change U-p*a'-V=q*b'
      calc _ = U-V-p*a' := by abel
           _ = _ := by rw [←sum,add_sub_cancel_left]
    exact congrArg (fun w:S=>(w:E)) lift
#print axioms lift_on_chart
end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedCrossingLift
