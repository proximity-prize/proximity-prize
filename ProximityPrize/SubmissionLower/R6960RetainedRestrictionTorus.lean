import ProximityPrize.SubmissionLower.R6960RetainedLineRestriction
import ProximityPrize.SubmissionLower.R6960TwoRulings

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
