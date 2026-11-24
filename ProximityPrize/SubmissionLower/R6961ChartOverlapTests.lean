import ProximityPrize.SubmissionLower.R6961MonicFourChartDescent
import ProximityPrize.SubmissionLower.R6960ChartTraceTests
import Mathlib.RingTheory.Localization.Integral

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.ChartOverlapTests
open MonicFourChartDescent Lower6960.MonicChart Lower6961.MonicChart Lower6960.ChartSections Polynomial Algebra Submodule
open K1_14 (L)

/-- The chart coordinates that have to be inverted to reach the other chart. -/
def boundary (s t : Chart) : ChartField :=
  (if s.1=t.1 then 1 else chartCoordinate s.1 RatFunc.X) *
  (if s.2=t.2 then 1 else chartCoordinate s.2 scalarCoordinate)

theorem scalar_ne : scalarCoordinate≠0 := by
  exact (map_ne_zero_iff _ RatFunc.C_injective).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) Scalar)).mpr X_ne_zero)

private theorem xmem (s : Chart) : chartCoordinate s.1 RatFunc.X∈baseChart s :=
  Subring.subset_closure (Or.inr (Or.inl rfl))
private theorem zmem (s : Chart) : chartCoordinate s.2 scalarCoordinate∈baseChart s :=
  Subring.subset_closure (Or.inr (Or.inr rfl))

theorem boundary_mem (s t : Chart) : boundary s t∈baseChart s := by
  apply (baseChart s).mul_mem
  · split <;> first | exact (baseChart s).one_mem | exact xmem s
  · split <;> first | exact (baseChart s).one_mem | exact zmem s

private theorem changed_product (s t : Bool) (x : ChartField) (hn : x≠0) (ne : s≠t) :
    chartCoordinate s x * chartCoordinate t x=1 := by
  cases s <;> cases t <;> simp_all [chartCoordinate]

theorem boundaries_cancel (s t : Chart) : boundary s t * boundary t s=1 := by
  unfold boundary
  rw [mul_mul_mul_comm]
  by_cases x : s.1=t.1 <;> by_cases z : s.2=t.2 <;>
    simp [x,z,eq_comm (a:=t.1) (b:=s.1),eq_comm (a:=t.2) (b:=s.2),
      changed_product s.1 t.1 _ RatFunc.X_ne_zero,changed_product s.2 t.2 _ scalar_ne]

section
variable {F : Type*} [Field F]

/-- Localization inside a fixed field, with the power that clears a given element retained. -/
def cleared (A : Subring F) (g : A) : Subring F where
  carrier := {x | ∃ n : ℕ, (g:F)^n*x ∈ A}
  zero_mem' := ⟨0,by simp⟩
  one_mem' := ⟨0,by simp⟩
  neg_mem' := by rintro _ ⟨n,h⟩; exact ⟨n,by simpa using A.neg_mem h⟩
  add_mem' := by
    rintro x y ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨m+n,?_⟩
    rw [mul_add,pow_add,mul_assoc, mul_comm ((g:F)^m) ((g:F)^n),mul_assoc]
    exact A.add_mem (A.mul_mem (A.pow_mem g.property _) hn) (A.mul_mem (A.pow_mem g.property _) hm)
  mul_mem' := by
    rintro x y ⟨n,hn⟩ ⟨m,hm⟩
    exact ⟨n+m,by simpa only [pow_add,mul_mul_mul_comm ((g:F)^n) x] using A.mul_mem hn hm⟩

theorem into_cleared (A : Subring F) (g : A) : A ≤ cleared A g :=
  fun x hx => ⟨0, by simpa using hx⟩

theorem localize_integral {E : Type*} [Field E] [Algebra F E]
    (A B : Subring F) (g : A) (ne : (g:F)≠0) (cover : B≤cleared A g)
    (x : E) (h : IsIntegral B x) :
    ∃ n : ℕ, IsIntegral A ((algebraMap F E (g:F))^n * x) := by
  let C:=cleared A g
  let : Algebra A C := (Subring.inclusion (into_cleared A g)).toAlgebra
  let : Algebra B C := (Subring.inclusion cover).toAlgebra
  let : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsLocalization.Away g C := IsLocalization.Away.mk g (by
    let inv : C:=⟨(g:F)⁻¹,1,by simp [ne]⟩
    exact ⟨⟨algebraMap A C g,inv,Subtype.ext (mul_inv_cancel₀ ne),Subtype.ext (inv_mul_cancel₀ ne)⟩,rfl⟩)
    (by intro z; obtain ⟨n,hn⟩:=z.property; exact ⟨n,⟨_,hn⟩,Subtype.ext (mul_comm ..)⟩)
    (by intro v w eq; exact ⟨0,by simpa using (show v=w from Subtype.ext (congrArg (fun z:C=>(z:F)) eq))⟩)
  obtain ⟨m,hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers g) x
    (show IsIntegral C x from h.tower_top)
  obtain ⟨n,eq⟩ := m.property
  rw [Submonoid.smul_def,Algebra.smul_def,←eq,map_pow] at hm
  exact ⟨n,hm⟩
end

theorem chart_cover (s t : Chart) :
    baseChart t ≤ cleared (baseChart s) ⟨boundary s t,boundary_mem s t⟩ := by
  apply Subring.closure_le.mpr
  intro v hv
  rcases hv with ⟨c,rfl⟩ | (eq|eq)
  · exact into_cleared _ _ (Subring.subset_closure (Or.inl ⟨c,rfl⟩))
  · change v=chartCoordinate t.1 RatFunc.X at eq
    subst v
    by_cases h:s.1=t.1
    · rw [←h]; exact into_cleared _ _ (xmem s)
    · refine ⟨1,?_⟩
      change boundary s t^1*chartCoordinate t.1 RatFunc.X ∈ baseChart s
      simp only [pow_one,boundary,h,reduceIte]
      rw [mul_right_comm,changed_product _ _ _ RatFunc.X_ne_zero h,one_mul]
      split <;> first | exact (baseChart s).one_mem | exact zmem s
  · change v=chartCoordinate t.2 scalarCoordinate at eq
    subst v
    by_cases h:s.2=t.2
    · rw [←h]; exact into_cleared _ _ (zmem s)
    · refine ⟨1,?_⟩
      change boundary s t^1*chartCoordinate t.2 scalarCoordinate ∈ baseChart s
      simp only [pow_one,boundary,h,reduceIte]
      rw [mul_assoc,changed_product _ _ _ scalar_ne h,mul_one]
      split <;> first | exact (baseChart s).one_mem | exact xmem s

#print axioms chart_cover
#print axioms localize_integral

variable {E : Type*} [Field E] [Algebra ChartField E]

/-- A scalar test regular on the first normalized chart has only boundary
poles on the second. The power clears the value on the entire order. -/
theorem uniform_transfer (s t : Chart)
    [Module.Finite (baseChart t) (integralClosure (baseChart t) E)]
    (test : E →ₗ[ChartField] ChartField)
    (regular : ∀ x : E, IsIntegral (baseChart s) x → test x ∈ baseChart s) :
    ∃ N : ℕ, ∀ x : E, IsIntegral (baseChart t) x → boundary t s^N*test x ∈ baseChart t := by
  classical
  let A:=baseChart t
  let B:=integralClosure A E
  let g:=boundary t s
  let h:=boundary s t
  have gh : g*h=1 := boundaries_cancel t s
  have hn : h≠0 := by intro z; simp [z] at gh
  have single (x : B) : ∃ n : ℕ, g^n*test x ∈ A := by
    obtain ⟨n,good⟩ := localize_integral (baseChart s) A ⟨h,boundary_mem s t⟩ hn
      (chart_cover s t) x.val x.property
    have eq : test ((algebraMap ChartField E h)^n*x.val)=h^n*test x := by
      rw [←map_pow,←Algebra.smul_def,map_smul,smul_eq_mul]
    obtain ⟨m,hm⟩ := chart_cover t s (eq ▸ regular _ good)
    change g^m*(h^n*test x) ∈ A at hm
    have ident : g^n*(g^m*(h^n*test x))=g^m*test x := by
      calc _ = (g*h)^n*(g^m*test x) := by rw [mul_pow]; ring
           _ = _ := by rw [gh,one_pow,one_mul]
    exact ⟨m,ident ▸ A.mul_mem (A.pow_mem (boundary_mem t s) n) hm⟩
  obtain ⟨G,spans⟩ := (inferInstance : Module.Finite A B).1
  choose order fits using single
  let N:=G.sup order
  refine ⟨N,fun x hx => ?_⟩
  let testMap : B →ₗ[A] ChartField :=
    (test.restrictScalars A).comp B.val.toLinearMap
  have covers (y : B) : g^N*test y ∈ A := by
    have hy : y∈span A (G:Set B) := spans ▸ mem_top
    induction hy using Submodule.span_induction with
    | mem u hu =>
      have le : order u≤N := Finset.le_sup (f:=order) hu
      rw [←Nat.sub_add_cancel le,pow_add,mul_assoc]
      exact A.mul_mem (A.pow_mem (boundary_mem t s) _) (fits u)
    | zero => simp
    | add u v _ _ su sv =>
      change g^N*test (u.val+v.val) ∈ A
      rw [map_add,mul_add]; exact A.add_mem su sv
    | smul c u _ su =>
      change g^N*testMap (c • u) ∈ A
      rw [map_smul]
      change g^N*((c:ChartField)*test u) ∈ A
      rw [mul_left_comm]; exact A.mul_mem c.property su
  exact covers ⟨x,hx⟩

#print axioms uniform_transfer
end Lower6961.ChartOverlapTests
