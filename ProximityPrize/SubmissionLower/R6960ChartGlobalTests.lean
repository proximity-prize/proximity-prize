import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import Mathlib.RingTheory.Localization.Integral

set_option Elab.async false

-- merged module R6960ChartOverlapTests
section Merged_R6960ChartOverlapTests
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.ChartOverlapTests
open MonicFourChartDescent MonicChart ChartSections Polynomial Algebra Submodule
open K1_14 (L)
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
end Lower6960.ChartOverlapTests

end
end Merged_R6960ChartOverlapTests

-- merged module R6960ChartGlobalTests
section Merged_R6960ChartGlobalTests
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.ChartGlobalTests
open MonicChart MonicFourChartDescent ChartSections ChartOverlapTests Algebra
open scoped Lower6960.MonicChartProbes
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view)
theorem frame_ne (a b : ℕ) (s : Chart) : frame a b s≠0 := by
  rcases s with ⟨i,j⟩
  cases i <;> cases j <;> simp [frame,RatFunc.X_ne_zero,scalar_ne]
theorem frame_ratio (D : ℕ) (t s : Chart) :
    frame D D s / frame D D t=boundary t s^D := by
  rcases s with ⟨i,j⟩
  rcases t with ⟨v,w⟩
  cases i <;> cases j <;> cases v <;> cases w <;>
    simp [frame,boundary,chartCoordinate,mul_pow,div_eq_mul_inv,mul_inv_rev,
      RatFunc.X_ne_zero,scalar_ne] <;> field_simp [RatFunc.X_ne_zero,scalar_ne]
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem simultaneous_tests (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (b : PowerBasis ChartField E)
    (root : aeval b.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    ∃ n D : ℕ, ∃ P : E →ₗ[ChartField] (Fin n → ChartField), ∀ s (x : E),
      IsIntegral (baseChart s) x ↔ ∀ j, P x j / frame D D s ∈ baseChart s := by
  classical
  let : FiniteDimensional ChartField E := b.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hi b root
  obtain ⟨T,tests⟩ := MonicChartProbes.actual_integral_iff_finite_traces f ir lo hi b root
  let J := (s : Chart) × ↥(T s)
  let ell (j:J) := traceForm ChartField E j.2.val
  have regular (j:J) (x:E) (h:IsIntegral (baseChart j.1) x) : ell j x∈baseChart j.1 :=
    (tests j.1 x).mp h j.2 j.2.property
  have existsBound (a : Chart×J) : ∃ N : ℕ, ∀ x : E, IsIntegral (baseChart a.1) x →
      boundary a.1 a.2.1^N*ell a.2 x∈baseChart a.1 := by
    let := IsIntegralClosure.finite (baseChart a.1) ChartField E (integralClosure (baseChart a.1) E)
    exact uniform_transfer a.2.1 a.1 (ell a.2) (regular a.2)
  choose bound works using existsBound
  let D:=Finset.univ.sup bound
  let reindex := (Fintype.equivFin J).symm
  let P := LinearMap.pi (fun j : Fin (Fintype.card J) =>
    frame D D (reindex j).1 • ell (reindex j))
  refine ⟨Fintype.card J,D,P,fun s x => ⟨?_,?_⟩⟩
  · intro int i
    let j:=reindex i
    have le : bound (s,j)≤D := Finset.le_sup (f:=bound) (Finset.mem_univ _)
    change frame D D j.1 * ell j x / frame D D s∈baseChart s
    rw [mul_div_right_comm,frame_ratio,←Nat.sub_add_cancel le,pow_add,mul_assoc]
    exact (baseChart s).mul_mem ((baseChart s).pow_mem (boundary_mem s j.1) _) (works (s,j) x int)
  · intro hx
    apply (tests s x).mpr
    intro d hd
    let j : J:=⟨s,⟨d,hd⟩⟩
    obtain ⟨i,eq⟩:= reindex.surjective j
    have val:=hx i
    change frame D D (reindex i).1*ell (reindex i) x / frame D D s∈baseChart s at val
    rw [eq] at val
    simpa only [j,mul_div_right_comm,div_self (frame_ne D D s),one_mul,ell,traceForm_apply] using val
theorem overlap_test (s t : Chart) (test : E →ₗ[ChartField] ChartField)
    (regular : ∀ x : E, IsIntegral (baseChart s) x → test x ∈ baseChart s) (x : E)
    (hx : IsIntegral (cleared (baseChart s) ⟨_,boundary_mem s t⟩) x) :
    test x∈cleared (baseChart s) ⟨_,boundary_mem s t⟩ := by
  have ne : boundary s t≠0 := by intro z; have h:=boundaries_cancel s t; simp [z] at h
  obtain ⟨n,good⟩ := localize_integral (baseChart s) _ ⟨_,boundary_mem s t⟩ ne le_rfl x hx
  refine ⟨n,?_⟩
  have val:=regular _ good
  rwa [←map_pow,←Algebra.smul_def,map_smul,smul_eq_mul] at val
#print axioms simultaneous_tests
#print axioms overlap_test
end Lower6960.ChartGlobalTests

end
end Merged_R6960ChartGlobalTests
