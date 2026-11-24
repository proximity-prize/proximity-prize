import ProximityPrize.SubmissionLower.R6960ChartOverlapTests
import ProximityPrize.SubmissionLower.R6960MonicChartProbes

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

/-- A single field-linear map tests the whole normalized cover. Its common positive twist
depends on the factor; it is independent of the sections and the twist to be corrected. -/
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

/-- Regular linear tests extend to each overlap by clearing exactly the inverted axes. -/
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
