import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Near6967Large19g5At2317
import ProximityPrize.SubmissionLower.Near6967Large19g6At2317
import ProximityPrize.SubmissionLower.Near6967Large19g6At2332
import ProximityPrize.SubmissionLower.Near6967Large21g5At2317
import ProximityPrize.SubmissionLower.Near6967RescueMoment21
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6966ProofNativeSurfaceTariff
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable0_1
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable1_2
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable2_4
import ProximityPrize.SubmissionLower.R6966ProofNearLedgerTable4_3

section Merged6967_R6960ChartGlobalTests
set_option Elab.async false




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

end Merged6967_R6960ChartGlobalTests

section Merged6967_R6966ProofFarPoleChart
set_option Elab.async false



set_option Elab.async false

section Merged_R6960Front6960PoleChart

set_option Elab.async false
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.FarPoleChart
noncomputable section
open Polynomial
open P1 (K I node twist p)
open K1_14 (L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open FarRescueGeometry (Model Family)
open scoped Polynomial

private def AdjacentChart {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
private theorem adjacent_chart {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := K1_14.trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    change H.map σ ∣ liftPoly (M.E.map K1.twist)
    rw [K1_14.twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← K1_14.twist_lift]
      exact congrArg liftPoly B.scalar_fixed
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)
private theorem chart_poles {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      Fin.forall_fin_two.mpr ⟨hm, hm'⟩,
      Fin.forall_fin_two.mpr ⟨hd, hd'⟩,
      hcop, Fin.forall_fin_two.mpr ⟨hdet0, hdet1⟩⟩
  refine ⟨D, rfl, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
/-- The actual 69.60 family supplies both coprime pole blocks and all residues
for the same CRT lift used by the high interpolation banks. -/
theorem of_family {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ D : PoleData M.overhead.toNat, Nonempty (CRTLift D) ∧
      (∀ j i, (D.block j).eval (nodeL i) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  obtain ⟨H, chart⟩ := adjacent_chart M F
  obtain ⟨D, _, regular, residues⟩ := chart_poles M F H chart
  exact ⟨D, P0_10_1.crt_lift D, regular, residues⟩

#print axioms of_family
end
end Lower6960.FarPoleChart

end Merged_R6960Front6960PoleChart

end Merged6967_R6966ProofFarPoleChart

section Merged6967_R6966ProofFarRescueRates
set_option Elab.async false



set_option Elab.async false

section Merged_R6960RescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.FarRescueGeometry
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179759
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 164768

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164768) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179759 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164768 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 164768) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33697) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤164768
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33697) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164768)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 164768) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33697) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound

#print axioms curve_tariff
#print axioms fixed_count

end Lower6960.FarRescueGeometry

end
end Merged_R6960RescueGeometryTariffs

section Merged_R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.FarRescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

#print axioms rated_curve_count
end Lower6960.FarRescueGeometry

end
end Merged_R6960RescueGeometryRates

end Merged6967_R6966ProofFarRescueRates

section Merged6967_R6966ProofHelperRescueCatalogue
set_option Elab.async false











set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem all_verified (r : Fin 54) : ∀ i, Checked (request r i) := by
  fin_cases r
  · exact route0
  · exact route1
  · exact route2
  · exact route3
  · exact route4
  · exact route5
  · exact route6
  · exact route7
  · exact route8
  · exact route9
  · exact route10
  · exact route11
  · exact route12
  · exact route13
  · exact route14
  · exact route15
  · exact route16
  · exact route17
  · exact route18
  · exact route19
  · exact route20
  · exact route21
  · exact route22
  · exact route23
  · exact route24
  · exact route25
  · exact route26
  · exact route27
  · exact route28
  · exact route29
  · exact route30
  · exact route31
  · exact route32
  · exact route33
  · exact route34
  · exact route35
  · exact route36
  · exact route37
  · exact route38
  · exact route39
  · exact route40
  · exact route41
  · exact route42
  · exact route43
  · exact route44
  · exact route45
  · exact route46
  · exact route47
  · exact route48
  · exact route49
  · exact route50
  · exact route51
  · exact route52
  · exact route53

abbrev rescue (r : Fin 54) := @HelperRescueSource.prepare r (all_verified r)

abbrev avoiding (r : Fin 54) := @HelperRescueSource.avoiding_rows r (all_verified r)

abbrev selected := @HelperRescueSelection.prepare_selected all_verified

#print axioms all_verified
#print axioms rescue
#print axioms avoiding
#print axioms selected
end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueCatalogue

section Merged6967_R6966ProofLargeSeedExclusion
set_option Elab.async false





set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.LargeSeedExclusion
end Research6966.LargeSeedExclusion

end Merged6967_R6966ProofLargeSeedExclusion

section Merged6967_R6966ProofNearLedgerApply
set_option Elab.async false



set_option Elab.async false

-- merged module R6966ProofNearLedgerQuote
section Merged_R6966ProofNearLedgerQuote

namespace Research6966.NearLedger

open HelperWindowCertificate (Witness)
open HelperWindowIntervals (box)
open HelperWindowNative (orient)

theorem Pick.verified (p : Pick) : HelperWindowCertificate.Verified p.bank :=
  HelperWindowCatalogue.ordinary_verified p.index

/-- The actual retained polynomial, its on/off graph split, and the
quotient estimates supplied by any admissible verified catalogue bank. -/
structure GraphEvidence (b : Band) (a : ℕ) (i j : Fin 55) where
  onDegree : ℕ
  offDegree : ℕ
  axes : Fin 2→ℕ
  onMass : ℕ
  offMass : ℕ
  degree_enough : b.low≤onDegree+offDegree
  on_high : onDegree≤b.high
  off_high : offDegree≤b.off a
  axes_mass : ∀ z, axes z≤onMass
  projected : ∀ w : Pick, w.Valid a i j →
    (w.bank.reserve+1)*onDegree≤w.bank.B+(a-1)*w.bank.J ∧
    ∀ z u, upper (binAt i j z)=some u →
      (w.bank.reserve+1)*axes z≤w.seedBudget z+w.bank.J*u

theorem Quote.bounds {b : Band} {a : ℕ} {i j : Fin 55} {q : Quote}
    (ok : q.Valid b a i j) (G : GraphEvidence b a i j) (small : G.onMass≤massCap) :
    G.onDegree≤q.degreeCap b a ∧ ∀ z, G.axes z≤q.axisCap i j z := by
  constructor
  · cases found : q.degreePick with
    | none => simpa only [Quote.degreeCap,found] using G.on_high
    | some p =>
      have good : p.Valid a i j := by
        have v := ok.1
        simpa only [allowedPick,found,Option.elim_some] using v
      simp only [Quote.degreeCap,found,le_min_iff]
      exact ⟨G.on_high,(Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by
        rw [Nat.mul_comm]
        exact (G.projected p good).1)⟩
  · intro z
    have base := (G.axes_mass z).trans small
    cases found : q.axisPick z with
    | none => simpa only [Quote.axisCap,found] using base
    | some p =>
      cases width : upper (binAt i j z) with
      | none => simpa only [Quote.axisCap,found,width] using base
      | some u =>
        have avail : allowedPick (q.axisPick z) a i j := by
          by_cases zero : z=0
          · simpa only [Quote.axisPick,ite_eq_left zero] using ok.2.1
          · simpa only [Quote.axisPick,ite_eq_right zero] using ok.2.2.1
        have good : p.Valid a i j := by simpa only [found,allowedPick,Option.elim_some] using avail
        simp only [Quote.axisCap,found,width,le_min_iff]
        exact ⟨base,(Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by
          rw [Nat.mul_comm]
          exact (G.projected p good).2 z u width)⟩

end Research6966.NearLedger

end Merged_R6966ProofNearLedgerQuote

-- merged module R6966ProofNearLedgerApply
section Merged_R6966ProofNearLedgerApply

namespace Research6966.NearLedger
set_option maxHeartbeats 600000

theorem Invoice.mass_le {r : Fin 58} (I : Invoice (branch r)) : I.mass≤massCap :=
  (Nat.add_le_add I.primary_cap I.rescue_cap).trans (branch_base r).2.2.2.1

theorem Invoice.paid_credit {r : Fin 58} (I : Invoice (branch r)) :
    I.paid+credit*I.mass≤(branch r).base :=
  I.credit_le (branch_base r).2.1 (branch_base r).2.2.1

theorem small (r : Fin 58) (I : Invoice (branch r)) (e tail : ℕ) (he : e≤18)
    (count : tail≤density e*I.mass+(max 3 e-1)*e) : I.paid+tail≤core := by
  have d := Nat.mul_le_mul_right prime (rate_mono he)
  have deb := I.debit_le (density 18)
  have cap := branch_native r (show 18<48 by decide)
  have fixed : (max 3 e-1)*e≤17*18 :=
    Nat.mul_le_mul (Nat.sub_le_sub_right (max_le (by decide) he) 1) he
  have price := Nat.mul_le_mul_right I.mass d
  change density e*I.mass≤density 18*I.mass at price
  have final := small_cap
  omega

/-- Only the inequality corresponding to the selected pricing method is
required. Degree exclusion follows from the quotient bounds. The physical
large-seed exclusion must be supplied by the graph argument. -/
def Quote.Demand {r : Fin 58} (q : Quote) (b : Band) (a : ℕ) (i j : Fin 55)
    (I : Invoice (branch r)) (G : GraphEvidence b a i j) (tail : ℕ) : Prop :=
  let g := q.degreeCap b a
  let off := b.off a
  match q.method with
  | .degree => True
  | .large => False
  | .native => tail≤density (max g off)*I.mass+b.additive
  | .axis => tail≤rate g*(G.axes 0+prime*G.axes 1)+density off*G.offMass+b.additive
  | .surface | .affine | .single | .fixed =>
    tail≤q.wordPrice b a i j+density off*G.offMass+b.additive

private theorem credit_word {r : Fin 58} (I : Invoice (branch r)) {tail fee offMass additive off : ℕ}
    (fits : offMass≤I.mass) (offPrice : off≤credit) (budget : fee+additive≤free)
    (count : tail≤fee+off*offMass+additive) : I.paid+tail≤core := by
  have pay := I.paid_credit
  have price := Nat.mul_le_mul offPrice fits
  have left := (branch_base r).1
  omega

private theorem split_credit (d m : ℕ) : d*m≤credit*m+(d-credit)*m := by
  by_cases low : d≤credit
  · exact (Nat.mul_le_mul_right m low).trans (Nat.le_add_right _ _)
  · rw [← Nat.add_mul, Nat.add_sub_of_le (show credit≤d by omega)]

theorem Quote.finish {r : Fin 58} (I : Invoice (branch r)) {b : Band} {a : ℕ} {i j : Fin 55} {q : Quote}
    (ok : q.Valid b a i j) (G : GraphEvidence b a i j)
    (mass : G.onMass+G.offMass≤I.mass) (tail : ℕ) (count : q.Demand b a i j I G tail) :
    I.paid+tail≤core := by
  have budget := ok.2.2.2
  have on : G.onMass≤I.mass := (Nat.le_add_right _ _).trans mass
  have off : G.offMass≤I.mass := (Nat.le_add_left _ _).trans mass
  obtain ⟨grade,axes⟩ := q.bounds ok G (on.trans I.mass_le)
  cases kind : q.method
  · simp only [Quote.Paid,kind] at budget
    have need := G.degree_enough
    have split := G.off_high
    omega
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    have debit := I.debit_le (density (max (q.degreeCap b a) (b.off a)))
    have limit := branch_native r budget.1
    have room := budget.2
    omega
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    let g := q.degreeCap b a
    let y := G.axes 1
    have fit : y+G.offMass≤I.mass := (Nat.add_le_add_right (G.axes_mass 1) _).trans mass
    have collected : credit*y+density (b.off a)*G.offMass≤credit*I.mass := by
      calc
        _ ≤ credit*y+credit*G.offMass :=
          Nat.add_le_add_left (Nat.mul_le_mul_right G.offMass budget.2.1) _
        _ = credit*(y+G.offMass) := by rw [Nat.mul_add]
        _ ≤ _ := Nat.mul_le_mul_left credit fit
    have onFee := split_credit (density g) y
    have rest : rate g*G.axes 0+(density g-credit)*y≤q.axisPrice b a i j :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (axes 0)) (Nat.mul_le_mul_left _ (axes 1))
    have exact_count :
        tail≤rate g*G.axes 0+density g*y+density (b.off a)*G.offMass+b.additive := by
      dsimp only [g,y,density]
      rw [Nat.mul_add, ← Nat.mul_assoc] at count
      exact count
    have pay := I.paid_credit
    have left := (branch_base r).1
    have floor := budget.2.2
    omega
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.1 budget.2.2 count
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.2.1 budget.2.2.2 count
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.2.2.1 budget.2.2.2.2 count
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.2.1 budget.2.2.2 count
  · simp only [Quote.Demand,kind] at count

#print axioms small
#print axioms Quote.finish
end Research6966.NearLedger

end Merged_R6966ProofNearLedgerApply

end Merged6967_R6966ProofNearLedgerApply

section Merged6967_R6966ProofNearLedgerCatalogue
set_option Elab.async false



























set_option Elab.async false
namespace Research6966.NearLedger
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def quote (b : Fin 7) (a : ℕ) : Fin 55 → Fin 55 → Quote :=
  match b.val,a with
  | 0,1 => q0_1
  | 0,2 => q0_2
  | 0,3 => q0_3
  | 0,4 => q0_4
  | 0,5 => q0_5
  | 0,6 => q0_6
  | 1,1 => q1_1
  | 1,2 => q1_2
  | 1,3 => q1_3
  | 1,4 => q1_4
  | 1,5 => q1_5
  | 2,1 => q2_1
  | 2,2 => q2_2
  | 2,3 => q2_3
  | 2,4 => q2_4
  | 3,1 => q3_1
  | 3,2 => q3_2
  | 3,3 => q3_3
  | 3,4 => q3_4
  | 4,1 => q4_1
  | 4,2 => q4_2
  | 4,3 => q4_3
  | 5,1 => q5_1
  | 5,2 => q5_2
  | 5,3 => q5_3
  | 6,1 => q6_1
  | 6,2 => q6_2
  | _,_ => fun _ _ => ⟨.degree,none,none,none⟩
theorem quote_valid (b : Fin 7) (a : ℕ) (lo : 0<a) (hi : a≤(band b).maxGraph) (i j : Fin 55) : (quote b a i j).Valid (band b) a i j := by
  fin_cases b
  · change a≤6 at hi
    interval_cases a
    · exact q0_1_ok i j
    · exact q0_2_ok i j
    · exact q0_3_ok i j
    · exact q0_4_ok i j
    · exact q0_5_ok i j
    · exact q0_6_ok i j
  · change a≤5 at hi
    interval_cases a
    · exact q1_1_ok i j
    · exact q1_2_ok i j
    · exact q1_3_ok i j
    · exact q1_4_ok i j
    · exact q1_5_ok i j
  · change a≤4 at hi
    interval_cases a
    · exact q2_1_ok i j
    · exact q2_2_ok i j
    · exact q2_3_ok i j
    · exact q2_4_ok i j
  · change a≤4 at hi
    interval_cases a
    · exact q3_1_ok i j
    · exact q3_2_ok i j
    · exact q3_3_ok i j
    · exact q3_4_ok i j
  · change a≤3 at hi
    interval_cases a
    · exact q4_1_ok i j
    · exact q4_2_ok i j
    · exact q4_3_ok i j
  · change a≤3 at hi
    interval_cases a
    · exact q5_1_ok i j
    · exact q5_2_ok i j
    · exact q5_3_ok i j
  · change a≤2 at hi
    interval_cases a
    · exact q6_1_ok i j
    · exact q6_2_ok i j

end Research6966.NearLedger

end Merged6967_R6966ProofNearLedgerCatalogue

section Merged6967_R6966ProofPhysicalHelperTariff
set_option Elab.async false



set_option Elab.async false

namespace Research6966.PhysicalHelperTariff
open Polynomial Finset
open K1 (I K p)
open K1_14 (Jet L FX Seeds seedEmbedding atX graphEval liftPoly jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct seedPair)
open K1_14_3 (SeedField SeedClosure)
open PadeNativeQuotient (Native)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 950000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev f:=algebraMap Seeds SeedField

def graphOf (N:Jet) : Pade.Row SeedField:=⟨(N.coeff 1).map f,-(N.coeff 0).map f⟩

private theorem equation {N:Jet} (deg:N.natDegree=1) :
    (graphOf N).polynomial=K1_14_1_4.doubleMap f N := by
  have eq:=congrArg (K1_14_1_4.doubleMap f) (eq_X_add_C_of_natDegree_le_one deg.le)
  simpa only [graphOf,Pade.Row.polynomial,map_neg,sub_neg_eq_add,K1_14_1_4.doubleMap,coe_mapRingHom,
    Polynomial.map_C,Polynomial.map_X,Polynomial.map_mul,Polynomial.map_add] using eq.symm

theorem primitive {N:Jet} (prime:Prime N) (deg:N.natDegree=1) : (graphOf N).primitive := by
  have fi:=IsFractionRing.injective Seeds SeedField
  have ir:=HelperPhysicalModel.generic_prime prime (show 0<N.natDegree from deg ▸ Nat.zero_lt_one)
  have nde:(K1_14_1_4.doubleMap f N).natDegree=1:=(natDegree_map_eq_of_injective (map_injective f fi) N).trans deg
  have prim:(graphOf N).polynomial.IsPrimitive := (equation deg) ▸ ir.isPrimitive (nde.trans_ne one_ne_zero)
  constructor
  · change (N.coeff 1).map f≠0
    apply (map_ne_zero_iff (mapRingHom f) (map_injective f fi)).mpr
    rw [←deg,coeff_natDegree];exact leadingCoeff_ne_zero.mpr prime.ne_zero
  · apply isRelPrime_iff_isCoprime.mp
    intro d da db
    apply prim d
    exact dvd_sub ((_root_.map_dvd C da).mul_right _) (_root_.map_dvd C db)

def realization {N:Jet} (prime:Prime N) (deg:N.natDegree=1) : Native (graphOf N) where
  poly:=N
  primitive:=prime.irreducible.isPrimitive (deg.trans_ne one_ne_zero)
  scalar:=1
  nonzero:=one_ne_zero
  eq:=by
    have eq:=congrArg (K1_14_1_4.doubleMap K1_14_3.seedGeneric) (eq_X_add_C_of_natDegree_le_one deg.le)
    simp only [graphOf,Pade.Row.map,Pade.Row.polynomial,K1_14_1.jetConstant,RingHom.comp_apply,map_one,one_mul,
      Polynomial.map_neg,map_neg,sub_neg_eq_add,Polynomial.map_map,K1_14_1_4.doubleMap,K1_14_3.fibreRow,coe_mapRingHom,
      Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,K1_14_3.seedGeneric] at eq ⊢
    exact eq

private theorem root_law {N:Jet} (nd:N.natDegree=1) {S:K[X]} {z:K} (root:jetAt N z S=0) :
    (N.coeff 1).eval₂ (graphEval z) (atX S)*atX S.derivative=(-N.coeff 0).eval₂ (graphEval z) (atX S) := by
  let ev:=eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  change ev N=0 at root
  have id:=congrArg ev (eq_X_add_C_of_natDegree_le_one nd.le)
  simp only [ev,map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X] at id
  rw [eval₂_neg];apply eq_neg_of_add_eq_zero_left
  exact id.symm.trans root

/-- Word-level price on the quadratic helper before terminal selection.
The CRT residues, physical graph weight, node count and seed degree all
refer to the same original helper and the same marked P1 words. -/
theorem price {u deleted maxHeight a} {anchor:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (fam:P1.FamilyAt a anchor Γ) (sub:T⊆Γ) {h:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N) (prime:Prime N) (ns:N.natDegree=1)
    (quad:K1_14_2_2_2_1.jetDegree N=2) (width d:ℕ)
    (cap:∀ j i,((N.coeff j).coeff i).totalDegree≤width) (small:3*width<p)
    (physical:(131071:ℤ)+anchor.overhead≤d) (dCap:d≤131071+h) (dp:d<p) (gap:d<a)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀ γ∈T,MarkResidues D (anchor.label γ) (fam.scalar γ))
    (belongs:∀ γ∈T,jetAt N (anchor.label γ) (fam.scalar γ)=0) :
    let w:=131071-h
    let Lw:=RawPhysicalDegree.weight w (w-1) M.raw
    let votes:=a-(Lw-(w-1))
    let target:=((Fintype.card I-a)*((2*d-1)*width)+(a-d))^2/(a-d)^2
    T.card*votes ≤ (3*(width+p*width))*votes+Fintype.card I*target := by
  classical
  let G:=graphOf N
  let N₀:=realization prime ns
  have gp:=primitive prime ns
  obtain ⟨data⟩:=IntegralGraphModels.exists_model M prime ns
  have graph:G.graphDegree=2 := (HelperWeightCap.native_degree N₀ gp).symm.trans quad
  let y (z:K):=atX (fam.scalar z)
  let evalAt (z:K) (P:K1_14.Equation):=P.eval₂ (graphEval (anchor.label z)) (y z)
  let bad:=T.filter (fun z=>evalAt z (N.coeff 1)=0)
  let good:=T\bad
  have good_sub:good⊆T:=sdiff_subset
  have nz (z:↥good):evalAt z.val (N.coeff 1)≠0 :=
    fun eq=>(mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨good_sub z.property,eq⟩)
  have law (z:K) (mem:z∈T):evalAt z (N.coeff 1)*atX (fam.scalar z).derivative=evalAt z (-N.coeff 0) :=
    root_law ns (belongs z mem)
  have inj:Function.Injective anchor.label:=fun _ _ eq=>sub_left_injective (b:=anchor.shift) eq
  have badBudget:bad.card≤3*(width+p*width) := by
    have bound:=NativeGraphExceptional.singular_count N₀ gp (fun _=>width)
      (fun j i z=>(((N.coeff j).coeff i).degreeOf_le_totalDegree z).trans (cap j i))
      (by change (2*G.graphDegree-1)*width<p;rw [graph];exact small)
      bad anchor.label inj.injOn y (fun z mem=>(mem_filter.mp mem).2) (by
        intro z mem
        obtain ⟨orig,den⟩:=mem_filter.mp mem
        have step:=law z orig;rw [den,zero_mul] at step;exact step.symm)
    change bad.card≤(2*G.graphDegree-1)*(width+p*width) at bound
    rwa [graph] at bound
  let words (z:↥good):=liftPoly (fam.scalar z.val)
  have mark (z:↥good):=fam.mark z.val (sub (good_sub z.property))
  have deg (z:↥good):(words z).natDegree≤d := by
    change ((fam.scalar z.val).map (algebraMap K L)).natDegree≤d
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (mark z).scalar_degree with zero|limit
    · simp [zero]
    · change ((fam.scalar z.val).natDegree:ℤ)≤131071+anchor.overhead at limit;omega
  let n (i:I):L:=algebraMap K L (K1.node i)
  let ans (i:I):L:=algebraMap K L (anchor.word i)
  have unique:Function.Injective words:=fun x z eq=>Subtype.ext (fam.distinct (sub (good_sub x.property))
    (sub (good_sub z.property)) ((map_injective _ (algebraMap K L).injective) eq))
  have weights:=FixedNodeTariff.count (fun z:↥good=>seedPair (anchor.label z.val)) words unique n
    ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective) ans
    (PhysicalOriginal.integralA data.original) (PhysicalOriginal.integralB data.original)
    d width a (RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw-(131071-h-1))
    (fun i=>by rw [PhysicalOriginal.integralA,coeff_map];exact (PhysicalOriginal.coefficient_height data 1 i).trans (cap 1 i))
    (fun i=>by rw [PhysicalOriginal.integralB,coeff_neg,MvPolynomial.totalDegree_neg,coeff_map];exact (PhysicalOriginal.coefficient_height data 0 i).trans (cap 0 i))
    (fun i hi=>by
      intro zero
      have badInt:=congrArg (algebraMap L FX) zero
      simp only [map_natCast,map_zero] at badInt
      exact K1_14_2_4_2.factorial_ne_zero (hi.trans_lt dp) badInt)
    gap deg (fun z=>PhysicalOriginal.word_law data _ _ (law z (good_sub z.property))) (by
      intro z;let b:=mark z
      exact ⟨b.bad.support,b.bad.agreement,fun i mem=>(Polynomial.eval_map_apply (algebraMap K L) _).trans (congrArg _ (b.scalar_hits i mem))⟩)
    (by
      intro z
      obtain ⟨P,pn,pd,whenGood⟩:=PhysicalMonitor.witness hp hl data (anchor.label z.val) (fam.scalar z.val)
        (res z (good_sub z.property)) ((deg z).trans dCap) (nz z)
      exact ⟨P,pn,pd,fun i=>whenGood _ (nodes i)⟩)
  rw [Fintype.card_coe] at weights
  have size:good.card+bad.card=T.card:=card_sdiff_add_card_eq_card (filter_subset _ _)
  dsimp only
  rw [←size,Nat.add_mul]
  exact (Nat.add_le_add weights (Nat.mul_le_mul_right _ badBudget)).trans_eq (Nat.add_comm _ _)

#print axioms price
end
end Research6966.PhysicalHelperTariff

end Merged6967_R6966ProofPhysicalHelperTariff
