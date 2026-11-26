import ProximityPrize.Benchmark.TargetLower

section Merged6967_Gate6966Gate
set_option Elab.async false





set_option Elab.async false

set_option autoImplicit false

namespace Gate6966Gate

open Module

section Overlap

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

theorem threshold_overlap (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (h : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < ∑ i ∈ s, finrank 𝕜 (V i)) :
    ∃ i ∈ s, W i < finrank 𝕜 ↥(V i ⊓ M i) := by
  classical
  by_contra! hn
  apply Nat.not_lt_of_ge ?_ h
  refine Finset.sum_le_sum fun i hi => ?_
  have he := Submodule.finrank_sup_add_finrank_inf_eq (V i) (M i)
  have hsup := (V i ⊔ M i).finrank_le
  have hi' := hn i hi
  omega

end Overlap

section Gate

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable {G : Type*}

theorem gate₂ (Target : Prop) (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (Good : ι → G → Prop) (free : ι → G → ℕ)
    (hdich : ∀ i ∈ s, ∀ U : Submodule 𝕜 E, U ≤ V i ⊓ M i → U ≠ ⊥ →
      ∃ g : G, finrank 𝕜 U ≤ free i g ∧ (Good i g → Target))
    (hW : ∀ i ∈ s, ∀ g : G, ¬ Good i g → free i g ≤ W i)
    (hsum : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < ∑ i ∈ s, finrank 𝕜 (V i)) :
    Target := by
  obtain ⟨i, hi, hlt⟩ := threshold_overlap s V M W hsum
  have hne : (V i ⊓ M i) ≠ ⊥ := by
    intro hb
    rw [hb, _root_.finrank_bot] at hlt
    exact Nat.not_lt_zero _ hlt
  obtain ⟨g, hfin, hgood⟩ := hdich i hi (V i ⊓ M i) le_rfl hne
  by_cases hG : Good i g
  · exact hgood hG
  · exact absurd (hfin.trans (hW i hi g hG)) (Nat.not_le_of_lt hlt)

theorem gate₂_of_need (Target : Prop) (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (Good : ι → G → Prop) (free : ι → G → ℕ) (need : ℕ)
    (hdich : ∀ i ∈ s, ∀ U : Submodule 𝕜 E, U ≤ V i ⊓ M i → U ≠ ⊥ →
      ∃ g : G, finrank 𝕜 U ≤ free i g ∧ (Good i g → Target))
    (hW : ∀ i ∈ s, ∀ g : G, ¬ Good i g → free i g ≤ W i)
    (hneed : need ≤ ∑ i ∈ s, finrank 𝕜 (V i))
    (hsum : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < need) :
    Target :=
  gate₂ Target s V M W Good free hdich hW (hsum.trans_le hneed)

end Gate

end Gate6966Gate

end Merged6967_Gate6966Gate

section Merged6967_KoalaCutGeometry
set_option Elab.async false




set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
namespace SplitCut
open Polynomial
theorem compress_rows {F : Type*} [Field F] (n m p D : ℕ) (hD : D < p)
    (hdim : m*p < n*(p-D)) (A : Fin m → Fin n → (Polynomial F))
    (hA : ∀ i j, (A i j).natDegree ≤ D) :
    ∃ w : Fin n → degreeLT F (p-D), w ≠ 0 ∧
      ∀ i, ∑ j, A i j * (w j : (Polynomial F)) = 0 := by
  classical
  have hs (w : Fin n → degreeLT F (p-D)) (i : Fin m) :
      (∑ j, A i j * (w j : (Polynomial F))) ∈ degreeLT F p := by
    apply Submodule.sum_mem
    intro j _
    by_cases hw : (w j : (Polynomial F)) = 0
    · simp [hw]
    by_cases ha : A i j = 0
    · simp [ha]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero ha hw)).mp
    have h := (natDegree_lt_iff_degree_lt hw).mpr
      (mem_degreeLT.mp (w j).property)
    have := natDegree_mul_le (p := A i j) (q := (w j : (Polynomial F)))
    have := hA i j
    omega
  let M : (Fin n → degreeLT F (p-D)) →ₗ[F] (Fin m → degreeLT F p) :=
    { toFun := fun w i => ⟨∑ j, A i j * (w j : (Polynomial F)), hs w i⟩
      map_add' := by
        intro w z
        funext i
        apply Subtype.ext
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext i
        apply Subtype.ext
        simp [Finset.smul_sum] }
  have hd (a b : ℕ) : Module.finrank F (Fin a → degreeLT F b) = a*b := by
    simp [Module.finrank_pi_fintype, (degreeLTEquiv F b).finrank_eq]
  have hni : ¬ Function.Injective M := fun hi => hdim.not_ge
    (by simpa only [hd] using LinearMap.finrank_le_finrank_of_injective hi)
  rw [LinearMap.ker_eq_bot.symm] at hni
  obtain ⟨w, hw, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hni
  refine ⟨w, hn, fun i => ?_⟩
  exact congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hw) i)
theorem compression_guard {n k p D m : ℕ} (hk : k ≤ n) (hD : D ≤ p)
    (hm : m ≤ n-k) (hg : n*D < k*p) : m*p < n*(p-D) := by
  calc
    m*p ≤ (n-k)*p := Nat.mul_le_mul_right p hm
    _ < n*(p-D) := by
      zify [hk, hD] at hg ⊢
      nlinarith
end SplitCut
#print axioms SplitCut.compress_rows
#print axioms SplitCut.compression_guard

end Merged6967_KoalaCutGeometry

section Merged6967_KoalaStableNode
set_option Elab.async false


set_option Elab.async false

set_option autoImplicit false

namespace SplitCut.StableNode

open Polynomial


/-- Evaluate the inner polynomial variable on a polynomial in the outer variable. -/
noncomputable def substitute {R : Type*} [CommRing R] (s : (Polynomial R)) : Polynomial (Polynomial R) →+* (Polynomial R) :=
  eval₂RingHom (eval₂RingHom C s) «X»



end SplitCut.StableNode


end Merged6967_KoalaStableNode

section Merged6967_Low50Euler2367JetDegree
set_option Elab.async false



set_option Elab.async false

open scoped BigOperators Polynomial
open Polynomial

namespace EulerJetDegree

variable {R : Type*} [CommRing R]

private def signedChoose (D i k : ℕ) : R :=
  ∑ r ∈ Finset.range (i + 1),
    (-1 : R) ^ r * (D-r).choose (i-r) * k.choose r

private theorem signedChoose_step (D i k : ℕ) :
    signedChoose (R := R) D (i+1) (k+1) =
      signedChoose D (i+1) k - signedChoose (D-1) i k := by
  unfold signedChoose
  simp only [Finset.sum_range_succ' _ (i+1), pow_zero, Nat.sub_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
  have h : (∑ r ∈ Finset.range (i+1),
      (-1 : R) ^ (r+1) * (D-(r+1)).choose ((i+1)-(r+1)) * (k+1).choose (r+1)) =
      (∑ r ∈ Finset.range (i+1),
        (-1 : R) ^ (r+1) * (D-(r+1)).choose ((i+1)-(r+1)) * k.choose (r+1)) -
      ∑ r ∈ Finset.range (i+1), (-1 : R) ^ r * (D-1-r).choose (i-r) * k.choose r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ,
      show D - (r+1) = D-1-r by omega,
      show i+1-(r+1)=i-r by omega]
    ring
  rw [h]
  ring

private theorem signedChoose_eq {D i k : ℕ} (h : k ≤ D) :
    signedChoose (R := R) D i k = ((D-k).choose i : R) := by
  induction k generalizing D i with
  | zero =>
    unfold signedChoose
    rw [Finset.sum_eq_single 0]
    · simp
    · intro r hr hne
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hne)]
    · simp
  | succ k ih =>
    cases i with
    | zero => simp [signedChoose]
    | succ i =>
      rw [signedChoose_step, ih (by omega : k ≤ D), ih (by omega : k ≤ D-1)]
      rw [show D-k = (D-(k+1))+1 by omega,
        show D-1-k = D-(k+1) by omega, Nat.choose_succ_succ, Nat.cast_add]
      ring

/-- Euler-adjusted Hasse jet, using physical degree cap `D`. -/
noncomputable def euler (D i : ℕ) (f : (Polynomial R)) : (Polynomial R) :=
  ∑ r ∈ Finset.range (i+1),
    C ((-1 : R) ^ r * (D-r).choose (i-r)) * («X»^r * hasseDeriv r f)


theorem coeff_euler {D i k : ℕ} (f : (Polynomial R)) (hk : k ≤ D) :
    (euler D i f).coeff k = ((D-k).choose i : R) * f.coeff k := by
  rw [← signedChoose_eq hk]
  unfold euler signedChoose
  rw [Polynomial.finsetSum_coeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hr : r ≤ k
  · simp [hr, hasseDeriv_coeff, Nat.sub_add_cancel hr, mul_assoc]
  · simp [hr, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hr)]

theorem natDegree_euler_le (D i : ℕ) (f : (Polynomial R)) : (euler D i f).natDegree ≤ f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  unfold euler
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro r _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hr : r ≤ k
  · simp [hr, hasseDeriv_coeff, Nat.sub_add_cancel hr, coeff_eq_zero_of_natDegree_lt hk]
  · simp [hr]

theorem natDegree_euler_le_sub {D i : ℕ} {f : (Polynomial R)} (hf : f.natDegree ≤ D) :
    (euler D i f).natDegree ≤ D-i := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases hD : k ≤ D
  · rw [coeff_euler f hD]
    simp [Nat.choose_eq_zero_of_lt (by omega : D-k < i)]
  · exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_euler_le D i f).trans_lt (hf.trans_lt (Nat.lt_of_not_ge hD)))










#print axioms natDegree_euler_le_sub

end EulerJetDegree

end Merged6967_Low50Euler2367JetDegree

section Merged6967_R6960ChartIntegrality
set_option Elab.async false









set_option Elab.async false

-- merged module R6960NormalizedFiber
section Merged_R6960NormalizedFiber
noncomputable section
set_option Elab.async false
namespace Lower6960.NormalizedFiber
open Polynomial
open scoped Polynomial
section
variable {A F : Type*} [CommRing A] [Field F]
private theorem clear_coeff [DecompositionMonoid A] (ι : A→+*F) (inj : Function.Injective ι) (a b : A) (ne : a≠0)
    (cop : IsRelPrime a b) (v : F) {u w : A} (hu : ι u=v*ι a) (hw : ι w=v*ι b) :
    ∃ q : A,ι q=v := by
  have cross : u*b=w*a := inj (by rw [map_mul,map_mul,hu,hw]; ring)
  have divides : a∣u*b := cross ▸ dvd_mul_left a w
  obtain ⟨q,hq⟩ := cop.dvd_of_dvd_mul_right divides
  refine ⟨q, mul_right_cancel₀ ((map_ne_zero_iff ι inj).mpr ne) ?_⟩
  rw [←hu,hq,map_mul,mul_comm]
variable [IsDomain A] [UniqueFactorizationMonoid A] {E : Type*} [Field E] [Algebra A E]
theorem integral_of_coprime_clearings (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [IsScalarTower A K E] [FiniteDimensional K E]
    {a b : A} (na : a≠0) (nb : b≠0) (cop : IsRelPrime a b) (v : E)
    (ca : IsIntegral A (algebraMap A E a*v)) (cb : IsIntegral A (algebraMap A E b*v)) :
    IsIntegral A v := by
  let ι:=algebraMap A K
  let p:=minpoly K v
  have inj : Function.Injective ι := IsFractionRing.injective A K
  have : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr
    (by rw [IsScalarTower.algebraMap_eq A K E]; exact (algebraMap K E).injective.comp inj)
  have vint : IsIntegral K v := Algebra.IsIntegral.isIntegral v
  have scaled (c : A) (cn : c≠0) (ci : IsIntegral A (algebraMap A E c*v)) (i : ℕ) :
      ι ((minpoly A (algebraMap A E c*v)).coeff i) = p.coeff i*ι (c^(p.natDegree-i)) := by
    have idpoly := minpoly.isIntegrallyClosed_eq_field_fractions' K ci
    have eq : algebraMap A E c*v = ι c • v := by
      simp only [ι,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    rw [eq,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff ι inj).mpr cn) vint] at idpoly
    have d := congrArg (fun q : (Polynomial K)=>q.coeff i) idpoly
    simpa only [p,eq,coeff_map,coeff_scaleRoots,map_pow,ι] using d.symm
  have lift : p∈Polynomial.lifts ι := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro i
    let n:=p.natDegree-i
    have disjoint : IsRelPrime (a^n) b := cop.pow_left
    exact clear_coeff ι inj (a^n) (b^n) (pow_ne_zero _ na) disjoint.pow_right
      (p.coeff i) (scaled a na ca i) (scaled b nb cb i)
  obtain ⟨q,hq⟩ := lift
  change q.map ι=p at hq
  have monic : q.Monic := by
    apply inj.monic_map_iff.mpr
    rw [hq]; exact minpoly.monic vint
  refine ⟨q,monic,?_⟩
  have root := minpoly.aeval K v
  rw [←show p=minpoly K v from rfl,←hq,aeval_map_algebraMap] at root
  exact root
theorem cancel_on_normalization (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [IsScalarTower A K E] [FiniteDimensional K E]
    {a b : A} (na : a≠0) (nb : b≠0) (cop : IsRelPrime a b)
    (u : integralClosure A E)
    (div : algebraMap A (integralClosure A E) a ∣ algebraMap A (integralClosure A E) b*u) :
    algebraMap A (integralClosure A E) a∣u := by
  obtain ⟨s,eq⟩ := div
  have inj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have av := (map_ne_zero_iff _ inj).mpr na
  let v := (u:E)/algebraMap A E a
  have aa : algebraMap A E a*v=u := by dsimp [v]; field_simp
  have bb : algebraMap A E b*v=s := by
    have eq' : algebraMap A E b*(u:E)=algebraMap A E a*(s:E) := congrArg Subtype.val eq
    dsimp [v]
    field_simp
    simpa only [mul_comm (s:E)] using eq'
  have vi := integral_of_coprime_clearings K na nb cop v (aa ▸ u.property) (bb ▸ s.property)
  exact ⟨⟨v,vi⟩,Subtype.ext aa.symm⟩
end
#print axioms integral_of_coprime_clearings
#print axioms cancel_on_normalization
section Plane
variable {k : Type*} [Field k]
abbrev Plane (k : Type*) [Field k] := Polynomial (Polynomial k)
variable (E : Type*) [Field E] [Algebra (Plane k) E]
abbrev Order (k E : Type*) [Field k] [Field E] [Algebra (Plane k) E] := integralClosure (Plane k) E
def sliceIdeal (z : k) : Ideal (Order k E) :=
  Ideal.span {algebraMap (Plane k) (Order k E) (Polynomial.X-C (C z))}
abbrev Fiber (z : k) : Type _ := @HasQuotient.Quotient (↥(Order k E)) _
  (Ideal.instHasQuotient (R:=↥(Order k E))) (sliceIdeal E z)
def quotientMap (z : k) := @Ideal.Quotient.mk (↥(Order k E)) (Order k E).toRing (sliceIdeal E z)
theorem quotientMap_surjective (z : k) : Function.Surjective (quotientMap E z) :=
  fun u=>Ideal.Quotient.mk_surjective u
def baseMap (z : k) : (Polynomial k) →+* Fiber E z :=
  ((Ideal.Quotient.mk _).comp (algebraMap (Plane k) (Order k E))).comp C
variable [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
    [FiniteDimensional (FractionRing (Plane k)) E]
theorem torsion_free (z : k) (q : (Polynomial k)) (nz : q≠0) (u : Fiber E z)
    (zero : baseMap E z q * u=0) : u=0 := by
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective u
  let a : Plane k := Polynomial.X-C (C z)
  let b : Plane k := C q
  have div : algebraMap (Plane k) (Order k E) a ∣ (algebraMap (Plane k) (Order k E) b)*v :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp
      (show Ideal.Quotient.mk (sliceIdeal E z) (_*v)=0 by
        simpa only [map_mul,baseMap,b,RingHom.comp_apply] using zero))
  have an : a≠0 := X_sub_C_ne_zero _
  have bn : b≠0 := C_ne_zero.mpr nz
  have cop : IsRelPrime a b := (irreducible_X_sub_C _).isRelPrime_iff_not_dvd.mpr (by
    intro h
    exact nz (by simpa [b,Polynomial.IsRoot] using (dvd_iff_isRoot.mp h)))
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr
    (cancel_on_normalization (FractionRing (Plane k)) an bn cop v div)
omit [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
    [FiniteDimensional (FractionRing (Plane k)) E] in
theorem specialize (z : k) (f : Plane k) :
    Ideal.Quotient.mk (sliceIdeal E z) (algebraMap (Plane k) (Order k E) f) =
      baseMap E z (f.eval (C z)) := by
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have h := map_dvd (algebraMap (Plane k) (Order k E)) (X_sub_C_dvd_sub_C_eval (a:=C z) (p:=f))
  simpa only [map_sub] using h
private theorem finite_image {A R M N : Type*} [Semiring A] [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module R N] [source : Module.Finite A M]
    (f : M →+ N) (surj : Function.Surjective f) (specializeScalar : A→R)
    (compat : ∀ a v,f (a • v)=specializeScalar a • f v) : Module.Finite R N := by
  classical
  obtain ⟨s,span⟩ := source.1
  let t:=s.image f
  refine ⟨⟨t,top_unique ?_⟩⟩
  intro u trivialMem
  clear trivialMem
  obtain ⟨v,rfl⟩ := surj u
  have inside : v∈Submodule.span A (s : Set M) := span ▸ Submodule.mem_top
  induction inside using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Finset.mem_image_of_mem f hx)
  | zero => exact f.map_zero ▸ Submodule.zero_mem _
  | add a b _ _ ha hb => exact (f.map_add a b) ▸ Submodule.add_mem _ ha hb
  | smul c a _ ha => exact (compat c a) ▸ Submodule.smul_mem _ _ ha
set_option maxHeartbeats 1400000 in
theorem finite_free [Algebra.IsSeparable (FractionRing (Plane k)) E] (z : k) :
    letI : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
    Module.Finite (Polynomial k) (Fiber E z) ∧ Module.Free (Polynomial k) (Fiber E z) := by
  classical
  let : Module (Polynomial k) (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
  have sourceFin : Module.Finite (Plane k) (Order k E) :=
    IsIntegralClosure.finite (Plane k) (FractionRing (Plane k)) E (Order k E)
  let m:=quotientMap E z
  have fin : Module.Finite (Polynomial k) (Fiber E z) :=
    finite_image (A:=Plane k) (R:=(Polynomial k)) (M:=↥(Order k E)) (N:=Fiber E z)
      m.toAddMonoidHom (quotientMap_surjective E z) (fun c=>c.eval (C z)) (by
        intro c v
        rw [Algebra.smul_def c v]
        change m (algebraMap (Plane k) (Order k E) c*v) = baseMap E z (c.eval (C z)) * m v
        rw [map_mul]; exact congrArg (·*m v) (specialize E z c))
  have tor : Module.IsTorsionFree (Polynomial k) (Fiber E z) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r u eq
    by_cases zero : r=0
    · exact Or.inl zero
    · exact Or.inr (torsion_free E z r zero u eq)
  exact ⟨fin,inferInstance⟩
end Plane
#print axioms torsion_free
#print axioms finite_free
end Lower6960.NormalizedFiber

end
end Merged_R6960NormalizedFiber

-- merged module R6960ChartIntegrality
section Merged_R6960ChartIntegrality

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartIntegrality
open Polynomial
open scoped Polynomial
variable {A F E : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra F E]
    [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]

private theorem in_base (v : F) (loc : ∀ q : A,Irreducible q →
    ∃ d c : A, ¬q∣d ∧ algebraMap A F c=v*algebraMap A F d) :
    ∃ c : A,algebraMap A F c=v := by
  classical
  let a:=IsFractionRing.num A v
  let b:A:=IsFractionRing.den A v
  let i:=algebraMap A F
  have inj:=IsFractionRing.injective A F
  have nb : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den A v).property
  have eq : i a=v*i b := (div_eq_iff ((map_ne_zero_iff _ inj).mpr nb)).mp (IsFractionRing.mk'_num_den' A v)
  have unit : IsUnit b := by
    by_contra nu
    obtain ⟨q,ir,dv⟩ := WfDvdMonoid.exists_irreducible_factor nu nb
    obtain ⟨d,c,nd,hc⟩ := loc q ir
    have cross : a*d=c*b := inj (by
      change i (a*d)=i (c*b); rw [map_mul,map_mul,eq,hc]; ring)
    have product : q∣a*d := cross ▸ dv.trans (dvd_mul_left ..)
    have qa := (ir.prime.dvd_mul.mp product).resolve_right nd
    exact ir.not_isUnit (IsFractionRing.num_den_reduced A v qa dv)
  obtain ⟨u,hu⟩ := unit
  refine ⟨a*↑u⁻¹,?_⟩
  rw [map_mul,eq,←hu,mul_assoc,←map_mul,Units.mul_inv,map_one,mul_one]

/-- Normalization on the affine plane can be tested one irreducible base
divisor at a time. Different monic ordinate coordinates can therefore be
used at different abscissa places. -/
theorem integral_from_places (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
    (x : E) (loc : ∀ q : A,Irreducible q →
      ∃ d : A, ¬q∣d ∧ IsIntegral A (algebraMap A E d*x)) : IsIntegral A x := by
  let ι:=algebraMap A F
  have inj : Function.Injective ι := IsFractionRing.injective A F
  have : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr
    (by rw [IsScalarTower.algebraMap_eq A F E]; exact (algebraMap F E).injective.comp inj)
  let f:=minpoly F x
  have intF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have lift : f∈Polynomial.lifts ι := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro j
    apply in_base (f.coeff j)
    intro q ir
    obtain ⟨d,nd,di⟩ := loc q ir
    have dn : d≠0 := fun eq=>nd (eq ▸ dvd_zero _)
    let n:=f.natDegree-j
    refine ⟨d^n,(minpoly A (algebraMap A E d*x)).coeff j,
      fun div=>nd (ir.prime.dvd_of_dvd_pow div),?_⟩
    have mp:=minpoly.isIntegrallyClosed_eq_field_fractions' F di
    have scale : algebraMap A E d*x=ι d • x := by
      simp only [ι,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    rw [scale,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff _ inj).mpr dn) intF] at mp
    have c:=congrArg (fun g : (Polynomial F)=>g.coeff j) mp
    simpa only [n,f,scale,coeff_map,coeff_scaleRoots,map_pow,ι] using c.symm
  obtain ⟨g,hg⟩:=lift
  change g.map ι=f at hg
  have monic : g.Monic := inj.monic_map_iff.mpr (hg ▸ minpoly.monic intF)
  refine ⟨g,monic,?_⟩
  have root : aeval x f=0 := minpoly.aeval F x
  rwa [←hg,aeval_map_algebraMap] at root

#print axioms integral_from_places
end Lower6960.ChartIntegrality

end
end Merged_R6960ChartIntegrality

end Merged6967_R6960ChartIntegrality

section Merged6967_R6960CollisionMarkedTwoChart
set_option Elab.async false




set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial
open scoped Polynomial
variable {k V Bf Bi : Type*} [Field k] [CommRing V] [CommRing Bf] [CommRing Bi]
  [Algebra (Polynomial k) Bi]
theorem boundary_clearings (φ : Bi→+*V) (a : (Polynomial k)→+*V)
    (scalars : ∀ f,φ (algebraMap (Polynomial k) Bi f)=a f)
    (w : V) (n : ℕ) (D : (Polynomial k)) (unit : D.eval 0≠0)
    (p : ∃ u : Bi,φ u=a (Polynomial.X^n)*w)
    (d : ∃ u : Bi,φ u=a D*w) : ∃ u : Bi,φ u=w := by
  have nx : ¬ (Polynomial.X:(Polynomial k))∣D := by
    intro dv
    obtain ⟨g,hg⟩ := dv
    apply unit
    rw [hg,eval_mul,eval_X,zero_mul]
  have cp : IsCoprime ((Polynomial.X:(Polynomial k))^n) D :=
    (irreducible_X.coprime_iff_not_dvd.mpr nx).pow_left
  obtain ⟨x,y,xy⟩ := cp
  obtain ⟨u,hu⟩ := p
  obtain ⟨v,hv⟩ := d
  refine ⟨x • u+y • v,?_⟩
  simp only [Algebra.smul_def,map_add,map_mul,scalars,hu,hv]
  calc _ = a (x*Polynomial.X^n+y*D)*w := by rw [map_add,map_mul,map_mul]; ring
       _ = w := by rw [xy,map_one,one_mul]
theorem marked_multiple_two_charts (ι : k→+*V) («X» : Vˣ)
    (φf : Bf→+*V) (φi : Bi→+*V)
    (scalars : ∀ f,φi (algebraMap (Polynomial k) Bi f)=f.eval₂ ι (↑«X»⁻¹))
    (common : ∀ u : Bf,∃ n : ℕ,∃ v : Bi,φi v=((↑«X»⁻¹:V)^n)*φf u)
    (η : V) (D : (Polynomial k)) (unit : D.eval 0≠0)
    (clears : ∃ v : Bi,φi v=D.eval₂ ι (↑«X»⁻¹)*η)
    (h : (Polynomial k)) (a : ℕ) (deg : h.natDegree≤a)
    (finite : ∃ u : Bf,φf u=h.eval₂ ι («X»:V)*η) :
    ∃ (u : Bf) (v : Bi),φf u=h.eval₂ ι («X»:V)*η ∧
      φi v=((↑«X»⁻¹:V)^a)*φf u := by
  obtain ⟨u,hu⟩ := finite
  obtain ⟨n,y,hy⟩ := common u
  obtain ⟨z,hz⟩ := clears
  let w : V := ((↑«X»⁻¹:V)^a)*φf u
  let j := eval₂RingHom ι (↑«X»⁻¹:V)
  have jX : j Polynomial.X=(↑«X»⁻¹:V) := eval₂_X ι (↑«X»⁻¹:V)
  have power_clear : ∃ v : Bi,φi v=j (Polynomial.X^n)*w := by
    refine ⟨((Polynomial.X:(Polynomial k))^a) • y,?_⟩
    rw [Algebra.smul_def,map_mul,scalars,hy]
    change j (Polynomial.X^a)*_ = _
    rw [map_pow,map_pow,jX]
    unfold w
    ring
  let : Invertible («X»:V) := invertibleOfLeftInverse («X»:V) (↑«X»⁻¹:V) «X».inv_mul
  have h_reflect : (h.reflect a).eval₂ ι (↑«X»⁻¹:V)=(↑«X»⁻¹:V)^a*h.eval₂ ι («X»:V) := by
    have eq := eval₂_reflect_mul_pow ι («X»:V) a h deg
    change (h.reflect a).eval₂ ι (↑«X»⁻¹:V)*(«X»:V)^a=h.eval₂ ι («X»:V) at eq
    rw [←eq,mul_left_comm,←mul_pow,Units.inv_mul,one_pow,mul_one]
  have det_clear : ∃ v : Bi,φi v=j D*w := by
    refine ⟨(h.reflect a) • z,?_⟩
    rw [Algebra.smul_def,map_mul,scalars,hz,h_reflect]
    change _ = D.eval₂ ι (↑«X»⁻¹:V)*w
    unfold w
    rw [hu]
    ring
  obtain ⟨v,hv⟩ := boundary_clearings φi j scalars w n D unit power_clear det_clear
  exact ⟨u,v,hu,hv⟩
#print axioms marked_multiple_two_charts
end
end Lower6960.CollisionMarked

end Merged6967_R6960CollisionMarkedTwoChart

section Merged6967_R6960CollisionTameDiscriminant
set_option Elab.async false




set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Matrix
open scoped Matrix BigOperators Pointwise
section Gram
variable {A M ι : Type*} [CommRing A] [AddCommMonoid M] [Module A M] [Fintype ι] [DecidableEq ι]
def tupleGram (tr : LinearMap.BilinForm A M) (u : ι→M) : Matrix ι ι A :=
  fun i j=>tr (u i) (u j)
def gramIdeal (tr : LinearMap.BilinForm A M) : Ideal A :=
  Ideal.span (Set.range (fun u : ι→M=>(tupleGram tr u).det))
theorem gramIdeal_mem (tr : LinearMap.BilinForm A M) (u : ι→M) :
    (tupleGram tr u).det∈gramIdeal (ι:=ι) tr := Ideal.subset_span ⟨u,rfl⟩
omit [Fintype ι] [DecidableEq ι] in
theorem tupleGram_smul (tr : LinearMap.BilinForm A M) (u : ι→M) (g : A) :
    tupleGram tr (fun i=>g • u i)=g^2 • tupleGram tr u := by
  apply Matrix.ext
  intro i j
  change tr (g • u i) (g • u j)=g^2*tr (u i) (u j)
  rw [tr.map_smul,LinearMap.smul_apply,(tr (u i)).map_smul]
  simp only [smul_eq_mul]
  ring
omit [DecidableEq ι] in
theorem tupleGram_change (tr : LinearMap.BilinForm A M) (u : ι→M) (T : Matrix ι ι A) :
    tupleGram tr (fun j=>∑ i,T i j • u i)=T.transpose*tupleGram tr u*T := by
  rw [mul_assoc]
  apply Matrix.ext
  intro i j
  simp only [tupleGram,Matrix.mul_apply,Matrix.transpose_apply,map_sum,LinearMap.sum_apply,
    LinearMap.map_smul,LinearMap.smul_apply,smul_eq_mul]
  simp only [Finset.mul_sum,mul_comm (T _ j)]
  exact Finset.sum_comm
theorem gramIdeal_clear (tr : LinearMap.BilinForm A M) (u : ι→M) (g : A)
    (clear : ∀ x : M,∃ t : ι→A,∑ i,t i • u i=g • x) :
    ∀ a∈gramIdeal (ι:=ι) tr, (tupleGram tr u).det∣g^(2*Fintype.card ι)*a := by
  let I := Ideal.span ({(tupleGram tr u).det} : Set A)
  have witnesses : gramIdeal (ι:=ι) tr ≤ Submodule.comap (LinearMap.mul A A (g^(2*Fintype.card ι))) I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    change g^(2*Fintype.card ι)*(tupleGram tr v).det∈I
    choose t ht using fun j=>clear (v j)
    let T : Matrix ι ι A := fun i j=>t j i
    have eq : tupleGram tr (fun j=>g • v j)=T.transpose*tupleGram tr u*T := by
      rw [←tupleGram_change tr u T]
      exact congrArg (tupleGram tr) (funext fun i=>(ht i).symm)
    rw [tupleGram_smul] at eq
    have det := congrArg Matrix.det eq
    rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,←pow_mul] at det
    change g^(2*Fintype.card ι)*(tupleGram tr v).det∈Ideal.span {(tupleGram tr u).det}
    rw [det,Ideal.mem_span_singleton]
    exact ⟨T.det^2,by ring⟩
  intro a ha
  exact Ideal.mem_span_singleton.mp (witnesses ha)
theorem gramIdeal_basis (tr : LinearMap.BilinForm A M) (b : Module.Basis ι A M) :
    gramIdeal (ι:=ι) tr=Ideal.span {(tupleGram tr b).det} := by
  apply le_antisymm
  · intro a ha
    apply Ideal.mem_span_singleton.mpr
    have h := gramIdeal_clear tr b 1 (fun x=>⟨b.equivFun x,by
      rw [one_smul]
      exact (b.equivFun_symm_apply (b.equivFun x)).symm.trans (b.equivFun.symm_apply_apply x)⟩) a ha
    simpa only [one_pow,one_mul] using h
  · exact (Ideal.span_singleton_le_iff_mem _).mpr (gramIdeal_mem tr b)
end Gram
section Principal
variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [IsNoetherianRing A]
omit [IsDomain A] in
theorem principal_of_clears (I : Ideal A)
    (patch : ∀ (P : Ideal A),P.IsMaximal→∃ (g d : A) (n : ℕ),g∉P ∧ d∈I ∧
      ∀ a∈I,d∣g^n*a) : I.IsPrincipal := by
  classical
  let : NormalizedGCDMonoid A := Classical.arbitrary _
  obtain ⟨G,hG⟩ := IsNoetherian.noetherian I
  let δ := G.gcd id
  have divides : I≤Ideal.span {δ} := by
    rw [←hG]
    apply Ideal.span_le.mpr
    exact fun _ h=>Ideal.mem_span_singleton.mpr (Finset.gcd_dvd h)
  have δmem : δ∈I := by
    by_contra notmem
    let J : Ideal A := Submodule.comap (LinearMap.mul A A δ) I
    have proper : J≠⊤ := by
      intro all
      have h : (1:A)∈J := all.symm ▸ Submodule.mem_top
      change δ*1∈I at h
      exact notmem (by simpa only [mul_one] using h)
    obtain ⟨P,hP,JP⟩ := Ideal.exists_le_maximal J proper
    obtain ⟨g,d,n,gn,dI,h⟩ := patch P hP
    have each : d∣G.gcd (fun r=>g^n*r) := Finset.dvd_gcd_iff.mpr fun a ha=>
      h a (hG ▸ Ideal.subset_span ha)
    have δdiv : d∣g^n*δ := each.trans (Finset.gcd_mul_left' (s:=G) (f:=id) (g^n)).dvd
    have inside : g^n∈J := by
      change δ*g^n∈I
      rw [mul_comm]
      obtain ⟨c,hc⟩ := δdiv
      rw [hc]
      exact I.mul_mem_right c dI
    exact gn (hP.isPrime.mem_of_pow_mem _ (JP inside))
  exact ⟨δ,le_antisymm divides ((Ideal.span_singleton_le_iff_mem _).mpr δmem)⟩
end Principal
#print axioms gramIdeal_clear
#print axioms principal_of_clears
end
end Lower6960.CollisionTame

end Merged6967_R6960CollisionTameDiscriminant

section Merged6967_R6960CollisionTameSmith
set_option Elab.async false




set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Matrix Module
open scoped Matrix BigOperators
variable {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Fintype ι] [DecidableEq ι]
private theorem injective_of_one_layer (π : A) (pir : Irreducible π) (M : Matrix ι ι A)
    (one_layer : ∀ w : ι→A, (∀ i,π^2∣(M *ᵥ w) i) → ∀ i,π∣w i) :
    Function.Injective (Matrix.toLin' M) := by
  classical
  let f := Matrix.toLin' M
  apply (injective_iff_map_eq_zero f).mpr
  intro w zero
  have all (n : ℕ) : ∃ t : ι→A,w=π^n • t ∧ f t=0 := by
    induction n with
    | zero => exact ⟨w,by simp,zero⟩
    | succ n ih =>
      obtain ⟨t,eq,ft⟩ := ih
      have allDvd : ∀ i,π∣t i := one_layer t (fun i=>by
        have e := congrFun ft i
        change (M *ᵥ t) i=0 at e
        rw [e]
        exact dvd_zero _)
      choose u hu using allDvd
      have tu : t=π • u := funext hu
      have fu : f u=0 := by
        rw [tu,f.map_smul] at ft
        funext i
        exact (mul_eq_zero.mp (congrFun ft i)).resolve_left pir.ne_zero
      refine ⟨u,?_ ,fu⟩
      rw [eq,tu,smul_smul,pow_succ]
  funext i
  by_contra nz
  obtain ⟨m,a,ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible nz pir
  obtain ⟨u,eq,_⟩ := all (m+1)
  have dvd : π^(m+1)∣w i := ⟨u i,congrFun eq i⟩
  rw [ha] at dvd
  have c := (IsDiscreteValuationRing.addVal_le_iff_dvd (R:=A)).mpr dvd
  simp only [AddValuation.map_mul,AddValuation.map_pow,IsDiscreteValuationRing.addVal_eq_zero_of_unit,
    IsDiscreteValuationRing.addVal_uniformizer pir,nsmul_eq_mul,mul_one,zero_add,ENat.natCast_le_natCast] at c
  omega
private theorem basis_change_unit {A : Type*} [CommRing A]
    (a b : Basis ι A (ι→A)) : IsUnit (LinearMap.toMatrix a b (LinearMap.id (R:=A))) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨LinearMap.toMatrix b a LinearMap.id,?_⟩
  rw [←LinearMap.toMatrix_comp b a b,LinearMap.id_comp,LinearMap.toMatrix_id]
omit [DecidableEq ι] in
private theorem count_zeros [DecidableEq K] (a : ι → K) :
    (∑ i,if a i=0 then (1:ℕ) else 0)=Fintype.card ι-Fintype.card {i // a i≠0} := by
  classical
  rw [Finset.sum_boole,←Fintype.card_subtype]
  simpa only [Nat.cast_id,ne_eq,not_not] using (Fintype.card_subtype_compl (fun i=>a i≠0))
theorem matrix_order_corank (π : A) (pir : Irreducible π) (M : Matrix ι ι A)
    (red : A→+*K) (ker : ∀ x,red x=0 ↔ π∣x)
    (nonunits : ∀ x:A,¬IsUnit x ↔ π∣x)
    (one_layer : ∀ w : ι→A, (∀ i,π^2∣(M *ᵥ w) i) → ∀ i,π∣w i) :
    Associated M.det (π^(Fintype.card ι-(M.map red).rank)) := by
  classical
  let f := Matrix.toLin' M
  let N := LinearMap.range f
  let e : (ι→A) ≃ₗ[A] N := LinearEquiv.ofInjective f (injective_of_one_layer π pir M one_layer)
  have rank : finrank A N=finrank A (ι→A) := e.finrank_eq.symm
  let b := Pi.basisFun A ι
  let dst := Submodule.smithNormalFormTopBasis b rank
  let bot := Submodule.smithNormalFormBotBasis b rank
  let src := bot.map e.symm
  let a := Submodule.smithNormalFormCoeffs b rank
  have diag_change (i : ι) : f (src i)=a i • dst i := by
    have h : f (src i)=(bot i:N) := congrArg Subtype.val (e.apply_symm_apply (bot i))
    exact h.trans (Submodule.smithNormalFormBotBasis_def b rank i)
  have shallow (i : ι) : ¬π^2∣a i := by
    rintro ⟨c,hc⟩
    have deep (j : ι) : π^2∣(M *ᵥ src i) j := by
      change π^2∣f (src i) j
      rw [diag_change]
      change π^2∣a i * dst i j
      rw [hc,mul_assoc]
      exact dvd_mul_right _ _
    choose u hu using one_layer (src i) deep
    have eq : src i=π • u := funext hu
    have bad := congrArg (fun v=>src.repr v i) eq
    rw [Basis.repr_self,Finsupp.single_eq_same,src.repr.map_smul,Finsupp.smul_apply,smul_eq_mul] at bad
    exact pir.not_isUnit (isUnit_iff_dvd_one.mpr ⟨_,bad⟩)
  have dia : LinearMap.toMatrix src dst f=diagonal a := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply,diag_change,dst.repr.map_smul,Finsupp.smul_apply,
      Basis.repr_self,Matrix.diagonal_apply]
    by_cases eq : j=i
    · subst i
      simp only [Finsupp.single_eq_same,smul_eq_mul,mul_one,ite_true]
    · rw [Finsupp.single_eq_of_ne (Ne.symm eq),smul_zero]
      simp only [Ne.symm eq,ite_false]
  let U := LinearMap.toMatrix b dst (LinearMap.id (R:=A))
  let V := LinearMap.toMatrix src b (LinearMap.id (R:=A))
  have uU : IsUnit U := basis_change_unit b dst
  have uV : IsUnit V := basis_change_unit src b
  have std : LinearMap.toMatrix b b f=M := by
    change LinearMap.toMatrix (Pi.basisFun A ι) (Pi.basisFun A ι) (Matrix.toLin' M)=M
    rw [←Matrix.toLin_eq_toLin',LinearMap.toMatrix_toLin]
  have scaled : U*M*V=diagonal a := by
    rw [←dia,←std]
    unfold U V
    rw [←LinearMap.toMatrix_comp b b dst,LinearMap.id_comp,
      ←LinearMap.toMatrix_comp src b dst,LinearMap.comp_id]
  have determinant : Associated M.det (∏ i,a i) := by
    obtain ⟨u,hu⟩ := (Matrix.isUnit_iff_isUnit_det U).mp uU
    obtain ⟨v,hv⟩ := (Matrix.isUnit_iff_isUnit_det V).mp uV
    refine ⟨u*v,?_⟩
    rw [Units.val_mul,hu,hv,←det_diagonal,←scaled,det_mul,det_mul]
    ac_rfl
  have urU : IsUnit ((U.map red).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (uU.map red.mapMatrix)
  have urV : IsUnit ((V.map red).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (uV.map red.mapMatrix)
  have rdiag : (U.map red)*(M.map red)*(V.map red)=diagonal (fun i=>red (a i)) := by
    have h := congrArg red.mapMatrix scaled
    rw [map_mul,map_mul] at h
    refine h.trans ?_
    apply Matrix.ext
    intro i j
    by_cases eq : i=j <;> simp [eq]
  have rr : (M.map red).rank=Fintype.card {i // red (a i)≠0} := by
    rw [←Matrix.rank_mul_eq_right_of_isUnit_det _ _ urU,
      ←Matrix.rank_mul_eq_left_of_isUnit_det _ _ urV,rdiag,rank_diagonal]
  have entries (i : ι) : Associated (a i) (π^(if red (a i)=0 then (1:ℕ) else 0)) := by
    by_cases hz : red (a i)=0
    · obtain ⟨c,hc⟩ := (ker _).mp hz
      have unit : IsUnit c := by
        by_contra hu
        obtain ⟨r,hr⟩ := (nonunits _).mp hu
        exact shallow i ⟨r,by rw [hc,hr,pow_two,mul_assoc]⟩
      obtain ⟨u,hu⟩ := unit
      simp only [hz,ite_true,pow_one]
      exact Associated.symm ⟨u,by rw [hu,hc]⟩
    · have unit : IsUnit (a i) := by
        by_contra nu
        exact hz ((ker _).mpr ((nonunits _).mp nu))
      simpa only [hz,ite_false,pow_zero] using (associated_one_iff_isUnit.mpr unit)
  refine determinant.trans ?_
  have product := Associated.prod Finset.univ _ _ (fun i _=>entries i)
  rw [Finset.prod_pow_eq_pow_sum,count_zeros,←rr] at product
  exact product
#print axioms matrix_order_corank
end
end Lower6960.CollisionTame

end Merged6967_R6960CollisionTameSmith

section Merged6967_R6960LineEulerComparison
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.LineEuler
noncomputable section
open Module Submodule LinearMap
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
theorem compare_lattices (F A B : Submodule k V) (inc : A≤B) (cover : F⊔B=⊤)
    [FiniteDimensional k ↥(F⊓B)] [FiniteDimensional k (B ⧸ A.comap B.subtype)] :
    FiniteDimensional k ↥(F⊓A) ∧ FiniteDimensional k (V ⧸ (F⊔A)) ∧
    finrank k ↥(F⊓A) + finrank k (B ⧸ A.comap B.subtype) =
      finrank k (V ⧸ (F⊔A)) + finrank k ↥(F⊓B) := by
  let D := A.comap B.subtype
  let P := F⊔A
  let toB : ↥(F⊓B) →ₗ[k] B := Submodule.inclusion inf_le_right
  let f : ↥(F⊓B) →ₗ[k] (B ⧸ D) := D.mkQ ∘ₗ toB
  let g : (B ⧸ D) →ₗ[k] (V ⧸ P) := D.mapQ P B.subtype fun y hy=>Submodule.mem_sup_right hy
  have eval_g (b : B) : g (D.mkQ b)=P.mkQ (b:V) := rfl
  have eval_f (b : ↥(F⊓B)) : f b=D.mkQ (toB b) := rfl
  have g_surj : Function.Surjective g := by
    intro v
    obtain ⟨v,rfl⟩ := P.mkQ_surjective v
    have mem : v∈F⊔B := cover.symm ▸ Submodule.mem_top
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp mem
    refine ⟨D.mkQ ⟨y,hy⟩,?_⟩
    have zero : P.mkQ x=0 := by
      rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left hx
    rw [eval_g,map_add,zero,zero_add]
  have exact_fg : f.range = g.ker := by
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      rw [LinearMap.mem_ker,eval_f,eval_g,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left x.property.1
    · intro hv
      obtain ⟨b,rfl⟩ := D.mkQ_surjective v
      rw [LinearMap.mem_ker,eval_g,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hv
      obtain ⟨x,hx,y,hy,h⟩ := Submodule.mem_sup.mp hv
      have xB : x∈B := by
        rw [show x=(b:V)-y by rw [←h,add_sub_cancel_right]]
        exact B.sub_mem b.property (inc hy)
      refine ⟨⟨x,⟨hx,xB⟩⟩,?_⟩
      rw [eval_f,←sub_eq_zero,←map_sub,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      change x-(b:V)∈A
      rw [←h,sub_add_cancel_left]
      exact A.neg_mem hy
  have e : ↥(F⊓A) ≃ₗ[k] f.ker := by
    let into : ↥(F⊓A) →ₗ[k] ↥(F⊓B) := Submodule.inclusion (inf_le_inf_left _ inc)
    have kernel (v : ↥(F⊓B)) : v∈f.ker ↔ (v:V)∈A := by
      rw [LinearMap.mem_ker,eval_f,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      rfl
    let i := into.codRestrict f.ker fun v=>(kernel (into v)).mpr v.property.2
    refine LinearEquiv.ofBijective i ⟨fun v w eq=>Subtype.ext (congrArg (fun z : f.ker=>(z.1:V)) eq),?_⟩
    intro z
    exact ⟨⟨z.1,⟨z.1.property.1,(kernel z.1).mp z.property⟩⟩,rfl⟩
  have : FiniteDimensional k (V ⧸ P) := FiniteDimensional.of_surjective g g_surj
  have : FiniteDimensional k ↥(F⊓A) := FiniteDimensional.of_injective e.toLinearMap e.injective
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hg := LinearMap.finrank_range_add_finrank_ker g
  rw [exact_fg,←e.finrank_eq] at hf
  rw [LinearMap.range_eq_top.mpr g_surj,finrank_top] at hg
  exact ⟨inferInstance,inferInstance,by dsimp only [P,D] at *; omega⟩
#print axioms compare_lattices
end
end Lower6960.LineEuler

end Merged6967_R6960LineEulerComparison

section Merged6967_R6966ProofAffineODE
set_option Elab.async false





set_option Elab.async false

namespace Research6966.AffineODE

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Numerators of the linear and constant terms after clearing the n-th
derivative of a solution of A*y' = B*y + C by A^n. -/
def pair (δ : R → R) (A B C : R) : ℕ → R × R
  | 0 => (1, 0)
  | n + 1 =>
    let (l, m) := pair δ A B C n
    (A * δ l - n * δ A * l + B * l, A * δ m - n * δ A * m + C * l)

private theorem clear_power (D : S →+ S) (one : D 1 = 0)
    (mul : ∀ a b, D (a*b) = D a*b + a*D b) (a : S) (n : ℕ) :
    a * D (a^n) = n * a^n * D a := by
  induction n with
  | zero => simp [one]
  | succ n ih =>
    rw [pow_succ, mul, Nat.cast_succ]; linear_combination a * ih

/-- Specializing the two seed coefficients commutes with abscissa
differentiation. No nonzero initial value or separant at a code node is needed. -/
theorem cleared_derivatives (δ : R → R) (D : S →+ S) (f : R →+* S)
    (one : D 1 = 0) (mul : ∀ a b, D (a*b) = D a*b + a*D b)
    (coeff : ∀ a, D (f a) = f (δ a)) (A B C : R) (y : S)
    (ode : f A * D y = f B * y + f C) (n : ℕ) :
    f A ^ n * D^[n] y = f (pair δ A B C n).1 * y + f (pair δ A B C n).2 := by
  induction n with
  | zero => simp [pair]
  | succ n ih =>
    have diff := congrArg D ih
    simp only [mul, map_add, coeff] at diff
    rw [Function.iterate_succ_apply', pow_succ, pair]
    simp only [map_add, map_sub, map_mul, map_natCast]
    have power := clear_power D one mul (f A) n
    rw [coeff] at power
    linear_combination f A * diff + f (pair δ A B C n).1 * ode
      - (D^[n] y) * power - (n:S) * f (δ A) * ih

open MvPolynomial in
theorem degree_bounds {σ k : Type*} [Field k] (δ : MvPolynomial σ k → MvPolynomial σ k)
    (keeps : ∀ p, (δ p).totalDegree ≤ p.totalDegree) (A B C : MvPolynomial σ k)
    (u : ℕ) (ha : A.totalDegree ≤ u) (hb : B.totalDegree ≤ u) (hc : C.totalDegree ≤ u) (n : ℕ) :
    (pair δ A B C n).1.totalDegree ≤ n*u ∧ (pair δ A B C n).2.totalDegree ≤ n*u := by
  induction n with
  | zero => simp [pair]
  | succ n ih =>
    have step («X» «Y» : MvPolynomial σ k) (hx : «X».totalDegree ≤ n*u)
        (hy : «Y».totalDegree ≤ n*u) (T : MvPolynomial σ k) (ht : T.totalDegree ≤ u) :
        (A*δ «X» - n*δ A*«X» + T*«Y»).totalDegree ≤ (n+1)*u := by
      apply (totalDegree_add _ _).trans; apply max_le
      · apply (totalDegree_sub _ _).trans; apply max_le
        · apply (totalDegree_mul _ _).trans;rw [Nat.succ_mul];have := keeps «X»;omega
        · apply (totalDegree_mul _ _).trans
          have hnum : ((n : MvPolynomial σ k) * δ A).totalDegree ≤ u := by
            apply (totalDegree_mul _ _).trans
            have hz : (n : MvPolynomial σ k).totalDegree=0 := by
              rw [← map_natCast (MvPolynomial.C : k →+* MvPolynomial σ k), totalDegree_C]
            have := keeps A
            omega
          rw [Nat.succ_mul];omega
      · apply (totalDegree_mul _ _).trans;rw [Nat.succ_mul];omega
    exact ⟨step _ _ ih.1 ih.1 B hb,step _ _ ih.2 ih.1 C hc⟩

#print axioms cleared_derivatives
#print axioms degree_bounds

/-- Put every Taylor coefficient over the same denominator. The weights are
the scalar evaluation weights at a physical coordinate. -/
def response (d : ℕ) (weights : ℕ → R) (A : R) (p : ℕ → R) : R :=
  ∑ i ∈ Finset.range (d+1), weights i * A^(d-i) * p i

theorem common_denominator (A : R) (f : R →+* S) (y : S)
    (l m : ℕ → R) (v : ℕ → S) (d : ℕ) (weights : ℕ → R)
    (entry : ∀ i ≤ d, f A^i * v i = f (l i)*y + f (m i)) :
    f A^d * (∑ i ∈ Finset.range (d+1), f (weights i)*v i) =
        f (response d weights A l)*y + f (response d weights A m) := by
  simp only [response,map_sum,map_mul,map_pow,Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have le : i≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  conv_lhs => rw [←Nat.sub_add_cancel le,pow_add]
  linear_combination f (weights i)*f A^(d-i)*entry i le

open MvPolynomial in
theorem response_degree {σ k : Type*} [Field k] (A : MvPolynomial σ k) (u d : ℕ)
    (weights p : ℕ → MvPolynomial σ k) (hA : A.totalDegree≤u)
    (hw : ∀ i : ℕ, (weights i).totalDegree = 0) (hp : ∀ i : ℕ, (p i).totalDegree ≤ i * u) :
    (response d weights A p).totalDegree ≤ d * u := by
  unfold response
  apply Finset.sum_induction _ (fun q:MvPolynomial σ k=>q.totalDegree≤d*u)
  · exact fun v w hv hw'=>(totalDegree_add _ _).trans (max_le hv hw')
  · simp
  · intro i hi
    have le : i≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    apply (totalDegree_mul _ _).trans
    have lhs: (weights i * A^(d-i)).totalDegree≤(d-i)*u := by
      apply (totalDegree_mul _ _).trans
      rw [hw,zero_add]
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hA)
    exact (Nat.add_le_add lhs (hp i)).trans_eq (by rw [←Nat.add_mul,Nat.sub_add_cancel le])

open Polynomial in
theorem evaluation_from_derivatives {k : Type*} [Field k] (p : k[X]) (x t : k)
    (d : ℕ) (deg : p.natDegree≤d) (fac : ∀ i ≤ d, (i.factorial : k)≠0) :
    p.eval t = ∑ i ∈ Finset.range (d+1), ((t-x)^i / (i.factorial:k)) *
      (derivative^[i] p).eval x := by
  calc
    _ = (taylor x p).eval (t-x) := (taylor_eval_sub x p t).symm
    _ = _ := by
      rw [(taylor x p).eval_eq_sum_range' (n:=d+1) (by rw [natDegree_taylor]; omega) (t-x)]
      apply Finset.sum_congr rfl
      intro i hi
      have le:=Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have h := congrFun (factorial_smul_hasseDeriv (R:=k) i) p
      change i.factorial • (hasseDeriv i p) = derivative^[i] p at h
      rw [taylor_coeff,←h, show (i.factorial • (hasseDeriv i p)).eval x =
        i.factorial • (hasseDeriv i p).eval x from map_nsmul (evalRingHom x) _ _,nsmul_eq_mul]
      field_simp [fac i le]

#print axioms common_denominator
#print axioms response_degree
#print axioms evaluation_from_derivatives

end Research6966.AffineODE

end Merged6967_R6966ProofAffineODE

section Merged6967_R6966ProofBoundaryRank
set_option Elab.async false



set_option Elab.async false

namespace Research6966.BoundaryRank
open Module Submodule
universe u
variable {k L ι : Type u} [Field k] [Field L] [Algebra k L]
variable (slots : Submodule k L) [FiniteDimensional k slots]

/-- A boundary of fraction-field rank r costs at most r times the native
seed-slot dimension. A row reduction need not preserve the individual slot
space under arbitrary fraction-field coefficients. -/
theorem slots_times_rank (r : ℕ) :
    ∀ (U V : Type u) [AddCommGroup U] [Module L U] [FiniteDimensional L U]
      [Module k U] [IsScalarTower k L U] [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      finrank L U = r → ∀ (coord : U →ₗ[L] (ι → L)) (embed : V →ₗ[k] U),
      Function.Injective coord → Function.Injective embed →
      (∀ x i,coord (embed x) i ∈ slots) → finrank k V ≤ r * finrank k slots := by
  classical
  induction r using Nat.strong_induction_on with
  | ind r smaller =>
    intro U V _ _ _ _ _ _ _ _ dim coord embed coords_inj embed_inj fits
    by_cases trivial : ∀ x : V, x=0
    · rw [Module.finrank_zero_iff.mpr (show Subsingleton V from
        ⟨fun x y=> (trivial x).trans (trivial y).symm⟩)]
      exact Nat.zero_le _
    push Not at trivial
    obtain ⟨x,xnz⟩:=trivial
    have vx : embed x ≠ 0 := fun h=>xnz (embed_inj (h.trans embed.map_zero.symm))
    have ux : coord (embed x) ≠ 0 := fun h=>vx (coords_inj (h.trans coord.map_zero.symm))
    obtain ⟨i,ix⟩ : ∃ i, coord (embed x) i ≠ 0 := by
      by_contra! hz
      exact ux (funext hz)
    let axis : U →ₗ[L] L := (LinearMap.proj i).comp coord
    let f : V →ₗ[k] slots := ((axis.restrictScalars k).comp embed).codRestrict slots (fun y=>fits y i)
    have pos : 0<finrank L axis.range := by
      let value : axis.range := ⟨axis (embed x),⟨embed x,rfl⟩⟩
      have ne : value≠0 := fun eq=>ix (congrArg Subtype.val eq)
      have : Nontrivial axis.range := ⟨⟨value,0,ne⟩⟩
      exact Module.finrank_pos
    have Udim:=axis.finrank_range_add_finrank_ker
    have lt : finrank L axis.ker < r := by omega
    let component : axis.ker →ₗ[L] (ι→L) := coord.comp axis.ker.subtype
    let sub : f.ker →ₗ[k] axis.ker :=
      (embed.comp f.ker.subtype).codRestrict (axis.ker.restrictScalars k) (by
        intro z
        change axis (embed z.val)=0
        exact congrArg Subtype.val (LinearMap.mem_ker.mp z.property))
    have remain:=smaller _ lt axis.ker f.ker rfl component sub
      (coords_inj.comp Subtype.val_injective)
      (fun x y eq=>Subtype.ext (embed_inj (congrArg Subtype.val eq)))
      (fun z j=>fits z.val j)
    have Vdim:=f.finrank_range_add_finrank_ker
    have rank:=f.range.finrank_le
    have rest := Nat.mul_le_mul_right (finrank k slots) (show finrank L axis.ker + 1 ≤ r by omega)
    rw [Nat.add_mul,one_mul] at rest
    omega

#print axioms slots_times_rank
end Research6966.BoundaryRank

end Merged6967_R6966ProofBoundaryRank

section Merged6967_R6966ProofLowTierWeight
set_option Elab.async false


set_option Elab.async false

namespace Research6966.LowTierWeight
open Finset

def weight (J j : ℕ) : ℕ := 4*j + if J < 2*j then J else 0

theorem mono (J : ℕ) {j k : ℕ} (h : j ≤ k) : weight J j ≤ weight J k := by
  unfold weight
  split <;> split <;> omega

theorem total {ι : Type*} (s : Finset ι) (f : ι → ℕ) {J : ℕ}
    (fits : ∑ i ∈ s, f i ≤ J) : ∑ i ∈ s, weight J (f i) ≤ 5*J := by
  classical
  let heavy := s.filter (fun i => J < 2*f i)
  have one : heavy.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨his, hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, hj'⟩ := Finset.mem_filter.mp hj
    by_contra ne
    have sub : ({i,j} : Finset ι) ⊆ s := by
      intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact his
      · exact hjs
    have h := (Finset.sum_le_sum_of_subset_of_nonneg sub (f:=f) (by intros; omega)).trans fits
    rw [Finset.sum_pair ne] at h
    omega
  have charged : (∑ i ∈ s, if J < 2*f i then J else 0) = heavy.card * J := by
    rw [← Finset.sum_filter]
    simp [heavy]
  simp only [weight,Finset.sum_add_distrib,← Finset.mul_sum,charged]
  have h := Nat.mul_le_mul_right J one
  omega

#print axioms total
end Research6966.LowTierWeight

end Merged6967_R6966ProofLowTierWeight

section Merged6967_R6966ProofNearLedgerBudget
set_option Elab.async false


set_option Elab.async false

-- merged module R6966ProofNearLedgerCore
section Merged_R6966ProofNearLedgerCore

namespace Research6966.NearLedger

abbrev core : ℕ := 274785163470757553
abbrev credit : ℕ := 1723299391600
abbrev prime : ℕ := 2130706433
abbrev nodes : ℕ := 262144
abbrev agreement : ℕ := 179759
abbrev wordDegree : ℕ := 133593
abbrev massCap : ℕ := 12585
abbrev graphCap : ℕ := 403

def rate (e : ℕ) : ℕ :=
  let n := max 3 e
  (9*n+2)*(n-1)+2*n-1+2*e-1

def density (e : ℕ) : ℕ := rate e*prime

theorem rate_mono : Monotone rate := by
  intro e f h
  have n : max 3 e ≤ max 3 f := max_le_max le_rfl h
  unfold rate
  dsimp only
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.sub_le_sub_right (Nat.add_le_add
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 n) 2)
        (Nat.sub_le_sub_right n 1)) (Nat.mul_le_mul_left 2 n)) 1)
    (Nat.mul_le_mul_left 2 h)) 1

structure Book where
  fee : ℕ
  credit : ℕ
  mass : ℕ
  grade : ℕ

structure Branch where
  extra : ℕ
  primary : Book
  rescue : Book

def Branch.base (b : Branch) : ℕ := b.extra+b.primary.fee+b.rescue.fee

def Book.debit (b : Book) (r : ℕ) : ℕ := b.fee+(r-b.credit)*b.mass

def Branch.debit (b : Branch) (r : ℕ) : ℕ :=
  b.extra+b.primary.debit r+b.rescue.debit r

/-- The two actual prefix invoices and their retained integer masses.
Use zero paid and zero mass when there is no rescue. -/
structure Invoice (b : Branch) where
  extraPaid : ℕ
  primaryPaid : ℕ
  rescuePaid : ℕ
  primaryMass : ℕ
  rescueMass : ℕ
  extra_le : extraPaid≤b.extra
  primary_bill : primaryPaid+b.primary.credit*primaryMass≤b.primary.fee
  rescue_bill : rescuePaid+b.rescue.credit*rescueMass≤b.rescue.fee
  primary_cap : primaryMass≤b.primary.mass
  rescue_cap : rescueMass≤b.rescue.mass

def Invoice.paid {b : Branch} (I : Invoice b) : ℕ := I.extraPaid+I.primaryPaid+I.rescuePaid
def Invoice.mass {b : Branch} (I : Invoice b) : ℕ := I.primaryMass+I.rescueMass

private theorem book_debit (b : Book) {paid m r : ℕ}
    (cap : m≤b.mass) (bill : paid+b.credit*m≤b.fee) :
    paid+r*m≤b.debit r := by
  unfold Book.debit
  by_cases bound : r≤b.credit
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_right m bound) paid).trans
      (bill.trans (Nat.le_add_right _ _))
  · have eq : r=b.credit+(r-b.credit) := by omega
    calc
      paid+r*m = paid+b.credit*m+(r-b.credit)*m := by
        conv_lhs => rw [eq, Nat.add_mul]
        omega
      _ ≤ _ := Nat.add_le_add bill (Nat.mul_le_mul_left (r-b.credit) cap)

theorem Invoice.debit_le {b : Branch} (I : Invoice b) (r : ℕ) :
    I.paid+r*I.mass≤b.debit r := by
  unfold Invoice.paid Invoice.mass Branch.debit
  rw [Nat.mul_add]
  have main := book_debit b.primary I.primary_cap I.primary_bill (r:=r)
  have rescue := book_debit b.rescue I.rescue_cap I.rescue_bill (r:=r)
  have other := I.extra_le
  omega

theorem Invoice.credit_le {b : Branch} (I : Invoice b)
    (main : credit≤b.primary.credit) (rescue : credit≤b.rescue.credit) :
    I.paid+credit*I.mass≤b.base := by
  unfold Invoice.paid Invoice.mass Branch.base
  rw [Nat.mul_add]
  have hm := (Nat.add_le_add_left (Nat.mul_le_mul_right I.primaryMass main) _).trans I.primary_bill
  have hr := (Nat.add_le_add_left (Nat.mul_le_mul_right I.rescueMass rescue) _).trans I.rescue_bill
  have other := I.extra_le
  omega

structure Band where
  low : ℕ
  high : ℕ
  content : ℕ
  maxGraph : ℕ

def band : Fin 7 → Band :=
  ![⟨19,20,8,6⟩,⟨21,23,8,5⟩,⟨24,24,8,4⟩,⟨25,28,7,4⟩,⟨29,40,7,3⟩,⟨41,42,8,3⟩,⟨43,403,8,2⟩]

def bandFor (e : ℕ) : Fin 7 := if e≤20 then 0 else if e≤23 then 1 else if e≤24 then 2 else if e≤28 then 3 else if e≤40 then 4 else if e≤42 then 5 else 6

theorem bandFor_bounds {e : ℕ} (lo : 19≤e) (hi : e≤graphCap) :
    (band (bandFor e)).low≤e ∧ e≤(band (bandFor e)).high := by
  change e ≤ 403 at hi
  unfold bandFor
  repeat' first | split | (simp [band]; omega)

def Band.off (b : Band) (a : ℕ) : ℕ := b.content-a
def Band.additive (b : Band) : ℕ := 2*b.high^2

def levels : Fin 55 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 96, 128, 160, 192, 256, 384, 512, 768, 1024, 1536, 2048, 2560, 3072, 3328, 3584, 3840, 3968, 4096]
def upper (i : Fin 55) : Option ℕ :=
  if h : i.val+1<55 then some (levels ⟨i.val+1,h⟩-1) else none

def InBin (i : Fin 55) (v : ℕ) : Prop :=
  levels i≤v ∧ ∀ u, upper i = some u → v≤u

private def binsAt (v : ℕ) : Finset (Fin 55) :=
  Finset.univ.filter (fun i => levels i≤v)

private theorem bins_nonempty (v : ℕ) : (binsAt v).Nonempty :=
  ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, Nat.zero_le v⟩⟩

def seedBin (v : ℕ) : Fin 55 := (binsAt v).max' (bins_nonempty v)

theorem seedBin_valid (v : ℕ) : InBin (seedBin v) v := by
  have chosen : seedBin v ∈ binsAt v := Finset.max'_mem _ (bins_nonempty v)
  refine ⟨(Finset.mem_filter.mp chosen).2, ?_⟩
  intro u eq
  unfold upper at eq
  split at eq
  · rename_i within
    let next : Fin 55 := ⟨(seedBin v).val+1,within⟩
    have value : levels next-1=u := Option.some.inj eq
    by_contra! tooBig
    have live : next ∈ binsAt v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have impossible : next≤seedBin v := Finset.le_max' _ _ live
    change (seedBin v).val+1≤(seedBin v).val at impossible
    omega
  · cases eq

end Research6966.NearLedger

end Merged_R6966ProofNearLedgerCore

-- merged module R6966ProofNearLedgerBudget
section Merged_R6966ProofNearLedgerBudget

namespace Research6966.NearLedger
set_option maxRecDepth 12000
set_option maxHeartbeats 0

def branch : Fin 58 → Branch :=
  ![⟨0,⟨144083194789679315,1723299391600,5082,246⟩,⟨0,1723299391600,0,0⟩⟩,
    ⟨417347318636111,⟨144083194789679315,1723299391600,5082,246⟩,⟨0,1723299391600,0,0⟩⟩,
    ⟨10653666579205813,⟨130933022881678518,1729199597045,4592,246⟩,⟨0,1729199597045,0,0⟩⟩,
    ⟨12000000000000000,⟨130933022881678518,1729199597045,4592,246⟩,⟨0,1729199597045,0,0⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨92610100963243990,1966757126305,8125,147⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨90358823570671163,2089493088750,7498,140⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨80170586702262012,1997341293528,7296,140⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨61477414510372506,2330068544742,5762,130⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨39295831866046273,2288329059737,3724,157⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨15435969365880012,2753396683095,2038,127⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨7214451125046820,5639420798540,877,57⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6925828274602807,5887582817645,860,44⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6306077059444644,5993674230270,801,33⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨35584831410235196,2186532478300,4279,149⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨34124913332834259,2209399385115,4114,148⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨32502133044203653,2222849828685,3916,149⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨26841347699298545,2353141367710,3265,142⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨19480561896717531,2558999450370,2507,133⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨11121008686898504,3505727704210,1456,95⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6610284632259213,5330167548730,815,62⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6671188754944467,5847015485405,819,49⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6214698061610365,5993674230270,774,38⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨14136796512309709,3073985113195,1749,107⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨13861532961091914,3078184974930,1695,108⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨13649275768198341,3094232072930,1687,107⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨12135845243725455,3341015152205,1487,99⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨10535562518662936,3461089144180,1277,98⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨8314232654019483,3983573602410,1074,84⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6128988906181846,5222716650680,752,64⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6464571108244754,5784640056410,783,55⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6249291093054034,6079358164345,758,43⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨8031123563385117,3896447414015,962,87⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨8209405599410345,4169057408100,996,79⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨8191924590225481,3957266785410,974,85⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨7839533479327399,4051190490280,959,83⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨7388062104987402,4178869240875,903,81⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6810926732396973,4343902164000,848,78⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5760174439848498,5229885936305,696,64⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6127778983546109,5690312204290,737,57⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6281101399543713,6069310057475,747,50⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5617505585440675,4623871063870,618,75⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5736751793132154,4589862163440,649,75⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5928548349122789,4519614574510,677,76⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5926936009212281,4583824528670,670,75⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5961556271662637,4516018072165,698,76⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5910531335684274,4589745745260,713,74⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5489428533286829,5360095826990,642,63⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5801510946411699,5455853097490,699,60⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨6149126784953953,6049798050175,726,51⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨4621585997943819,4952080442295,498,70⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨4673141435185573,4850890833080,506,72⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨4761783281351884,4699883025460,514,75⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨4926075113228897,4825021524430,543,72⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5151670333708823,4964608685930,569,69⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5384337433737958,4907682509695,626,69⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5207160863916676,5392997627335,607,62⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5577081789534753,5356187234400,671,61⟩⟩,
    ⟨0,⟨127815628075157321,1729755992975,4460,246⟩,⟨5847153368777549,5732210930305,701,56⟩⟩]

def free : ℕ := 54359434432356242

private def debitTable : Fin 48 → ℕ :=
  ![220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220425729038401311, 220940572608294691, 224940433021693546, 230410680875391766, 236363597657357476, 242799183367590676, 249717438006091366, 257118361572859546, 265001954067895216, 273368215491198376, 282217145842769026, 291548745122607166, 301363013330712796, 311659950467085916, 322439556531726526, 333701831524634626, 345446775445810216, 357674388295253296, 370384670072963866, 383577620778941926, 397253240413187476, 411411528975700516, 426052486466481046, 441176112885529066, 456782408232844576, 472871372508427576, 489443005712278066, 506497307844396046, 524034278904781516, 542053918893434476, 560556227810354926, 579541205655542866, 599008852428998296, 618959168130721216, 639392152760711626, 660307806318969526, 681706128805494916, 703587120220287796, 725950780563348166]

def nativeCap (n : ℕ) : ℕ := if h : n<48 then debitTable ⟨n,h⟩ else core+1

theorem branch_base (i : Fin 58) : (branch i).base+free≤core ∧
    credit≤(branch i).primary.credit ∧ credit≤(branch i).rescue.credit ∧
    (branch i).primary.mass+(branch i).rescue.mass≤massCap ∧
    (branch i).primary.grade+(branch i).rescue.grade≤graphCap := by
  fin_cases i <;> decide +kernel

private theorem cap0 : ∀ r : Fin 58, (branch r).debit (density 0)≤nativeCap 0 := by
  decide +kernel

private theorem cap1 : ∀ r : Fin 58, (branch r).debit (density 1)≤nativeCap 1 := by
  decide +kernel

private theorem cap2 : ∀ r : Fin 58, (branch r).debit (density 2)≤nativeCap 2 := by
  decide +kernel

private theorem cap3 : ∀ r : Fin 58, (branch r).debit (density 3)≤nativeCap 3 := by
  decide +kernel

private theorem cap4 : ∀ r : Fin 58, (branch r).debit (density 4)≤nativeCap 4 := by
  decide +kernel

private theorem cap5 : ∀ r : Fin 58, (branch r).debit (density 5)≤nativeCap 5 := by
  decide +kernel

private theorem cap6 : ∀ r : Fin 58, (branch r).debit (density 6)≤nativeCap 6 := by
  decide +kernel

private theorem cap7 : ∀ r : Fin 58, (branch r).debit (density 7)≤nativeCap 7 := by
  decide +kernel

private theorem cap8 : ∀ r : Fin 58, (branch r).debit (density 8)≤nativeCap 8 := by
  decide +kernel

private theorem cap9 : ∀ r : Fin 58, (branch r).debit (density 9)≤nativeCap 9 := by
  decide +kernel

private theorem cap10 : ∀ r : Fin 58, (branch r).debit (density 10)≤nativeCap 10 := by
  decide +kernel

private theorem cap11 : ∀ r : Fin 58, (branch r).debit (density 11)≤nativeCap 11 := by
  decide +kernel

private theorem cap12 : ∀ r : Fin 58, (branch r).debit (density 12)≤nativeCap 12 := by
  decide +kernel

private theorem cap13 : ∀ r : Fin 58, (branch r).debit (density 13)≤nativeCap 13 := by
  decide +kernel

private theorem cap14 : ∀ r : Fin 58, (branch r).debit (density 14)≤nativeCap 14 := by
  decide +kernel

private theorem cap15 : ∀ r : Fin 58, (branch r).debit (density 15)≤nativeCap 15 := by
  decide +kernel

private theorem cap16 : ∀ r : Fin 58, (branch r).debit (density 16)≤nativeCap 16 := by
  decide +kernel

private theorem cap17 : ∀ r : Fin 58, (branch r).debit (density 17)≤nativeCap 17 := by
  decide +kernel

private theorem cap18 : ∀ r : Fin 58, (branch r).debit (density 18)≤nativeCap 18 := by
  decide +kernel

private theorem cap19 : ∀ r : Fin 58, (branch r).debit (density 19)≤nativeCap 19 := by
  decide +kernel

private theorem cap20 : ∀ r : Fin 58, (branch r).debit (density 20)≤nativeCap 20 := by
  decide +kernel

private theorem cap21 : ∀ r : Fin 58, (branch r).debit (density 21)≤nativeCap 21 := by
  decide +kernel

private theorem cap22 : ∀ r : Fin 58, (branch r).debit (density 22)≤nativeCap 22 := by
  decide +kernel

private theorem cap23 : ∀ r : Fin 58, (branch r).debit (density 23)≤nativeCap 23 := by
  decide +kernel

private theorem cap24 : ∀ r : Fin 58, (branch r).debit (density 24)≤nativeCap 24 := by
  decide +kernel

private theorem cap25 : ∀ r : Fin 58, (branch r).debit (density 25)≤nativeCap 25 := by
  decide +kernel

private theorem cap26 : ∀ r : Fin 58, (branch r).debit (density 26)≤nativeCap 26 := by
  decide +kernel

private theorem cap27 : ∀ r : Fin 58, (branch r).debit (density 27)≤nativeCap 27 := by
  decide +kernel

private theorem cap28 : ∀ r : Fin 58, (branch r).debit (density 28)≤nativeCap 28 := by
  decide +kernel

private theorem cap29 : ∀ r : Fin 58, (branch r).debit (density 29)≤nativeCap 29 := by
  decide +kernel

private theorem cap30 : ∀ r : Fin 58, (branch r).debit (density 30)≤nativeCap 30 := by
  decide +kernel

private theorem cap31 : ∀ r : Fin 58, (branch r).debit (density 31)≤nativeCap 31 := by
  decide +kernel

private theorem cap32 : ∀ r : Fin 58, (branch r).debit (density 32)≤nativeCap 32 := by
  decide +kernel

private theorem cap33 : ∀ r : Fin 58, (branch r).debit (density 33)≤nativeCap 33 := by
  decide +kernel

private theorem cap34 : ∀ r : Fin 58, (branch r).debit (density 34)≤nativeCap 34 := by
  decide +kernel

private theorem cap35 : ∀ r : Fin 58, (branch r).debit (density 35)≤nativeCap 35 := by
  decide +kernel

private theorem cap36 : ∀ r : Fin 58, (branch r).debit (density 36)≤nativeCap 36 := by
  decide +kernel

private theorem cap37 : ∀ r : Fin 58, (branch r).debit (density 37)≤nativeCap 37 := by
  decide +kernel

private theorem cap38 : ∀ r : Fin 58, (branch r).debit (density 38)≤nativeCap 38 := by
  decide +kernel

private theorem cap39 : ∀ r : Fin 58, (branch r).debit (density 39)≤nativeCap 39 := by
  decide +kernel

private theorem cap40 : ∀ r : Fin 58, (branch r).debit (density 40)≤nativeCap 40 := by
  decide +kernel

private theorem cap41 : ∀ r : Fin 58, (branch r).debit (density 41)≤nativeCap 41 := by
  decide +kernel

private theorem cap42 : ∀ r : Fin 58, (branch r).debit (density 42)≤nativeCap 42 := by
  decide +kernel

private theorem cap43 : ∀ r : Fin 58, (branch r).debit (density 43)≤nativeCap 43 := by
  decide +kernel

private theorem cap44 : ∀ r : Fin 58, (branch r).debit (density 44)≤nativeCap 44 := by
  decide +kernel

private theorem cap45 : ∀ r : Fin 58, (branch r).debit (density 45)≤nativeCap 45 := by
  decide +kernel

private theorem cap46 : ∀ r : Fin 58, (branch r).debit (density 46)≤nativeCap 46 := by
  decide +kernel

private theorem cap47 : ∀ r : Fin 58, (branch r).debit (density 47)≤nativeCap 47 := by
  decide +kernel

private theorem cap_fin (g : Fin 48) (r : Fin 58) :
    (branch r).debit (density g.val)≤nativeCap g.val := by
  fin_cases g
  · exact cap0 r
  · exact cap1 r
  · exact cap2 r
  · exact cap3 r
  · exact cap4 r
  · exact cap5 r
  · exact cap6 r
  · exact cap7 r
  · exact cap8 r
  · exact cap9 r
  · exact cap10 r
  · exact cap11 r
  · exact cap12 r
  · exact cap13 r
  · exact cap14 r
  · exact cap15 r
  · exact cap16 r
  · exact cap17 r
  · exact cap18 r
  · exact cap19 r
  · exact cap20 r
  · exact cap21 r
  · exact cap22 r
  · exact cap23 r
  · exact cap24 r
  · exact cap25 r
  · exact cap26 r
  · exact cap27 r
  · exact cap28 r
  · exact cap29 r
  · exact cap30 r
  · exact cap31 r
  · exact cap32 r
  · exact cap33 r
  · exact cap34 r
  · exact cap35 r
  · exact cap36 r
  · exact cap37 r
  · exact cap38 r
  · exact cap39 r
  · exact cap40 r
  · exact cap41 r
  · exact cap42 r
  · exact cap43 r
  · exact cap44 r
  · exact cap45 r
  · exact cap46 r
  · exact cap47 r

theorem branch_native (r : Fin 58) {g : ℕ} (small : g<48) :
    (branch r).debit (density g)≤nativeCap g := cap_fin ⟨g,small⟩ r

theorem small_cap : nativeCap 18+17*18≤core := by decide +kernel
#print axioms branch_base
#print axioms branch_native
end Research6966.NearLedger

end Merged_R6966ProofNearLedgerBudget

end Merged6967_R6966ProofNearLedgerBudget

section Merged6967_R6966ProofPadeCoverage
set_option Elab.async false




set_option Elab.async false

-- merged module R6966ProofPadeClassification
section Merged_R6966ProofPadeClassification

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K : Type*} [Field K]

/-- The graph equation is a(Y)V=b(Y). -/
structure Row (K : Type*) [Semiring K] where
  a : K[X]
  b : K[X]

def Row.fits (F : Row K) (d : ℕ) : Prop :=
  (∀ j, d≤j → F.a.coeff j=0) ∧ (∀ j, d<j → F.b.coeff j=0)

def Row.err (F : Row K) (v : K→K) (x : K) := F.a.eval x * v x - F.b.eval x
def Row.det (F G : Row K) := F.a*G.b-G.a*F.b
def nodes (s : Finset K) : K[X] := ∏ y∈s,(«X»-C y)

/-- Divide-and-cancel interpolation. The two shifted degree caps always
sum to one plus the number of processed ordinates. -/
structure Frame (s : Finset K) (v : K→K) where
  left : Row K
  right : Row K
  l : ℕ
  r : ℕ
  lfit : left.fits l
  rfit : right.fits r
  total : l+r=s.card+1
  lhit : ∀ y∈s,left.err v y=0
  rhit : ∀ y∈s,right.err v y=0
  scalar : K
  scalar_ne : scalar≠0
  det_eq : left.det right=C scalar*nodes s

private def Frame.swap {s : Finset K} {v : K→K} (F : Frame s v) : Frame s v where
  left := F.right
  right := F.left
  l := F.r
  r := F.l
  lfit := F.rfit
  rfit := F.lfit
  total := (Nat.add_comm ..).trans F.total
  lhit := F.rhit
  rhit := F.lhit
  scalar := -F.scalar
  scalar_ne := neg_ne_zero.mpr F.scalar_ne
  det_eq := by
    rw [map_neg,neg_mul,← F.det_eq]
    unfold Row.det;ring

private def shift (F : Row K) (x : K) : Row K :=
  ⟨(«X»-C x)*F.a,(«X»-C x)*F.b⟩
private def cancel (F G : Row K) (t : K) : Row K :=
  ⟨G.a-C t*F.a,G.b-C t*F.b⟩

private theorem shift_fit {F : Row K} {d : ℕ} (hf : F.fits d) (x : K) :
    (shift F x).fits (d+1) := by
  constructor
  · rintro (_|j) hj
    · omega
    · simp only [shift,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,hf.1 j (by omega),
        hf.1 (j+1) (by omega),mul_zero,sub_zero]
  · rintro (_|j) hj
    · omega
    · simp only [shift,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,hf.2 j (by omega),
        hf.2 (j+1) (by omega),mul_zero,sub_zero]

private theorem cancel_fit {F G : Row K} {d e : ℕ} (hf : F.fits d) (hg : G.fits e)
    (t : K) (ok : d≤e ∨ t=0) : (cancel F G t).fits e := by
  rcases ok with le|rfl
  · constructor
    · intro j h
      simp [cancel,coeff_C_mul,hg.1 j h,hf.1 j (by omega)]
    · intro j h
      simp [cancel,coeff_C_mul,hg.2 j h,hf.2 j (by omega)]
  · simpa [Row.fits,cancel] using hg

private theorem shift_err (F : Row K) (v : K→K) (x y : K) :
    (shift F x).err v y=(y-x)*F.err v y := by
  simp [Row.err,shift];ring
private theorem cancel_err (F G : Row K) (t : K) (v : K→K) (y : K) :
    (cancel F G t).err v y=G.err v y-t*F.err v y := by
  simp [Row.err,cancel];ring

private theorem eval_nodes_ne {s : Finset K} {x : K} (hx : x∉s) : (nodes s).eval x≠0 := by
  classical
  simpa only [nodes,eval_prod,eval_sub,eval_X,eval_C] using
    (prod_ne_zero_iff.mpr (fun y hy=>sub_ne_zero.mpr (fun eq : x=y=>hx (eq ▸ hy))) :
      ∏ y∈s,(x-y)≠0)

private def Frame.step [DecidableEq K] {s : Finset K} {v : K→K}
    (F : Frame s v) (x : K) (fresh : x∉s) (active : F.left.err v x≠0)
    (cheap : F.l≤F.r ∨ F.right.err v x=0) : Frame (insert x s) v := by
  let t:=F.right.err v x/F.left.err v x
  refine ⟨shift F.left x,cancel F.left F.right t,F.l+1,F.r,shift_fit F.lfit x,
    cancel_fit F.lfit F.rfit _ (cheap.imp_right (by intro z;simp [t,z])),?_,?_,?_,
    F.scalar,F.scalar_ne,?_⟩
  · rw [card_insert_of_notMem fresh];have := F.total;omega
  · intro y hy
    rw [shift_err]
    rcases mem_insert.mp hy with rfl|mem
    · simp
    · simp [F.lhit _ mem]
  · intro y hy
    rw [cancel_err]
    rcases mem_insert.mp hy with rfl|mem
    · simp [t,active]
    · simp [F.lhit _ mem,F.rhit _ mem]
  · rw [show nodes (insert x s)=(«X»-C x)*nodes s by simp [nodes,fresh]]
    calc
      _=(«X»-C x)*F.left.det F.right := by simp only [shift,cancel,Row.det];ring
      _=_ := by rw [F.det_eq];ring

/-- Two actual slope-linear interpolation rows for every finite set of
distinct ordinates. Their determinant has exactly those simple roots. -/
theorem frame_exists (s : Finset K) (v : K→K) : Nonempty (Frame s v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⟨⟨1,0⟩,⟨0,1⟩,1,0,?_,?_,by simp,by simp,by simp,1,one_ne_zero,?_⟩⟩
    · constructor
      · intro j hj;simp [coeff_one,show j≠0 by omega]
      · simp
    · constructor
      · simp
      · intro j hj;simp [coeff_one,show j≠0 by omega]
    · simp [Row.det,nodes]
  | insert x s fresh ih =>
    obtain ⟨F⟩:=ih
    have some_active : F.left.err v x≠0 ∨ F.right.err v x≠0 := by
      by_contra! both
      have eq := congrArg (eval x) F.det_eq
      have le := sub_eq_zero.mp both.1
      have ri := sub_eq_zero.mp both.2
      change F.left.a.eval x*v x=F.left.b.eval x at le
      change F.right.a.eval x*v x=F.right.b.eval x at ri
      simp only [Row.det,eval_sub,eval_mul,eval_C,←le,←ri] at eq
      have impossible:=mul_ne_zero F.scalar_ne (eval_nodes_ne fresh)
      apply impossible
      rw [←eq];ring
    by_cases l : F.left.err v x=0
    · exact ⟨F.swap.step x fresh (some_active.resolve_left (not_not.mpr l)) (Or.inr l)⟩
    by_cases r : F.right.err v x=0
    · exact ⟨F.step x fresh l (Or.inr r)⟩
    by_cases cmp : F.l≤F.r
    · exact ⟨F.step x fresh l (Or.inl cmp)⟩
    · exact ⟨F.swap.step x fresh r (Or.inl (Nat.le_of_not_ge cmp))⟩

#print axioms frame_exists

def Row.graphDegree (F : Row K) := max (F.a.natDegree+1) F.b.natDegree
def Row.primitive (F : Row K) : Prop := F.a≠0 ∧ IsCoprime F.a F.b

private theorem fits_degree {F : Row K} {d : ℕ} (fit : F.fits d) (nz : F.a≠0) :
    F.graphDegree ≤ d := by
  apply max_le
  · by_contra! above
    have z := fit.1 F.a.natDegree (by omega)
    rw [coeff_natDegree] at z
    exact leadingCoeff_ne_zero.mpr nz z
  · exact natDegree_le_iff_coeff_eq_zero.mpr fit.2

private theorem nodes_ne (s : Finset K) : nodes s ≠ 0 := by
  classical
  exact prod_ne_zero_iff.mpr (fun y _=>X_sub_C_ne_zero y)

private theorem nodes_degree (s : Finset K) : (nodes s).natDegree=s.card := by
  classical
  unfold nodes
  rw [natDegree_prod s (fun x=>«X»-C x) (fun x _=>X_sub_C_ne_zero x)]
  simp

private theorem zero_count [DecidableEq K] (s : Finset K) (p : K[X]) (nz : p≠0) :
    (s.filter (fun x=>p.eval x=0)).card ≤ p.natDegree := by
  classical
  have sub : s.filter (fun x=>p.eval x=0) ⊆ p.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (mem_filter.mp hx).2)
  exact (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))

private theorem Frame.left_active {s : Finset K} {v : K→K} (F : Frame s v)
    (lt : F.l<s.card) : F.left.a≠0 := by
  classical
  intro az
  have hits (x) (hx:x∈s) : F.left.b.eval x=0 := by
    simpa [Row.err,az] using F.lhit x hx
  have bz : F.left.b=0 := by
    by_contra nz
    have count := zero_count s _ nz
    rw [filter_eq_self.mpr hits] at count
    have := natDegree_le_iff_coeff_eq_zero.mpr F.lfit.2
    omega
  have nd := mul_ne_zero (C_ne_zero.mpr F.scalar_ne) (nodes_ne s)
  rw [←F.det_eq] at nd
  simp [Row.det,az,bz] at nd

/-- Removing the vertical content loses at most one ordinate per unit of its degree. -/
theorem primitive_part [DecidableEq K] (F : Row K) (v : K→K) (s : Finset K)
    (nz : F.a≠0) (hits : ∀ x∈s,F.err v x=0) :
    ∃ (G : Row K) (t : Finset K), G.primitive ∧ t⊆s ∧
      s.card + G.graphDegree ≤ t.card + F.graphDegree ∧ ∀ x∈t,G.err v x=0 := by
  classical
  let g:=gcd F.a F.b
  have gn : g≠0 := gcd_ne_zero_of_left nz
  let G : Row K := ⟨F.a/g,F.b/g⟩
  have aa : g*G.a=F.a := EuclideanDomain.mul_div_cancel' gn (gcd_dvd_left ..)
  have bb : g*G.b=F.b := EuclideanDomain.mul_div_cancel' gn (gcd_dvd_right ..)
  have ga : G.a≠0 := by intro h;apply nz;rw [←aa,h,mul_zero]
  have adeg := natDegree_mul gn ga
  rw [aa] at adeg
  have bound : g.natDegree+G.graphDegree ≤ F.graphDegree := by
    by_cases zero : G.b=0
    · unfold Row.graphDegree
      rw [zero,natDegree_zero]
      omega
    · have deg := natDegree_mul gn zero
      rw [bb] at deg
      unfold Row.graphDegree
      omega
  let t:=s.filter (fun x=>g.eval x≠0)
  refine ⟨G,t,⟨ga,isCoprime_div_gcd_div_gcd_of_gcd_ne_zero gn⟩,filter_subset _ _,?_,?_⟩
  · have split:=s.card_filter_add_card_filter_not (fun x=>g.eval x=0)
    have loss:=zero_count s g gn
    dsimp [t]
    omega
  · intro x hx
    obtain ⟨xs,active⟩:=mem_filter.mp hx
    have eq:=hits x xs
    unfold Row.err at eq ⊢
    rw [←aa,←bb,eval_mul,eval_mul,mul_assoc,←mul_sub] at eq
    exact (mul_eq_zero.mp eq).resolve_left active

private theorem Frame.slope_pair {s : Finset K} {v : K→K} (F : Frame s v)
    {x : K} (hx : x∈s) : F.left.a.eval x ≠ 0 ∨ F.right.a.eval x ≠ 0 := by
  classical
  by_contra! both
  have lb : F.left.b.eval x=0 := by simpa [Row.err,both.1] using F.lhit x hx
  have rb : F.right.b.eval x=0 := by simpa [Row.err,both.2] using F.rhit x hx
  have rem : nodes s=nodes (s.erase x)*(«X»-C x) :=
    (s.prod_erase_mul (fun y=>(«X»-C y : K[X])) hx).symm
  have identity:=congrArg (fun p:K[X]=>p.derivative.eval x) F.det_eq
  simp [Row.det,rem,derivative_mul,derivative_sub,both.1,both.2,lb,rb,
    F.scalar_ne,eval_nodes_ne (notMem_erase x s)] at identity

private theorem coprime_at {p : K[X]} {x:K} (h:p.eval x≠0) : IsCoprime p («X»-C x) := by
  have div : «X»-C x ∣ p-C (p.eval x) := by apply dvd_iff_isRoot.mpr;simp [IsRoot]
  obtain ⟨d,hd⟩ := div
  refine ⟨C (p.eval x)⁻¹,-C (p.eval x)⁻¹*d,?_⟩
  have inv : C (p.eval x)⁻¹*C (p.eval x)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ h,C_1]
  linear_combination C (p.eval x)⁻¹*hd + inv

private theorem det_bound (F G : Row K) : (F.det G).natDegree+1 ≤ F.graphDegree+G.graphDegree := by
  have h:=natDegree_sub_le (F.a*G.b) (G.a*F.b)
  have h₁:=natDegree_mul_le (p:=F.a) (q:=G.b)
  have h₂:=natDegree_mul_le (p:=G.a) (q:=F.b)
  unfold Row.graphDegree Row.det at *
  omega

/-- An independent interpolation row gives a primitive full-point graph of
the complementary degree, even when both shifted degrees coincide. -/
theorem Frame.full_graph [Infinite K] {s : Finset K} {v : K→K} (F : Frame s v)
    (ordered : F.l≤F.r) (short : F.l<s.card) :
    ∃ G : Row K,G.primitive ∧ G.graphDegree=F.r ∧ ∀x∈s,G.err v x=0 := by
  classical
  let rejected:=s.image (fun x=>F.right.a.eval x/F.left.a.eval x)
  obtain ⟨t,ok⟩:=rejected.exists_notMem
  let G:=cancel F.left F.right t
  have nz (x) (hx:x∈s) : G.a.eval x≠0 := by
    change (F.right.a-C t*F.left.a).eval x≠0
    simp only [eval_sub,eval_mul,eval_C,sub_ne_zero]
    intro eq
    by_cases z:F.left.a.eval x=0
    · have r := (F.slope_pair hx).resolve_left (not_not.mpr z)
      exact r (by rw [eq,z,mul_zero])
    · apply ok
      apply mem_image.mpr
      exact ⟨x,hx,(div_eq_iff z).mpr eq⟩
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<s.card by omega)
  have gn : G.a≠0 := fun z=>nz x hx (by rw [z,eval_zero])
  have det : F.left.det G=F.left.det F.right := by dsimp [G,cancel,Row.det];ring
  have dc := det.trans F.det_eq
  have left := F.left_active short
  have exactD : (F.left.det G).natDegree=s.card := by rw [dc,natDegree_C_mul F.scalar_ne,nodes_degree]
  have size:=det_bound F.left G
  have large:G.graphDegree≤F.r:=fits_degree (cancel_fit F.lfit F.rfit t (Or.inl ordered)) gn
  have little:=fits_degree F.lfit left
  have pair:=F.total
  rw [exactD] at size
  refine ⟨G,⟨gn,?_⟩,by omega,?_⟩
  · have cp : IsCoprime G.a (nodes s) := IsCoprime.prod_right (fun y h=>coprime_at (nz y h))
    obtain ⟨u,w,bz⟩ := cp
    let inv : K[X] := C F.scalar⁻¹
    have unit : inv*C F.scalar=(1:K[X]) := by dsimp [inv];rw [←C_mul,inv_mul_cancel₀ F.scalar_ne,C_1]
    have nd : nodes s=inv*F.left.det G := by rw [dc,←mul_assoc,unit,one_mul]
    rw [nd] at bz
    refine ⟨u-w*inv*F.left.b,w*inv*F.left.a,?_⟩
    unfold Row.det at bz
    linear_combination bz
  · intro y hy
    rw [show G=cancel F.left F.right t from rfl,cancel_err,F.rhit y hy,F.lhit y hy]
    ring

/-- The qualitative alternatives tested by the terminal-grade receipts. -/
theorem interpolation_alternatives [Infinite K] (s : Finset K) (v : K→K) (enough : 2≤s.card) :
    ∃ l : ℕ, 1≤l ∧ l≤(s.card+1)/2 ∧
      (∃ (G : Row K) (t : Finset K), G.primitive ∧ t⊆s ∧
        G.graphDegree≤l ∧ s.card+G.graphDegree≤t.card+l ∧ ∀ x∈t,G.err v x=0) ∧
      (∃ G : Row K,G.primitive ∧ G.graphDegree=s.card+1-l ∧ ∀x∈s,G.err v x=0) := by
  classical
  obtain ⟨F₀⟩:=frame_exists s v
  obtain ⟨F,sorted⟩ : ∃ F:Frame s v,F.l≤F.r := by
    by_cases h:F₀.l≤F₀.r
    · exact ⟨F₀,h⟩
    · exact ⟨F₀.swap,Nat.le_of_not_ge h⟩
  have total:=F.total
  have short:F.l<s.card:=by omega
  have nz:=F.left_active short
  have cap:=fits_degree F.lfit nz
  have pos:1≤F.left.graphDegree := (Nat.succ_le_succ (Nat.zero_le _)).trans (le_max_left ..)
  obtain ⟨G,t,prim,sub,kept,hits⟩ := primitive_part F.left v s nz F.lhit
  have ct:=card_le_card sub
  refine ⟨F.l,by omega,by omega,⟨G,t,prim,sub,by omega,by omega,hits⟩,?_⟩
  simpa only [show s.card+1-F.l=F.r by omega] using F.full_graph sorted short

#print axioms interpolation_alternatives
end
end Research6966.Pade

end Merged_R6966ProofPadeClassification

-- merged module R6966ProofPadeCoverage
section Merged_R6966ProofPadeCoverage

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K:Type*} [Field K]

def Row.scale (F : Row K) (c:K) : Row K := ⟨C c*F.a,C c*F.b⟩

theorem Row.err_scale (F:Row K) (c:K) (v:K→K) (x:K) :
    (F.scale c).err v x=c*F.err v x := by simp [Row.scale,Row.err];ring

theorem Row.degree_scale (F : Row K) {c:K} (nz:c≠0) :
    (F.scale c).graphDegree=F.graphDegree := by simp [Row.graphDegree,Row.scale,natDegree_C_mul nz]

theorem scale_of_det_zero {F G : Row K} (f:F.primitive) (g:G.primitive)
    (d:F.det G=0) : ∃ t : K,t≠0 ∧ G=F.scale t := by
  classical
  have eq : F.a*G.b=G.a*F.b := sub_eq_zero.mp d
  have fg : F.a∣G.a := f.2.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right ..)
  have gf : G.a∣F.a := g.2.dvd_of_dvd_mul_right (eq.symm ▸ dvd_mul_right ..)
  obtain ⟨p,hp⟩:=fg
  have pn : p≠0 := right_ne_zero_of_mul (hp ▸ g.1)
  have sz:=natDegree_le_of_dvd gf f.1
  rw [hp,natDegree_mul f.1 pn] at sz
  have cp:=eq_C_of_natDegree_eq_zero (show p.natDegree=0 by omega)
  have nz:p.coeff 0 ≠ 0 := by intro h;apply pn;rw [cp,h,C_0]
  let c:=p.coeff 0
  have aeq:G.a=C c*F.a := by rw [hp,mul_comm,←cp]
  have beq:G.b=C c*F.b := by
    apply mul_left_cancel₀ f.1
    rw [eq,aeq];ring
  refine ⟨c,nz,?_⟩
  cases G
  cases F
  congr

private def good [DecidableEq K] (F:Row K) (v:K→K) (s:Finset K) :=
  s.filter (fun y=>F.err v y=0)

def misses [DecidableEq K] (F:Row K) (v:K→K) (s:Finset K) :=
  s.filter (fun y=>F.err v y≠0)

private theorem partition [DecidableEq K] (F:Row K) (v:K→K) (s:Finset K) :
    (good F v s).card+(misses F v s).card=s.card :=
  s.card_filter_add_card_filter_not _

private theorem same_of_hits [DecidableEq K] {F G:Row K} (f:F.primitive) (g:G.primitive)
    (v:K→K) (s:Finset K)
    (many:s.card+F.graphDegree+G.graphDegree≤(good F v s).card+(good G v s).card) :
    ∃ t : K,t≠0 ∧ G=F.scale t := by
  classical
  apply scale_of_det_zero f g
  by_contra dn
  let common:=good F v s ∩ good G v s
  have sub : common ⊆ (F.det G).roots.toFinset := by
    intro x hx
    obtain ⟨hf,hg⟩ := mem_inter.mp hx
    have hf' := sub_eq_zero.mp ((mem_filter.mp hf).2 : F.err v x=0)
    have hg' := sub_eq_zero.mp ((mem_filter.mp hg).2 : G.err v x=0)
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots dn).mpr
    simp only [IsRoot,Row.det,eval_sub,eval_mul,←hf',←hg']
    ring
  have cap := (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))
  have tot:=card_union_add_card_inter (good F v s) (good G v s)
  have union : good F v s ∪ good G v s ⊆ s := union_subset (filter_subset ..) (filter_subset ..)
  have size:=card_le_card union
  have dcap:=natDegree_sub_le (F.a*G.b) (G.a*F.b)
  have h₁:=natDegree_mul_le (p:=F.a) (q:=G.b)
  have h₂:=natDegree_mul_le (p:=G.a) (q:=F.b)
  dsimp [common,Row.det] at cap
  unfold Row.graphDegree at many
  omega

/-- Choose disjoint ordinate sets with specified numbers of good and bad
points, even when an ordinate can support either kind of slope. -/
private theorem choose_colours {K : Type*} [DecidableEq K] (g b : Finset K) (n m : ℕ)
    (hg:n≤g.card) (hb:m≤b.card) (hu:n+m≤(g∪b).card) :
    ∃ G B : Finset K,G⊆g ∧ B⊆b ∧ Disjoint G B ∧ G.card=n ∧ B.card=m := by
  classical
  by_cases enough : n≤(g\b).card
  · obtain ⟨G,inG,ng⟩:=exists_subset_card_eq enough
    obtain ⟨B,inB,nb⟩:=exists_subset_card_eq hb
    refine ⟨G,B,inG.trans sdiff_subset,inB,disjoint_left.mpr ?_,ng,nb⟩
    intro x hx hB
    exact (mem_sdiff.mp (inG hx)).2 (inB hB)
  · have split:=card_sdiff_add_card_inter g b
    obtain ⟨D,hin,hd⟩:= exists_subset_card_eq (show n-(g\b).card≤(g∩b).card by omega)
    have db : D⊆b := hin.trans inter_subset_right
    have dg : D⊆g := hin.trans inter_subset_left
    have disj : Disjoint (g\b) D := disjoint_left.mpr (fun x hx h=> (mem_sdiff.mp hx).2 (db h))
    have tot:=card_union_add_card_inter g b
    have remain:=card_sdiff_add_card_eq_card db
    obtain ⟨B,hB,nb⟩:=exists_subset_card_eq (show m≤(b\D).card by omega)
    refine ⟨(g\b)∪D,B,union_subset sdiff_subset dg,hB.trans sdiff_subset,disjoint_left.mpr ?_,?_,nb⟩
    · intro x hx hx'
      obtain ⟨xb,xd⟩:=mem_sdiff.mp (hB hx')
      rcases mem_union.mp hx with e|e
      · exact (mem_sdiff.mp e).2 xb
      · exact xd e
    · rw [card_union_of_disjoint disj];omega

/-- A graph controls every selectable off-graph ordinate in the fibre.
This formulation also covers an infinite ambient set of possible sheets. -/
def Controls (F:Row K) (sheet:K→K→Prop) (c:ℕ) : Prop :=
  ∀ (s:Finset K) (v:K→K), (∀x∈s,sheet x (v x) ∧ F.err v x≠0) →
    s.card+F.graphDegree≤c

theorem global_of_local [DecidableEq K] (sheet:K→K→Prop) (e c limit:ℕ) (gap:2*c<e)
    (initial : ∃ (s:Finset K) (v:K→K),s.card=e ∧ ∀x∈s,sheet x (v x))
    (chooseGraph : ∀ (s:Finset K) (v:K→K),s.card=e → (∀x∈s,sheet x (v x)) →
      ∃ F : Row K,F.primitive ∧ F.graphDegree≤limit ∧ (misses F v s).card+F.graphDegree≤c) :
    ∃ F : Row K,F.primitive ∧ F.graphDegree≤limit ∧ Controls F sheet c := by
  classical
  obtain ⟨s,v,se,known⟩:=initial
  obtain ⟨F,fp,degree,fc⟩:=chooseGraph s v se known
  refine ⟨F,fp,degree,?_⟩
  intro T w off
  by_contra! heavy
  let G₀:=good F v s
  let B₀:=misses F v s
  change B₀.card+F.graphDegree≤c at fc
  let B:=T∪B₀
  let m:=c-F.graphDegree+1
  let n:=e-m
  have partition₀ : G₀.card+B₀.card=e := (partition ..).trans se
  have nm:n+m=e := by dsimp [n,m];omega
  have nG:n≤G₀.card := by dsimp [m,n];omega
  have mB:m≤B.card := by
    have :=card_le_card (subset_union_left (s₁:=T) (s₂:=B₀))
    dsimp [B,m];omega
  have covered : s⊆G₀∪B := by
    intro x hx
    by_cases z:F.err v x=0
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,z⟩)
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hx,z⟩))
  obtain ⟨U,V,gu,bv,disj,nu,mv⟩ := choose_colours G₀ B n m nG mB (nm ▸ se ▸ card_le_card covered)
  let slope (x:K) := if x∈V ∧ x∈T then w x else v x
  have badV (x) (hx:x∈V) : sheet x (slope x) ∧ F.err slope x≠0 := by
    rcases mem_union.mp (bv hx) with xt|xb
    · simpa [slope,Row.err,hx,xt] using off x xt
    · by_cases xt:x∈T
      · simpa [slope,Row.err,hx,xt] using off x xt
      · have hz:=mem_filter.mp xb
        simpa [slope,Row.err,hx,xt] using And.intro (known x hz.1) hz.2
  have goodU (x) (hx:x∈U) : sheet x (slope x) ∧ F.err slope x=0 := by
    have nv : x∉V := fun hv=>disjoint_left.mp disj hx hv
    have hz := mem_filter.mp (gu hx)
    simpa [slope,Row.err,nv] using And.intro (known x hz.1) hz.2
  let S:=U∪V
  have cs:S.card=e := by dsimp [S];rw [card_union_of_disjoint disj,nu,mv,nm]
  obtain ⟨G,gp,_,gc⟩ := chooseGraph S slope cs (by
    intro x hx;rcases mem_union.mp hx with h|h
    · exact (goodU x h).1
    · exact (badV x h).1)
  have us : U⊆good F slope S := fun x hx=>mem_filter.mpr ⟨mem_union_left _ hx,(goodU x hx).2⟩
  have gcount:=partition G slope S
  have many:=card_le_card us
  obtain ⟨t,tn,rfl⟩:=same_of_hits fp gp slope S (by dsimp [n,m] at *;omega)
  have subset : V⊆misses (F.scale t) slope S := by
    intro x hx
    exact mem_filter.mpr ⟨mem_union_right _ hx,by rw [Row.err_scale];exact mul_ne_zero tn (badV x hx).2⟩
  have := card_le_card subset
  rw [Row.degree_scale F tn] at gc
  dsimp [m] at mv
  omega

#print axioms global_of_local

/-- Two global controls for the same sheets define the same rational graph. -/
theorem unique_control (sheet : K→K→Prop) (e c : ℕ) (gap : 2*c<e)
    (initial : ∃ (s:Finset K) (v:K→K),s.card=e ∧ ∀x∈s,sheet x (v x))
    {F G:Row K} (fp:F.primitive) (gp:G.primitive)
    (fc:Controls F sheet c) (gc:Controls G sheet c) :
    ∃ t:K,t≠0 ∧ G=F.scale t := by
  classical
  obtain ⟨s,v,size,sel⟩ := initial
  have count {Q : Row K} (qc:Controls Q sheet c) :
      (misses Q v s).card+Q.graphDegree≤c :=
    qc _ v (fun x hx=> ⟨sel x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩)
  have b₁ := count fc
  have b₂ := count gc
  have h₁ := partition F v s
  have h₂ := partition G v s
  exact same_of_hits fp gp v s (by omega)

theorem Row.primitive_scale {F : Row K} (p : F.primitive) {c:K} (nz:c≠0) :
    (F.scale c).primitive := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr nz) p.1,?_⟩
  obtain ⟨u,w,bez⟩:=p.2
  use u*C c⁻¹,w*C c⁻¹
  change u*C c⁻¹*(C c*F.a)+w*C c⁻¹*(C c*F.b)=1
  have inv:C c⁻¹*C c=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ nz,C_1]
  calc
    _ = (C c⁻¹*C c)*(u*F.a+w*F.b) := by ring
    _ = _ := by rw [inv,bez,one_mul]

theorem Controls.scale {F:Row K} {sheet:K→K→Prop} {c:ℕ} (h:Controls F sheet c)
    {t:K} (nz:t≠0) : Controls (F.scale t) sheet c := by
  intro s v hv
  rw [Row.degree_scale _ nz]
  exact h s v (fun x hx => ⟨(hv x hx).1,fun eq=>(hv x hx).2 (by rw [Row.err_scale,eq,mul_zero])⟩)

theorem unique_monic_control (sheet : K→K→Prop) (e c : ℕ) (gap : 2*c<e)
    (initial : ∃ (s:Finset K) (v:K→K),s.card=e ∧ ∀x∈s,sheet x (v x))
    {F G:Row K} (fp:F.primitive) (gp:G.primitive) (fm:F.a.Monic) (gm:G.a.Monic)
    (fc:Controls F sheet c) (gc:Controls G sheet c) : G=F := by
  obtain ⟨u,nu,rfl⟩:=unique_control sheet e c gap initial fp gp fc gc
  have h:u=1 := (fm.leadingCoeff_C_mul u).symm.trans gm
  cases F
  simp [h,Row.scale]

#print axioms unique_monic_control
end
end Research6966.Pade

end Merged_R6966ProofPadeCoverage

end Merged6967_R6966ProofPadeCoverage
